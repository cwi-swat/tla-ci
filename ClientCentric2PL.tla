-------------------------- MODULE ClientCentric2PL --------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets, Util
CONSTANTS transactions, resources

(*
2PL/2PC where processes interleave

Assumes that no messages are lost, but can be received out of order.

2PC for atomicity.
2PL for isolation => serializability
No deadlock, because TM is allowed to abort
*)

\* Client Centric instance for checking consistency levels
CC == INSTANCE ClientCentric WITH Keys <- resources, Values <- 0..10 \* Nat doesn't work for some reason

w(k,v) == CC!w(k,v)
r(k,v) == CC!r(k,v)

(* --algorithm 2pl
variables
\*  append send in the system
  msgs = {},
\*  reads and writes per transaction id
  operations = [ tId \in transactions |-> <<>> ]
  ;

define
  InitialState == [k \in resources |-> 0]
end define;
  
macro sendMessage(msg) begin
  msgs := msgs \union {msg};
end macro

fair process tm \in transactions
begin
  INIT: sendMessage([id |-> self, type |-> "VoteRequest"]);
  WAIT: either \* receive commit votes
    await \A rm \in resources: [id |-> self, type |-> "VoteCommit", rm |-> rm] \in msgs;
    sendMessage( [id |-> self, type |-> "GlobalCommit"]);
    goto COMMIT;
  or \* receive at least 1 abort votes
    await \E rm \in resources: [id |-> self, type |-> "VoteAbort", rm |-> rm] \in msgs;
    sendMessage([id |-> self, type |-> "GlobalAbort"]);
    goto ABORT;
  or \* or timeout, solves deadlock when two transactions lock each others resources
    sendMessage([id |-> self, type |-> "GlobalAbort"]);
    goto ABORT;
  end either;
  ABORT: goto Done;
  COMMIT: goto Done;
end process

fair process tr \in resources
  variables maxTxs = 5,
            voted = {}, committed = {}, aborted = {},
            state = 0;
begin TR_INIT:
while maxTxs >= 0 do
  either skip; \* skip to not deadlock
  or \* Wait on VoteRequest
    with tId \in transactions \ voted do 
      await [id |-> tId, type |-> "VoteRequest"] \in msgs;
      either \* If preconditions hold, VoteCommit, else VoteAbort
        sendMessage([id |-> tId, type |-> "VoteCommit", rm |-> self]);
        voted := voted \union {tId};
      or 
        sendMessage([id |-> tId, type |-> "VoteAbort", rm |-> self]);
        voted := voted \union {tId};
        aborted := aborted \union {tId};
        goto STEP;
      end either;
    end with;
  READY: \* Wait on Commit/Abort  
    either \* receive GlobalAbort
      with tId \in voted \ committed do 
        await [id |-> tId, type |-> "GlobalCommit"] \in msgs;
        committed := committed \union {tId};
\*      Add read and write operations of local values to the relevant transaction's operations
        operations[tId] := operations[tId] \o << r(self, state), w(self, state+1) >>;
        state := state + 1;
      end with;
    or \* receive GlobalCommit
      with tId \in voted \ aborted do 
        await [id |-> tId, type |-> "GlobalAbort"] \in msgs;
        aborted := aborted \union {tId};
      end with;
    end either;
  end either;
  STEP: maxTxs := maxTxs - 1;
end while;
end process;

end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-efe09d31a02f8d81e9b79186e3a46bba
VARIABLES msgs, operations, pc

(* define statement *)
InitialState == [k \in resources |-> 0]

VARIABLES maxTxs, voted, committed, aborted, state

vars == << msgs, operations, pc, maxTxs, voted, committed, aborted, state >>

ProcSet == (transactions) \cup (resources)

Init == (* Global variables *)
        /\ msgs = {}
        /\ operations = [ tId \in transactions |-> <<>> ]
        (* Process tr *)
        /\ maxTxs = [self \in resources |-> 5]
        /\ voted = [self \in resources |-> {}]
        /\ committed = [self \in resources |-> {}]
        /\ aborted = [self \in resources |-> {}]
        /\ state = [self \in resources |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in transactions -> "INIT"
                                        [] self \in resources -> "TR_INIT"]

INIT(self) == /\ pc[self] = "INIT"
              /\ msgs' = (msgs \union {([id |-> self, type |-> "VoteRequest"])})
              /\ pc' = [pc EXCEPT ![self] = "WAIT"]
              /\ UNCHANGED << operations, maxTxs, voted, committed, aborted, 
                              state >>

WAIT(self) == /\ pc[self] = "WAIT"
              /\ \/ /\ \A rm \in resources: [id |-> self, type |-> "VoteCommit", rm |-> rm] \in msgs
                    /\ msgs' = (msgs \union {([id |-> self, type |-> "GlobalCommit"])})
                    /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
                 \/ /\ \E rm \in resources: [id |-> self, type |-> "VoteAbort", rm |-> rm] \in msgs
                    /\ msgs' = (msgs \union {([id |-> self, type |-> "GlobalAbort"])})
                    /\ pc' = [pc EXCEPT ![self] = "ABORT"]
                 \/ /\ msgs' = (msgs \union {([id |-> self, type |-> "GlobalAbort"])})
                    /\ pc' = [pc EXCEPT ![self] = "ABORT"]
              /\ UNCHANGED << operations, maxTxs, voted, committed, aborted, 
                              state >>

ABORT(self) == /\ pc[self] = "ABORT"
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << msgs, operations, maxTxs, voted, committed, 
                               aborted, state >>

COMMIT(self) == /\ pc[self] = "COMMIT"
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << msgs, operations, maxTxs, voted, committed, 
                                aborted, state >>

tm(self) == INIT(self) \/ WAIT(self) \/ ABORT(self) \/ COMMIT(self)

TR_INIT(self) == /\ pc[self] = "TR_INIT"
                 /\ IF maxTxs[self] >= 0
                       THEN /\ \/ /\ TRUE
                                  /\ pc' = [pc EXCEPT ![self] = "STEP"]
                                  /\ UNCHANGED <<msgs, voted, aborted>>
                               \/ /\ \E tId \in transactions \ voted[self]:
                                       /\ [id |-> tId, type |-> "VoteRequest"] \in msgs
                                       /\ \/ /\ msgs' = (msgs \union {([id |-> tId, type |-> "VoteCommit", rm |-> self])})
                                             /\ voted' = [voted EXCEPT ![self] = voted[self] \union {tId}]
                                             /\ pc' = [pc EXCEPT ![self] = "READY"]
                                             /\ UNCHANGED aborted
                                          \/ /\ msgs' = (msgs \union {([id |-> tId, type |-> "VoteAbort", rm |-> self])})
                                             /\ voted' = [voted EXCEPT ![self] = voted[self] \union {tId}]
                                             /\ aborted' = [aborted EXCEPT ![self] = aborted[self] \union {tId}]
                                             /\ pc' = [pc EXCEPT ![self] = "STEP"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << msgs, voted, aborted >>
                 /\ UNCHANGED << operations, maxTxs, committed, state >>

STEP(self) == /\ pc[self] = "STEP"
              /\ maxTxs' = [maxTxs EXCEPT ![self] = maxTxs[self] - 1]
              /\ pc' = [pc EXCEPT ![self] = "TR_INIT"]
              /\ UNCHANGED << msgs, operations, voted, committed, aborted, 
                              state >>

READY(self) == /\ pc[self] = "READY"
               /\ \/ /\ \E tId \in voted[self] \ committed[self]:
                          /\ [id |-> tId, type |-> "GlobalCommit"] \in msgs
                          /\ committed' = [committed EXCEPT ![self] = committed[self] \union {tId}]
                          /\ operations' = [operations EXCEPT ![tId] = operations[tId] \o << r(self, state[self]), w(self, state[self]+1) >>]
                          /\ state' = [state EXCEPT ![self] = state[self] + 1]
                     /\ UNCHANGED aborted
                  \/ /\ \E tId \in voted[self] \ aborted[self]:
                          /\ [id |-> tId, type |-> "GlobalAbort"] \in msgs
                          /\ aborted' = [aborted EXCEPT ![self] = aborted[self] \union {tId}]
                     /\ UNCHANGED <<operations, committed, state>>
               /\ pc' = [pc EXCEPT ![self] = "STEP"]
               /\ UNCHANGED << msgs, maxTxs, voted >>

tr(self) == TR_INIT(self) \/ STEP(self) \/ READY(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in transactions: tm(self))
           \/ (\E self \in resources: tr(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in transactions : WF_vars(tm(self))
        /\ \A self \in resources : WF_vars(tr(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-346d41f8806fe21f1d5c7e0a276c2fbf

Message == [id: transactions, type: {"VoteRequest", "GlobalCommit", "GlobalAbort"}] \union
  [id: transactions, type: {"VoteAbort", "VoteCommit"}, rm: resources]

TypeOK == /\ msgs \subseteq Message
          /\ \A res \in resources: 
             /\ committed[res] \in SUBSET transactions
             /\ aborted[res] \in SUBSET transactions
             /\ voted[res] \in SUBSET transactions

Atomicity == 
\* When resource are done
  \A id \in transactions: pc[id]="Done" => 
    \A a1,a2 \in resources:
          \* no participants differ from result aborted or committed
        ~ /\ id \in aborted[a1] 
          /\ id \in committed[a2]
          
AllTransactionsFinish == <>(\A t \in transactions: pc[t] = "Done")

ccTransactions == Range(operations)

CCTypeOK == CC!TypeOKT(ccTransactions)

Serializable == 
\*  PrintT(<<"InitialState", InitialState>>) /\
\*  PrintT(<<"ccTransactions2", ccTransactions2>>) /\
  CC!Serializability(InitialState, ccTransactions)
    
SnapshotIsolation == CC!SnapshotIsolation(InitialState, ccTransactions)
ReadCommitted == CC!ReadCommitted(InitialState, ccTransactions)
ReadUncommitted == CC!ReadUncommitted(InitialState, ccTransactions)

=============================================================================
\* Modification History
\* Last modified Wed Jun 24 13:52:10 CEST 2020 by tim
\* Created Tue Apr 28 16:41:42 CEST 2020 by tim
