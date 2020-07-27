--------------------------- MODULE ClientCentricPaperExamples ---------------------------
EXTENDS ClientCentric, Sequences, FiniteSets, TLC, Integers

x == "x"
y == "y"
z == "z"
keys == {x,y,z}

\* example figure 2
s0 == [k \in keys |-> 0] \* equivalent to ("x" :> 0) @@ ("y" :> 0) @@ ("z" :> 0)
s1 == (x :> 1) @@ (y :> 0) @@ (z :> 0)
s2 == (x :> 1) @@ (y :> 1) @@ (z :> 0)
s3 == (x :> 1) @@ (y :> 2) @@ (z :> 1)

\* operations
r2 == r(y,1) \* [op |-> "read", key |-> "y", value |-> 1]
r3 == r(z,0) \* [op |-> "read", key |-> "z", value |-> 0]
r4 == r(x,0) \* [op |-> "read", key |-> "x", value |-> 0]
r5 == r(z,1) \* [op |-> "read", key |-> "z", value |-> 1]
w1 == w(x,1) \* [op |-> "write", key |-> "x", value |-> 1]

\* transactions
ta == <<w1>>
tb == <<r2, r3>>
tc == <<w(y,1)>>
td == <<
  w(y,2),
  w(z,1)
>>
te == << r4, r5 >>

e1 == [parentState |-> s0, transaction |-> ta ]
e2 == [parentState |-> s2, transaction |-> tb ]
e3 == [parentState |-> s1, transaction |-> tc ]
e4 == [parentState |-> s2, transaction |-> td ]
e5 == [parentState |-> s3, transaction |-> te ]

exampleExecution  == << e1,e3,e2,e4,e5 >>
exampleStates == << s0,s1,s2,s2,s3 >>
transactions == {ta,tb,tc,td,te}

\* TypeOK == /\ transactions \subseteq Transaction
\*           /\ exampleExecution \subseteq Execution

ExampleTypeOK == TypeOK(transactions, exampleExecution) 

\* to let model checker run
Init == FALSE /\ Keys = 0
Next == FALSE /\ Keys' = Keys

ASSUME test(executionStates(exampleExecution), exampleStates)
\* parentState
ASSUME test(parentState(exampleExecution, ta), s0)
ASSUME test(parentState(exampleExecution, tc), s1)
ASSUME test(parentState(exampleExecution, td), s2)

ASSUME test(ReadStates(exampleExecution, w1, ta), { s0 })

ASSUME test(WriteSet(ta), {x})

\* examples from paper
\* "Looking again at Figure 2, s2 is a complete state for transaction Tb , as it is in the set of candidate read states of both r2 (y,y1 ) ({s2 }) and r3(z,z0) ({s0,s1,s2})."
ASSUME test(ReadStates(exampleExecution, r2, tb), { s2 })
ASSUME test(ReadStates(exampleExecution, r3, tb), { s0,s1,s2 })
ASSUME test(Complete(exampleExecution, tb, s2), TRUE)
ASSUME test(SeqToSet(executionStates(exampleExecution)), {s0,s1,s2,s3})
ASSUME \E state \in SeqToSet(executionStates(exampleExecution)):
  Complete(exampleExecution, tb, state)

\* "A complete state is not guaranteed to exist: no such state exists for Te , as the sole candidate read states of r4 and r5 (respectively, s0 and s3) are distinct."
ASSUME test(ReadStates(exampleExecution, r4, te), { s0 })
ASSUME test(ReadStates(exampleExecution, r5, te), { s3 })
ASSUME test(SeqToSet(executionStates(exampleExecution)), {s0,s1,s2,s3})
ASSUME Complete(exampleExecution, te, s0) = FALSE
ASSUME Complete(exampleExecution, te, s1) = FALSE
ASSUME Complete(exampleExecution, te, s2) = FALSE
ASSUME Complete(exampleExecution, te, s3) = FALSE
ASSUME ~\E state \in SeqToSet(executionStates(exampleExecution)): 
  Complete(exampleExecution, te, state)
ASSUME test(executionSatisfiesCT(exampleExecution, CT_SER), FALSE)

\* extra tests
transactionWithoutTe == {ta,tb,tc,td}
executionWithoutTe == << e1,e3,e2,e4 >>
ASSUME test(parentState(executionWithoutTe, ta), s0)
\* "By convention, write operations have read states too: for a write operation in T , they include all states in Se up to and including T's parent state."
ASSUME test(ReadStates(executionWithoutTe, w1, ta), { s0 })
ASSUME Complete(executionWithoutTe, ta, s0) = TRUE
ASSUME test(executionTransactions(executionWithoutTe), transactionWithoutTe)
ASSUME test(executionSatisfiesCT(executionWithoutTe, CT_SER), TRUE)

\* check for which isolation level all transaction in example hold
ASSUME test(executionSatisfiesCT(exampleExecution, CT_SER), FALSE)
ASSUME test(executionSatisfiesCT(exampleExecution, CT_SI), FALSE)
ASSUME test(executionSatisfiesCT(exampleExecution, CT_RC), TRUE)
ASSUME test(executionSatisfiesCT(exampleExecution, CT_RU), TRUE)

\* PermSeqs
ASSUME test(PermSeqs({"t1","t2","t3"}), {<<"t1", "t2", "t3">>, <<"t1", "t3", "t2">>, <<"t2", "t1", "t3">>, <<"t2", "t3", "t1">>, <<"t3", "t1", "t2">>, <<"t3", "t2", "t1">>})
\* should give all possible executions given transactions
execE1 == << [parentState |-> s0, transaction |-> ta ], [parentState |-> s1, transaction |-> tb ] >>
execE2 == << [parentState |-> s0, transaction |-> tb ], [parentState |-> s0, transaction |-> ta ] >>
ASSUME test(executions(s0, {ta,tb}), { execE1,execE2 })

\* Isolation tests for example transactions (exists a execution)
\* Execution found by Serializability(s0, transactions)
exampleSerializableExecutionCP ==               
   << [ parentState |-> [x |-> 0, y |-> 0, z |-> 0],
        transaction |-> <<[op |-> "write", key |-> "y", value |-> 1]>> ],
      [ parentState |-> [x |-> 0, y |-> 1, z |-> 0],
        transaction |->
            << [op |-> "read", key |-> "y", value |-> 1],
               [op |-> "read", key |-> "z", value |-> 0] >> ],
      [ parentState |-> [x |-> 0, y |-> 1, z |-> 0],
        transaction |->
            << [op |-> "write", key |-> "y", value |-> 2],
               [op |-> "write", key |-> "z", value |-> 1] >> ],
      [ parentState |-> [x |-> 0, y |-> 2, z |-> 1],
        transaction |->
            << [op |-> "read", key |-> "x", value |-> 0],
               [op |-> "read", key |-> "z", value |-> 1] >> ],
      [ parentState |-> [x |-> 0, y |-> 2, z |-> 1],
        transaction |-> <<[op |-> "write", key |-> "x", value |-> 1]>> ] >>
exampleSerializableExecution ==               
   << [ parentState |-> s0,
        transaction |-> tc ],
      [ parentState |-> [x |-> 0, y |-> 1, z |-> 0],
        transaction |-> tb ],
      [ parentState |-> [x |-> 0, y |-> 1, z |-> 0],
        transaction |-> td ],
      [ parentState |-> [x |-> 0, y |-> 2, z |-> 1],
        transaction |-> te ],
      [ parentState |-> [x |-> 0, y |-> 2, z |-> 1],
        transaction |-> ta ] >>
ASSUME test(exampleSerializableExecutionCP, exampleSerializableExecution)
ASSUME test(executionSatisfiesCT(exampleSerializableExecution, CT_SER), TRUE)
ASSUME test(Serializability(s0, transactions), TRUE)
ASSUME test(SnapshotIsolation(s0, transactions), TRUE)
ASSUME test(ReadCommitted(s0, transactions), TRUE)
ASSUME test(ReadUncommitted(s0, transactions), TRUE)

\* start and commit time stamps are not specified by the example 
\* ASSUME test(CT_SSER(transactions, exampleExecution), FALSE)

\* Simple Banking Example (figure 3)
\* example A
S == "S"
C == "C"
\* states
as1 == (C :>  30) @@ (S :> 30)
as2 == (C :> -10) @@ (S :> 30)
\* as3 == ("C" :> 30) @@ ("S" :> 30) FAIL

\* transactions
talice == << r(S,30), r(C, 30), w(C,-10) >>
tbob   == << r(S,30), r(C,-10) (* w(S,-10) Write does not happen *) >>

\* execution
ae1 == [parentState |-> as1, transaction |-> talice ]
ae2 == [parentState |-> as2, transaction |-> tbob ]
aExecution  == << ae1, ae2 >>

bankTransactions == {talice, tbob}

BankExampleATypeOK == TypeOK(bankTransactions, aExecution)

ASSUME test(parentState(aExecution, talice), as1)
ASSUME Complete(aExecution, talice, as1)
ASSUME Complete(aExecution, tbob, as2)
\* test isolation levels
ASSUME test(executionSatisfiesCT(aExecution, CT_SER), TRUE) 
ASSUME test(executionSatisfiesCT(aExecution, CT_SI), TRUE)
ASSUME test(executionSatisfiesCT(aExecution, CT_RC), TRUE)
ASSUME test(executionSatisfiesCT(aExecution, CT_RU), TRUE)

ASSUME test(Serializability(as1, bankTransactions), TRUE)
ASSUME test(SnapshotIsolation(as1, bankTransactions), TRUE)
ASSUME test(ReadCommitted(as1, bankTransactions), TRUE)
ASSUME test(ReadUncommitted(as1, bankTransactions), TRUE)

\* talices comes strictly before tbob
bankTimeStamps == (talice :> [start |-> 1, commit |-> 2]) @@ (tbob :> [start |-> 3, commit |-> 4])
ASSUME test(StrictSerializability(as1, bankTransactions, bankTimeStamps), TRUE) 

\* example B
bs1 == (C :>  30) @@ (S :>  30)
bs2 == (C :> -10) @@ (S :>  30)
bs3 == (C :> -10) @@ (S :> -10)

\* transactions
tbAlice == << r(S, 30), r(C,30), w(C,-10) >>
tbBob   == << r(S, 30), r(C,30), w(S,-10) >>
\* tread == <<
\*   [op |-> "read", key |-> "S", value |-> -10],
\*   [op |-> "read", key |-> "C", value |-> -10]
\* >>

bbe1 == [parentState |-> bs1, transaction |-> tbAlice ]
bbe2 == [parentState |-> bs2, transaction |-> tbBob ]
\* bbe3 == [parentState |-> bs3, transaction |-> tread ]
bExecution  == << bbe1, bbe2>>

bBankTransactions == {tbAlice, tbBob}

BankExampleBTypeOK == TypeOK(bBankTransactions, bExecution)

ASSUME test(executionSatisfiesCT(bExecution, CT_SER), FALSE)  \* not Serializable 
ASSUME test(Serializability(as1, bBankTransactions), FALSE)

\* prerequisits for SI
ASSUME \E state \in SeqToSet(executionStates(bExecution)):
  Complete(bExecution, tbAlice, state) \* bs1
ASSUME \E state \in SeqToSet(executionStates(bExecution)):
  Complete(bExecution, tbBob, state) \* bs1
ASSUME NoConf(bExecution, tbAlice, bs1)
ASSUME NoConf(bExecution, tbBob, bs1)
ASSUME test(executionSatisfiesCT(bExecution, CT_SI), TRUE)  \* but is allowed under SI
ASSUME test(SnapshotIsolation(bs1, bBankTransactions), TRUE)

ASSUME test(executionSatisfiesCT(bExecution, CT_RC), TRUE)
ASSUME test(executionSatisfiesCT(bExecution, CT_RU), TRUE)
ASSUME test(ReadCommitted(bs1, bBankTransactions), TRUE)
ASSUME test(ReadUncommitted(bs1, bBankTransactions), TRUE)

\* Some extra tests on CC helper functions 
ASSUME test(effects(s0, <<>>), s0)
ASSUME test(effects(s0, tb), s0)
ASSUME test(effects(s0, ta), s1)
ASSUME test(effects(s1, tc), s2)
ASSUME test(effects(s2, td), s3)

\* test with empty operation
ASSUME test(executions(s0, {<<>>}), {<<[parentState |-> s0, transaction |-> <<>>]>>})

\* Empty transactions should also be Serializable, because they can read from all states
InitalState == ("r1" :> 0 @@ "r2" :> 0)
ccTransactions2 == {<<>>}

emptyTransaction == <<>>
emptyExecution == <<[parentState |-> InitalState, transaction |-> emptyTransaction ]>>

ASSUME Preread(emptyExecution, emptyTransaction) \* TRUE as expected because of \forall operations, so empty operations means TRUE
ASSUME CT_SER(emptyTransaction, emptyExecution)
ASSUME Serializability(InitalState, ccTransactions2)



\* Debug serializability 2PL/2PC
2plr1 == "r1"
2plr2 == "r2"
2plt1 == << r(2plr1,0), r(2plr2,1) >>
2plt2 == << r(2plr1,0), w(2plr1,1), r(2plr2,0), w(2plr2,1) >>
2ple1 == << [ parentState |-> (2plr1 :> 0 @@ 2plr2 :> 0), transaction |-> << r(2plr1,0), r(2plr2,1) >> ],
            [ parentState |-> (2plr1 :> 0 @@ 2plr2 :> 0), transaction |-> << r(2plr1,0), w(2plr1,1), r(2plr2,0), w(2plr2,1) >> ]  >>
2ple2 == << [ parentState |-> (2plr1 :> 0 @@ 2plr2 :> 0), transaction |-> << r(2plr1,0), w(2plr1,1), r(2plr2,0), w(2plr2,1) >> ],
            [ parentState |-> (2plr1 :> 1 @@ 2plr2 :> 1), transaction |-> << r(2plr1,0), r(2plr2,1) >> ] >>     
2plEs == { 2ple1, 2ple2 }

ASSUME CT_SER(2plt1, 2ple1) = FALSE
ASSUME CT_SER(2plt2, 2ple1) = TRUE

ASSUME CT_SER(2plt1, 2ple2) = FALSE
ASSUME CT_SER(2plt2, 2ple2) = TRUE

ASSUME Serializability(InitalState, {2plt1, 2plt2}) = FALSE
\* As expected, because `r(2plr2,1)` makes it non-serializable.

=============================================================================
