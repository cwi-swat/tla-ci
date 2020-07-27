---- MODULE ClientCentric2PL_MC ----
EXTENDS ClientCentric2PL, TLC

CONSTANTS
t1, t2, t3, t4
CONSTANTS
r1, r2, r3

mc_transactions == {t1,t2}
mc_resources == {r1,r2}
mc_symm == Permutations(mc_transactions) \union Permutations(mc_resources)

SerializabilityDebug == CC!SerializabilityDebug(InitialState, ccTransactions)

=============================================================================
