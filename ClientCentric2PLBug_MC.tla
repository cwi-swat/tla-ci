---- MODULE ClientCentric2PLBug_MC ----
EXTENDS ClientCentric2PLBug, TLC

CONSTANTS
t1, t2, t3, t4
CONSTANTS
r1, r2, r3

mc_transactions == {t1,t2,t3}
mc_resources == {r1,r2}
mc_symm == Permutations(mc_transactions) \union Permutations(mc_resources)

SerializabilityDebug == CC!SerializabilityDebug(InitialState, ccTransactions)

=============================================================================
