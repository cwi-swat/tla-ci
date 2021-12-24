# TLA-CI
TLA+ specifications accompanying paper: Automated Validation of State-Based Client-Centric Isolation with TLA+ (ASYDE'20) (https://doi.org/10.1007/978-3-030-67220-1_4). Based on [Crooks' Isolation](https://dl.acm.org/doi/10.1145/3087801.3087802).

The code can be run with both:

- [TLA+ Toolbox](http://lamport.azurewebsites.net/tla/toolbox.html)
- [TLA+ VSCode plugin](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus)


Contents
- `ClientCentric.tla` contains the definitions of Crooks' Isolation model.
- `ClientCentricPaperExamples.tla` contains some examples from the paper.
   For example `ASSUME test(Serializability(as1, bankTransactions), TRUE)` shows that the banking example is serializable, but the other ordering isn't (`Serializability(as1, bBankTransactions = FALSE`), but is Snapshot Isolatable: `ASSUME test(executionSatisfiesCT(bExecution, CT_SI), TRUE)`.
- The `2PL` related files show how a specification bug in a 2PL/2PC protocol can result in not serializable behavior.

Please contact me for more details.
