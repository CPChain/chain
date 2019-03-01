# CPChain Changelog

## March 2019 Version 0.2.0 (Current)

This release is not compatible with Mainnet Alpha (Version 0.1.0)

Notable Changes

- LBFT 2.0 Consensus
    - Bipartite Committee: 
        - Proposers, exclusively responsible for generating new block.
        - Validators, exclusively responsible for validating newly proposed block.
    - Introduce *Impeachment* to handle faulty or non-responding proposer.
    - Design a finite state machine with five states to implement LBFT 2.0 process
    - Countermeasures for several illicit actions:
        - Double spend attack.
        - Unknown ancestor block.
        - Past and future block.
        - Unrecognized block.
    - Recovery mechanism for lagging validators catching up with the rest.
- Wallet 
    - Android UI 
- Automation Testing Framework
    - Inspired by [Jepsen](https://jepsen.io/).
    - A master starts a local chain and fetch a test case.
    - The master creates following processes which work independently on the chain:
        - B1 and B2, ran as bootnodes.
        - P1 to P12, ran as proposers.
        - CA, short for control admission.
        - Back, ran for refunding.
        - IPFA, optional.
    - Each process has its own broker to communicating with the master
        - The master invokes RPC APIs to send commands to processes
    - Each test case runs in several phases.
        - Each process can pause at the end of each phase
        - After the last phase finishes, the process returns the log to master
        
        
