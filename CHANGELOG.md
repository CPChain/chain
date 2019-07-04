# CPChain Changelog

## June 2019 Version 0.4.4

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
- Automation Testing Framework
    - Developed based on [Jepsen](https://jepsen.io/).
    - There is a master assumes responsibilities of 
        - starting a local chain;
        - fetching test cases;
        - creating and communicating with several processes
    - The following processes created by the master work independently on the chain.
        - B1 and B2, ran as bootnodes.
        - P1 to P12, ran as proposers.
        - CA, short for contract admin, 
        are used for deploying smart contracts.
        - Bank, used exclusively for providing tokens.
        - IPFA, optional.
    - Each process has its own broker to communicate with the master.
        - The master invokes RPC APIs to send commands to brokers.
    - Each test case runs in several phases.
        - Each process can pause at the end of each phase.
        - After the last phase terminates, 
        the process returns the test log to master.
    - The master is about to run the next test case 
    after it collects logs from all processes.
- Rewards
    - Implement [basic reward](https://docs.cpchain.io/overview/overview.html#basic-rewards)
    and [maintenance reward](https://docs.cpchain.io/overview/overview.html#maintenance-reward)
- APIs
    - Adjusted and optimized RPC and Python APIs from [CPC fusion](https://github.com/CPChain/fusion)

        
