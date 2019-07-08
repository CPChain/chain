.. _test-overview:

Testing Overview
==================

The testing conducted on CPChain is a fundamental part of CPChain continuous integration workflow.

We deploy `Jenkins`_ as the automation server, and `Jepsen`_ as the framework simulating test cases.

.. _`Jenkins`: https://jenkins.io/
.. _`Jepsen`: https://jepsen.io/

In the following sections, we presents our testing framework from different perspectives.

White Box Testing
--------------------------------------

The white box testing is for examining the internal functions and structures of the chain.
Developers clearly know the functionality of all code they test.
The white box testing contains three levels: *unit, integration* and *regression testing*.


Unit Testing
++++++++++++++

The unit testing is written in Golang accompanied with chain code,
which are altogether stored in CPChain `repository`_.
All unit testing files are ending with ``_test.go``.
And each unit testing file contains several testing functions to
examine its corresponding functionality given pairs of input and output.

.. _`repository`: https://bitbucket.org/cpchain/chain/src/master/

The functionality of :ref:`fusion-api` and :ref:`rpc-api` is also tested.


Integration Testing
++++++++++++++++++++++

Some Go files in CPChain import and integrate multiple files
to implement functions in higher levels.
These files also have their corresponding testing files to
conduct on integration testing.


Regression Tesing
++++++++++++++++++++

Each time a certain branch is updated in its remote repository,
`Jenkins`_ activates a regression testing via going through all testing files.
By this means, all unit testing and integration testing can be redone,
ensuring that no bug is introduced in old code blocks.


Black Box Testing
----------------------

The black box testing examines the functionality of the chain
without a priori knowledge on its internal implementation.
In black box testing, a list of test cases is curated to examine whether
the chain can work properly.
Each test case contains three major components:

1. **Scenario**: briefly describe the case;
#. **Steps**: how to reproduce the case;
#. **Expected result**: what is the expected output as a working chain.

Abnormal Consensus Test Cases
++++++++++++++++++++++++++++++++

Consensus is the core of a blockchain.
We need to assure the chain's safety and consistency when facing Byzantine faults
among validators and proposers.
Thus, we design plenty of test cases on consensus, including abnormal and normal ones,
to test the functionality of the chain.
For each possible abnormal scenario, as curated in :ref:`illicit-actions`,
an input and its expected output are designed to simulate it.
This simulation is implemented by adopting `Jepsen`_ framework.

Stability Test Cases
+++++++++++++++++++++++

Stability testing involves the launch, reboot, and abort of
the bootnodes, proposers, validators, civilians and contract administrators.
This testing provides the stability proof of the chain
under extreme cases like black out, connection error, etc.


Mining Test Cases
++++++++++++++++++++++++++

A proposer has its duty to seal and mine a block.
This set of test cases are categorized into several types:

1. Proposer: contain curated test cases in which a proposer conducts different behaviors.
#. Campaign: examine the campaign log, APIs, candidate list, and smart contract.
#. RNode: assure the admission of RNode is correct given different conditions.
#. Reward: guarantee both basic and maintenance reward is correctly calculated and dispensed.
#. Admission Control (AC): make sure he threshold set for minimum CPU capacity works as expected.
#. Validator: test the validity of validator contract and domain.
#. Start and Stop: robustness test by multiple aborting and restarting the chain.


Nemesis Test Cases
+++++++++++++++++++

By adopting Jepsen Nemesis, we can simulate abnormal scenarios like:

1. Delay of sending package
#. Disconnection from the network
#. Crash of a node
#. Time drift (incorrect local clock)

Note that some nemesis test cases may overlap with previously stated cases.


Compatibility Test Cases
+++++++++++++++++++++++++

Compatibility is a major challenge for all decentralized systems,
as not all nodes may update to the latest version.
Similar to the concepts of soft fork and hard fork of Bitcoin,
CPChain also have *soft update* and *hard update*.
In a soft update, old version can still work with the chain.
while in a hard update, old versions are rejected when claiming campaign,
proposing blocks, or even cannot sync with the chain.

Compatibility testing assures that
the chain and all updated nodes are not affected by old version nodes.


Stress Test Cases
++++++++++++++++++


Stress testing is conducted via increasing transactions per second (tps) to
approach the limit of the throughput of the chain.
The stress testing can be divided into two major classes:

    1. Send out transactions in a speed close to our tps limit.
    It can help us test if the chain can maintain stable
    and handle all transactions under this stress.

    2. Send out transactions in a speed outnumbering out tps limit.
    It can help us test if the chain can maintain stable
    and if the outnumbered transactions can be postponed to successive blocks.


Anti-DDoS Attack
---------------------

DDoS Attack, a.k.a., Distributed Denial of Service attack,
is a major challenge all distributed systems have to confront.
By uniting multiple servers, DDoS can send out a flood of requests to a single target,
in order to occupying all computing resources or bandwidth of the target.
A targeted machine flooded with these superfluous requests will lose its functionality
to answer any legal requests.

DDoS ia a major concern for classic blockchains like Bitcoin and Ethereum,
due to their decentralized structure.
Malfunctions of each single node or a small portion has literally no impact to the whole chain.
However, validators of CPChain can be a latent targets for DDoS attacks.
Thus, we design the following scheme for potential DDoS attack:

1. Set up multiple trusted nodes as default proposers.

2. Validators hold a while list that contains all default proposers.

3. Each validator has a monitor on its computing resources.
    Once the validator is under high performance for a long time,
    it considers it is under DDoS attack, and activate the white list.
    The white list will reject all nodes except default proposers in the level of firewall.

4. When any of the following conditions satisfies, the while list is removed:
    * No DDoS attack detected in a period of time;
    * The white list has been activated for a long time;
    * Deactivate the white list manually.



Formal Specification
----------------------


Software testing neither reflects any glitch,
nor proves the completeness of a piece of code in terms of mathematics.
Thus, we introduce formal specification to the chain.

Formal specification languages describes a program at a higher level
through a certain form or specification,
such that it can determine whether it is mathematically correct.
Formal verification is especially important in highly parallel programs,
where deadlocks and race conditions are vital issues.

To this end, we will use TLA+ as a formal specification language
to ensure the correctness of the algorithm of CPChain.
