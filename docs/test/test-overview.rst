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

Some Go files in CPChain imports and integrates multiple files.
These files also have their corresponding testing files to
conducting on integration testing.


Regression Tesing
++++++++++++++++++++

Each time a certain branch is updated in its remote repository,
`Jenkins`_ activates a regression testing going through all testing files.
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


Private Transaction Test Cases
+++++++++++++++++++++++++++++++


These cases examines the functionality of
InterPlanetary File System (IPFS) server as well as private transactions.
