.. _test-overview:

Testing
==================

The testing conducted on CPChain is a fundamental part of CPChain continuous integration workflow.

We deploy `Jenkins`_ as the automation server, and `Jepsen`_ as the framework simulating test cases.

.. _`Jenkins`: https://github.com/CPChain/chain/releases
.. _`Jepsen`: https://jepsen.io/

In the following sections, we presents our testing framework from different perspectives.

White Box Testing
--------------------------------------

The white box testing is for examining the internal functions and structures of the chain.
Developers clearly know the functionality of all code they test.
The white box testing contains three levels: *unit, integration* and *regression testing*.


Unit Testing
++++++++++++++

The unit testing is written in Golang accompanied with other code,
which altogether stored in CPChain `repository`.
All unit testing files are ending with `_test.go`.
Each unit testing file contains several testing functions to
examine its corresponding functionality given pairs of input and output.

.. _`repository`: https://bitbucket.org/cpchain/chain/src/master/

The functionality of :ref:`fusion-api` and :ref:`rpc-api` is also tested.


Integration Testing
++++++++++++++++++++++

Some go files in CPChain imports and integrates multiple files.
These files also have their corresponding testing files to
conducting on integration testing.


Regression Tesing
++++++++++++++++++++

Each time a certain branch is changed in its remote repository,
Jenkins activates a regression testing going through all testing files.
By this means, all unit testing and integration testing can be redone,
ensuring that no bug is introduced in old code blocks.


Black Box Testing
----------------------

The black box testing examines the functionality of the chain
without a priori knowledge on its internal implementation.
In black box testing,

Abnormal Test Cases
++++++++++++++++++++

We design plenty of test cases, including abnormal and normal ones,
to test the functionality of the chain.
For each possible abnormal scenario, as curated in :ref:`illicit-actions`,
a input and its expected output is designed to simulate it.
This simulation is implemented by adopting Jepsen framework.

Stability Test Cases
+++++++++++++++++++++++

It





