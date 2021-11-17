.. _glossary:


Glossary
~~~~~~~~~~

.. code-block:: table
	+---------------------------+------------------------------------+
	| Term                      |           Description              |
	+===========================+====================================+
	| DPoR                      | Short for *Dynamic Proof of*       |
	|                           | *Reputation*. It is the consensus  |
	|                           | algorithm among proposers.         |
	+---------------------------+------------------------------------+
	| LBFT                      | Short for *Lightweight Byzantine*  |
	|                           | *Fault Tolerance*. It is a         |
	|                           | consensus algorithm inspired by    |
	|                           | PBFT.                              |
	+---------------------------+------------------------------------+
	| LBFT 2.0                  | An improved version of LBFT.       |
	|                           | It is the current consensus        |
	|                           | algorithm among                    |
	|                           | validators.                        |
	+---------------------------+------------------------------------+
	| Validators Committee      | A group of users that can validate |
	|                           | a newly proposed block.            |
	+---------------------------+------------------------------------+
	| Validator                 | A member of validators committee.  |
	+---------------------------+------------------------------------+
	| Proposers Committee       | A group of users elected for a     |
	|                           | certain term that can propose      |
	|                           | blocks.                            |
	+---------------------------+------------------------------------+
	| Proposer                  | A member of proposers committee    |
	|                           | that can can proposes a new block  |
	|                           | in this view.                      |
	+---------------------------+------------------------------------+
	| Civilian                  | All users except the proposer and  |
	|                           | validators from the committee.     |
	+---------------------------+------------------------------------+
	| RNode                     | Short for *reputation node*.       |
	|                           | By depositing 200k tokens in       |
	|                           | reputation pool, a node            |
	|                           | can become an RNode.               |
	+---------------------------+------------------------------------+
	| Economy node              | By depositing 20k tokens in        |
	|                           | economy node, a node can become an |
	|                           | economy node. Sometimes it is      |
	|                           | abbreviated into *ENode*.          |
	+---------------------------+------------------------------------+
	| Industry node             | The node held CPChain partners.    |
	|                           | It can also propose blocks like    |
	|                           | other RNodes.                      |
	+---------------------------+------------------------------------+
	| Seal                      | A unforgeable signature indicating |
	|                           | the proposer of corresponding      |
	|                           | for a certain block number.        |
	+---------------------------+------------------------------------+
	| Sigs                      | An array of unforgeable signatures |
	|                           | the proposer of corresponding      |
	|                           | for a certain block number.        |
	+---------------------------+------------------------------------+
	| Quorum                    | A quorum refers to a subset of     |
	|                           | committee members that can         |
	|                           | represent the whole committee      |
	|                           | to proceed to next state.          |
	+---------------------------+------------------------------------+
	| Strong Quorum             | A quorum of 2f+1 members. It       |
	|                           | is used in normal cases. Unless    |
	|                           | otherwise specified, *quorum* is   |
	|                           | always referring to strong quorum. |
	+---------------------------+------------------------------------+
	| Weak Quorum               | A quorum of f+1 members. It is     |
	|                           | only used in impeach cases.        |
	+---------------------------+------------------------------------+
	| Certificate               | a validator has a certificate if   |
	|                           | it is a member of a quorum.        |
	|                           | holding a certificate indicates it |
	|                           | can enter the next state           |
	+---------------------------+------------------------------------+
	| Strong Certificate        | The certificate obtained by a      |
	|                           | strong quorum.                     |
	+---------------------------+------------------------------------+
	| Weak Certificate          | The certificate obtained by a      |
	|                           | weak quorum.                       |
	+---------------------------+------------------------------------+
	| P-Certificate             | A validator has a P-certificate    |
	|                           | if it has 2f+1 PREPARE messages    |
	|                           | or f+1 impeach PREPARE messages    |
	|                           | for a certain block number.        |
	+---------------------------+------------------------------------+
	| C-Certificate             | A validator has a C-certificate    |
	|                           | if it has 2f+1 COMMIT messages     |
	|                           | or f+1 impeach COMMIT messages     |
	|                           | for a certain block number.        |
	+---------------------------+------------------------------------+
	| Impeachment               | If a validator suspects the propo  |
	|                           | ser is faulty or non-responding,   |
	|                           | it activate an impeachment process.|
	+---------------------------+------------------------------------+
	| Impeachment block         | In an impeachment, a validator is  |
	|                           | aiming to propose an impeach block |
	|                           | on behalf of the a faulty proposer.|
	+---------------------------+------------------------------------+
	| Term                      | A term refers a period that a batch|
	|                           | of proposers elected for a certain |
	|                           | proposers committee. Term is a     |
	|                           | monotone increasing integer, whose |
	|                           | value is added by one each time    |
	|                           | it changes.                        |
	+---------------------------+------------------------------------+
	| Epoch                     | An obsolete variable name for      |
	|                           | *term*.                            |
	|                           |                                    |
	+---------------------------+------------------------------------+
	| TermLen                   | Short for term length. It refers to|
	|                           | the number of proposers in a       |
	|                           | certain term. This value limits    |
	|                           | the size of proposers committee,   |
	|                           | and remains a constant unless the  |
	|                           | consensus model adjusts.           |
	+---------------------------+------------------------------------+
	| View                      | Available values of *view* are     |
	|                           | 0,1, and 2. It represents the      |
	|                           | sequence number of the block       |
	|                           | sealed by any proposer. Each view  |
	|                           | contains 12 blocks and their       |
	|                           | corresponding proposers.           |
	+---------------------------+------------------------------------+
	| Round                     | An obsolete variable name for      |
	|                           | *view*.                            |
	|                           |                                    |
	+---------------------------+------------------------------------+
	| ViewLen                   | A proposer is able to propose one  |
	|                           | or more blocks when it comes to its|
	|                           | view. The number of blocks it can  |
	|                           | propose is ViewLen. It is also     |
	|                           | fixed unless the consensus model   |
	|                           | adjusts.                           |
	+---------------------------+------------------------------------+
	| Period                    | Minimum time interval between two  |
	|                           | consecutive blocks.                |
	|                           | The value is set to 10 seconds.    |
	+---------------------------+------------------------------------+
