.. _reward-sm:


Reward Smart Contract
===============================

As described in :ref:`basic-reward`, each season is divided into three parts:
raising (3 days),
lock-up (84 days),
and settlement (3 days).

API
------

There are several APIs in reward contract which are further divided into two classes
**admin** and **investor** according to the authority.

Here we list all APIs below.

Admin API
***************

+-----------------------------------------------------------------+
|                             Admin                               |
+----------------------------------+------------------------------+
| API                              |           Description        |
+==================================+==============================+
| ``newRaise()``                   | Inaugurate a new raising     |
|                                  | period.                      |
+----------------------------------+------------------------------+
| ``newLock()``                    | Inaugurate a new lock-up     |
|                                  | period.                      |
+----------------------------------+------------------------------+
| ``newSettlement()``              | Inaugurate a new settlement  |
|                                  | period.                      |
+----------------------------------+------------------------------+
| ``distributeInterest(address     | Distribute interest for a    |
| investor)``                      | user.                        |
+----------------------------------+------------------------------+
| ``setRaisePeriod(uint256         | Set the length for raising   |
| _raisePeriod)``                  | period. The default value is |
|                                  | 3 days.                      |
+----------------------------------+------------------------------+
| ``setLockPeriod(uint256          | Set the length for lock-up   |
| _lockPeriod)``                   | period. The default value is |
|                                  | 84 days.                     |
+----------------------------------+------------------------------+
| ``setSettlementPeriod(uint256    | Set the length for settlement|
| _settlementPeriod)``             | period. The default value is |
|                                  | 3 days.                      |
+----------------------------------+------------------------------+
| ``setEnodeThreshold(uint256      | Set the threshold to become  |
| _enodeThreshold)``               | an economy node. The default |
|                                  | value is 20,000 tokens.      |
+----------------------------------+------------------------------+
| ``setNextRaiseTime(uint256       | Set the the time to          |
| _NextRaiseTime)``                | inaugurate the next period.  |
|                                  | Normally, it is automatically|
|                                  | calculated.                  |
+----------------------------------+                              |
| ``setNextLockTime(uint256        |                              |
| _NextLockTime)``                 |                              |
|                                  |                              |
+----------------------------------+                              +
| ``setNextSettlementTime(uint256  |                              |
| _NextSettlementTime)``           |                              |
|                                  |                              |
+----------------------------------+------------------------------+
| ``refund(address investor,       | Refund the deposit in this   |
| uint 256 amount)``               | contract to a node, and      |
+----------------------------------+ disable the contract.        +
|                                  | Both functions are           |
| ``disable()``                    | invoked only when this smart |
|                                  | contract is going to         |
|                                  | terminate.                   |
+----------------------------------+------------------------------+


Investor API
****************

+-----------------------------------------------------------------+
|                            Investor                             |
+----------------------------------+------------------------------+
| API                              |           Description        |
+==================================+==============================+
| ``deposit()``                    | It is invoked when deposit   |
|                                  | in economy pool. The value   |
|                                  | of the transaction is the    |
|                                  | amount of deposit.           |
+----------------------------------+------------------------------+
| ``withdraw(uint amount)``        | It is invoked when withdraw  |
|                                  | deposit.                     |
+----------------------------------+------------------------------+
| ``claimInterest()``              | Investor claim interest in   |
|                                  | settlement period.           |
+----------------------------------+------------------------------+