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

.. code-block:: table
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

.. code-block:: table
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



Read-only API
**********************

The reward contract all provides read-only API to seek information about the node.

.. code-block:: table
	+-----------------------------------------------------------------+
	|                             Read-only                           |
	+----------------------------------+------------------------------+
	| API                              |           Description        |
	+==================================+==============================+
	| ``mapping(address => uint 256)   | Query for the invest of an   |
	| public investments``             | address in the pool.         |
	+----------------------------------+------------------------------+
	| ``mapping(address => mapping(    | Return a boolean result that |
	| address => bool )) returned``    | whether an address has been  |
	|                                  | distributed interest in a    |
	|                                  | certain round.               |
	+----------------------------------+------------------------------+
	| ``uint256 public                 | Query for current total      |
	| totalInvestment``                | investment of the pool.      |
	+----------------------------------+------------------------------+
	| ``uint256 public                 | Query for distributed        |
	| totalInterest``                  | interest of the current      |
	|                                  | season.                      |
	+----------------------------------+------------------------------+
	| ``bool public inRaise``          | Return if it is in raising   |
	|                                  | period.                      |
	+----------------------------------+------------------------------+
	| ``bool public inLock``           | Return if it is in lock-up   |
	|                                  | period.                      |
	+----------------------------------+------------------------------+
	| ``bool public inSettlement``     | Return if it is in           |
	|                                  | settlement period.           |
	+----------------------------------+------------------------------+
	| ``uint256 public bonusPool``     | Query for the total bonus    |
	|                                  | in the pool.                 |
	+----------------------------------+------------------------------+
	| ``uint256 public round``         | Query for the sequence       |
	|                                  | number of the current season.|
	+----------------------------------+------------------------------+
	| ``uint256 public nextRaiseTime`` | Query for the beginning of   |
	|                                  | the next raising period.     |
	+----------------------------------+------------------------------+
	| ``uint256 public nextLockTime``  | Query for the beginning of   |
	|                                  | the next lock-up period.     |
	+----------------------------------+------------------------------+
	| ``uint256 public                 | Query for the beginning of   |
	| nextSettlementTime``             | the next settlement period.  |
	+----------------------------------+------------------------------+
	| ``function getEnodes() public    | Retrieve the address of      |
	| view returns(address[])``        | all economy nodes.           |
	+----------------------------------+------------------------------+





Availability of API
--------------------------

Some APIs can ony be called in a certain period.
The table below lists all available APIs for each period. 


.. code-block:: table
	+----------------------------------+------------------------------+
	| Period                           |           API                |
	+==================================+==============================+
	| **Raising**                      | ``deposit()``                |
	|                                  +------------------------------+
	|                                  | ``withdraw(uint amount)``    |
	|                                  +------------------------------+
	|                                  | Receive transfer.            |
	|                                  +------------------------------+
	|                                  | Read-only API                |
	+----------------------------------+------------------------------+
	| **Lock-up**                      | Read-only API                |
	+----------------------------------+------------------------------+
	| **Settlement**                   | ``claimInterest``            |
	|                                  +------------------------------+
	|                                  | ``distributeInterest(address |
	|                                  | investor)``                  |
	|                                  +------------------------------+
	|                                  | Read-only API                |
	+----------------------------------+------------------------------+
