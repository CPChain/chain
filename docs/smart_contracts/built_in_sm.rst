.. _built-in-sm:


Built-in Smart Contract
#########################

CPChain comes with 5 built-in smart contracts to ensure normal operations of DPoR.
Other contract files in out code repository are either abandoned or not yet activated.

Admission Contract
*********************************

   Admission contract is called by campaign contract to verify whether
   the candidates' CPU and memory resources match the requirements of mining.
   Admission contract uses primitive contract mechanism, so that contract code can directly call
   functions implemented in golang.
   Two functions ``updateCPUDifficulty()`` and ``updateMemoryDifficulty()``
   are implemented to adjust the difficulty.

Campaign Contract
********************

   Campaign contract will be called once a user starts mining.
   Campaign contract will check whether the applicants' hardware resources match basic requirement by calling admission
   contract and check whether the applicants are rnodes by calling rnode contract.
   If applicants pass the tests, Campaign contract will add them into candidates list for next three terms by default.

   Here we list two view only functions in campaign contract.

   ``candidatesOf(uint term)``: returns all candidates' addresses of specified term.

   ``candidateInfoOf(address candidate)``: returns campaign information of specified candidate, including its start, end and total terms.

Network Contract
******************

    Network contract provides configs for testing network status.
    Applicants have to pass the network test before becoming rnodes and candidates.

    The contract contains 5 configuration parameters:

    ``host``: the address applicants need to connect to.

    ``count``: times applicants is allowed to try.

    ``timeout``: maximum allowable time.

    ``gap``: time interval between attempts.

    ``open``: switch of the contract.



Rnode Contract
****************

    Rnode contract records addressed of all rnodes, and holds their deposits.

    Two main parameters:

    ``period``: rnode can quit and withdraw deposit after period.

    ``rnodeThreshold``: standard to become rnodes.

    Applicants join or quit rnodes through functions ``joinRnode()`` and ``quitRnode()``.

.. _rpt-contract:

RPT Contract
***************

   Rpt contract provides configs for reputation calculation.
   Proposers will be elected from candidates based on their rpt value.
   Rpt is calculated based on five dimensions.

   The contract contains 5 weight parameters:

   ``alpha`` for balance.
   ``beta`` for transactions.
   ``gamma`` for proxy reputation.
   ``psi`` for data contribution.
   ``omega`` for blockchain maintenance.



