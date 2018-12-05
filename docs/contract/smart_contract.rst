Smart Contract
=====================

Environment setup
-----------------

Install Solc
*************
Currently, CPC smart contracts programming depends on the vm of Ethereum. In future we will become independent of
Ethereum.Developers need install solc to compile the contracts code.

npm / Node.js

Use npm for a convenient and portable way to install solc.

.. code::

   npm install -g solc@ 0.4.24

Docker

Ethereum provide up to date docker builds for the compiler.The stable repository contains released versions while
the nightly repository contains potentially unstable changes in the develop branch.

.. code::

   docker run ethereum/solc:stable solc ---0.4.24

Deploy Smart Contract
*********************
Cpchain already write 5 init smart contracts to maintain the normal operation of Dpor. Developers should deploy them when
chain started.

.. code::

   export GOPATH=${gopath}
   cd ../../
   go run ${gopath}/src/bitbucket.org/cpchain/chain/tools/smartcontract/main.go
   replace ${gopath} with real env path. ex:/home/${user}/workspace/chain_dev

init smart contract
-------------------

ProxyContractRegister contract
******************************

   Developers can call ProxyContractRegister contract's function
   ``registerProxyContract()`` to bind proxy contract address
   and deployed or updated contract address.Thus,developers not need to modify the contract address on Go or Solidity when the contract is update.
   Developers can use function
   ``getRealContract()`` to get real contract address.

RPT Contract
************

   RPT Contract will calculation the Rnode's reputation value(RPT).Reputation value is consists of 5 dimensions,
   **Account Balance（AB)**,
   **Transaction(TX)**,
   **Data Contribution(DC)**,
   **Blockchain Maintenance(BM)**,
   **Proxy Reputation(PR)**. you can call function
   ``getRpt()`` to get node's RPT. Rpt Contract can be update by contract depolyer to avoid some evil node maliciously increase it RPT.
   you can update the weight of the 5 dimensions and windowSize by
   call RPT contract's function
   ``updateAlpha()``,
   ``updateBeta()``,
   ``updateGamma()``,
   ``updatePsi()``,
   ``updateOmega()``,
   ``updateWindow()``.

Campaign Contract
*****************

   Campaign Contract will be called when you start miner, the campaign contract will register you as Rnode after pass the
   Admission Contract's test.If you RPT is top 21 in all Rnodes,you will get the opportunity to add bolck on cpchain and obtain
   some cpc reward. You can call function
   ``claimCampaign()`` to submits campaign required. You must send some cpc to Campaign Contract's address
   as deposit and pass Admission Contract's test. If a Rnode want quit campaign, he can call
   ``quitCampaign()`` to get beck him deposit.
   When Contract deployer observe a Rnode have malicious behavior, he can call function
   ``punishCandidate()`` to detain the Rnode's deposit.
   Campaign Contract provide function
   ``candidatesOf()`` and
   ``candidateInfoOf()`` to inquiry which node is Rnode and it information.

Admission Contract
******************

   Admission contract is called by Campaign Contract to proof your cpu and memory can competent miner task.
   The Difficulty of test can be update by call function
   ``updateCPUDifficulty()`` and
   ``updateMemoryDifficulty()``.

Pdash Contract
**************

   The Pdash contract is a important Dapp on cpchain,it help RPT contract calculation the RNode's Proxy Reputation(PR).
   You can click here https://github.com/CPChain/pdash to get more detail.

Register Contract
*****************

   Register will recoding the upload history of nodes,it help RPT contract to calculation node's Data Contribution.

private Contract
----------------
   We designed the data privacy mechanism, which allows users to deploy and call private contract on cpchain for completing their
   private transactions in a secure way. Besides the agent P(validator and intermediary) and the account accepted by deployer,
   no one else could see the private transaction. Although the private transactions are invisible for others who
   are not the transaction's participants, some sophisticated key data is recorded and maintained in blockchain and the
   data could be used for audition and validation for private transactions whenever it requires.

   Here we offer a privateContract example.

   .. code::




