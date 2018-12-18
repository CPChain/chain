Introduction
=====================

Smart Contract
^^^^^^^^^^^^^^^^^

.. Environment setup
.. -------------------

.. Install Solc
.. *************
.. Currently, CPC smart contracts programming depends on the Ethereum's VM. In future we will become independent of
.. Ethereum. Developers need install solc to compile the contracts code.

.. npm / Node.js

.. Use npm for a convenient and portable way to install solc.

.. .. code::

..    $ npm install -g solc@ 0.4.24

.. Docker

.. Ethereum provide up to date docker builds for the compiler.The stable repository contains released versions while
.. the nightly repository contains potentially unstable changes in the develop branch. So we fix solc version on 0.4.24

.. .. code::

..    $ docker run ethereum/solc:stable solc ---0.4.24

.. Deploy Smart Contract
.. *********************
.. Cpchain already write 5 init smart contracts to maintain normal operation of Dpor. Developers should deploy them when
.. chain started.

.. .. code::

..    $ ./deploy-contracts.sh

.. .. image:: deploy-contract.png

Init Smart Contract
-------------------

ProxyContractRegister Contract
******************************

   Developers can call ProxyContractRegister contract's function
   ``registerProxyContract()`` to bind proxy contract address
   and real contract address.Thus,developers not need to modify the contract address on Go or Solidity when the contract is update.
   Developers can use function
   ``getRealContract()`` to get real contract address.

RPT Contract
************

   RPT Contract will calculation the Rnode's reputation value.It's an important part of the RNode Ecosystem Structure.
   `Here <https://cpchain.io/rnodes/>`_ is detail of the RNode Ecosystem Structure.
   Reputation value consists of 5 dimensions,
   **Account Balance（AB)**,
   **Transaction(TX)**,
   **Data Contribution(DC)**,
   **Blockchain Maintenance(BM)**,
   **Proxy Reputation(PR)**.Developers can call function
   ``getRpt()`` to get node's reputation value. RPT Contract can be update by contract depolyer to avoid some evil node maliciously increase it RPT.
   Developers can update the weight of the 5 dimensions and windowSize by
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
   You can click `here <https://github.com/CPChain/pdash>`_ to get more detail.

Register Contract
*****************

   Register will recoding the upload history of nodes,it help RPT contract to calculation node's Data Contribution.

Private Contract
----------------
   We designed the data privacy mechanism, which allows users to deploy and call private contract on cpchain for completing their
   private transactions in a secure way. Besides the agent P(validator and intermediary) and the account accepted by deployer,
   no one else could see the private transaction. Although the private transactions are invisible for others who
   are not the transaction's participants, some sophisticated key data is recorded and maintained in blockchain and the
   data could be used for audition and validation for private transactions whenever it requires.

   User Scenario Steps

   1. Seller A registers an item via the private contract CT. An item includes name, ipfs_cid, price, description and so on.

   2. Buyer B checked the registered items on contract CT and choose some items to buy.

   3. Buyer B pays money to the escrow contract CE.

   4. Buyer B sends contract CT an order about which item to buy and his public key, which is used to encrypt the item's symmetric key(e.g. AES).

   5. Seller A notices the order from contract CT, and checks if the buyer have enough money from the escrow contract CE.

   6. Seller A sends contract CT the confirmation message attached with the symmetric key encrypted by the buyer's public key.

   7. Buyer B received the encrypted symmetric key, and then decrypt it. With the symmetric key, the buyer B can decrypt the data on IPFS and then confirm that it is what they need.

   8. The agent P notice the confirmation and transfer money to seller A.

.. image:: process.png




