Overview
~~~~~~~~~~~

What is CPChain
################

CPChain is a new blockchain infrastructure for next generation IoT.

Built-in smart contract
#########################

CPChain comes with 6 built-in smart contracts to ensure normal operation of DPoR.

ProxyContractRegister contract
*********************************

   Proxy contract address and real contract address can be binded through function ``registerProxyContract()``. Thus, there is no need to modify address in Go or Solidity when contract is update.
   The real contract address can be obtained through function ``getRealContract()``.


RPT contract
***************

   RPT contract will calculate Rnode's reputation value. It is a core component of Rnode ecosystem.
   `Here <https://cpchain.io/rnodes/>`_ is the detail of the Rnode ecosystem.
   Reputation value consists of 5 dimensions,
   **Account Balance（AB)**,
   **Transaction(TX)**,
   **Data Contribution(DC)**,
   **Blockchain Maintenance(BM)**,
   **Proxy Reputation(PR)**.Developers can call function
   ``getRpt()`` to get node's reputation value. RPT contract can be updated by contract depolyer to avoid some evil nodes maliciously increasing their RPT values.
   Developers can update the weights of the 5 dimensions and windowSize by
   calling RPT contract's function
   ``updateAlpha()``,
   ``updateBeta()``,
   ``updateGamma()``,
   ``updatePsi()``,
   ``updateOmega()``,
   ``updateWindow()``.

Campaign contract
********************

   Campaign contract will be called when you start mining, the campaign contract will register you as a Rnode after passing the
   admission contract's test. If your RPT vaule is in the top 21 of all Rnodes, you will get the opportunity to add bolck on cpchain and obtain
   some cpc rewards. You can call function
   ``claimCampaign()`` to submit campaign requires. You must send some cpc to campaign contract
   as deposit and pass admission contract's test. A Rnode can call function
   ``quitCampaign()`` to get back his deposit when quiting campaign.
   When contract deployer observes that a Rnode has malicious behavior, he can call function
   ``punishCandidate()`` to detain the Rnode's deposit.
   campaign contract provides functions
   ``candidatesOf()`` and
   ``candidateInfoOf()`` to inquiry Rnodes and their information.

Admission contract
*********************

   Admission contract is called by campaign contract to verify that candicates' cpu and memory resoures match the requirements of mining.
   ``updateCPUDifficulty()`` and
   ``updateMemoryDifficulty()``.

PDash contract
****************

   PDash contract is a important Dapp on cpchain, it helps RPT contract to calculate nodes' Proxy Reputation(PR).
   You can click `here <https://github.com/CPChain/pdash>`_ to get more details.

Register contract
*******************

   Register will recode the upload history of nodes, it helps RPT contract to calculate nodes' Data Contribution.

Private contract
###################

   We designed the data privacy mechanism, which allows users to deploy and call private contract on cpchain for completing their
   private transactions in a secure way. Besides the agent P(validator and intermediary) and the account accepted by deployer,
   no one else could see the private transaction. Although the private transactions are invisible for others who
   are not the transaction's participants, some sophisticated key data is recorded and maintained in blockchain and the
   data could be used for audition and validation for private transactions whenever it requires.

User Scenario Steps
***********************

   1. Seller A registers an item via the private contract CT. An item includes name, ipfs_cid, price, description and so on.

   2. Buyer B checked the registered items on contract CT and choose some items to buy.

   3. Buyer B pays money to the escrow contract CE.

   4. Buyer B sends contract CT an order about which item to buy and his public key, which is used to encrypt the item's symmetric key(e.g. AES).

   5. Seller A notices the order from contract CT, and checks if the buyer have enough money from the escrow contract CE.

   6. Seller A sends contract CT the confirmation message attached with the symmetric key encrypted by the buyer's public key.

   7. Buyer B received the encrypted symmetric key, and then decrypt it. With the symmetric key, the buyer B can decrypt the data on IPFS and then confirm that it is what they need.

   8. The agent P notice the confirmation and transfer money to seller A.

.. image:: process.png
