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


Consensus
#####################

Dpor Bipartite Committee
**************************



1. **Validator** and **Proposer** and **Civilian**
    a. Block validators, or validators refer to a group of users that can validate a newly proposed block.
        i. The validator committee consists of nodes nominated from CPC Foundation, governments and companies.
        #. Except for some abnormal cases, validators may not produce blocks.
        #. The validator committee follows our improved *LBFT* 2.0 protocol to achieve a consensus.
        #. The size of number is always equaling to 3f+1, where f is the number of byzantine nodes.
    #. Block proposer, or proposer refers to the user that can propose block.
        i. It is one member of the proposers committee.
        #. The proposers committee is elected based on reputations of candidates and a random seed.
        #. Each number in the proposers committee takes the responsibility of producing block one by one.
    #. Civilians refer to the rest of users
        i. A civilian can become a proposer if it claims campaign and is elected.

Normal and Abnormal Case Handler
**********************************
#. **Normal Case**
    a. Block production
        i. An ordinary user claims campaign, undergoes the admission qualification, and then enters the *candidate list*.
        #. After being elected in a periodical election, a candidate enters a block proposer committee.
        #. When it comes its view, the proposer proposes a block and broadcasts to all validators.
    #. Block validation
        i. Once receives a newly proposed block, a validator in validators committee tries to verify the block.
        #. This verification process scrutinizes the seal of proper, timestamp, etc.
        #. If true, this validator broadcast a PREPARE message to other validators; otherwise, it enters Abnormal Case 2 or 3.
        #. Once receives 2f+1 PREPARE messages (P-certificate), a validator broadcasts COMMIT message to other validators.
        #. Once received 2f+1 COMMIT messages (C-certificate), a validator inserts the block into local chain, and broadcasts VALIDATE message long with these 2f+1 validators' signatures to all users.
        #. Any user receives this VALIDATE message with enough signatures, insert the block into local chain


#. **Abnormal Cases**
    a. Abnormal Case 1: *A validator does not receive a block from the proposer*
        i. It is for the case when Step 2.a.f cannot be reached
        #. After a validator sends out its address to the proposer, it sets up a timer
        #. If the timer expires, the validators committee activates *impeachment*, a two-phase protocol in PBFT manner to propose an impeach block on behalf of the faulty proposer.
    #. Abnormal Case 2: *The proposer proposes one or more faulty blocks*
        i. Faulty blocks cannot be verified in Step 2.b.a
        #. The validators committee activates *impeachment*
    #. Abnormal Case 3: *The proposer proposes multiple valid blocks*
        i. Each validator can only validate one block for a same block number
        #. Thus, it is impossible for two or more blocks to collect P-certificates simultaneously. Only one block can enter Step 2.b.d
        #. It is possible that no block receives 2f+1 PREPARE messages
        #. *Impeachment* is activated if a validator cannot collect a P-certificate
    #. Abnormal Case 4: *Some members in the validators committee are faulty*
        #. The system can reach a consensus, as long as the number of total faulty validators is no more than f.
    #. Abnormal Case 5:
        i. It is for the cases when P-certificate, C-certificate or VALIDATE messages cannot be collected
        #. Each validators have distinct timers for collecting PREPARE, COMMIT and VALIDATE messages
        #. Any of these timers expires, the validators committee activates *impeachment*

Impeachment
**************


#. **Impeachment**
    a. It is an abnormal handler when the proposer is either faulty, or non responding
    #. It is a two-phase protocol in PTBF manner, consisting of *prepare* and *commit* phases.
    #. Impeachment steps:
        a. A validator in the committee generates a block on behalf of the faulty (or non responding) proposer.
            i. In the header of this block, the *timestamp* is set to be previousBlockTimestamp+period+timeout, where previousBlockTimestamp is the timestamp of block proposed in previous view, period is the interval between two blocks and timeout is the threshold validator that triggers impeachment.
            #. The *seal* in the header is set to be empty
            #. A penalty on proposer is the only transaction in the block's body
        #. This block, used as an IMPEACH PREPARE message, is broadcast to all validators in the committee.
        #. Once receives 2f+1 PREPARE messages with same header and body, a validator broadcasts an IMPEACH COMMIT message to other validators.
        #. Once receives 2f+1 COMMIT messages, a validator inserts the block into local chain, and broadcasts an IMPEACH VALIDATE message along with 2f+1 signatures to all users.
        #. All users insert the block into local chain, if they receive a IMPEACH VALIDATE messages.
    #. The reason the leader is not required
        a. The leader in classic PBFT model takes the following roles:
            i. Receives the request from the client, and broadcasts it to all backups in distributed system.
            #. Assign a sequence number to each request, to guarantee that all requests are processed in order.
        #. Impeachment does not requires a leader to fulfill above duties, since
            i. Each non faulty validator is about to propose a completely same block.
            #. Each block is associated with a unique block number, which circumvents the usage of sequence number.
    #. It is possible for some validators obtains 2f+1 PREPARE messages of a newly proposed block while another validators obtain 2f+1 PREPARE messages of empty block
        a. This scenario occurs only when the proposer is faulty
        b. This scenario does not affects the security of the system, since validators can only collect 2f+1 COMMIT messages for one block


