Overview
~~~~~~~~~~~

What is CPChain
################

CPChain is a new blockchain infrastructure for the next generation IoT.

Built-in smart contract
#########################

CPChain comes with 6 built-in smart contracts to ensure normal operations of DPoR.

Proxy Register contract
*********************************

   Proxy contract addresses and real contract addresses can be bound through function ``registerProxyContract()``. Thus, there is no need to modify the address in Go or Solidity when a contract is update.
   The real contract address can be obtained through function ``getRealContract()``.


RPT contract
***************

   RPT (abbreviated from reputation) contract calculates RNode's reputation value. It is a core component of RNode ecosystem.
   `Here <https://cpchain.io/rnode/>`_ is the detail of the RNode ecosystem.
   Reputation value consists of 5 dimensions,
   **Account Balance（AB)**,
   **Transaction (TX)**,
   **Data Contribution (DC)**,
   **Blockchain Maintenance (BM)**,
   and **Proxy Reputation (PR)**.

   By invoking function ``getRpt()``, developer can obtain the reputation value of corresponding node.
   RPT contract can be updated by contract deployer to avoid some faulty nodes maliciously increasing their RPT values.
   The weights of above 5 dimensions can be customized by 5 PRT contract functions
   ``updateAlpha()``,
   ``updateBeta()``,
   ``updateGamma()``,
   ``updatePsi()``,
   and ``updateOmega()``.
   The weight of window size can also be adjusted via the function ``updateWindow()``.

Campaign contract
********************

   A campaign contract is called once a user starts mining. If its passes the test of admission contract,
   it is registered as an RNode by the campaign contract.
   Furthermore, given the condition that RPT value of  the user is one of the top 21 RNodes,
   it is qualified to claim campaign aiming to become one of the committee members.
   In other words, that user acquires an opportunity to insert a block into cpchain and obtain some cpc as rewards.

   Here we list some vital functions in campaign contract.

   ``claimCampaign()``: this function is called when a user claims a campaign.
   A fee paid in cpc is required by campaign contract as a deposit.

   ``quitCampaign()``: this function is called after a user quits the campaign. It is about to get its deposit back via this function.

   ``punishCandidate()``: this function can only be invoked by contract deployer.
   The deployer can detain the RNode's deposit if it observes any malicious behavior from an RNode.

   ``candidatesOf()`` and ``candidateInfoOf()``: functions to retrieve RNodes and their information.

Admission contract
*********************

   Admission contract is called by campaign contract to verify whether
   the candidates' CPU and memory resources match the requirements of mining.
   Two functions ``updateCPUDifficulty()`` and ``updateMemoryDifficulty()`` are implemented to fulfil this verification purpose.

PDash contract
****************

   PDash contract is an important app on cpchain, which helps RPT contract to calculate Proxy Reputation.
   You can click `here <https://github.com/CPChain/pdash>`_ to get more details.

Register contract
*******************

   Register contract is used for recoding the upload history of nodes.
   It collaborates with RPT contract to calculate nodes' Data Contribution.

Private contract
###################

   Our data privacy mechanism allows users to deploy and call private contract on cpchain for completing their
   private transactions in a secure way.
   Besides the agent P (validator and intermediary) and accounts accepted by the deployer,
   others are permitted from viewing the private transactions.
   Although the private transactions are invisible for others who
   are not the transaction's participants, some sophisticated key data is recorded and maintained in blockchain.
   The data is available for audition and validation for private transactions when necessary.

User Scenario Steps
***********************

   1. Seller A registers an item via the private contract CT. An item includes name, ipfs_cid, price, description and so on.

   2. Buyer B checks the registered items on contract CT and chooses some items to buy.

   3. Buyer B pays money to an escrow contract CE.

   4. Buyer B sends contract CT an order describing which item to buy and its public key, the one used to encrypt the item's symmetric key (e.g. AES).

   5. Seller A receives the notification about the order from contract CT, and checks if the buyer have enough money from the escrow contract CE.

   6. Seller A sends contract CT the confirmation message attached with the symmetric key encrypted by the buyer's public key.

   7. Buyer B receives the encrypted symmetric key, and then decrypts it. With the symmetric key, the buyer B can decrypt the data on IPFS and then confirm whether it is what it needs.

   8. The agent P notices the confirmation and transfer money to seller A.

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
    #. It is a two-phase protocol in PBFT manner, consisting of *prepare* and *commit* phases.
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






RNode Ecosystem
####################

CPChain Nodes Roles
**********************

**Economy Node**: Requires a minimum of 20,000 CPC tokens for participation.
Investors who meet this requirement may participate as an economy node and have the right to vote in the community.

**Reputation Node**: Requires a minimum of 200,000 CPC tokens for participation.
Investors with the basic configuration of computing and storing can participate to support the CPChain Open Transmission Protocol (COTP).

**Industry Node**:
IoT Industry partners and CPChain ecosystem’s peer developers have the right to participate as an Industry Node.

Reputation Nodes
*****************

A node has to meet one of the following requirements to become a Reputation Node:

a. Economic node + Computing and Storing node:
An economy node must lock-up a specific amount of tokens (200,000 minimum and 5,000,000 maximum)
for 90 days and must satisfy the software, hardware, and network connection requirements.
The locked up tokens have a positive correlation with the basic rewards.
Reputation nodes will be refunded after they leave the election.

#. Industry Node + Computing and Storage Node:
An industry node will be upgraded to a reputation node once meeting all the hardware,
software, and network requirements.
Industry nodes must be verified by the CPChain foundation.

Reputation Nodes have the right to be elected as a proposers committee member and to be granted rewards from the Blockchain.

Node Entitlements & Rewards
*******************************

CPChain’s ecosystem is established by a lot of Internet of Things (IoT) enterprises, developers and users.
It is a long-term process. As a result, CPChain will divide the incentive system into two stages.
In the first stage, CPChain Foundation would be the main fund provider, for the ecosystem establishment and the chain maintenance.
The next stage is mainly performed by the market. With the optimization of CPChain ecosystem and the increase in data sharing and transferring, the reward for RNodes will mainly be generated by smart contracts and market transactions.

In the first stage, reputation nodes’ entitlements will be allocated to two parts:

Basic Rewards
+++++++++++++++++

CPChain will create a reward pool with 5 million CPC annually (1.25 million CPC quarterly, 13,700 CPC daily).
The RNodes and the Economy Nodes receive the corresponding CPC reward based on the ratio of the locked margin to the total margin.
(Economy Node and RNode will both need a 90-day lock-up session). The detailed process goes as follows:

Each season contains 90 days, which is also named as **duration**.
There are 7 special days served as **fundraising** ahead of each duration.
Each fundraising is overlapped with previous duration.
In fundraising, the following operations are allowed:

1. All civilians can deposit coin in the reward pool, to become economic nodes or RNodes.
#. Nodes that have already had coins deposited in the pool can choose to whether continue deposit the next season or renew the deposit value.

When a duration ends, the following rules are applied:

1. No one adjusts or withdraw its deposit until next fundraising
#. Nodes that decide to withdraw the deposit, receive the coins
#. Any node that renews its deposit balance get recalculated its CPChain nodes role as economic node, RNode or the rest.
#. All nodes with deposit in this duration receive their reward from the pool.

The reward for a certain node from the pool is proportional to its deposit in a season.
In other word, the basic reward is calculated as 5000000*d/D, where d is deposit of a certain node,
and D is the total value of coins in the reward pool.



.. image:: reward_pool.png

Maintenance Reward
+++++++++++++++++++++

Proposers committee nodes are entitled to blockchain maintenance rewards after it proposes a block and successfully gets it inserted into the chain.
As defined in `the RNode ecosystem <https://cpchain.io/rnode/>`_,
the annual supply from maintenance is 40 million CPC in the first year,
and being decreased by 25% annually for the next four years.
Thus, the annual supply for five years is 40 million, 30 million, 22.5 million, 17 million and 12.75 million respectively.
After five years, the supply runs out. In other words, no CPC is rewarded after that time.

Meanwhile, CPC Mainnet inserts a block every 10 seconds, which yields around 3 million blocks each year.
Therefore, we conclude the reward and supply in the table below.

+--------+--------+---------------+--------------+
| Year   | Reward | Num of Blocks |   Supply     |
+========+========+===============+==============+
| 1      | 12.65  |  3,162,240*   | 40,002,336   |
+--------+--------+---------------+--------------+
| 2      | 9.51   |  3,153,600    | 29,990,736   |
+--------+--------+---------------+--------------+
| 3      | 7.13   |  3,153,600    | 22,485,168   |
+--------+--------+---------------+--------------+
| 4      | 5.39   |  3,153,600    | 16,997,904   |
+--------+--------+---------------+--------------+
| 5      | 4.03   |  3,162,240*   | 12,743,827.2 |
+--------+--------+---------------+--------------+
\* Both the first and the fifth year contain a leap day (29 Feb 2020 and 2024, respectively),
which results in a larger number of generated blocks compared to the other three years.

Note that in our LBFT 2.0 protocol, an impeach block in inserted into the chain if the proposer is faulty or non-responding.
Intuitively, a faulty proposer cannot receive the reward. Hence, the amount of annual supply could be smaller than the
one listed in the table above.


Lock Deposit
***************

Use smart contracts to lock deposit, the functions are as follow:

    Determine the node level based on the amount of deposit of the node.
    lock the deposit to fixed range of length of blockchain.
    Reward distribution according to proportion of node's deposits.
    Connection with Reputation list.