Overview
~~~~~~~~~~~

What is CPChain
################

CPChain is a new blockchain infrastructure for the next generation IoT.

Built-in Smart Contract
#########################

CPChain comes with 6 built-in smart contracts to ensure normal operations of DPoR.

Proxy Register Contract
*********************************

   Proxy contract addresses and real contract addresses can be bound through function ``registerProxyContract()``. Thus, there is no need to modify the address in Go or Solidity when a contract is update.
   The real contract address can be obtained through function ``getRealContract()``.


RPT Contract
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

Campaign Contract
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

Admission Contract
*********************

   Admission contract is called by campaign contract to verify whether
   the candidates' CPU and memory resources match the requirements of mining.
   Two functions ``updateCPUDifficulty()`` and ``updateMemoryDifficulty()`` are implemented to fulfil this verification purpose.

PDash Contract
****************

   PDash contract is an important app on cpchain, which helps RPT contract to calculate Proxy Reputation.
   You can click `here <https://github.com/CPChain/pdash>`_ to get more details.

Register Contract
*******************

   Register contract is used for recoding the upload history of nodes.
   It collaborates with RPT contract to calculate nodes' Data Contribution.

Private Contract
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

The consensus in LBFT 2.0 is determined by two two committees: **Validators Committee** and **Proposers Committee**,
which leads to a bipartite committee structure.
Proposers and validators, just as their names imply, take the responsibility of proposing and validating blocks respectively.

The consensus process works in a finite state machine which consists of five states
**idle**, **prepare**, **commit**, **impeach prepare** and **impeach commit**.
The former three states are designed for normal cases, and the rest are specializing in handling abnormal cases.

Due to the lack of space in this page, we explicate LBFT 2.0 in :ref:`consensus`


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

    1. Economic node + Computing and Storing node:
    An economy node must lock-up a specific amount of tokens (200,000 minimum and 5,000,000 maximum)
    for 90 days and must satisfy the software, hardware, and network connection requirements.
    The locked up tokens have a positive correlation with the basic rewards.
    Reputation nodes will be refunded after they leave the election.

    2. Industry Node + Computing and Storage Node:
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

Each season contains 90 days, which is also named as **lock-up period**.
There are 7 special days served as **fundraising** ahead of each lock-up period.
Each fundraising is overlapped with previous lock-up period.
In fundraising, the following operations are allowed:

1. All civilians can deposit coin in the reward pool, to become economic nodes or RNodes.
#. Nodes that have already had coins deposited in the pool can choose to whether continue deposit the next season or renew the deposit value.

When a fundraising ends, the following rules are applied:

1. No one adjusts or withdraw its deposit until next fundraising.
#. Nodes that decide to withdraw the deposit, receive the coins.
#. Any node that renews its deposit balance get recalculated its CPChain nodes role as economic node, RNode or the rest.
#. All nodes with deposit in this lock-up period receive their reward from the pool.

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