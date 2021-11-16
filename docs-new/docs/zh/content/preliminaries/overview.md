# Overview

## What is CPChain

CPChain is a new blockchain infrastructure for the next generation IoT.

## Built-in Smart Contract

CPChain comes with 5 built-in smart contracts to ensure normal
operations of DPoR. Other contract files in out code repository are
either abandoned or not yet activated. Due to the lack of space in this
page, we explicate all five smart contracts in
[Built-in Smart Contract](../smart_contracts/built_in_sm.md#built-in-smart-contract).

## Private Contract

> Our data privacy mechanism allows users to deploy and call private
> contract on cpchain for completing their private transactions in a
> secure way. Besides the agent P (validator and intermediary) and
> accounts accepted by the deployer, others are permitted from viewing
> the private transactions. Although the private transactions are
> invisible for others who are not the transaction's participants, some
> sophisticated key data is recorded and maintained in blockchain. The
> data is available for audition and validation for private transactions
> when necessary.

### User Scenario Steps

> 1.  Seller A registers an item via the private contract CT. An item
>     includes name, ipfs_cid, price, description and so on.
> 2.  Buyer B checks the registered items on contract CT and chooses
>     some items to buy.
> 3.  Buyer B pays money to an escrow contract CE.
> 4.  Buyer B sends contract CT an order describing which item to buy
>     and its public key, the one used to encrypt the item's symmetric
>     key (e.g. AES).
> 5.  Seller A receives the notification about the order from contract
>     CT, and checks if the buyer have enough money from the escrow
>     contract CE.
> 6.  Seller A sends contract CT the confirmation message attached with
>     the symmetric key encrypted by the buyer's public key.
> 7.  Buyer B receives the encrypted symmetric key, and then decrypts
>     it. With the symmetric key, the buyer B can decrypt the data on
>     IPFS and then confirm whether it is what it needs.
> 8.  The agent P notices the confirmation and transfer money to
>     seller A.

![image](./process.png)

## Consensus

The consensus in LBFT 2.0 is determined by two committees: **Validators
Committee** and **Proposers Committee**, which together lead to a
bipartite committee structure. Proposers and validators, just as their
names imply, take the responsibility of proposing and validating blocks
respectively.

The consensus process works in a finite state machine which consists of
five states **idle**, **prepare**, **commit**, **impeach prepare** and
**impeach commit**. The former three states are designed for normal
cases, and the rest, named as impeachment, are specializing in handling
abnormal cases.

Due to the lack of space in this page, we explicate LBFT 2.0 in
[Consensus](../detailed_algorithms/consensus.md#consensus).

## CPChain Ecosystem

### CPChain Nodes Roles and Pools

**Economy Node**: Requires a minimum of 20,000 CPC tokens deposited in
*Economy Pool* for participation. Investors who meet this requirement
may participate as an economy node and have the right to vote in the
community.

**Reputation Node**: Requires a minimum of 200,000 CPC tokens deposited
in *RNode Pool* for participation. Investors with the basic
configuration of computing and storage can participate to support the
CPChain Open Transmission Protocol (COTP).

**Industry Node**: IoT Industry partners and CPChain ecosystem's peer
developers have the right to participate as an Industry Node.

Note that there are two separate pools for deposit.

**Economy Pool**: Any node deposit at least 20,000 CPC tokens in this
pool is qualified as an economy node.

**RNode Pool**: Any node deposit at least 200,000 CPC tokens in this
pool is qualified as an RNode.

### Reputation Nodes

A node has to meet one of the following requirements to become a
Reputation Node:

> 1\. At least 200,000 CPC in RNode Pool + Computing and Storage node: A
> node must lock-up a specific amount of tokens (200,000 minimum and
> 5,000,000 maximum) for 90 days and must satisfy the software,
> hardware, and network connection requirements. The locked up tokens
> have a positive correlation with the basic rewards. Reputation nodes
> will be refunded after they leave the election.
>
> 2\. Industry Node + Computing and Storage Node: An industry node will
> be upgraded to a reputation node once meeting all the hardware,
> software, and network requirements. Industry nodes must be verified by
> the CPChain foundation.

Reputation Nodes have the right to be elected as a proposers committee
member and to be granted rewards from the Blockchain.

### RPT Evaluation

RPT (abbreviated from reputation) value of a node is evaluated by
extracting data from blockchain. By employing
[RPT Contract](../smart_contracts/built_in_sm.md#rpt-contract), a node can evaluates its
RPT value by following five dimensions:

-   **Account Balance（AB)**,
-   **Transaction (TX)**,
-   **Data Contribution (DC)**,
-   **Blockchain Maintenance (BM)**,
-   **Proxy Reputation (PR)**.

Each dimension has a full score of 100 point. And the total score is
calculated as:

$RPT = 50\times AB +
15\times TX +
10\times PR +
15\times DC +
10\times BM$,

which leads to 10,000 full score of RPT.

::: tip

All scores for each dimension are evaluated within to a time window,
which is latest 100 blocks. Data outside this window are no longer taken
into consideration.
:::

Unless otherwise stated, the score for each dimension is calculated by
the same methodology. In total, there are at most 100 RNodes in each
term campaign. The RNode with $i$-th highest RPT will get $(100-i+1)$
score.

#### Account Balance

A *account balance* score is granted to an RNode according to its
account balance ranking among all RNode addresses (excluding CPChain
Foundation and Exchange addresses).

#### Transaction

*Transactions* here include all transactions sent by a given user. The
definition of *transactions* can be expanded as the of CPChain ecosystem
develops.

TX score is evaluated by all *transactions* statistics. The distribution
of transactions can follow a long tail distribution or power laws.

#### Proxy Reputation

An RNode can serve as a *proxy* helping other nodes complete
transactions. Its RPT is augmented after assuming the responsibility as
a proxy.

Proxy reputation score is calculated according to following rules:

1.  Once an RNode registers as a proxy, it obtains 10 initial points.
2.  For each successful transaction with the node's help as a proxy, it
    gets 5 points.
3.  The full score is 100 points.

#### Data Contribution

Uploading data augments RPT value. There are two parts in data
contribution, as basic DC score and bonus DC score.

Data contribution score is calculated according to following rules:

1.  For each file an RNode uploads, the node is rewarded 3 points in DC
    score.
2.  The full score of basic DC is 30 points.
3.  Each time other node purchases a file that RNode uploads, the RNode
    is rewarded 5 bonus points.
4.  The full score of bonus DC is 70 points.

#### Blockchain Maintenance

Blockchain Maintenance score is calculated given a node's contribution
in proposing a certain block.

### Node Entitlements & Rewards 

CPChain's ecosystem is established by a lot of Internet of Things (IoT)
enterprises, developers and users. It is a long-term process. As a
result, CPChain will divide the incentive system into two stages. In the
first stage, CPChain Foundation would be the main fund provider, for the
ecosystem establishment and the chain maintenance. The next stage is
mainly performed by the market. With the optimization of CPChain
ecosystem and the increase in data sharing and transferring, the reward
for RNodes will mainly be generated by smart contracts and market
transactions.

In the first stage, reputation nodes' entitlements will be allocated to
two parts:

#### Basic Rewards 

CPChain will create a reward pool with 5 million CPC annually (1.25
million CPC quarterly, 13,700 CPC daily). The Economy Nodes receive the
corresponding CPC reward based on the ratio of the locked margin to the
total margin. (Economy Node needs a 90-day lock-up session). The
detailed process goes as follows:

Each season lasts for 90 days, including the first 3 days for the
**raising period**, the 86 days for the **lock-up period**, and the last
3 days for the **settlement period**. There is no overlap between each
period, and the second period can only be opened after the end of the
first period. Each period does not overlap with other one. And the
contract is always at a certain period, the raise period, the lock
period or the settlement period. In the raise period, you can deposit
tokens into the economic pool or withdraw the tokens. No operation is
permitted during the lock period. And interest for each season can be
taken away during the settlement period. If the user does not take the
interest, the administrator will assign them one by one.

In raising, the following operations are allowed:

1.  All civilians can deposit coin in the reward pool, to become Economy
    Nodes.

2.  

    Nodes that have already had coins deposited in the pool can choose to

    :   1.  whether continue deposit the next season
        2.  or renew the deposit value.

3.  For a node determines to withdraw deposit, it needs to call withdraw
    function on their own initiative after lock-up period finishes.

In settlement, the following rules are applied:

1.  No one adjusts or withdraw its deposit until next fundraising.
2.  Nodes can collect interest of this season.
3.  Interest that do not proactively collected by its owner will be
    allotted to the owner by admins.

Interested reader can refer to [Reward Smart Contract](../smart_contracts/reward_sm.md#reward-smart-contract)
to check detailed smart contract implementation.

The reward for a certain node from the pool is proportional to its
deposit in a season. In other word, the basic reward is calculated as
$5000000 \cdot d/D$, where $d$ is deposit of a certain node, and $D$ is
the total value of coins in the reward pool.

![image](./reward_pool.png)

#### Maintenance Reward

Proposers committee nodes are entitled to blockchain maintenance
rewards, after it proposes a block and successfully gets it inserted
into the chain. As defined in [the RNode
ecosystem](https://cpchain.io/rnode/), the annual supply from
maintenance is 40 million CPC in the first year, and being decreased by
25% annually for the next four years. Thus, the annual supply for five
years is 40 million, 30 million, 22.5 million, 17 million and 12.75
million respectively. After five years, the supply runs out. In other
words, no CPC is rewarded after that time.

Meanwhile, CPC Mainnet inserts a block every 10 seconds, which yields
around 3 million blocks each year. Therefore, we conclude the reward and
supply in the table below.

<table cellspacing="0" cellpadding="5">
	<tr>
		<th colspan="1"> Year   </th>
		<th colspan="1"> Reward </th>
		<th colspan="1"> Num of Blocks </th>
		<th colspan="1">   Supply     </th>
	</tr>
	<tr>
		<td  rowspan="1"> 1 </td>
		<td  rowspan="1"> 12.65 </td>
		<td  rowspan="1"> 3,162,240* </td>
		<td  rowspan="1"> 40,002,336 </td>
	</tr>
	<tr>
		<td  rowspan="1"> 2 </td>
		<td  rowspan="1"> 9.51 </td>
		<td  rowspan="1"> 3,153,600 </td>
		<td  rowspan="1"> 29,990,736 </td>
	</tr>
	<tr>
		<td  rowspan="1"> 3 </td>
		<td  rowspan="1"> 7.13 </td>
		<td  rowspan="1"> 3,153,600 </td>
		<td  rowspan="1"> 22,485,168 </td>
	</tr>
	<tr>
		<td  rowspan="1"> 4 </td>
		<td  rowspan="1"> 5.39 </td>
		<td  rowspan="1"> 3,153,600 </td>
		<td  rowspan="1"> 16,997,904 </td>
	</tr>
	<tr>
		<td  rowspan="1"> 5 </td>
		<td  rowspan="1"> 4.03 </td>
		<td  rowspan="1"> 3,162,240* </td>
		<td  rowspan="1"> 12,743,827.2 </td>
	</tr>
</table>

\* Both the first and the fifth year contain a leap day (29 Feb 2020 and
2024, respectively), which results in a larger number of generated
blocks compared to the other three years.

Note that in our LBFT 2.0 protocol, an impeach block in inserted into
the chain if the proposer is faulty or non-responding. Intuitively, a
faulty proposer cannot receive the reward. Hence, the amount of annual
supply could be smaller than the one listed in the table above.

### Lock Deposit

Use smart contracts to lock deposit, the functions are as follow:

> Determine the node level based on the amount of deposit of the node.
> lock the deposit to fixed range of length of blockchain. Reward
> distribution according to proportion of node's deposits. Connection
> with Reputation list.

## Hardware Specification

### Minimum Requirement

-   Memory: 4GB
-   Storage: 100GB
-   CPU: Intel Xeon E5-1650 v3 (alike)
-   Network: 300Mbps

::: tip

Some operation systems may have system processes with very large space
or computing overheads running in background. An example is
`tracker-store` in CentOS, which may cause up to 100% CPU load.

Beware of these kind of processes if you encounter an unexpected killing
of `cpchain` by the operation system, especially the one due to *out of
memory (OOM)* error.
:::

### Recommended Requirement

-   Memory: 16GB
-   Storage: 1TB
-   CPU: Intel Xeon E5-2686 v4 (alike)
-   Network: 1Gbps

### Example Configurations for Proposers

Cloud servers (like Microsoft Azure or Amazon Web Service) of monthly
cost at around 50 dollars suffice to become an RNode.

**Basic VPS configurations:**

-   

    Amazon Web Service t2.medium

    :   -   4GB memory, 2 vCPU, located in Singapore.
        -   \$0.0584 per hour pay as you go.
        -   \$0.03504 per hour pay one year reserved.

-   

    Microsoft Azure B2S

    :   -   4GB memory, 2 vCPU, located in Singapore.
        -   \$0.0528 per hour pay as you go.
        -   \$0.0309 per hour one year reserved.

**Better computing capability configurations:**

These severs are equipped with Xeon Processors.

-   

    Amazon Web Service c5.large

    :   -   4GB memory, 2 vCPU, in Singapore.
        -   \$0.098 per hour pay as you go.
        -   \$0.0588 per hour one year reserved.

-   

    Microsoft Azure F2s v2

    :   -   4GB memory, 2 vCPU, in Singapore.
        -   \$0.098 per hour pay as you go.
        -   \$0.0736 per hour one year reserved.

### Civilian Requirement

For normal civilians, a lower end of setup may also suffice. Our
experiments show that a server with 2GB memory can work normally for at
least thousands of blocks. But one requirement is that there are no
other space-consuming processes competing with `cpchain` for space
resources.

And usually a user run a civilian node to invoke APIs. Some APIs have
higher space and computing overheads like
[Cpc.getRNodes](../api/cpc_fusion.md#cpc-getrnodes). We recommend you to use a
machine with memory of at least 3GB as a civilian.

## Execution Fee - Gas System

All operations in CPC is not conducted free. An amount of tokens are
cost as operation fees, whose unit is denoted by **Gas**. Gas is
measured by the amount of computational overheads when executing a
certain operation. Every single operation, no matter transaction or
smart contract, is executed along with gas deducted.

Here we list important definitions:

1.  **Gas**, the unit measuring execution fee.
2.  **Gas Limit**, the maximum gas the applicant willing to pay.
3.  **Gas price**, the amount the applicant pays for each unit of gas.

### Gas

Gas is a special unit, measuring the amount of computational overheads
when executing a certain operation. Every operation is associated with
an fixed number of gas, indicating the computational effort of this
operation.

All gas-consuming operations are curated in
`configs/protocol_params.go`. An instance is shown below, demonstrating
the value of gas of a non-smart-contract transaction and creating a
smart contract.

``` {.go}
// Per transaction not creating a contract.
// NOTE: Not payable on data of calls between transactions.
TxGas                 uint64 = 21000
// Per transaction that creates a contract.
// NOTE: Not payable on data of calls between transactions.
TxGasContractCreation uint64 = 53000
```

Thus, a normal transaction requires 21,000 gas, while a smart contract
is created at a cost of 53000 gas.

### Gas Limit

Gas limit, as its name indicates, refers to the maximum gas a node is
going to pay in a transaction. Apparently, the equation
$gas \leq gasLimit$ always holds. It limits the upper bound of
transaction fees in a contract, and avoid a contract involving
unexpectedly high gas. This kind of situation occurs when an error, like
too much loops, is embedded in the contract.

Gas limit is tunable parameter when a node applies for a transaction. We
also offer a default setting for it, preventing the node from being
drained out.

### Gas Price

Gas price is the fee for each gas a node pays. By analogy, gas is like
gallon when fueling a car. Gas limit is the fuel tank of the car,
limiting maximum gas. And gas price is the petroleum price per gallon.
Thus, the total fee for a transaction is $gas \times gasPrice$.

When a node applies for a transaction, the system calculates a gas price
based on transaction history on the chain. However, gas price is also
tunable. A node can define gas price at any value as long as it can
afford it. Transactions with high gas price have higher chance being
selected by committee, and further get inserted into the chain. But it
expenses more for the node. In comparison, a low gas price demands low
cost of tokens, by sacrificing the possibility of being verified by
committee.

### Fee Calculation

The fee of a certain transaction is $gas \times gasPrice$. However, for
smart contract transaction involving multiple operations, fee cannot be
determined until the whole transaction terminates. Thus, when a node
applies for a transaction, it is required to pay
$gasLimit \times gasPrice$ tokens. And after the transaction terminates,
unused fee $(gasLimit-gas) \times gasPrice$ is refunded to this node.

Note that transaction fee as $gas \times gasPrice$ is not refundable.
Even the transaction fails, like an abnormal contract involving gas
outnumbering gas limit, the system does not refunds deducted fee. The
rationale is that committee members have assumed their responsibility of
verifying this transaction at the cost of their computing overheads,
which should be rewarded with transaction fee. In addition, this
mechanism avoids malicious nodes occupying computing capability of the
chain at no cost.
