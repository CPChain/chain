# Abstract

This page succinctly describes the features and novelty of CPChain.

We present a CPChain, a blockchain infrastructure for the next
generation IoT. The main novelties of the CPChain are **BFT consensus
protocol**, and **CPChain ecosystem**.

In CPChain, a bipartite committee constitutes the core members of the
chain. We separate the rights of proposing and validating a certain
block, to reduce the potential risk of misbehavior.

The consensus protocol of CPChain, namely LBFT 2.0, is a three-layer
consensus algorithm handling Byzantine fault problem in a blockchain. On
one hand, the majority of existing blockchain, can hardly handle a
Byzantine fault due to its fully decentralized structure. On the other
hand, classic Practical Byzantine Fault Tolerance (PBFT) algorithm
cannot be trivially applied in a blockchain. Thus, we are motivated to
develop LBFT 2.0, an algorithm retaining the the superior 1/3 fault
tolerance of PBFT while perfectly fit in a blockchain. In particular,
each validator is a five-state finite state machine, accepting legal
blocks and reject illegal ones. Correctness of these algorithms are
guaranteed by mathematical proofs, formal specification (via TLA+),
exhaustive test cases and plans for all possible abnormal cases and
attacks.

The CPChain ecosystem are constituted by three kinds of nodes: Economy
nodes (ENodes), Reputation Nodes (RNodes), and Industry Nodes. ENodes
gain interest for each of a year by holding a certain amount of tokens.
RNodes have the right to mine a block, to earn maintenance rewards.
Industry Nodes are special nodes endorsed by CPChain Foundation, which
reflects the some properties of permissioned blockchain.

We experimentally evaluate the performance of Chain in public
environment for a month. Over 70 RNodes and 800 common nodes all over
the world have participated in this testing. In total 400,000 blocks a
long with 4.4 million transactions are generated during the month. And
the transactions peeks at 1,000 blocks per second.

In summary, our contributions are as follows:

1\. We propose LBFT 2.0 protocol that can handle at most 1/3 of faulty
nodes in the validation process

2\. We design DPoR consensus among proposers committee, which evaluates
RPT value for each RNode based on five dimensions.

3\. We design an ecosystem that nodes can gain rewards from various
methods.

4\. We theoretically prove the accuracy of the algorithm. And we use
TLA+ as the formal specification language to guarantee the correctness
of the concurrent processing. In addition, we have exhaustive test cases
and plans to handle latent risk and attacks.

5\. We experiment with hundreds of nodes all over the nodes in a public
environment for a month. The results show satisfactory stability as well
as throughput of the chain. And the value of 1000 tps is on a par with
the existing BFT-like blockchains.
