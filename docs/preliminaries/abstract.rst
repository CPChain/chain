.. _abstract:


Abstract
=========================

This page succinctly describes the features and novelty of CPChain.

We present a CPChain, a blockchain infrastructure for the next generation IoT.
The main novelties of the CPChain are its
**CPChain ecosystem**,
**BFT consensus protocol**,


In CPChain, a bipartite committee constitutes the core members of the chain.
We separate the rights of proposing and validating a certain block,
to reduce the potential risk of misbehavior.

The consensus protocol of CPChain, namely LBFT 2.0,
is a three-layer consensus algorithm handling Byzantine fault problem in a blockchain.
On one hand, the majority of existing blockchain,
can hardly handle a Byzantine fault due to its fully decentralized structure.
On the other hand, classic Practical Byzantine Fault Tolerance (PBFT) algorithm cannot
be trivially applied in a blockchain.
Thus, we are motivated to develop LBFT 2.0,
an algorithm retaining the the superior 1/3 fault tolerance of PBFT while
perfectly fit in a blockchain.
In particular, each validator is a five-state finite state machine,
accepting legal blocks and reject illegal ones.