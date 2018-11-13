# DPoR - Dynamic Proof of Reputation, a PBFT based consensus protocol

## Keywords

    consensus protocol, PBFT, reputation calculaction.

## Introduction

* PBFT based
* Reputation Calculation involved
* Dynamic Committee
* Round Robin style
* ViewChange with empty block

## Terminology

* Committee
    a group of signers

* Signer
    sign a block to make it legal

* Leader
    generate a block and broadcast to all signers

* Epoch
    epoch is the committee size
    epoch index is the index of different committee

* Round
    round is the index of a signer in a committee

* View
    view is the number of blocks a signer can generate in a committee

## Consensus

1. Consensus States

    * New Round
    * Preprepared
    * Prepared
    * Committed
    * Final Committed

2. State Transitions

    ```mermaid
    graph LR;
        A(NewRound)-- #1 -->B;
        B(Preprepared)-- #2 -->C;
        C(Prepared)-- #3 -->D;
        D(Committed)-- #4 -->E;
        E(FinalCommitted)-- #5 -->A;
    ```

    #1
    the leader generated the block and broadcasted to all signers
    a signer received the propragated block, validated basic fields of the block, then sign it and broadcast prepare msg.

    #2
    a signer received enough prepare msg, then broadcast commit msg.

    #3
    a signer received enough commit msg, then try to insert into chain.

    #4
    a signer inserted the block into local chain.

    #5
    a signer broadcasted the block to all of his normal peers.

3. Leader Selection(View Change in PBFT)

4. Committee Election

5. Reputation Calculation

## Architecture

* Call Graph

```mermaid
graph LR;
    CmdRun-->CpchainService;
    CpchainService-->ProtocolManager;
    CpchainService-->Dpor;
    ProtocolManager-->Miner;
    ProtocolManager-->Dpor;
    ProtocolManager-->Blockchain;
    Dpor-->DporHandler;
    Dpor-->Snapshot;
    Snapshot-->RptCollector;
    RptCollector-->campaignc[Campaign Contract];
    RptCollector-->rptc[Rpt Contract];
    RptCollector-->pdashc[Pdash Contract];
    Snapshot-->Election;
    DporHandler-->Signer;
    DporHandler-.->ProtocolManager;
    DporHandler-.->Miner;
    DporHandler-.->Dpor;
    DporHandler-.->Blockchain;
```

## Committee Network Building

```mermaid
graph TB;

A(received a block) --> B{verify the block};
B -- true --> C{check if signer};
B -- false --> C1(discard the block);
C -- true --> D(upload my NodeID);
C -- false --> D1(do nothing);
D --> E(fetch other signers' NodeIDs);
E --> F(dial other signers);

G(received a new signer request) --> H{verify the signer};
H -- true --> I(build the connection);
H -- false --> I1(ignore the request);
I --> J(start to sync and broadcast);
```