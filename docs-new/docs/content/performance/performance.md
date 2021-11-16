# Performance

Under different environments, the chain performs differently. There are
two particular environment setups that we are specifically interested in
**public environment** and **controlled environment**.

## Public Environment

The public environment refers to the real world. It has the following
traits:

-   The nodes are distributed all over the world;
-   Each nodes has drastically different configurations in terms of both
    hardware and network;
-   Each nodes is operated by a distinct user that not familiar with
    CPChain implementation;
-   Not all nodes are updated to latest version.

All validators, deployed by CPChain Foundation, have identical
configurations. They are deployed in AWS (Amazon Web Services) in
Singapore.

-   **VPS model:** AWS t2.large model.

-   

    **Network condition:** 1 Gbps

    :   It is an estimated speed. AWS does not offer an exact number of
        network performance for AWS t2.large model.

-   **Location:** all in Singapore.

-   **Processor:** 3.0 GHz Intel Scalable Processor.

-   **Memory:** 8 GB.

-   **Number:** in total 7 servers.

Under this setting, we conducted a beta test between 1 May and 5 June
2019. In total, 795 common nodes all over the world, 70 RNodes and 7
verification nodes distributed in Singapore participated in the test. In
the end, the Beta Mainnet received 700,000 blocks (including nearly
300,000 blocks generated during the Beta test), 4.4 million
transactions, and the transaction peaked at 1,000 transactions per
second.

## Controlled Environment

The controlled environment refers to perfect condition. It has the
following traits:

-   All nodes are either distributed in local are network or launched in
    multiple threads in a server.
-   The network bandwidth can be considered unlimited, or reaching
    maximum ethernet capability.
-   All nodes are all updated to the latest version.
-   All nodes have identical local clocks.

Under this setting, we can push tps to the maximum value of 10,000.
