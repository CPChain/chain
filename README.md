# The Cyber Physical Blockchain

***Towards a trusted future with blockchain.***

[![Website](https://i.imgur.com/MzU7ovE.png)](https://www.cpchain.io)
 

[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![Pull Requests](https://img.shields.io/bitbucket/pr-raw/cpchain/chain.svg)](https://bitbucket.org/cpchain/chain/pull-requests/)

IoT is having a profound and unprecedented impact on human society. However, without trust, it is no
more than a castle built on sand. You share the benefits, but with your privacy and financial safety
as the cost.


For us, **trust** is of utmost concern. **The mission of cpchain is to build a vital IoT ecosystem
which is secured by the blockchain technology.** Everyone can enjoy the convenience of M2M
payment, self-driving, wearable monitoring, etc. to the fullest extent without worry.


We are shaping a trusted future with blockchain, from smart home to smart city, from edge to cloud
computing, with you and with everyone! Please come and join us.  
[![Follow Twitter](https://img.shields.io/twitter/follow/cpchain_io.svg?label=Follow&style=social)](https://twitter.com/intent/follow?screen_name=cpchain_io)


*While the codebase has evovled much since the first commit, we owe a debt of thanks to
[go-ethereum](https://github.com/ethereum/go-ethereum) for the initial codebase.*

# Table of Contents
- [Features](#features)
- [Installation](#installation)
- [Quick Start](#quick-start)
- [Documentation](#documentation)
- [Tools and Libraries](#tools-and-libraries)
- [Contributing](#contributing)
- [FAQ](#faq)
- [Contact](#contact)
- [License](#license)


---
## Features
### LBFT Consensus

We propose LBFT (Lightweight Byzantine Fault Tolerance), 
a two-phase algorithm aiming to achieve a fast consensus among the committee.
The two phases are prepare and verification respectively. 


In prepare phase, the leader of the committee member constructs a block and broadcasts to all members in the committee. 
Each committee member that receives the block is about to verify the block enters the verification phase. 
It signs a verified block, and broadcasts to other members. 
Once a member collects signatures from two thirds of committee members, 
it commits the block to the network. 
This two-phase process provides the robustness of our system 
when at most one third of committee members delay or act unexpectedly.


We further improve our LBFT algorithm to version 2.0, providing higher robust 
to achieve a consensus among the committee while retaining the properties of liveness and safety. 
The core ideas are **bipartite committee** and **impeachment** process.

The figure below illustrate the detailed steps of LBFT 2.0: ![LBFT 2.0](https://i.imgur.com/44njmCj.jpg)

The bipartite committee refers to two separate committees, namely, 
the **proposers committee** and the **validators committee**. A Proposer is a node elected 
based on its reputation. It takes the responsibility of proposing a block and broadcasting to validators.
All proposers of a certain term constitute the proposers committee.

Meanwhile, the validator committee consists of nodes nominated by CPC Foundation, governments and companies.
Unlike proposers, validators cannot propose a block in normal cases. 
This committee validates a newly proposed block in three phases, 
similar to PBFT (Practical Byzantine Fault Tolerance). 
And it can also tolerate at most one third faulty or non-responding members. 


This bipartite structure eliminates the role of the primary node of traditional PBFT protocol. 
In addition, it guarantees the independence of block proposal and validation, which decreases 
the risk and feasibility of byzantine faults. 


To handle abnormal cases, we propose **impeachment**, 
a novel two-phase protocol assuring the properties of both liveness and safety in LBFT 2.0. 
When a validator suspects the proposer is faulty, it proposes an impeach
block on behalf of the faulty proposer. The validators committee is about to 
achieve a consensus on this impeach block if a quorum of validators considers 
the proposer faulty. 



### Private Transactions

We design a data privacy mechanism that allows users to conduct private transactions on cpchain in a
secure manner. Other than the valid participants, no one else has the ability to see the
transaction. While private transactions are invisible for outsiders, we keep critical footprint of a
transaction on chain for later audition.

A user scenario:
![private transaction user scenario](https://i.imgur.com/H3L1vJN.png)


---

## Installation

### Download stable binaries

All versions of cpchain are built and available for download [here](https://bitbucket.org/cpchain/chain/downloads/).

The download page provides a zip file, containing the executable files that can be used without installing.

### Building from source

Install latest distribution of [Go](https://golang.org/) if it has yet to be installed. Do not forget to configure $GOPATH. Then clone the repository to a directory that you'd like:

```shell
git clone https://bitbucket.org/cpchain/chain.git
```

Finally, build the programs using the following commands.

```shell
cd chain
make clear
make all
```




---
## Quick Start

After installation, you are able to start running cpchain. 
Refer to `./build/bin/cpchain --help` to check the help menu.

### Connect to testnet
```shell
cd build/bin
./cpchain run --runmode testnet
```

### Create an account
```shell
./cpchain account new --datadir ./datadir
```

### Run a private network
```shell
cd examples/cpchain
./cpchain-all.sh

check logs
tail -f data/logs/*.log | grep number=
```

##4 Run a local node
```shell
./cpchain run --datadir ./datadir --unlock <You Address>
```

    
---
## Documentation
The above should be enough to get you up to speed. For details, please visit our [documentation portal](https://docs.cpchain.io).


---
## Tools and Libraries
### CPChain Blockchain Explorer
Check our [website repository](https://github.com/CPChain/cpchain-website).
It shows the ongoing transactions and blocks.


---
## Contributing
Your hacks are always welcome!🔨🔨🔨

Please fork on bitbucket and make pull request [there](https://bitbucket.org/cpchain/chain/pull-requests/).


---
## FAQ
- When will the mainnet be formally launched?

  The scheduled launch time is in late March, 2019.


---
## Contact
Shout to us at one of the following places!

- Website at [cpchain.io](https://cpchain.io)
- Twitter at [@cpchain_io](https://twitter.com/cpchain_io)
- Telegram at [cpchain](https://t.me/cpchain)

---
## License
Unless otherwise specified in the source files (or the vanilla files from go-ethereum), the licence by
default is [![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)

Copyright 2018-2025 © [The CPChain Foundation](https://www.cpchain.io)