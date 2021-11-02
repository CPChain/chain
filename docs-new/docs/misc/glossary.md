---
title: Glossary
---

| Term                      |           Description              |
| ------------------------- |:----------------------------------:|
| DPoR                      | Short for *Dynamic Proof of**Reputation*. It is the consensusalgorithm among proposers. |
| LBFT                      | Short for *Lightweight Byzantine**Fault Tolerance*. It is aconsensus algorithm inspired byPBFT. |
| LBFT 2.0                  | An improved version of LBFT.It is the current consensusalgorithm amongvalidators. |
| Validators Committee      | A group of users that can validatea newly proposed block. |
| Validator                 | A member of validators committee.|
| Proposers Committee       | A group of users elected for acertain term that can proposeblocks. |
| Proposer                  | A member of proposers committeethat can can proposes a new blockin this view. |
| Civilian                  | All users except the proposer andvalidators from the committee. |
| RNode                     | Short for *reputation node*.By depositing 200k tokens inreputation pool, a nodecan becomeanRNode.                                  |
| Economy node              | By depositing 20k tokens ineconomy node, a node can become aneconomy node. Sometimes it isabbreviated into *ENode*.|
| Industry node             | The node held CPChain partners.It can also propose blocks likeother RNodes.                                   |
| Seal                      | A unforgeable signature indicatingthe proposer of correspondingfor a certain block number.                                   |
| Sigs                      | An array of unforgeable signaturesthe proposer of correspondingfor a certain block number.                                   |
| Quorum                    | A quorum refers to a subset ofcommittee members that canrepresent the whole committeeto proceed to next state.|
| Strong Quorum             | A quorum of 2f+1 members. Itis used in normal cases. Unlessotherwise specified, *quorum* isalways referring to strong quorum.|
| Weak Quorum               | A quorum of f+1 members. It isonly used in impeach cases.                                   |
| Certificate               | a validator has a certificate ifit is a member of a quorum.holding a certificate indicates itcan enter the next state |
| Strong Certificate        | The certificate obtained by astrong quorum.                                   |
| Weak Certificate          | The certificate obtained by aweak quorum.                                   |
| P-Certificate             | A validator has a P-certificateif it has 2f+1 PREPARE messagesor f+1 impeach PREPARE messagesfor a certain block number. |
| C-Certificate             | A validator has a C-certificateif it has 2f+1 COMMIT messagesor f+1 impeach COMMIT messagesfor a certain block number. |
| Impeachment               | If a validator suspects the proposer is faulty or non-responding,it activate an impeachment process.  |
| Impeachment block         | In an impeachment, a validator isaiming to propose an impeach blockon behalf of the a faulty proposer. |
| Term                      | A term refers a period that a batchof proposers elected for a certainproposers committee. Term is amonotone increasing integer, whosevalue is added by one each timeit changes.|
| Epoch                     | An obsolete variable name for*term*. |
| TermLen                   | Short for term length. It refers tothe number of proposers in acertain term. This value limitsthe size of proposers committee,and remains a constant unless theconsensus model adjusts.|
| View                      | Available values of *view* are0,1, and 2. It represents thesequence number of the blocksealed by any proposer. Each viewcontains 12 blocks and theircorresponding proposers.|
| Round                     | An obsolete variable name for*view*.                                   |
| ViewLen                   | A proposer is able to propose oneor more blocks when it comes to itsview. The number of blocks it canpropose is ViewLen. It is alsofixed unless the consensus modeladjusts. |
| Period                    | Minimum time interval between twoconsecutive blocks.The value is set to 10 seconds.                                   |
