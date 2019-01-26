.. _consensus:

Consensus
=====================

Dpor Bipartite Committee
--------------------------

The consensus in LBFT 2.0 is determined by two two committees: **Validators Committee** and **Proposers Committee**.
Here we list the properties of validators and proposers, as well as the rest nodes denoted as civilians.


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
----------------


Before we dive into explaining case handler, let us introduce an important concept **quorum**.
A quorum is a subset of validators committee members such that a consensus can be reached among a quorum in a certain state.
These quorum have two vital properties:

1. Intersection: any two quorums have at least one loyal validator in common.
#. Availability: there is always a quorum available with no faulty validator.

When members in a quorum endorse information from a same block, they collect a *quorum certificate*.
There are two certificates, prepare certificate (P-certificate) and commit certificate (C-certificate), which indicates
that there exist a quorum agree on a prepare message and a commit message respectively.



1. **Normal Case**
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
        #. Once A validator receive the VALIDATE message for the first time in a view, it broadcast a same message to all nodes.
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
    #. Other complicated abnormal cases:
        i. There are more complicated abnormal cases. We list them explicitly in `Illicit Actions`_.


Impeachment
--------------


#. **Impeachment**
    a. It is an abnormal handler when the proposer is either faulty, or non responding
    #. It is a two-phase protocol in PBFT manner, consisting of *prepare* and *commit* phases.
    #. Impeachment steps:
        a. A validator in the committee generates a block on behalf of the faulty (or non responding) proposer.
            i. In the header of this block, the *timestamp* is set to be previousBlockTimestamp+period+timeout, where previousBlockTimestamp is the timestamp of block proposed in previous view, period is the interval between two blocks and timeout is the threshold validator that triggers impeachment.
            #. The *seal* in the header is set to be empty
            #. A penalty on proposer is the only transaction in the block's body
        #. This block, used as an IMPEACH PREPARE message, is broadcast to all validators in the committee.
        #. Once receives f+1 IMPEACH PREPARE messages with same header and body, a validator broadcasts an IMPEACH COMMIT message to other validators.
        #. Once receives f+1 IMPEACH COMMIT messages, a validator broadcasts an IMPEACH VALIDATE message along with f+1 signatures to all users.
        #. Any validate receives the IMPEACH VALIDATE message for the first time, it insert the impeach block and broadcast the same message to all nodes.
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


Note that a quorum in normal case consists of 2f+1 members, while a quorum in impeachment consists of f+1 members.
The necessity of 2f+1 in normal case is that in extreme cases,
there are f faulty nodes send arbitrary messages, we need f+1 more loyal nodes to outnumber faulty counterparts.
In comparison, that even one loyal nodes triggers impeachment indicates a improper behavior of proposer.
Thus, f+1 impeachment validators suffice a quorum of impeachment.

In addition, a validator repeats a validate message (or impeach validate message) for the first time it receive it.
This repetition process ensures the validate message can be delivered to all nodes.
In an edge case, a node can lose its connection while broadcasting a validate message.
If there were no repetition mechanism, this edge case would sabotage the consistency of LBFT 2.0.

Finite State Machine
----------------------

The LBFT 2.0 protocol can be considered as a finite state machine (FSM) with 5 states:
**idle**, **prepare**, **commit**, **impeach prepare** and **impeach commit**.
The former three states are designed for normal cases, and the rest are specializing in handling abnormal cases.

The illustration below demonstrates these five states as well as transitions between states.
Note that not all transitions are shown in this figure due to the lack of space.
The text on an arrow between two states refers to the condition of this transition.
And the message box near the arrow represents the message broadcast to other nodes.

.. image:: lbft_fsm.png


Pseudocode
*************

For more detailed implementation, interested reader can refer to the pseudocode below.


**FSM for LBFT2.0**


    .. code-block:: go

        LbftFsm20(input, state) {
            switch state{
            case idle:
                idleHandler(input)
            case prepare:
                prepareHandler(input)
            case commit:
                commitHandler(input)
            case impeachPrepare:
                impeachPrepareHandler(input)
            case impeachCommit:
                impeachCommitHandler(input)
        }


**Normal Case Handlers**


    .. code-block:: go

        commitHandler(input) {
            switch input{
            case expiredTimer, impeachPrepareMsg, impeachCommitMsg, impeachValidateMsg:
                impeachHandler(input)
            case validateMsg:
                insert the block
                broadcast validateMsg
                transit to idle state
            case commitMsg:
                if commitCertificate {
                    broadcast validateMsg
                    transit to idle state
                }
            case block:
                if block is not cached{
                    if verifyBlock(block) {
                        add block into the cache
                    }
                }
        }

        prepareHandler(input) {
            switch input{
            case expiredTimer, impeachPrepareMsg, impeachCommitMsg, impeachValidateMsg:
                impeachHandler(input)
            case validateMsg, commitMsg:
                commitHandler(input)
            case prepareMsg:
                if prepareCertificate {
                    broadcast commitMsg
                    if commitCertificate {
                        broadcast validateMsg
                        transit to idle state
                    }else{
                        transit to commit state
                    }
                }
            }
        }

        idleHandler(input) {
            switch input{
            case expiredTimer, impeachPrepareMsg, impeachCommitMsg, impeachValidateMsg:
                impeachHandler(input)
            case validateMsg, commitMsg, prepareMsg:
                prepareHandler(input)
            case block:
                if !verifyBlock(block) {
                    propose an impeach block
                    broadcast the impeach block
                    transit to impeachPrepare state
                }
                else{
                    add block into the cache
                    broadcast prepareMsg
                    if prepareCertificate {
                        broadcast commitMsg
                        if commitCertificate {
                            broadcast validateMsg
                            transit to idle state
                        }else{
                            transit to commit state
                        }
                    }else{
                        transit to prepare state
                    }
                }
            }
        }

**Impeachment Handlers**

    .. code-block:: go

        impeachCommitHandler(input) {
            switch input{
            case validateMsg:
                insert the block
                broadcast validateMsg
                transit to idle state
            case impeachValidateMsg:
                insert impeach block
                broadcast impeachValidateMsg
                transit to idle state
            case impeachCommitMsg:
                if impeachCommitCertificate(input) {
                    broadcast impeachValidateMsg
                    transit to idle state
                }
            }
        }

        impeachPrepareHandler(input) {
            switch input{
            case validateMsg, impeachValidateMsg, impeachCommitMsg:
                impeachCommitHandler(input)
            case impeachPrepareMsg:
                if impeachPrepareCertificate(input) {
                    broadcast impeachCommitMsg
                    if impeachCommitCertificate(input) {
                        broadcast impeachValidateMsg
                        transit to idle state
                    }
                    transit to impeachCommit state
                }
        }

        impeachHandler(input) {
            case expiredTimer:
                propose an impeach block
                broadcast the impeach block
                transit to impeachPrepare state
            case impeachPrepareMsg, impeachCommitMsg:
                impeachPrepareHandler(input)
        }


Illicit Actions
----------------------

Illicit actions refer any messages or blocks sending to a validator that cannot be processed in this validator's normal cases.
From validators' perspective, Illicit actions falls into the following categories:

1. Double spend attack from the proposer
#. A future block whose block height is higher than the one a validator is processing
#. A past block whose block height is higher than the one a validator is processing
#. A block from any unrecognized node

Double Spend Attack
*********************

Double Spend Attack is that two distinct blocks are proposed by a proposer, and sent to validators.
If this attack succeeded, the proposer would be granted two sets of rewards,
and a fork would occur in the blockchain since two blocks with same block height were both legal.

The sophisticated mechanism in LBFT 2.0 protocol prohibits the occurrence of double spend attack.
The following theorem holds in LBFT 2.0.

**Lemma 1:** *There cannot exist two blocks proposed by a same node with the same block number being validated simultaneously.*

**Proof:** Assume that a proposer p proposes two distinct blocks b and b', and broadcasts them to validators.
And to achieve its wicked purpose, f faulty validators collaborate with p.
Suppose that p fulfill its wicked aim that both b and b' are inserted into the chain.
Thus, there exists two quorums of validators that endorse b and b' respectively.
Since only 3f+1 members in the committee, these two quorums have f+1 members in common. Except for f faulty validators
can be members of both quorums, there still exits one validator signs both b and b'. It contracts the
fact that each loyal validator only sign one block. Hence, there cannot be two proposed blocks are
both legit. **Q.E.D.**



In contrast to the fact that each validator only signs one proposed block, a validator can sign an
impeach block even if it has signed a block from p given that it cannot collect a certificate on time.
Then is that possible for a proposer takes advantages of this mechanism to makes its proposed block
b and an impeach block b0 both legit simultaneously?
The answer is no. Here we lists two lemmas and shows their correctness.

**Observation 1:** *It is possible that both a block b proposed from a proposer p and an impeach block b' suffice
a prepare certificate simultaneously.*

**Observation 2:** *It is impossible that both a block b proposed from a proposer p and an impeach block b' suffice
a commit certificate simultaneously.*

**Proof:** Observation 1 indicates that one quorum endorses b while another one endorse b'. It is possible
that if a loyal validator v1 signs b then broadcasts its prepare messages, but its receiver is blocked
such that it later proposes an impeach block. Combining f faulty validators, two quorums are made up.

However, Observation 2 ensures the safety of our consensus system. It is because once v1
propose an impeach block b0, it can no longer send out b’s commit message even if it collects a
prepare certificate for b. The state transmission of a validator is illustrated in the `Finite State Machine`_.
Once a validator enters either impeach prepare or impeach commit phase, it no
long signs a normal block. **Q.E.D.**

Observation 2 leads to the following lemma:

**Lemma 2:** *A proposed block and an impeach block cannot be validated simultaneously.*

**Proof:** Given Observation 2, either a normal block or an impeach block can obtain a commit certificate.
Thus, they cannot be validated simultaneously. **Q.E.D.**




