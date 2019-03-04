.. _consensus:

Consensus
=====================

DPoR Bipartite Committee
--------------------------

The consensus in LBFT 2.0 is determined by two two committees: **Validators Committee** and **Proposers Committee**.
Here we list the properties of validators and proposers, as well as the rest nodes denoted as civilians.


1. **Validators** or block validators refer to a group of users that can validate a newly proposed block.
    i. All validators together constitute **validators committee**.
    #. The validator committee consists of nodes nominated from CPC Foundation, governments and companies.
    #. Except for some abnormal cases, validators may not produce blocks.
    #. The validator committee follows our improved *LBFT* 2.0 protocol to achieve a consensus.
    #. The size of number is always equaling to 3f+1, where f is the number of byzantine nodes.

#. **Proposers committee** is a fixed number of elected RNodes for a certain term.
    i. The proposers committee is elected based on reputations of candidates and a random seed.
    #. Each incumbent member alternately assumes the responsibility to propose blocks during their tenure.
    #. The **proposer**, or block proposer refers to member assigned to propose a new block in current view.
    #. A proposer behaves inappropriately will face an `Impeachment`_ from validators which punishes this proposer due to its failure in proposal.

#. **Default proposers**, a special set of RNodes, have higher priority to be elected.
    i. RNodes with very high RPT and excellent maintenance history are qualified to apply for default proposers.
    #. Default proposers mainly play two following roles:
        i. Serve as backups in case of inadequate number of candidates;
        #. Constitutes a proportion of proposers committee assuring throughput.

#. Civilians refer to the rest of users.
    i. If a civilian is qualified as an RNode, it can claim campaign to be come a candidate.
    i. After being elected, the candidate is about to join proposers committee next term.


Normal and Abnormal Cases Handler
--------------------------------------


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
        #. This verification process scrutinizes the seal of proposer, timestamp, etc.
        #. If true, this validator broadcast a PREPARE message to other validators; otherwise, it enters Abnormal Case 2 or 3.
        #. Once receives 2f+1 PREPARE messages (P-certificate), a validator broadcasts COMMIT message to other validators.
        #. Once received 2f+1 COMMIT messages (C-certificate), a validator inserts the block into local chain, and broadcasts VALIDATE message long with these 2f+1 validators' signatures to all users.
        #. Once A validator receives the VALIDATE message for the first time in a view, it broadcasts a same message to all nodes.
        #. Any user receives this VALIDATE message with enough signatures, insert the block into local chain


#. **Abnormal Cases**
    a. Abnormal Case 1: *A validator does not receive a block from the proposer*
        i. It is for the case when Step 2.a.f cannot be reached
        #. Let the previousBlockTimestamp be the timestamp of block proposed in previous view, and period is the minimum interval between two blocks.
        #. A timer is set up when reaching the timestamp of previousBlockTimestamp+period.
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
        i. There are more complicated abnormal cases. We list them explicitly in `Countermeasures for Illicit Actions`_.



Note that a validator repeats a validate message (or impeach validate message) for the first time it receive it.
This repetition process ensures the validate message can be delivered to all nodes.
Refer to `Echo of Validate Message`_ to details.


Impeachment
--------------

Impeachment is a vital abnormal handler in LBFT 2.0, invoked when the proposer is either faulty, or non responding.
It is a two-phase protocol in PBFT manner, consisting of *prepare* and *commit* phases.
When a validator triggers its impeach process, it generates a block on behalf of the faulty (or non responding) proposer.
And impeachment has higher priority compared to normal case handler.
In other word, validator in impeachment does not process any normal case messages except for validate messages.
An impeachment can be activated under the following two cases:

1. The timer of validator expires;
#. A validator in idle state receives an illicit block from the proposer.

Timer expiration can be caused by several reasons, like a non-responding proposer, `Double Spend Attack`_ and `Past and Future Block`_.
An illicit block can be a block with improper transactions and seal.
Here we list the steps for an impeachment process.

Impeachment Steps
**********************

1. A validator v in the committee generates an impeachment block
    i. In the header of this block, the *timestamp* is set to be previousBlockTimestamp+period+timeout, where previousBlockTimestamp is the timestamp of block proposed in previous view, period is the interval between two blocks and timeout is the threshold validator that triggers impeachment.
    #. The *seal* in the header is set to be empty
    #. A penalty on proposer is the only transaction in the block's body
#. This block, used as an IMPEACH PREPARE message, is broadcast to all validators in the committee.
#. Once receives f+1 IMPEACH PREPARE messages with same header and body, validator v broadcasts an IMPEACH COMMIT message to other validators.
#. Once receives f+1 IMPEACH COMMIT messages, a validator broadcasts an IMPEACH VALIDATE message along with f+1 signatures to all users.
#. Any validate receives the IMPEACH VALIDATE message for the first time, it inserts the impeach block and broadcasts the same message to all nodes.
#. All users insert the block into local chain, if they receive an IMPEACH VALIDATE messages.


Explanation
****************


Three things are noteworthy here.
The first is that impeachment only requires two state instead of three in original PBFT.
The second one is that block can endorse a newly proposed block and an impeach block in a view.
The last one is that only a weak quorum certificate of f+1 members is required in impeachment consensus.

The absence of an idle state, or pre-prepare state in PBFT, results from the unnecessity of a leader.
Let's recall the roles of a leader in classic PBFT model.
The leader in classic PBFT model assumes the following responsibilities:

    i. Receive the request from the client, and broadcasts it to all backups in the distributed system.
    #. Assign a sequence number to each request, to guarantee that all requests are processed in order.

However, impeachment does not requires a leader to fulfill above duties, since:

    i. Each non faulty validator is about to propose a completely same block.
    #. Each block is associated with a unique block number, which circumvents the usage of sequence number.

The second is that a validator can sign two distinct blocks, one is the proposed block and another one is an impeach block.
Thus, it is possible for some validators obtains 2f+1 PREPARE messages of a newly proposed block,
while another validators obtain a prepare certificate for the impeach block.
This scenario occurs only when the proposer is faulty, misbehaves like `Double Spend Attack`_.
But it does not affects the security of the system.
Refer to `Double Spend Attack`_ to check detailed proof.


The last notable point is that a quorum in normal case consists of 2f+1 members,
while a quorum in impeachment consists of f+1 members.
The necessity of 2f+1 in normal case is that in extreme cases,
there are f faulty nodes send arbitrary messages, we need f+1 more loyal nodes to outnumber faulty counterparts.
In comparison, that even one loyal nodes triggers impeachment indicates a improper behavior of proposer.
Thus, f+1 impeachment validators suffice a quorum of impeachment.

In addition, impeachment also requires `Echo of Validate Message`_ similar to normal case handler.

Implementation
----------------------

Finite State Machine
*************************

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

For more detailed implementation, interested reader can refer to the pseudocode below (the grammar is close to golang).


**FSM for LBFT 2.0**


    .. code-block:: go

        // a general code for LBFT FSM
        func LbftFsm20(input, state) {
            switch state{
            case idle:
                idleHandler(input)
            case prepare:
                prepareHandler(input)
            case commit:
                commitHandler(input)
            case validate:
                validateHandler(input)
            case impeachPrepare:
                impeachPrepareHandler(input)
            case impeachCommit:
                impeachCommitHandler(input)
        }

**Utilities**

    .. code-block:: go

        // sign is a slice storing signs of a given block header
        // prepareSignatures stores signs of prepare messages for a given block header
        var prepareSignatures map[header]sign

        // commitSignatures stores signs of commit messages for a given block header
        var commitSignatures map[header]sign

        // refresh signatures
        func refreshPrepareSignatures(input) {
            header = header(input)  // Retrieve the block header of given message
            if input contains signs that are not stored in prepareSignatures[header]{
                append these signs into prepareSignatures[header]
            }
        }

        func refreshCommitSignatures(input) {
            header = header(input)  // Retrieve the block header of given message
            if input contains signs that are not stored in CommitSignatures[header]{
                append these signs into CommitSignatures[header]
            }
        }

        // determine whether a quorum certificate is sufficed
        func prepareCertificate(input) bool{
            if (len(prepareSignatures[header]) >= 2f+1) {
                return true
            }
            return false
        }

        func commitCertificate(input) bool{
            if (len(commitSignatures[header]) >= 2f+1) {
                return true
            }
            return false
        }

        func impeachPrepareCertificate(input) bool {
            if (len(prepareSignatures[header]) >= f+1) {
                return true
            }
            return false
        }

        func impeachCommitCertificate(input) bool {
            if (len(commitSignatures[header]) >= f+1) {
                return true
            }
            return false
        }

        // cacheBlock is invoked to cache a block if necessary
        func cacheBlock(block) {
            if block is not cached && verifyBlock(block){
                add block into the cache
            }
        }

**Normal Case Handlers**


    .. code-block:: go

        // handler for validate state
        // it is a quasi state for repeating validate message
        // the only valid input is validate message

        // it is worth mentioning that the operation broadcast can be executed to two groups of nodes:
        // one is all validators;
        // and the other one is all nodes including validators, civilians and proposers
        // all messages regarding consensus between validators are only sent to validators
        // newBlockMsg, in contrast, is sent to all nodes indicating a block is confirmed validated
        // unless otherwise specified, all broadcast operations are done only for validators

        func validateHandler(input) {
            switch input{
            // only accept normal case and impeachment validate message
            case validateMsg, impeachValidateMsg:
                insert the block
                broadcast newBlockMsg to all nodes including civilians
                transit to idle state
            }
        }

        // handler for commit state
        func commitHandler(input) {
            switch input{
            // when receive impeachment related messages
            case expiredTimer, impeachPrepareMsg, impeachCommitMsg, impeachValidateMsg:
                impeachHandler(input)
            case validateMsg:
                insert the block
                // echo of validate message
                broadcast validateMsg to validators
                // send out new block message
                broadcast newBlockMsg to all nodes
                transit to idle state
            case commitMsg:
                if commitCertificate {
                    broadcast validateMsg
                    transit to validate state
                }
            // add the block into the cache if necessary
            case block:
                cacheBlock(input)

        }

        // handler for prepare state
        func prepareHandler(input) {
            switch input{
            // when receive impeachment related messages
            case expiredTimer, impeachPrepareMsg, impeachCommitMsg, impeachValidateMsg:
                impeachHandler(input)
            case validateMsg, commitMsg:
                commitHandler(input)
            case prepareMsg:
                if prepareCertificate {
                    // it is possible for suffice two certificates simultaneously
                    if commitCertificate {
                        broadcast validateMsg
                        transit to validate state
                    } else {
                        broadcast commitMsg
                        transit to commit state
                    }
                }
            }
        }

        // handler for idle state
        func idleHandler(input) {
            switch input{
            // when receive impeachment related messages
            case expiredTimer, impeachPrepareMsg, impeachCommitMsg, impeachValidateMsg:
                impeachHandler(input)
            case validateMsg, commitMsg, prepareMsg:
                prepareHandler(input)
            case block:
                if !verifyBlock(block) {
                    propose an impeach block
                    broadcast the impeach block
                    transit to impeachPrepare state
                } else {
                // a cascade of determination of certificates
                    if prepareCertificate {
                        if commitCertificate {
                            broadcast validateMsg
                            transit to validate state
                        } else {
                            add block into the cache
                            broadcast prepareMsg
                            broadcast commitMsg
                            transit to commit state
                        }
                    } else {
                        add block into the cache
                        broadcast prepareMsg
                        transit to prepare state
                    }
                }
            }
        }

**Impeachment Handlers**

    .. code-block:: go

        // handler for impeach commit state
        func impeachCommitHandler(input) {
            switch input{
            case validateMsg:
                insert the block
                broadcast validateMsg
                broadcast newBlockMsg to all nodes
                transit to idle state
            case impeachValidateMsg:
                insert impeach block
                broadcast impeachValidateMsg
                broadcast newBlockMsg to all nodes
                transit to idle state
            case impeachCommitMsg:
                if impeachCommitCertificate(input) {
                    broadcast impeachValidateMsg
                    transit to validate state
                }
            }
        }

        // handler for impeach prepare state
        func impeachPrepareHandler(input) {
            switch input{
            case validateMsg, impeachValidateMsg, impeachCommitMsg:
                impeachCommitHandler(input)
            case impeachPrepareMsg:
                // it is possible to suffice two impeach certificates
                if impeachPrepareCertificate(input) {
                    if impeachCommitCertificate(input) {
                        broadcast impeachValidateMsg
                        transit to validate state
                    } else {
                        broadcast impeachCommitMsg
                        transit to impeachCommit state
                    }
                }
        }

        // a general impeachment message handler for normal case states
        func impeachHandler(input) {
            case expiredTimer:
                propose an impeach block
                add the impeach block into cache
                broadcast the impeach block
                transit to impeachPrepare state
            case impeachPrepareMsg, impeachCommitMsg, impeachValidateMsg:
                impeachPrepareHandler(input)
        }



Echo of Validate Message
*****************************

Echo of validates message refers to a mechanism in implementation that
a validator echoes a validate message when it receives it for the first time.
A validator does not insert a block, no matter a normal or impeach one,
until it receives a validate message.
This statement is valid even if a validator v sends out a validate message itself.
Validator v can only insert the block after it hears the echo from other validators.

The reason of introducing echo is to get rid of depending on one single validator broadcasting a validate message.
In an edge case, a validate can lose its connection while broadcasting a validate message.
If there were no echo mechanism, this edge case would sabotage the consistency of LBFT 2.0,
since only a proportion of nodes could receive this validate message.

Instead of trivially repeating validate message, we introduce a quasi state named as **validate** state.
The word *Quasi* here indicates that validate state is not a real state like idle state.
It does not contribute on consensus process, neither is compulsory.
It serves as following roles:

    1. A distinct state corresponding to validate message.
    #. Preventing a validator handling any messages from previous block height.
    #. A counter to make sure that each validator only broadcasts validate message only once.
    #. Partitioning original validate messages into two sets:
        a. Validate messages between validators committee.
        #. Validate messages broadcasts to all civilians (renamed as **New Block** message).

When a validator collects a commit certificate, the following operations are being executed:

    1. It enters validate state, and broadcasts a validate message to the validators committee.
    #. After it receives validate message from another validator, it broadcasts a new block message to all nodes including civilians.
    #. It enters idle state for the next block height.

For validators that have not suffice a commit certificate yet, it works as follows:

    1. If it receives a validate message, it broadcasts out two messages:
        a. validate message to all validators
        #. new block message to all civilians
    #. It enters idle state for the next block height.

Apparently, only validators that have collected a validate certificate can enter validate state.
The total number of validators in validate state can be larger than one,
since all validators and its message processing are running in parallel.
Other validators directly enters idle state after receiving a validate message.




Verification of Blocks
----------------------------


As stated in `Normal and Abnormal Cases Handler`_,
a validator verifies each newly proposed block before proceeding to next state.

A block, as shown below, contains a header and a list of transactions.


.. code-block:: go

    // Block represents an entire block in the CPChain blockchain.
    type Block struct {
        header       *Header
        transactions Transactions

        // caches
        hash atomic.Value
        size atomic.Value

        // Td is used by package core to store the total difficulty
        // of the chain up to and including the block.
        td *big.Int

        // These fields are used to track inter-peer block relay.
        ReceivedAt   time.Time
        ReceivedFrom interface{}
    }


Verification contains two parts, verification of transactions and header.


Transactions
****************

The ``transactions`` in a block are all pending transactions the proposer
holds before proposing it.
For a validator' standpoint, it does not care what transactions in the block,
neither it has any clue whether these transactions are correct.
It only checks whether the format of all transactions are correct.

An impeach block is different.
All transactions in an impeach block are composed by validators in a pre-defined format.
Any impeach block with different transactions will be regarded as faulty,
and rejected by all loyal validators.

Header
**********


Despite that the structure of transactions is relatively simple,
the header is rather complicated.
Here we further list all components in a header.

.. code-block:: go


    // Header represents a block header in the CPChain blockchain.
    type Header struct {
        ParentHash   common.Hash
        Coinbase     common.Address
        StateRoot    common.Hash
        TxsRoot      common.Hash
        ReceiptsRoot common.Hash
        LogsBloom    Bloom
        Number       *big.Int
        GasLimit     uint64
        GasUsed      uint64
        Time         *big.Int
        Extra        []byte
        Dpor         DporSnap
    }

``ParentHash``, as its name indicates, stores the hash of the parent block.
The validator rejects the block if ``ParentHash`` is inconsistent with the one of the last block in the chain.

``Coinbase``,

Countermeasures for Illicit Actions
------------------------------------------

Illicit actions refer any messages or blocks sending to a validator that cannot be processed in this validator's normal cases.
From validators' perspective, Illicit actions falls into the following categories:

1. Double spend attack from the proposer
#. An unknown ancestor block whose block height is higher than the one a validator is processing
#. A past or future block whose timer stamp is unexpected
#. A block from any unrecognized node (and potential DDoS attack)

Double Spend Attack
*********************

Double Spend Attack is that two distinct blocks are proposed by a proposer, and sent to validators.
If this attack succeeded, the proposer would be granted two sets of rewards,
and a fork would occur in the blockchain since two blocks with same block height were both legal.

The sophisticated mechanism in LBFT 2.0 protocol prohibits the occurrence of double spend attack.
The following lemmas holds in LBFT 2.0.

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
b and an impeach block b' both legit simultaneously?
The answer is no. Here we lists two lemmas and shows their correctness.

**Observation 1:** *It is possible that both a block b proposed from a proposer p and an impeach block b' suffice
a prepare certificate simultaneously.*

**Observation 2:** *It is impossible that both a block b proposed from a proposer p and an impeach block b' suffice
a commit certificate simultaneously.*

**Proof:** Observation 1 indicates that one quorum endorses b while another one endorse b'. It is possible
that if a loyal validator v1 signs b then broadcasts its prepare messages, but its receiver is blocked
such that it later proposes an impeach block. Combining f faulty validators, two quorums are made up.

However, Observation 2 ensures the safety of our consensus system. It is because once v1
proposes an impeach block b', it can no longer send out b’s commit message even if it collects a
prepare certificate for b. The state transmission of a validator is illustrated in the `Implementation`_.
Once a validator enters either impeach prepare or impeach commit phase, it no
long signs a normal block. **Q.E.D.**

Observation 2 leads to the following lemma:

**Lemma 2:** *A proposed block and an impeach block cannot be validated simultaneously.*

**Proof:** Given Observation 2, either a normal block or an impeach block can obtain a commit certificate.
Thus, they cannot be validated simultaneously. **Q.E.D.**

Combining both Lemma 1 and 2, we conclude the following theorem to guarantee the safety facing double spend attack.

**Theorem 1:** *LBFT 2.0 is guaranteed to generate only one validated block for each block height under double spend attack.*




Unknown Ancestor Block
*************************

An unknown ancestor block refers to a block whose block height is higher than the one the validator is currently processing.
The name comes from the fact that the predecessor of this block is yet unknown in the chain.


Four Scenarios
#################

Suppose a validator v which is processing a block b in block height h,
and receives an unknown ancestor block b\ :sub:`2`\   with block height h\ :sub:`2`\   from a node p\ :sub:`2`\ .
There are following possible scenarios:

1. The block is proposed by a legit proposer at the correct time; the validator is delaying.
#. The block is proposed by a legit proposer at an incorrect time.
#. The block is proposed by a faulty node.
#. The validator is lagging behind for at least one term, and cannot verify whether the proposer is legit.

Here the word *legit* indicates that p is an incumbent proposer from the committee in the current term,
having been recognized by v.
When a proposers committee is elected, each validator receives a list of all elected candidates as
well as the corresponding block heights to propose their blocks.
Thus, a validator has a priori knowledge on all legit proposers in this term, unless the proposer is
delaying for at least a term.


**First scenario:** b\ :sub:`2`\   actually is not an unknown ancestor block.

The validator v regards b\ :sub:`2`\   as an unknown ancestor block simply because it is delaying
After receiving b\ :sub:`2`\ , the validator v records the block in the cache.
As it is delaying, it is counted as one of f non-responding block.
Despite that it receives b\ :sub:`2`\ , v stays in the block height h,
and it does not participate in consensus of block height h\ :sub:`2`\
In other word, it does not broadcasts a prepare message endorsing b\ :sub:`2`\ .
Other members in the validators committee suffice a quorum to complete the consensus process on b\ :sub:`2`\   without v's participation.
v is going to catch up with the schedule after it receives the validate message from other committee members,
or by `Recovery`_.

**Second scenario:** p\ :sub:`2`\   behaves faultily.

Similar to the first scenario, v records it in the cache without signing it.
A quorum can still complete the consensus on b.
When it comes to the correct view of p\ :sub:`2`\ , if p\ :sub:`2`\   proposes the block again, then it is going to be processed normally.
Otherwise, the timer of a quorum of validators (including v) will expire and enter impeach process.

**Third and fourth scenario:** v cannot recognize p\ :sub:`2`\   as a proposer.

It can due to either b\ :sub:`2`\   is faulty (scenario 3) and v is delaying (scenario 4).
In both scenarios, v is going to sync, determining if it is delaying.
For the third scenario, v rejects b\ :sub:`2`\   and added v into blacklist.
For the fourth one, it acts same as the first scenario.

Here comes another concern.
A faulty node can raise a DDoS attack on validators, forcing them continuously syncing.
To address this issue, we can set a timer of a validator as the minimum gap between two syncs.
A reasonable setting is 10*|P| seconds, where \|P\| is the size of proposers
committee, and 10 is time interval between two consecutive blocks.

Thus, we can write a pseudocode to depict the processes above.

Pseudocode
###############

    .. code-block:: go

        func unknownAncestorBlockHandler(b2) {
            // v: a validator
            // b: the block v is processing
            // h: b’s block height
            // b2: a future block proposed by p2 with block height h2
            if h2<=h {
                return
            }
            if v knows p2 is a legit proposer {
                v stores b2 in the cache
                v continue processing b
            }
            if v has not synced for 10*|P| seconds {
                sync()  // v synchronizes with the committee
                unknownAncestorBlockHandler(b2)
            } else {
                punish p2
            }
        }

The primary principle underlying this pseudocode is that a validator does not process this unknown ancestor block
unless it is convinced the block is proposed by current proposer.
This principle assures the safety of LBFT 2.0 when facing mischievous blocks,
and relies on the rest loyal validators processing a proper one.


Past and Future Block
************************

Since all timer operations are depending on local timers of each validator,
timestamp of the block is not involved in consensus among validators.
Despite that timestamp does not play an important role in our consensus,
it is an important attribute of a block.
In fact, timestamp is one of factors verifying a block.

A validator v regards a block b as a future one, if the following two conditions are met:

    1. The timestamp of b is larger than the one of v;
    #. The block height of b is same as v.

Similarly, a block b' is considered a past block if

    1. The timestamp of b' is smaller than previousBlockTimestamp+period;
    #. The block height of b' is same as v,

where previousBlockTimestamp is the timestamp of previous block,
and period is the time interval between two consecutive blocks.

Do not confuse future block with the concept of unknown ancestor block.
An unknown ancestor block may holds a larger timestamp,
but are processed as an unknown ancestor one instead of a future block.

For past block, a validator fails in verifying it and triggers impeachment.
For a future block, the validator wait until the timestamp of the block.
But if it is larger than previousBlockTimestamp+period+timeout,
an impeachment is about to take place.
Thus, we come up with a psuedocode for timestamp verification.

    .. code-block:: go

        func timestampVerification(b) bool {
            // v: a validator
            // t: timestamp of v
            // b: a block with timestamp tb
            if tb < previousBlockTimestamp+period || tb > previousBlockTimestamp+period+timeout{
                return false
            }
            select{
                case <-Time.after(tb)
                    return true
                case <-quit //quit is true if v triggers impeachment
                    return false
            }
        }


Unrecognized Node and DDoS Attack
***************************************

An unrecognized node refers to any node that is not from the incumbent proposers committee.
When a validator receives a message from an unrecognized node,
it omits it if the block height is smaller or equal than the current one.
For messages with higher block height, the validator invokes `Unknown Ancestor Block`_ method to process it.


Malicious multiple messages from unrecognized nodes may form a DDoS attack against validators committee.
As described in `Unknown Ancestor Block`_,
an interval of at least 10*|P| between two consecutive synchronizations is enforced
to prevent I/O and computing resource exhaustion.

Recovery
-----------

LBFT 2.0 provides both liveness and safety under the assumption
that at most one third of validators misbehave in a certain view.
But without providing a recovery mechanism, the percentage of faulty validators would accumulate,
outnumber one third, and finally degrade superior safety of LBFT 2.0.
It motivates us to develop a sophisticated recovery mechanism, such that a delaying validator can catch up others.

Delaying validators are categorized into two different types according to how far behind they are:
1. The block height of delaying validator is same as the functioning validators
2. The validator delaying for at least a view.


Intra-view Recovery
*************************

Under the original framework of LBFT 2.0, once a validator has been losing its connection for a state,
it can hardly join the consensus process at the rest part of this view. Here we give an example.

**Example 1:** validator v\ :sub:`1`\  from a committee of four members, disconnects from the network in the prepare state.
The other three validators suffice a quorum for a prepare certificate and proceed to commit state.
Even v\ :sub:`1`\  somehow reconnects to the net, it cannot contribute to collect a commit certificate in this view
since it has yet collected a prepare certificate missed prepare messages from others.

Without any recovery, v\ :sub:`1`\  would be regarded as a non-responding node,
and return to normal consensus processing in the next view, after it receives a validate message.
The intra-view recovery address the problem by appending the certificate to the message.
Applying intro-view recovery in Example 1,
the other three validators broadcast a commit message accompanied with a prepare certificate.
Validator v\ :sub:`1`\  can forward to commit state after it verifies the certificate.

Some readers may wonder that LBFT 2.0 works perfectly as long as the assumptions are kept,
what the necessity of intra-view recovery is.
The key reason is that communications between validators are finished in the blink of an eye.
The possibility that a validator loses some packets is not that low.
Our experimental results indicate that even in a committee of four loyal validator,
one of them faces the problem that it lags behind one state every hundreds of blocks.

By introducing intra-view recovery, our system can tolerate two or more distinct validators
lose their connection in different states.
Even though this scenario violates our original assumptions, LBFT 2.0 with intra-view recovery reaches a consensus.
At the cost of larger space consumption for each message, we increase the robustness of the protocol.


Extra-view Recovery
*************************

If intra-view recovery does not work for a validator v and the block height of v is same as the chain,
it is about to catch up other validators once it receives a validate message.
As demonstrated in `Pseudocode`_, validate message (as well as impeach validate mesage) has highest priority,
which forwards v to idle state of next view regardless of the state of v.

However, if v has been losing its connection for a long time, it should invoke *sync* function.
Sync function, as indicated by the name, synchronizes with Mainnet chain.
Then it can rejoin consensus process after receiving validate message of the current view.
The function is called a validator suspects it is delaying like receiving `Unknown Ancestor Block`_.





Restore Cache
***************

Once a block is validated and inserted into the chain, it can be labelled as a permanent data.
And all permanent data are written in hard disks.
In comparison, information like current state, collected signatures as well as block caches are temporary data.
As temporary data are stored in volatile memory, they are not retained once a validator shuts down or restarts.
Hence, before a validator shuts down, it writes all temporary data in hard disk,
and retrieves these data after it starts up.

Note that it is highly possible that a validator is lagging behind other committee members after it restarts.
In this case, it processes the block as explained in `Unknown Ancestor Block`_.


Failback
-------------------

Failback is a process to restore the whole system after if all validators halt at the same time.
Apparently, the chain has to be suspended since no validator can continue working on consensus.
The main challenge here is to reach a consensus for the first block after all validators reboot.

From the proposer's perspective, it has no clue when the validation system can restore.
Thus, the first block right after the reboot of validators, must be an impeach block to regain liveness.

As we described in `Impeachment Steps`_, the timestamp of an impeach block is determined by previous block.
In the scenario of failback, we cannot use the equation previousBlockTimestamp+period+timeout to calculate the timestamp,
since this timestamp is out of date.
It motivates us to design a mechanism to reach a consensus on the issue of timestamp
among validators whose local clocks are not consistent.

We are aiming to fulfil two main objectives:

1. Reach a consensus on an impeach block with consistent timestamp
#. Do not design extra states of validators.

The second objective is to keep simplicity as well as robust of the system.
By exploiting existent five states to reach a consensus on timestamp,
we could reduce the risk of introducing new mechanism.


Preliminaries
**********************


Let t\ :sub:`i`\   be the local clock of validator v\ :sub:`i`\   .
Except for assumptions of LBFT 2.0, several more assumptions are required for failback procedure.
There exist a timestamp T larger than 0 satisfying following assumptions:

    1. The local clocks of all loyal validators (at least 2f+1) are within an interval of T.
    2. Maximum possible delay of broadcasting messages is less than T

The first assumption can be also interpreted as
max(t\ :sub:`i`\ -t\ :sub:`j`\ ) < 2T.
We name it as the sample space of validators.
This assumption is reasonable since all loyal validators are connecting to the network
and get their local clock calibrated before reboot.

Now we construct a set of discrete timestamps TS={t|t=2k*T, k is a natural number}.
A validator v\ :sub:`i`\   chooses timestamp ts for the failback impeach block, satisfying

1. ts\ :sub:`i`\   is an element of TS
#. ts\ :sub:`i`\   > t\ :sub:`i`\

After reboot, all validators are set to idle state.
When the local clock of v\ :sub:`i`\  is ts\ :sub:`i`\ , it proposes an impeach block with this timestamp,
and enters impeach prepare state.
If it cannot collect an impeach prepare certificate at ts\ :sub:`i`\   + 2T
v\ :sub:`i`\   proposes another impeach block with timestamp ts\ :sub:`i`\   +2T.
The rest of consensus part are same as LBFT 2.0.

In practice, T can be set to be 5 minutes.
Hence, the system can regain its liveness in 20 minutes.
The pseudocode is shown below.

Pseudocode
********************



    .. code-block:: go

        // this function can only be invoked when reboot
        func failback () {
            // v: a validator
            // t: local clock of v in Unix timestamp
            T := 600 // 5 minutes
            set the state to idle state

            // timestamp of failback impeach block
            Ts1 := (t/(2*T)+1)*2*T
            // the timestamp if no certificate collected for Ts1
            Ts2 := Ts1+2*T

            select{
                case <- Time.after(Ts1)
                    LBFTFsm20(expiredTimer, idle)
                case <- Time.after(Ts2)
                    LBFTFsm20(expiredTimer, idle)
            }

        }




This approach guarantees that an impeach block can reach validate state
within a time of at most 2T.
To prove the correctness of the algorithm, we will discuss several cases.


Correctness
*****************


**Theorem 2:**
*Function* ``failback`` *guarantees that validators committee can reach a consensus on an impeach block within 4T time.*

**Proof:**
Let v\ :sub:`i`\  represent i-th validator, and t\ :sub:`i`\  be its local clock timestamp.
Construct a set TS={t|t=2k*T, k is a natural number}.
Select three elements ts\ :sub:`0`\ , ts\ :sub:`1`\  and ts\ :sub:`2`\   from TS,
satisfying ts\ :sub:`2`\  = ts\ :sub:`1`\  + 2T= ts\ :sub:`0`\  + 4T,
ts\ :sub:`0`\  < min(t\ :sub:`i`\ ), and ts\ :sub:`2`\  > max(t\ :sub:`i`\ ).

Here we introduce two subsets of validators, V\ :sub:`1`\   and V\ :sub:`2`\ .
V\ :sub:`1`\   is made of all validators whose local clocks are smaller than ts\ :sub:`1`\   ,
and V\ :sub:`2`\   is made of all validators whose local clocks are large than or equal to ts\ :sub:`1`\ .

Here we discuss different cases according to the cardinalities of V\ :sub:`1`\   and V\ :sub:`2`\ .

**Case 1:** |V\ :sub:`2`\ | = 0.

It means all local clocks of loyal validators are between two timestamp ts\ :sub:`1`\   and ts\ :sub:`2`\ .
This is the simplest scenario. all validators agree on ts\ :sub:`1`\ .
And the system will insert the impeach block right after f+1 validators passes ts\ :sub:`1`\ .

Thus, the validators committee can collect an impeach certificate at ts\ :sub:`1`\ .

**Case 2:** |V\ :sub:`1`\ | >= f + 1, and |V\ :sub:`2`\ | < f + 1.

It means there are at least f+1 validators whose local clocks are smaller than ts\ :sub:`1`\ ,
but less than f+1 validators with their local clock larger than or equal to ts\ :sub:`1`\ .
It is similar to case 1.
Despite some validators agree on ts\ :sub:`2`\ , they cannot constitute a quorum.
When f+1 validators from |V\ :sub:`1`\ | passes ts\ :sub:`1`\ ,
the system will insert an impeach block.

Thus, the validators committee can collect an impeach certificate at ts\ :sub:`1`\ .

**Case 3:** |V\ :sub:`1`\ | < f + 1, and |V\ :sub:`2`\ | >= f + 1.

It means there are no more than f+1 validators whose local clocks are smaller than ts\ :sub:`1`\ ,
but at least f+1 validators with their local clock larger than or equal to ts\ :sub:`1`\ .
In this case, when f+1 validators from V\ :sub:`2`\   reaches timestamp ts\ :sub:`2`\ ,
an impeach block certificate can be collected by all online validators.

Thus, the validators committee can collect an impeach certificate at ts\ :sub:`2`\ .


**Case 4:** |V\ :sub:`1`\ | < f + 1, and |V\ :sub:`2`\ | < f + 1.

In this case, validators in V\ :sub:`1`\   cannot suffice a certificate for t\ :sub:`1`\ .
Because at least we have loyal f+1 validators online,
the equation |V\ :sub:`1`\ |+|V\ :sub:`2`\ | >= f+1 must hold.
When time flows, validators in V\ :sub:`1`\  gradually pass timestamp ts\ :sub:`2`\ .
And these validators propose another impeach block agreeing on ts\ :sub:`2`\ .
Thus, there exists a subset V\ :sub:`1`\ \' of validators in V\ :sub:`1`\
such that V\ :sub:`1`\   reaches ts\ :sub:`2`\
and |V\ :sub:`1`\ \'|+|V\ :sub:`2`\ | >= f+1.

Let ts\ :sub:`3`\  be the next timestamp in TS after ts\ :sub:`2`\ ,
i.e., t2\ :sub:`3`\  = ts\ :sub:`2`\  + 2T.
As we can see, the validator with largest local timestamp has not reached ts\ :sub:`3`\   yet.
At this moment, V\ :sub:`1`\  \'+V\ :sub:`2`\   suffices a quorum
for an impeach block agreeing on ts\ :sub:`2`\ .

Thus, the validators committee can collect an impeach certificate at ts\ :sub:`2`\ .


**Case 5:** |V\ :sub:`1`\ | >= f + 1, and |V\ :sub:`2`\ | >= f + 1.

At first glance, it seems impeach block of either ts\ :sub:`1`\   and ts\ :sub:`2`\   is legal.
However, validators in V\ :sub:`1`\   reaches ts\ :sub:`1`\   earlier than
counterparts in V\ :sub:`2`\   reaching ts\ :sub:`2`\ .
The reason is simple, as the the following equation indicates:
ts\ :sub:`2`\   - max(t\ :sub:`i`\ ) > ts\ :sub:`1`\   + 2T - (min(t\ :sub:`i`\ )+T)
> ts\ :sub:`1`\    - min(t\ :sub:`i`\ ).

Thus, the validators committee can collect an impeach certificate at ts\ :sub:`1`\ .


By summing up above five cases, we can conclude that the theorem holds. **Q.E.D**





Comparison with PBFT
---------------------------

This section compares LBFT 2.0 with classic PBFT.
We name both proposer in LBFT 2.0 and primary replica in PBFT as the leader,
since they assume similar responsibility to dispatch a query to all nodes.
And insistence on P-certificate indicates that
a replica does not changes its endorsement in a query once it collects a prepare certificate.

In other word, LBFT 2.0 has weaker assumption, higher liveness and more complicated faulty
leader handler. Note that the view change reduces the faulty leader problem into a normal case
handler in the next view. We cannot adopt similar method since our high command on liveness.
Liveness is also the reason that a validator cannot insist on a P-certificate.


+---------------------------+------------------------------------+-----------------------------+
| Aspect                    |           LBFT 2.0                 |         PBFT                |
+===========================+====================================+=============================+
| Assumption                | Tolerate at most f faulty          | Tolerate at most f replicas |
|                           | validators and a faulty proposer   |                             |
+---------------------------+------------------------------------+-----------------------------+
| Liveness                  | Insert a block every 10 seconds    | Response in finite time     |
+---------------------------+------------------------------------+-----------------------------+
| Insistence on             | Trigger impeachment if timer       | Insist on the query with    |
| P-certificate             | expires                            | P-certificate               |
+---------------------------+------------------------------------+-----------------------------+
| Faulty leader handler     | Impeachment                        | View change                 |
+---------------------------+------------------------------------+-----------------------------+


