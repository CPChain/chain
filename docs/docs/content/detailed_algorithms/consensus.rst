.. _consensus:

Consensus
=====================

.. _bipartite:

DPoR Bipartite Committee
--------------------------

The consensus in LBFT 2.0 is determined by two committees: **Validators Committee** and **Proposers Committee**.
Here we list the properties of validators and proposers, as well as the rest nodes denoted as civilians.


1. **Validators** or block validators refer to a group of users that can validate a newly proposed block.
    i. All validators together constitute **validators committee**.
    #. The validators committee consists of nodes nominated from CPC Foundation, governments and companies.
    #. Except for some abnormal cases, validators may not produce blocks.
    #. The validators committee follows our improved *LBFT* 2.0 protocol to achieve a consensus.
    #. The size of number is always equaling to :math:`3f+1`, where :math:`f` is the number of Byzantine nodes.

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
    i. After being elected, the candidate is about to join proposers committee in future term.


Normal and Abnormal Cases Handler
--------------------------------------


Before we dive into explaining case handler, let us introduce an important concept **quorum**.
A quorum is a subset of validators committee members such that
a consensus can be reached among this quorum in a certain state.
These quorums have two vital properties:

1. Intersection: any two quorums have at least one loyal validator in common.
#. Availability: there is always a quorum available with no faulty validator.

When members in a quorum endorse information from a same block, they collect a *quorum certificate*.
There are two certificates, **prepare certificate (P-certificate)** and
**commit certificate (C-certificate)**, which indicate
that there exists a quorum agreeing on a prepare message and a commit message, respectively.



1. **Normal Case**
    a. Block production
        i. An ordinary user claims campaign, undergoes the admission qualification, and then enters the *candidate list*.
        #. After being elected in a periodical election, a candidate enters a block proposer committee.
        #. When it comes its block height, the proposer proposes a block and broadcasts to all validators.
    #. Block validation
        i. Once receives a newly proposed block, a validator in validators committee tries to verify the block.
        #. This `Verification of Blocks`_ process scrutinizes the seal of proposer, timestamp, etc.
        #. If true, this validator broadcast a PREPARE message to other validators; otherwise, it enters Abnormal Case 2 or 3.
        #. Once receives :math:`2f+1` PREPARE messages (P-certificate), a validator broadcasts COMMIT message to other validators.
        #. Once receives :math:`2f+1` COMMIT messages (C-certificate), a validator inserts the block into local chain, and broadcasts VALIDATE message along with these :math:`2f+1` validators' signatures to all users.
        #. Once a validator receives the VALIDATE message for the first time in a block height, it broadcasts a same message to all nodes.
        #. Any user receives this VALIDATE message with enough signatures, inserts the block into local chain


#. **Abnormal Cases**
    a. Abnormal Case 1: *A validator does not receive a block from the proposer:*
        i. It is for the case when Step 1.b.a cannot be reached
        #. Let the :math:`previousBlockTimestamp` be the timestamp of block proposed in previous block height, and period is the minimum interval between two blocks.
        #. A timer is set up when reaching the timestamp of :math:`previousBlockTimestamp+period`.
        #. If the timer expires, the validators committee activates *impeachment*, a two-phase protocol in PBFT manner to propose an impeach block on behalf of the faulty proposer.
    #. Abnormal Case 2: *The proposer proposes one or more faulty blocks*
        i. Faulty blocks cannot be verified in Step 1.b.b and 1.b.c
        #. The validators committee activates *impeachment*
    #. Abnormal Case 3: *The proposer proposes multiple valid blocks*
        i. Each validator can only validate one block for a same block number
        #. Thus, it is impossible for two or more blocks to collect P-certificates simultaneously. Only one block can enter Step 1.b.d
        #. It is possible that no block receives :math:`2f+1` PREPARE messages
        #. *Impeachment* is activated if a validator cannot collect a P-certificate
    #. Abnormal Case 4: *Some members in the validators committee are faulty*
        #. The system can reach a consensus, as long as the number of total faulty validators is no more than :math:`f`.
    #. Abnormal Case 5:
        i. It is for the cases when P-certificate, C-certificate or VALIDATE messages cannot be collected
        #. Each validators have distinct timers for collecting PREPARE, COMMIT and VALIDATE messages
        #. Any of these timers expires, the validators committee activates *impeachment*
    #. Other complicated abnormal cases:
        i. There are more complicated abnormal cases. We list them explicitly in `Countermeasures for Illicit Actions`_.


.. NOTE::

    A validator repeats a validate message (or an impeach validate message) for the first time it receive it.
    This repetition process ensures the validate message can be delivered to all nodes.
    Refer to :ref:`Implementation` for details.


.. _impeachment:

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



.. _impeachment-steps:



Impeachment Steps
**********************

1. A validator :math:`v` in the committee generates an impeachment block
    i. In the header of this block, the *timestamp* is set to be :math:`previousBlockTimestamp+period+timeout`.
    #. Here :math:`previousBlockTimestamp` is the timestamp of block proposed in previous block height.
    #. The term :math:`period` is the interval between two blocks.
    #. And :math:`timeout` is the threshold validator that triggers impeachment.
    #. The *seal* in the header is set to be empty
    #. A penalty on proposer is the only transaction in the block's body
#. This block, used as an IMPEACH PREPARE message, is broadcast to all validators in the committee.
#. Once receives :math:`f+1` IMPEACH PREPARE messages with same header and body, validator :math:`v` broadcasts an IMPEACH COMMIT message to other validators.
#. Once receives :math:`f+1` IMPEACH COMMIT messages, a validator broadcasts an IMPEACH VALIDATE message along with :math:`f+1` signatures to all users.
#. Any validate receives the IMPEACH VALIDATE message for the first time, it inserts the impeach block and broadcasts the same message to all nodes.
#. All users insert the block into local chain, if they receive an IMPEACH VALIDATE messages.


Explanation
****************


Three things are noteworthy here.

.. NOTE::

    1. Impeachment only requires two state instead of three in original PBFT.
    #. A validator can endorse a newly proposed block and an impeach block in a block height.
    #. Only a weak quorum certificate of :math:`f+1` members is required in impeachment consensus.

The absence of an idle state, or pre-prepare state in PBFT, results from the unnecessity of a leader.
Let's recall the roles of a leader in classic PBFT model.
The leader in classic PBFT model assumes the following responsibilities:

    i. Receive the request from the client, and broadcasts it to all backups in the distributed system.
    #. Assign a sequence number to each request, to guarantee that all requests are processed in order.

However, impeachment does not requires a leader to fulfill above duties, since:

    i. Each non faulty validator is about to propose a completely same block.
    #. Each block is associated with a unique block number, which circumvents the usage of sequence number.

The second is that a validator can sign two distinct blocks, one is the proposed block and another one is an impeach block.
Thus, it is possible for some validators obtains :math:`2f+1` PREPARE messages of a newly proposed block,
while another validators obtain a prepare certificate for the impeach block.
This scenario occurs only when the proposer is faulty, misbehaves like `Double Spend Attack`_.
But it does not affects the security of the system.
Refer to `Double Spend Attack`_ to check detailed proof.


The last notable point is that a quorum in normal case consists of :math:`2f+1` members,
while a quorum in impeachment consists of :math:`f+1` members.
The necessity of :math:`2f+1` in normal case is that in extreme cases,
there are :math:`f` faulty nodes send arbitrary messages, we need :math:`f+1` more loyal nodes to outnumber faulty counterparts.
In comparison, that even one loyal nodes triggers impeachment indicates a improper behavior of proposer.
Thus, :math:`f+1` impeachment validators suffice a quorum of impeachment.

In addition, impeachment also requires :ref:`echo-validate` similar to normal case handler.



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

The field ``transactions`` in a block represents all pending transactions the proposer
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

``Coinbase``, refers to the address of reward receiver.
In principle, it is identical with the address of the proposer.
However, a validator accepts any ``Coinbase`` value.
The reward is about to be sent to the coinbase address after the block is inserted into the chain.
It is the proposer's responsibility to write a correct one.

``StateRoot``, ``TxsRoot``, ``ReceiptRoot`` and ``LogsBloom``,
are all insensitive in verification process.

``Number``, is the block height.
It must equal to the block height of parent block adding one.
Any other value is regarded as illegal and is further rejected by any loyal validator.

``GasLimit``, determines the total number of possible transaction in this block.
A low value of ``GasLimit`` restricts the total number of transactions,
while a high value enlarges the size of block as well as transmission cost.
Thus, ``GasLimit`` is bounded by an upper and a lower bound.
Only values in a certain range is accepted by validators.

``GasUsed``, refers to the gas used in ``transactions``.
This number is at most as large as ``GasLimit``.
And it can be calculated by ``transactions`` in this block.
In theory, validators and the proposer can obtain a same result
given a same ``transactions``.
Thus, a validator calculated a GasUsed value itself according to ``transactions``,
and compares it with ``GasUsed`` in the block.
It they are not equal, then the block is rejected.

``Time``, is writen in Unix timestamp.
We have explicated this problem in `Past and Future Block`_.

``Extra``, as indicated by its name, is used to any extra attribute.
Currently, this field is blank.

``Dpor`` is a ``type DporSnap struct`` variable containing its own components, which are


.. code-block:: go

    type DporSnap struct {
        // the signature of the block's proposer
        Seal       DporSignature
        // the signatures of validators to endorse the block
        Sigs       []DporSignature
        // current proposers committee
        Proposers  []common.Address
        // updated validator committee in next epoch if it is not nil.
        // keep the same to current if it is nil.
        Validators []common.Address
    }

Before explaining these four fields, one thing is noteworthy here.

.. NOTE::

    Despite the election is a random process, all random seeds are pre-defined, as the hash value of parent block.
    Thus, all nodes can obtain an identical list of proposers for this term.

Now let's dive in these fields of ``Dpor``

``Seal``, is the signature of the proposer.
A validator rejects the block if this value is not the proper proposer of this block height.
Note that ``Coinbase`` can be decoded from ``Seal``.
Thus, in most cases, these two attributes are referring to a same node.

``Sigs``, contains signatures for LBFT consensus.
It should be nil in a newly proposed block.

``Proposers``, indicates all proposers in this term.
As we stated above, it can be calculated by any node given the hash of parent block.
Verification fails if this field is not correct.

``Validators``, is usually an empty slice.
It is set to all validators in the committee if validators committee is initialized or changed.
``Validators`` in the genesis block contains addresses of all validators,
announce all nodes about this information.
Blocks with height larger than one, contains a nil ``Validators``,
unless members of validators committee change.

However, in LBFT 2.0, the mechanism of changing validators have not been implemented yet.
Validators simply omit this field.


Subsequent Operations of Non-validators After Receiving Blocks
-------------------------------------------------------------------

The structure and components are listed in `Verification of Blocks`_.
And similar to validators in `Verification of Blocks`_,
non-validators, including civilians and proposers,
also verify blocks before insert it into the chain.
Besides, they are also going to execute some subsequent operations after receiving a validated block.
This section discusses operations of civilians and proposers in such scenario.


Civilian
****************

Once a civilian receives a block, it first checks

    1. Whether the block is from validators;
    #. If there are enough distinct signatures in ``Sigs``,
        i. at least :math:`f+1` for impeach block,
        #. at least :math:`2f+1` for normal block,

If both criteria pass, it is a validated block and can be inserted in to the chain.

It further checks ``Validators``.
If ``Validators`` are not empty, civilian should update its validator list.



Proposer
***************

Besides all criteria as civilians,
any member from proposers committee has more items in their checklist.
It first checks if the block is validated:

    1. Whether the block is from validators;
    #. If there are enough distinct signatures,
        i. at least :math:`f+1` for impeach block.
        #. at least :math:`2f+1` for normal block.


Then,

    1. If validator list i.e., ``Validators`` is not nil.
    #. If proposer list i.e., ``Proposers`` is consistent with its own calculation.

Non-trivial ``Validators`` value indicates that a new validators committee.
And it should update its validator list.


The second point here is similar to validators' `Verification of Blocks`_.
A validator pre-calculates proposers list of the current term,
and compares it with ``Proposers``.
Meanwhile, a proposer utilizes ``Proposers`` to reassure if its own calculation is correct,
and confirms its position to propose its block.


.. _`illicit-actions`:

Countermeasures for Illicit Actions
------------------------------------------

Illicit actions refer any messages or blocks sending to
a validator that cannot be processed in this validator's normal cases.
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

**Lemma 1:**
*There cannot exist two blocks proposed by a same node with the same block number being validated simultaneously.*

**Proof:**
Assume that a proposer :math:`p` proposes two distinct blocks :math:`b` and :math:`b'`,
and broadcasts them to validators.
And to achieve its wicked purpose, :math:`f` faulty validators collaborate with :math:`p`.
Suppose that :math:`p` fulfill its wicked aim that both :math:`b` and :math:`b'` are inserted into the chain.
Thus, there exists two quorums of validators that endorse :math:`b` and :math:`b'` respectively.
Since only :math:`3f+1` members in the committee, these two quorums have :math:`f+1` members in common.
Except for :math:`f` faulty validators can be members of both quorums,
there still exits one validator signs both :math:`b` and :math:`b'`.
It contracts the fact that each loyal validator only sign one block.
Hence, there cannot be two proposed blocks are both legit.
**Q.E.D.**



In contrast to the fact that each validator only signs one proposed block, a validator can sign an
impeach block even if it has signed a block from :math:`p` given that it cannot collect a certificate on time.
Then is that possible for a proposer takes advantages of this mechanism to makes its proposed block
:math:`b` and an impeach block :math:`b'` both legit simultaneously?
The answer is no. Here we lists two lemmas and shows their correctness.

**Observation 1:**
*It is possible that both a block* :math:`b` *proposed from a proposer* :math:`p`
*and an impeach block* :math:`b'` *suffice a prepare certificate simultaneously.*



**Proof:**
As we know the certificate of impeach block and normal block
requires different size of quorum respectively.
Let's name the normal quorum of :math:`2f+1` validators as strong quorum,
and its corresponding certificate as strong certificate.
Similarly, the impeach quorum and certificate are denoted
by weak quorum and week certificate respectively.

Observation 1 indicates that one quorum endorses :math:`b` while another one endorse :math:`b'`.
It is possible that if a loyal validator :math:`v_1` signs
:math:`b` then broadcasts its prepare messages,
but its receiver is blocked such that it later proposes an impeach block.
Combining :math:`f` faulty validators, two quorums are made up.
**Q.E.D**


**Observation 2:**
*It is impossible that both a block* :math:`b`
*proposed from a proposer* :math:`p` *and an impeach block* :math:`b'`
*suffice a commit certificate simultaneously.*


**Proof:**
Observation 2 ensures the safety of our consensus system.
Once :math:`v_1` proposes an impeach block :math:`b'`,
it can no longer send out :math:`b`'s commit message even if it collects a prepare certificate for :math:`b`.
The state transmission of a validator is illustrated in the :ref:`Implementation`.
Once a validator enters either impeach prepare or impeach commit phase, it no
long signs a normal block.

To suffice a weak quorum for impeach commit certificate,
there must be at least a loyal validator, say :math:`v_1`, agreeing on impeach block instead of normal one.
This validator assures the legality of this impeach block.

As stated in :ref:`Transitivity`,
:math:`v_1` can transmit the its impeach prepare certificate to other loyal validators.
Thus, these loyal validators in commit state will transit to impeach commit state
and abandon its prepare certificate for :math:`b`,
which assures that a strong commit certificate and a weak certificate cannot be
obtained simultaneously.
**Q.E.D.**


**Observation 3:**
*Under the parameter setting of LBFT 2.0, It is impossible that both a block*
:math:`b` *proposed from a proposer* :math:`p` *and an impeach block* :math:`b'`
*get validate message in one block height.*

**Proof:**
Observation 2 has a glitch in an edge case.
If :math:`v_1` firstly delivers its impeach commit message to :math:`f` faulty validators then loses connection,
a weak quorum suffices while the strong quorum for commit certificate has
not clue about :math:`v_1`'s impeach prepare certificate.
Despite of the fact that a validator sends out message to all its peers in a random order,
the chance of this situation is not zero.

However, in LBFT 2.0 timeout is set to be 10 seconds,
same as the period of a normal case.
Before the timer of :math:`v_1` expires,
the strong quorum has collected a prepare certificate of block :math:`b`
and get :math:`v_1` transited to prepare state.
**Q.E.D**


Observation 2 and 3 lead to the following lemma:

**Lemma 2:**
*A proposed block and an impeach block cannot be validated in a same block height.*

**Proof:**
According to Observation 2 and 3,
either a normal block or an impeach block can obtain a commit certificate, and be further validated.
Thus, they cannot be validated in same block height.
**Q.E.D.**

Combining both Lemma 1 and 2, we conclude the following theorem to guarantee the safety facing double spend attack.

**Theorem 1:**
*LBFT 2.0 is guaranteed to generate only one validated block for each block height under double spend attack.*


.. _unknown-ancestor-block:



Unknown Ancestor Block
*************************

An unknown ancestor block refers to a block whose block height is higher than the one the validator is currently processing.
The name comes from the fact that the predecessor of this block is yet unknown in the chain.


Four Scenarios
#################

Suppose a validator :math:`v` which is processing a block :math:`b` in block height :math:`h`,
and receives an unknown ancestor block :math:`b_2`
with block height :math:`h_2` from a node :math:`p_2`.
There are following possible scenarios:

1. The block is proposed by a legit proposer at the correct time; the validator is delaying.
#. The block is proposed by a legit proposer at an incorrect time.
#. The block is proposed by a faulty node.
#. The validator is lagging behind for at least one term, and cannot verify whether the proposer is legit.

Here the word *legit* indicates that :math:`p` is an incumbent proposer from the committee in the current term,
having been recognized by :math:`v`.
When a proposers committee is elected, each validator receives a list of all elected candidates as
well as the corresponding block heights to propose their blocks.
Thus, a validator has a priori knowledge on all legit proposers in this term, unless the proposer is
delaying for at least a term.


**First scenario:** :math:`b_2` actually is not an unknown ancestor block.

The validator :math:`v` regards :math:`b_2` as an unknown ancestor block simply because it is delaying.
After receiving :math:`b_2`, the validator :math:`v` records the block in the cache.
As it is delaying, it is counted as one of :math:`f` non-responding validators.

Despite that it receives :math:`b_2`, :math:`v` stays in the block height h,
and it does not participate in consensus of block height :math:`h_2`.
In other word, it does not broadcasts a prepare message endorsing :math:`b_2`.
Other members in the validators committee suffice a quorum to 
complete the consensus process on :math:`b_2` without :math:`v`'s participation.
:math:`v` is going to catch up with the schedule after it receives the validate message from other committee members,
or by :ref:`recovery`.

**Second scenario:** :math:`p_2` behaves faultily.

Similar to the first scenario, :math:`v` records it in the cache without signing it.
A quorum can still complete the consensus on :math:`b`.
When it comes to the correct block height of :math:`p_2`, if :math:`p_2` proposes the block again,
then it is going to be processed normally.
Otherwise, the timer of a quorum of validators (including :math:`v`) will expire and enter impeach process.

**Third and fourth scenario:** :math:`v` cannot recognize :math:`p_2` as a proposer.

It can due to either :math:`b_2` is faulty (scenario 3) and :math:`v` is delaying (scenario 4).
In both scenarios, :math:`v` is going to sync, determining if it is delaying.
For the third scenario, :math:`v` rejects :math:`b_2` and adds :math:`p_2` into blacklist.
For the fourth one, it acts same as the first scenario.

Here comes another concern.
A faulty node can raise a DDoS attack on validators, forcing them continuously syncing.
To address this issue, we can set a timer of a validator as the minimum gap between two syncs.
A reasonable setting is :math:`10\times |P|` seconds, where :math:`|P|` is the size of proposers
committee, and :math:`10` is time interval between two consecutive blocks.

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

A validator :math:`v` regards a block :math:`b` as a future one, if the following two conditions are met:

    1. The timestamp of :math:`b` is larger than the one of :math:`v`;
    #. The block height of :math:`b` is same as :math:`v`.

Similarly, a block :math:`b'` is considered a past block if

    1. The timestamp of :math:`b'` is smaller than :math:`previousBlockTimestamp+period`;
    #. The block height of :math:`b'` is same as :math:`v`,

where :math:`previousBlockTimestamp` is the timestamp of previous block,
and period is the time interval between two consecutive blocks.

Do not confuse future block with the concept of unknown ancestor block.
An unknown ancestor block may holds a larger timestamp,
but are processed as an unknown ancestor one instead of a future block.

For past block, a validator fails in verifying it and triggers impeachment.
For a future block, the validator wait until the timestamp of the block.
But if it is larger than :math:`previousBlockTimestamp+period+timeout`,
an impeachment is about to take place.
Thus, we come up with a pseudocode for timestamp verification.

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
                case <-quit // quit is true if v triggers impeachment
                    return false
            }
        }


Timestamp of Receiving a Block
*************************************************

Despite that the interval between two consecutive normal blocks is 10 seconds,
a validator can hardly accept a block received in any timestamp within this 10 seconds.
It is because consensus and broadcast processes are also consuming this period.


Thus, we introduce a threshold as **block delay**,
indicating the broadcast delay of a block.
By setting it to 2.5 seconds, a validator has sufficient time for consensus process.


Let :math:`b` be a block with timestamp tb written in its header.
The proposer should broadcast :math:`b` at timestamp :math:`tb`.
As stated in previous chapter, tb is usually set to :math:`previousBlockTimestamp+period`.
A validator invokes its normal case handler if it receives :math:`b` before :math:`previousBlockTimestamp+period+2.5`.
and rejects this block otherwise.
The pseudocode below demonstrates this process.


    .. code-block:: go

        func receivingTimeVerification(b) bool {
            // v: a validator
            // t: timestamp of v when receiving b
            // b: a block
            blockDelay := 2.5 * time.Minute
            if t > previousBlockTimestamp+period+blockDelay{
                return false
            } else {
                return true
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
an interval of at least :math:`10\times |P|` between two consecutive synchronizations is enforced
to prevent I/O and computing resource exhaustion.







Comparison with PBFT
---------------------------

This section compares LBFT 2.0 with classic PBFT.
We name both proposer in LBFT 2.0 and primary replica in PBFT as the **leaders** ,
since they assume similar responsibility to dispatch a query to all nodes.
And insistence on P-certificate indicates that
a replica does not changes its endorsement in a query once it collects a prepare certificate.

In other word, LBFT 2.0 has weaker assumption, higher liveness and more complicated faulty
leader handler.
Note that the view change reduces the faulty leader problem into a normal case
handler in the next view. We cannot adopt similar method since our high command on liveness.
Liveness is also the reason that a validator cannot insist on a P-certificate.


.. code-block:: table
	+---------------------------+------------------------------------+-----------------------------+
	| Aspect                    |           LBFT 2.0                 |         PBFT                |
	+===========================+====================================+=============================+
	| Assumption                | Tolerate at most :math:`f` faulty  | Tolerate at most            |
	|                           | validators and a faulty proposer   | :math:`f` replicas          |
	+---------------------------+------------------------------------+-----------------------------+
	| Liveness                  | Insert a block within at most      | Response in finite time     |
	|                           | period+timeout (20 seconds)        |                             |
	+---------------------------+------------------------------------+-----------------------------+
	| Insistence on             | Trigger impeachment if timer       | Insist on the query with    |
	| P-certificate             | expires                            | P-certificate               |
	+---------------------------+------------------------------------+-----------------------------+
	| Faulty leader handler     | Impeachment                        | View change                 |
	+---------------------------+------------------------------------+-----------------------------+


