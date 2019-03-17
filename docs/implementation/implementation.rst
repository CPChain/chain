.. _implementation:

Implementation
=====================




Finite State Machine
---------------------

The LBFT 2.0 protocol can be considered as a finite state machine (FSM) with 5 states:
**idle**, **prepare**, **commit**, **impeach prepare** and **impeach commit**.
The former three states are designed for normal cases, and the rest are specializing in handling abnormal cases.

The illustration below demonstrates these five states as well as transitions between states.
Note that not all transitions are shown in this figure due to the lack of space.
The text on an arrow between two states refers to the condition of this transition.
And the message box near the arrow represents the message broadcast to other nodes.


.. image:: lbft_fsm.png


.. _LBFT-2-Pseudocode:


LBFT 2.0 Pseudocode
-----------------------

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

        // period is the minimal time between two consecutive blocks
        // timeout is used for whether the timer expires
        var period, timeout int
        period = 10 * time.Second   // set period as 10 seconds
        timeout = 10 * time.Second  // set timeout as 10 seconds

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
                        broadcast prepareMsg    // transitivity of certificate
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

                    // a cascade of determination of certificate
                    if impeachPrepareCertificate(b) {
                        if impeachCommitCertificate(b) {
                            add the impeach block b into cache
                            broadcast impeachValidateMsg
                            transit to validate state
                        } else {
                            add the impeach block b into cache
                            broadcast the impeachPrepareMsg
                            broadcast the impeachCommitMsg
                            transit to impeachCommit state
                        }
                    } else {
                        add the impeach block b into cache
                        broadcast the impeachPrepareMsg
                        transit to impeachPrepare state
                    }
                } else {

                    // a cascade of determination of certificates
                    if prepareCertificate {
                        if commitCertificate {
                            add block into the cache
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
                        broadcast impeachPrepareMsg // transitivity of certificate
                        broadcast impeachCommitMsg
                        transit to impeachCommit state
                    }
                }
            }
        }

        // a general impeachment message handler for normal case states
        func impeachHandler(input) {
            switch input{
            case expiredTimer:
                propose an impeach block
                // a cascade of determination of certificate
                if impeachPrepareCertificate(b) {
                    if impeachCommitCertificate(b) {
                        add the impeach block b into cache
                        broadcast impeachValidateMsg
                        transit to validate state
                    } else {
                        add the impeach block b into cache
                        broadcast the impeachPrepareMsg
                        broadcast the impeachCommitMsg
                        transit to impeachCommit state
                    }
                } else {
                    add the impeach block b into cache
                    broadcast the impeachPrepareMsg
                    transit to impeachPrepare state
                }

            case impeachPrepareMsg, impeachCommitMsg, impeachValidateMsg:
                impeachPrepareHandler(input)
            }
        }




.. _echo-validate:



Echo of Validate Message
----------------------------

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


Cascade of Determination of Certificates
-------------------------------------------

A cascade of determination of certificates refers to a phenomenon that
a message can suffice more than one certificate.

Recall an example in ``func idleHandler()`` in `LBFT 2.0 Pseudocode`_.
A block adds one distinct signature in ``prepareSignatures``,
which is possible to suffice a prepare certificate.
Under the case that a prepare certificate is collected,
one more distinct signature is added in ``commitSignatures``,
it is also possible that a commit certificate can be collected.

.. code-block:: go

    func idleHandler(input) {
        switch input{
        // some code here
        case block:
            // some code here

            // a cascade of determination of certificates
            if prepareCertificate {
                if commitCertificate {
                    add block into the cache
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
        // some code here
        }
    }


A similar cascade of determination also applies in impeach handlers.
An example is ``func impeachHandler()`` as shown below.


.. code-block:: go


    func impeachHandler(input) {
        switch input{
        case expiredTimer:
            propose an impeach block
            // a cascade of determination of certificate
            if impeachPrepareCertificate(b) {
                if impeachCommitCertificate(b) {
                    add the impeach block b into cache
                    broadcast impeachValidateMsg
                    transit to validate state
                } else {
                    add the impeach block b into cache
                    broadcast the impeachPrepareMsg
                    broadcast the impeachCommitMsg
                    transit to impeachCommit state
                }
            } else {
                add the impeach block b into cache
                broadcast the impeachPrepareMsg
                transit to impeachPrepare state
            }

            // some code here
        }
    }


.. _transitivity:

Transitivity of Certificate
-----------------------------


Readers may notice comments in `LBFT 2.0 Pseudocode`_
referring to transitivity of certificate.
An example of ``func prepareHandler()`` is demonstrated below.

.. code-block::go

    func prepareHandler(input) {
        switch input{
        // some code here

        case prepareMsg:
            if prepareCertificate {
                // some code here
                broadcast prepareMsg    // transitivity of certificate
                broadcast commitMsg
                transit to commit state
            }
        }
    }


When a validator suffices a prepare certificate,
it does not only broadcast the commit message with its signature,
it but also sends out the prepare certificate it just collects.
The essence of a prepare certificate is 2f+1 (f+1) prepare signatures (impeach prepare signatures).
Thus, by sending out the broadcast a prepare message with all signatures it collects,
other validators can obtain the certificate.


The motivation of introducing this mechanism is to
implement `Intra-view Recovery`_.
And by utilizing prepare message,
we can implement it without adding too much code.




.. _recovery:


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

In practice, we use a prepare message with all signature the validator collects,
as the certificate.
Refer to :ref:`transitivity` for detailed implementation.

By introducing intra-view recovery, our system can tolerate two or more distinct validators
lose their connection in different states.
Even though this scenario violates our original assumptions, LBFT 2.0 with intra-view recovery reaches a consensus.
At the cost of larger space consumption for each message, we increase the robustness of the protocol.


Extra-view Recovery
*************************

If intra-view recovery does not work for a validator v and the block height of v is same as the chain,
it is about to catch up other validators once it receives a validate message.
As demonstrated in :ref:`LBFT-2-Pseudocode`, validate message (as well as impeach validate mesage) has highest priority,
which forwards v to idle state of next view regardless of the state of v.

However, if v has been losing its connection for a long time, it should invoke *sync* function.
Sync function, as indicated by the name, synchronizes with Mainnet chain.
Then it can rejoin consensus process after receiving validate message of the current view.
The function is called a validator suspects it is delaying like receiving :ref:`unknown-ancestor-block`.





Restore Cache
***************

Once a block is validated and inserted into the chain, it can be labelled as a permanent data.
And all permanent data are written in hard disks.
In comparison, information like current state, collected signatures as well as block caches are temporary data.
As temporary data are stored in volatile memory, they are not retained once a validator shuts down or restarts.
Hence, before a validator shuts down, it writes all temporary data in hard disk,
and retrieves these data after it starts up.

Note that it is highly possible that a validator is lagging behind other committee members after it restarts.
In this case, it processes the block as explained in :ref:`unknown-ancestor-block`.


Failback
-------------------

Failback is a process to restore the whole system after if all validators halt at the same time.
Apparently, the chain has to be suspended since no validator can continue working on consensus.
The main challenge here is to reach a consensus for the first block after all validators reboot.

From the proposer's perspective, it has no clue when the validation system can restore.
Thus, the first block right after the reboot of validators, must be an impeach block to regain liveness.

As we described in :ref:`impeachment`, the timestamp of an impeach block is determined by previous block.
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
    #. Maximum possible delay of broadcasting messages is less than T/2.
    #. All validators restarts within a time window of T/2.

The first assumption can be also interpreted as
max(t\ :sub:`i`\ -t\ :sub:`j`\ ) < T.
We name it as the sample space of validators.
This assumption is reasonable since all loyal validators are connecting to the network
and get their local clock calibrated before reboot.

Now we construct a set of discrete timestamps TS={t|t=2k*T, k is a natural number}.
A validator v\ :sub:`i`\   chooses timestamp ts for the failback impeach block, satisfying

1. ts\ :sub:`i`\   is an element of TS
#. ts\ :sub:`i`\   > t\ :sub:`i`\0.

After reboot, all validators are set to idle state.
When the local clock of v\ :sub:`i`\  is ts\ :sub:`i`\ , it proposes an impeach block with this timestamp,
and enters impeach prepare state.
If it cannot collect an impeach prepare certificate at ts\ :sub:`i`\   + 2T
v\ :sub:`i`\   proposes another impeach block with timestamp ts\ :sub:`i`\   +2T.
The rest of consensus part are same as LBFT 2.0.

The coefficient 2 in 2T is derived from the second and third assumptions.
Thus, each validator can receive messages from all other validators within a time window of T.

In practice, T can be set to be 1 minutes.
Hence, the system can regain its liveness in 4 minutes.
The pseudocode is shown below.

Failback Pseudocode
***********************



    .. code-block:: go

        // this function can only be invoked when reboot
        func failback () {
            // v: a validator
            // t: local clock of v in Unix timestamp
            T := 1 * time.Minute // 1 minutes
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


By summing up above five cases, we can conclude that the theorem holds.
**Q.E.D**


P2P Hierarchy
-----------------------

As we know all nodes in blockchain network are connecting with each other via P2P method.
Each node holds a list of peers that it can directly connects
To enhance connection between committee members,
we design a hierarchy of P2P connection according to the roles of peers.

Overview
************

When a node kick-starts CPC and connects to bootnode,
it receives a list of peers, whose amount is usually 25.
Via edges between this nodes and its peers, it now connects to the P2P network.

As described in :ref:`consensus`, there are three roles in a consensus process.
Thus, in total we have 9 possible P2P connection types according to the roles of two peers.
And we refers to each type in the form of A-B, where A and B can be V, P or C,
Like P-V refers to P2P connections from P to V.

However, some P2P types in practice do not to be distinguished from each other.
Like for civilians, they have no need to distinguish connections from other civilians,
or a committee member.

The table below presents all possible connections and four distinct types.

+---------------+-------------+--------------+-----------+
| P2P types     | Validator   | Proposer     | Civilian  |
+---------------+-------------+--------------+-----------+
| Validator     | V-V         | V-P          | C-C       |
+---------------+-------------+--------------+-----------+
| Proposer      | P-V         | C-C          | C-C       |
+---------------+-------------+--------------+-----------+
| Civilian      | C-C         | C-C          | C-C       |
+---------------+-------------+--------------+-----------+

C-C
*******

C-C is the basic P2P connection type.
It serves as the normal P2P connection,
providing basic functions like receiving blocks and syncing with the chain.


P-V
********

P-V is the third layer in P2P hierarchy.
When an RNode is elected as a proposer for a further term,
it will insert addresses of all validators into its list of peers,
and updates the connection to P-V.
The address of validators, unlike other addresses,
will not be kicked out from the list of peers as long as it yet proposes the block.

V-P
**********

V-P is the second layer in the hierarchy.


V-V
*********
