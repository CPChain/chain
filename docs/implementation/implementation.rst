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
implement :ref:`Intra-view Recovery`.
And by utilizing prepare message,
we can implement it without adding too much code.