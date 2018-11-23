Dpor
******
..
    +------------+------------+
    |PBFT        | Blockchain |
    +============+============+
    | primary    | leader     |
    +------------+------------+
    | backup     | signer     |
    +------------+------------+
    | replica    |            |
    +------------+------------+
    | sequence number | block number|
    +------------+------------+
    |  | |
    +------------+------------+

    - **Normal Case**
        - **Pre-prepare**
            - The *leader* p broadcasts a <<PRE−PREPARE, v, n, d>,m>
            - v: the view
            - n: block number
            - d: digest of message
            - m: message
        - **Prepare**
            - A *signer* i enters prepare phase after it accepts a PRE-PREPARE message for this view
            - i multicasts a <PREPARE, v, n, d, i> to all replicas
            - i adds PRE-PREPARE and PREPARE messages into the log
            - i is collecting *prepare certificate*
                - Prepare certificate is 2f+1 PREPARE messages (including i) matching with the PRE-PREPARE message in terms of v, d and n
        - **Commit**
            - i is *prepared* if it collects the prepare certificate, and enters commit phase
            - i multicasts a <COMMIT, v, n, d, i> message to all replicas
            - i adds COMMIT message into the log
            - i is collecting *commit certificate*
                - Commit certificate is 2f+1 COMMIT messages (including i) matching with each other with the same v, d and n
        - **Reply**
            - After i collects a commit certificate, it executes the request
            - i add the block into its log
    - **View Change**
        - In view i
            - Once the timer of a signer i expires, i multicasts a empty block with a VIEW-CHANGE message into the network
            - The VIEW-CHANGE message is <VIEW − CHANGE, v+1 ,n ,i>
            - The primary p of view v+1 is collecting view-change certificate
                - View-change certificate is 2f+1 VIEW-CHANGE messages (including p)
        - Entering new view i+1
            - After p collects a view-change certificate, it multicast a <NEW-VIEW, v+1> message
            - Signer i enters new view v+1, if i has 2f VIEW-CHANGE messages (including i) and receives NEW-VIEW message

1. **Validator** and **Proposer** and **Ordinary** users
    a. Block validators, or validators refer to a group of users that can validate a newly proposed block
        - The validator committee consists of nodes nominated from CPC Foundation, governments and companies.
        - Except for some abnormal cases, validators have no right producing blocks
        - The validator committee follows *Practical Byzantine Fault Tolerance (PBFT)* protocol, and the size of number is always equaling to 3f+1, where f is a integer
    #. Block proposer, or proposer refers to the user that can propose block
        - It is one member of the proposer committee
        - The proposer committee is elected based on reputations of candidates and a random seed
        - Each number in the proposer committee takes the responsibility of producing block one by one
    #. Ordinary users refer to the rest of users
        - An ordinary user can become a proposer if it claims campaign and is elected
#. **Normal Case**
    a. Block production
        i. An ordinary user claims campaign and enters the *candidate list*
        #. After being elected in a periodical election, a candidate enters a block proposer committee
        #. The proposer encrypts his address with all public key of the validator committee to a contrast
        #. If a validators receives the encrypted message, it is about to connect the proposer with its address
        #. If the proposer receives 2f+1 connection from validators, it proposes a block and broadcasts to them
    #. Block validation
        i. Once receives a newly proposed block, a validator in validator committee tries to validate the block.
        #. If true, this validator broadcast PREPARE message to other validators.
        #. Once receives 2f+1 PREPARE messages, a validator broadcasts COMMIT message to other validators.
        #. Once received 2f+1 COMMIT messages, a validator inserts the block into local chain, and broadcasts VALIDATION message to all users.
        #. All users insert the block into local chain, if they receive f+1 VALIDATION messages
#. **Abnormal Cases**
    a. Abnormal Case 1: *The proposer does not fetch at least 2f+1 Validators' addresses*
        i. It is for the case when Step 2.a.iv cannot be reached
        #. After the proposer write its encrypted address in contrast (Step 2.a.iii), it set up a timer
        #. If the timer expires, and the proposer does not receive 2f+1 connections,  the proposer is about to retrieve the addresses from public
    #. Abnormal Case 2: *Validators does not receive a block from the proposer*
        i. It is for the case when Step 2.a.v cannot be reached
        #. After a validator sends out its address to the proposer, it sets up a timer
        #. If the timer expires, the validator committee activates *impeachment*, a three-phase protocol in PBFT manner to propose the block
    #. Abnormal Case 3: *The proposer proposes one or more faulty blocks*
        i. Faulty blocks cannot be validated in Step 2.b.i
        #. The validator committee activates impeachment
    #. Abnormal Case 4: *The proposer proposes multiple valid blocks*
        i. Each validator can only validate one block for a same block number
        #. Thus, it is impossible for two or more blocks to receive 2f+1 PREPARE messages simultaneously. Only one block can enter Step 2.b.4
        #. It is possible that no block receives 2f+1 PREPARE messages
    #. Abnormal Case 5: *Some members in validators committee are faulty*
        i. The validator committee follows the PBFT protocol.
        #. The system can reach a consensus, as long as the number of total faulty validators are less than f.
    #. Abnormal Case 6:
        i. It is for the cases when 2f+1 PREPARE messages, COMMIT messages or 2f+1 VALIDATION messages cannot be collected
        #. Each validators have distinct timers for collecting PREPARE, COMMIT and VALIDATION messages
        #. Any of these timer expires, the validator committee activates *impeachment*

#. **Impeachment**
    a. It is an abnormal handler when the proposer is either faulty, or non responding
    #. It is a two-phase protocol in PTBF manner, consisting of *prepare* and *commit* phases.
    #. Impeach steps:
        a. A validator in committee generates a block on behalf of the faulty (or non responding) proposer
            i. In the header of this block, the *timestamp* is set to be previousBlockTimestamp+Period+timeout, where previousBlockTimestamp is the timestamp of block proposed in previous view, Period is the interval between two blocks and timeout is the threshold validator that triggers impeachment
            #. The *seal* in the header is set to be empty
            #. A penalty on proposer is the only transaction in the block's body
        #. This block, used as a PREPARE message, is broadcasted to all validators in the committee
        #. Once receives 2f+1 PREPARE messages with same header and body, a validator broadcasts COMMIT message to other validators
        #. Once received 2f+1 COMMIT messages, a validator inserts the block into local chain, and broadcasts VALIDATION message to all users
        #. All users insert the block into local chain, if they receive f+1 VALIDATION messages
    #. The reason the leader is not required
        a. The leader in classic PBFT model take the following roles:
            i. Receive the request from the client, and broadcast to all backups in distributed system
            #. Assign a sequence number to each request, to guarantee that all requests are processed in order
        #. Impeachment does not requires a leader to fulfill above duties, since
            i. Each non faulty validator is about to propose a completely same block
            #. Each block is associated with a unique block number, which circumvents the usage of sequence number
..
    #. **Impeachment**
        a. It is an abnormal handler when the proposer is either faulty, or no responding
        #. It is a PBFT three-phase protocol, consisting of *pre-prepare*, *prepare* and *commit* phases.
        #. There is a *leader* in validator committee takes the responsibility to propose a block when the impeachment is activated
        #. Impeach steps:
            i. The leader broadcasts PRE-PREPARE messages to all validators, indicating the proposer is not working properly
            #. After receiving a PRE-PREPARE message, each validator broadcasts a PREPARE message to all validators
            #. Once receives 2f+1 PREPARE messages, a validator broadcasts COMMIT message to other validators
            #. Once received 2f+1 COMMIT messages, a validator inserts the block into local chain, and broadcasts VALIDATION message to all users
            #. All users insert the block into local chain, if they receive f+1 VALIDATION messages
        #. Each validator takes the role of leader one by one for one view
        #. Leader change
            i. *View change* is activated when leader is faulty
            #. A validator suspects the leader is faulty, when any of following situations happens
                - The validator committee should start the impeachment, but the timers expires and the validator does not receive PRE-PREPARE message
                - The validator committee should not start the impeachment, and the validator receive a PRE-PREPARE message from the leader
            #. If a validator suspects the leader, it broadcasts a LEADER-CHANGE message to all validators
            #. If the leader of the next view collects 2f+1 LEADER-CHANGE messages, it broadcasts a NEW-LEADER message to all validator
            #. Other validators accepts this NEW-LEADER message if they receive 2f VIEW-CHANGE messages
            #. The new leader takes the responsibility of proposing block, as in the Step 4.d.i