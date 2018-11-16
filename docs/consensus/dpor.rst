dpor
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

1. **Validator** and **proposer** and **Ordinary** users
    a. Block validators, or validators refer to a group of users that can validate a newly produced block
        - The validator committee consists of nodes nominated from CPC Foundation, governments and companies.
        - Except for some abnormal cases, validators have no right producing blocks
        - The validator committee follows *Practical Byzantine Fault Tolerance (PBFT)* protocol, and the size of number is always equaling to 3f+1, where f is a integer
    #. Block proposer, or proposer refers to the user that can produce block
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
        #. If the proposer receives 2f+1 connection from validators, it produces a block and broadcasts to them
    #. Block validation
        i. Once receives a newly produced block, a validator in validator committee tries to validate the block.
            - If true, broadcast PREPARE message to other validators.
        #. Once receives 2f+1 PREPARE messages, a validator broadcasts COMMIT message to other validators.
        #. Once received 2f+1 COMMIT messages, a validator inserts the block into local chain, and broadcasts VALIDATION message to all users.
        #. All users insert the block into local chain, if they receive f+1 VALIDATION messages
#. **Abnormal Cases**
    a. Abnormal Case 1: *The proposer does not fetch at least 2f+1 Validators' addresses*
        i. It is for the case when Step 2.a.iv cannot be reached
        #. After the proposer write its encrypted address in contrast (Step 2.a.iii), it set up a timer
        #. If the timer expires, and the proposer does not receive 2f+1 connections,  the proposer is about to retrieve the addresses from public
    b. Abnormal Case 2: *Validators does not receive a block from the proposer*
        i. It is for the case when Step 2.a.v cannot be reached
        #. A validator set up a timer,  after it send out its address to proposer
        #. If the timer expires, the validator committee starts a three-phase protocol in PBFT manner to produce the block