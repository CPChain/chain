Validators
************

1. Check the contract, to retrieve the encrypted *Proposer.NodeId*, and then decrypt it
#. *Dial()* is called to connect to Proposer
#. Once *Proposer.synced* is true and receives a valid block from Proposer, the **Normal Case** scenario is triggered
#. After receiving the block from proposer
    1. Cache the block
    #. Verify the block. To put it more specifically, check the legality of *term*, *view*, and *Proposer.NodeId* in header
    #. Sign *(header, PREPARE)* into header
    #. Invoke *ValidatorHandshake()* to connect to all members in validators committee
    #. Broadcast PREPARE message to other validators
    #. Wait an ackPrepare message from other validators
#. After receiving the PREPARE message
    1. Return an ackPrepare to the sender of PREPARE message
    #. Cache the header
    #. Verify 2f+1 PREPARE message
    #. Sign *(header, COMMIT)* into header
    #. Broadcast COMMIT message to other validators
    #. wait an ack_commit message from other validators
#. After receiving the COMMIT message
    1. Return an ackCommit
    #. Cache the header
    #. Verify 2f+1 COMMIT message
    #. Sign *(header, VALIDATION)* into header
    #. Insert the block into its local chain
    #. Broadcast FINAL_COMMIT messages to all nodes