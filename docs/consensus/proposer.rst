Proposer
************

1. Invoke *setContractCaller()* to connect to a contract
#. In *updateNodeId()*, NodeId is encrypted and then update to the contract
#. Whenever get dialed from a validator, *addValidators()* is called to add this validator into *Proposer.validators*
#. Before the return statement, *proposeHandshake()* is invoked to connect this validator
#. Get sync with the quorum of validators, and set a boolean flag *synced* to be true
#. When it is the view for the Proposer to propose new block, *broadcastBlock()* is called to broadcast block to each member in *Proposer.validators*
#. A goroutine *WaitValidation()* is running to collect f+1 VALIDATION messages from validators, and a boolean flag *Validated* is set to be true after collecting them
#. Once *Validated* is true, it is safe to insert the block into its local chain