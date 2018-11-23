1. Upload encrypted NodeID to a contract
#. Whenever get dialed from a validator, *addValidators()* is called to add this validator into *Proposer.validators*
#. Before the return statement, *proposeHandshake()* is invoked to connect this validator
#. In *proposeHandshake()*, the newly proposed block is broadcasted to
#.