CPChain Smart Contract
======================

This module is CPChain built-in smart contracts for dpor consensus, including rnode, campaign, admission and rpt.

Whole processes of campaign
###########################

1. a new block comes, node will TryCampaign(). in miner/engine.go/update()
#. check if the node IsRnode(). in consensus/dpor/consensus.go/TryCampaign().
    i. IsRnode() will finally call rnode contract to check isRnode()
    #. if the node is not a rnode, it will FundForRnode(). FundForRnode() will finally call rnode contract joinRnode().
    #. if the node is a rnode, it will go to next step.
#. the node claim Campaign(), the actual working code is in admission/admission.go/Campaign()
#. the node will try to calculate a memory proof and a cpu proof, using own address, current block hash and nonce.
#. if the node get the proofs that meet the target, it will ClaimCampaign(), the logic is in campaign contract.
#. parameters of ClaimCampaign() include nonce, address, block number.
#. campaign contract will call rnode contract to check if the node is rnode through interface
#. campaign contract should check the submitted block number is within the latest n block.
#. campaign contract will call admission contract to check if the proofs meet requirements.
    i. admission contract will get block hash by block number
    #. then call go function contracts/dpor/primitives/primitive_pow_verify.go/Run()
    #. then go to admission/verify.go
#. if the node pass all requires, campaign contract will add it into candidate.