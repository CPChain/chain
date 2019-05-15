CPChain Smart Contract
======================

This module is smart contract of cpchain, including dpor, pdash, proxy, and reward.


dpor
####

Dpor contracts are built-in contracts to support consensus of cpchain, including rnode, campaign, admission and rpt.

rnode
*****

Rnode contract is for nodes to join and quit rnodes, and for other contracts to check if a node is rnode.

campaign
********

Campaign contract is for nodes to claim campaign, and checks if nodes satisfy all requirements to become candidates.

admission
*********

Admission contract is for campaign contract to check the proofs submitted by nodes.
The verification is done in go functions which are called by admission contract through primitive contract.

rpt
****

Rpt contract provides weight configs for reputation calculation.

pdash
#####

Pdash contracts are currently not used, and may be removed in the future.

proxy
#####

Proxy contract is a mechanism that realizes upgradable contract.
Proxy contract needs improvements and is currently unused.
It will open in the future.

reward
######

reward contract is a fund pool game which can be accessed in out mobile app.
