// Copyright 2019 The cpchain authors
// Copyright 2016 The go-ethereum Authors

/*
Package downloader is for chain synchronization from the cpchain network.

There are three conditions/situations in which downloader will sync blocks
from network.

The first condition is satisfied when a new peer is added. This is obviously,
because a new added peer is likely to be a new best peer, which means the peer
has the longest chain among local peers.

The second one is called ForceSync. As its name implies, ForceSync tries to sync
the chain without any other pre-requirements. It is a periodic task with a given
period called `forceSyncCycle`, which is defined in `protocols/cpc/sync.go`.

The third one is unknown ancestor sync or too slow sync. When received an
unknown ancestor block or a new generated block with much larger block number
than current latest block, it is necessary to sync local chain to latest to
continue the block verification process.

All of those synchronization processes can be handled with `Synchronise` funcs
in downloader.

In Synchronise function, a sub-function is called. It calls syncWithPeer, which
will call fetchHeight, findAncestor, then spawnSync to call fetchHeaders,
fetchBodies, fetchReceipts, processHeaders with goroutines.

When received a downloader synchronization related msg, ProtocolManager in
cpc/handler.go would call corresponding msg handling functions in downloader.go
with common prefix "Deliver", i.e.DeliverHeaders, DeliverBodies... to handle it.

There are some remaining problems in downloader module and ProtocolManager.handleSyncMsg func.

*/
package downloader
