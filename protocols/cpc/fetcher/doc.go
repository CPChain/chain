// Copyright 2016 The cpchain authors
// Copyright 2016 The go-ethereum Authors

/*
Package fetcher is for new block body/hash broadcast msg handling.

When a validator generated a new Validation msg, he multicasts it to all his
peers.

There are two kinds of Validation msg, one is the NewBlockMsg, and another
is NewBlockHashesMsg.

When received a NewBlockMsg, handleSyncMsg in ProtocolManager will enqueue
the msg to pm.fether.

When received a NewBlockHashesMsg, handleSyncMsg in ProtocolManager will notify
pm.fether to fetch the new available block.

*/
package fetcher
