package cpc

import (
	"math/big"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

func (pm *ProtocolManager) broadcastGeneratedBlock(block *types.Block) {
	committee := pm.peers.committee
	for _, peer := range committee {
		peer.AsyncSendNewPendingBlock(block)
	}
}

// BroadcastSignedHeader broadcasts signed header to remote committee.
func (pm *ProtocolManager) BroadcastSignedHeader(header *types.Header) {
	committee := pm.peers.committee
	for _, peer := range committee {
		peer.AsyncSendPrepareSignedHeader(header)
	}
}

// BroadcastBlock will either propagate a block to a subset of it's peers, or
// will only announce it's availability (depending what's requested).
func (pm *ProtocolManager) BroadcastBlock(block *types.Block, propagate bool) {
	pm.broadcastBlock(block, propagate, false)
}

func (pm *ProtocolManager) broadcastBlock(block *types.Block, propagate bool, ifMined bool) {
	hash := block.Hash()
	peers := pm.peers.PeersWithoutBlock(hash)

	if ifMined {
		pm.broadcastGeneratedBlock(block)
		return
	}

	// If propagation is requested, send to a subset of the peer
	if propagate {
		// Calculate the TD of the block (it's not imported yet, so block.Td is not valid)
		var td *big.Int
		if parent := pm.blockchain.GetBlock(block.ParentHash(), block.NumberU64()-1); parent != nil {
			td = new(big.Int).Add(block.Difficulty(), pm.blockchain.GetTd(block.ParentHash(), block.NumberU64()-1))
		} else {
			log.Error("Propagating dangling block", "number", block.Number(), "hash", hash.Hex())
			return
		}

		// Send the block to a subset of our peers
		// transfer := peers[:int(math.Sqrt(float64(len(peers))))])
		transfer := peers

		for _, peer := range transfer {
			peer.AsyncSendNewBlock(block, td)
		}

		log.Debug("Propagated block", "hash", hash.Hex(), "recipients", len(transfer), "duration", common.PrettyDuration(time.Since(block.ReceivedAt)))
		return
	}

	// Otherwise if the block is indeed in out own chain, announce it
	if pm.blockchain.HasBlock(hash, block.NumberU64()) {
		for _, peer := range peers {
			peer.AsyncSendNewBlockHash(block)
		}
		log.Debug("Announced block", "hash", hash.Hex(), "recipients", len(peers), "duration", common.PrettyDuration(time.Since(block.ReceivedAt)))
	}
}

// BroadcastTxs will propagate a batch of transactions to all peers which are not known to
// already have the given transaction.
func (pm *ProtocolManager) BroadcastTxs(txs types.Transactions) {
	var txset = make(map[*peer]types.Transactions)

	// Broadcast transactions to a batch of peers not knowing about it
	for _, tx := range txs {
		peers := pm.peers.PeersWithoutTx(tx.Hash())
		for _, peer := range peers {
			txset[peer] = append(txset[peer], tx)
		}
		log.Debug("Broadcast transaction", "hash", tx.Hash().Hex(), "recipients", len(peers))
	}
	// FIXME include this again: peers = peers[:int(math.Sqrt(float64(len(peers))))]
	for peer, txs := range txset {
		peer.AsyncSendTransactions(txs)
	}
}

// Mined broadcast loop
func (pm *ProtocolManager) minedBroadcastLoop() {

	// automatically stops if unsubscribe
	for obj := range pm.minedBlockSub.Chan() {
		switch ev := obj.Data.(type) {
		case core.NewMinedBlockEvent:
			pm.broadcastBlock(ev.Block, true, true)  // First propagate block to peers
			pm.broadcastBlock(ev.Block, false, true) // Only then announce to the rest
		}
	}

}

func (pm *ProtocolManager) txBroadcastLoop() {
	for {
		select {
		case event := <-pm.txsCh:
			pm.BroadcastTxs(event.Txs)

		// Err() channel will be closed when unsubscribing.
		case <-pm.txsSub.Err():
			return
		}
	}
}

// BroadcastPBFT broadcasts pbft messages to other signers
func (pm *ProtocolManager) BroadcastPBFT(msg interface{}, pbftStatus uint8) error {
	peers := pm.peers.committee
	switch m := msg.(type) {
	case *types.Header:
		for _, p := range peers {
			switch pbftStatus {
			case consensus.Prepare:
				p.AsyncSendPrepareSignedHeader(m)
			case consensus.Commit:
				p.AsyncSendCommitSignedHeader(m)
			}
		}

	case *types.Block:
		for _, p := range peers {
			switch pbftStatus {
			case consensus.Preprepare:
				p.AsyncSendNewPendingBlock(m)
			}
		}
	}
	return nil
}
