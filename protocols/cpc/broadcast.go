// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package cpc

import (
	"math"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// // BroadcastGeneratedBlock broadcasts generated block to committee
// func (pm *ProtocolManager) BroadcastGeneratedBlock(block *types.Block) {
// 	committee := pm.peers.committee
// 	for _, peer := range committee {
// 		peer.AsyncSendNewPendingBlock(block)
// 	}
// }

// // BroadcastPrepareSignedHeader broadcasts signed prepare header to remote committee
// func (pm *ProtocolManager) BroadcastPrepareSignedHeader(header *types.Header) {
// 	committee := pm.peers.committee
// 	for _, peer := range committee {
// 		peer.AsyncSendPrepareSignedHeader(header)
// 	}
// }

// // BroadcastCommitSignedHeader broadcasts signed commit header to remote committee
// func (pm *ProtocolManager) BroadcastCommitSignedHeader(header *types.Header) {
// 	committee := pm.peers.committee
// 	for _, peer := range committee {
// 		peer.AsyncSendCommitSignedHeader(header)
// 	}
// }

// BroadcastBlock will either propagate a block to a subset of it's peers, or
// will only announce it's availability (depending what's requested).
func (pm *ProtocolManager) BroadcastBlock(block *types.Block, propagate bool) {
	log.Debug("peers:")
	for p := range pm.peers.peers {
		log.Debug("signer", "id", p)
	}

	hash := block.Hash()
	peers := pm.peers.PeersWithoutBlock(hash)

	// If propagation is requested, send to a subset of the peer
	if propagate {
		if parent := pm.blockchain.GetBlock(block.ParentHash(), block.NumberU64()-1); parent == nil {
			log.Error("Propagating dangling block", "number", block.Number(), "hash", hash.Hex())
			return
		}

		// Send the block to a subset of our peers
		transfer := peers[:int(math.Sqrt(float64(len(peers))))]

		for _, peer := range transfer {
			peer.AsyncSendNewBlock(block)
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

			if pm.chainconfig.Dpor != nil {

				log.Debug("handling mined block with dpor handler")

				// broadcast mined block with dpor handler
				pm.engine.(*dpor.Dpor).HandleMinedBlock(ev.Block)
			} else {
				pm.BroadcastBlock(ev.Block, true)
			}

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
