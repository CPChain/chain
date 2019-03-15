// Copyright 2015 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package core

import (
	"errors"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/core/state"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/private"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	RemoteDBAbsenceError = errors.New("remoteDB is not set, no capability of processing private transaction")
	NoPermissionError    = errors.New("the node doesn't have the permission/responsibility to process the private tx")
)

// StateProcessor is a basic Processor, which takes care of transitioning
// state from one point to another.
//
// StateProcessor implements Processor.
type StateProcessor struct {
	config *configs.ChainConfig // Chain configuration options
	bc     *BlockChain          // Canonical block chain
	engine consensus.Engine     // Consensus engine used for block rewards
	accm   *accounts.Manager    // Account manager
}

// NewStateProcessor initialises a new StateProcessor.
func NewStateProcessor(config *configs.ChainConfig, bc *BlockChain, engine consensus.Engine, accm *accounts.Manager) *StateProcessor {
	return &StateProcessor{
		config: config,
		bc:     bc,
		engine: engine,
		accm:   accm,
	}
}

// Process processes the state changes according to the Cpchain rules by running
// the transaction messages using the pubStateDB and applying any rewards to both
// the processor (coinbase) and any included uncles.
//
// Process returns the public receipts, private receipts(if have) and logs accumulated during the process and
// returns the amount of gas that was used in the process. If any of the
// transactions failed to execute due to insufficient gas it will return an error.
func (p *StateProcessor) Process(block *types.Block, statedb *state.StateDB, statePrivDB *state.StateDB,
	remoteDB database.RemoteDatabase, cfg vm.Config) (types.Receipts, types.Receipts, []*types.Log, uint64, error) {
	var (
		pubReceipts  types.Receipts
		privReceipts types.Receipts
		usedGas      = new(uint64)
		header       = block.Header()
		allLogs      []*types.Log
		gp           = new(GasPool).AddGas(block.GasLimit())
	)

	// Iterate over and process the individual transactions
	for i, tx := range block.Transactions() {
		statedb.Prepare(tx.Hash(), block.Hash(), i)
		statePrivDB.Prepare(tx.Hash(), block.Hash(), i)
		pubReceipt, privReceipt, _, err := ApplyTransaction(p.config, p.bc, nil, gp, statedb, statePrivDB, remoteDB, header, tx,
			usedGas, cfg, p.accm)
		if err != nil {
			return nil, nil, nil, 0, err
		}
		pubReceipts = append(pubReceipts, pubReceipt)
		if privReceipt != nil {
			privReceipts = append(privReceipts, privReceipt)
		}
		allLogs = append(allLogs, pubReceipt.Logs...) // not include private receipt's logs.
		// TODO: if need to add private receipt's logs to allLogs variable.
	}
	// Finalize the block, applying any consensus engine specific extras (e.g. block rewards)
	p.engine.Finalize(p.bc, header, statedb, block.Transactions(), []*types.Header{}, pubReceipts)

	// TODO: if return private logs separately or merge them together as a whole logs collection?
	return pubReceipts, privReceipts, allLogs, *usedGas, nil
}

// ApplyTransaction attempts to apply a transaction to the given state database
// and uses the input parameters for its environment. It returns the receipt
// for the transaction, gas used and an error if the transaction failed,
// indicating the block was invalid.
func ApplyTransaction(config *configs.ChainConfig, bc ChainContext, author *common.Address, gp *GasPool, pubStateDb *state.StateDB,
	privateStateDb *state.StateDB, remoteDB database.RemoteDatabase, header *types.Header, tx *types.Transaction, usedGas *uint64,
	cfg vm.Config, accm *accounts.Manager) (*types.Receipt, *types.Receipt, uint64, error) {
	msg, err := tx.AsMessage(types.MakeSigner(config))
	if err != nil {
		return nil, nil, 0, err
	}

	// For private tx, its payload is a replacement which cannot be executed as normal tx payload, thus set it to be empty to skip execution.
	// This around of execution generates stuff stored in public blockchain.
	if tx.IsPrivate() {
		msg.SetData([]byte{})
	}

	// Create a new context to be used in the EVM environment
	context := NewEVMContext(msg, header, bc, author)
	// Create a new environment which holds all relevant information
	// about the transaction and calling mechanisms.
	vmenv := vm.NewEVM(context, pubStateDb, config, cfg)
	// Apply the transaction to the current state (included in the env)
	_, gas, failed, err := ApplyMessage(vmenv, msg, gp)
	if err != nil {
		return nil, nil, 0, err
	}
	pubStateDb.Finalise(true)
	*usedGas += gas

	// Create a new pubReceipt for the transaction, storing the intermediate root and gas used by the tx
	// based on the eip phase, we're passing whether the root touch-delete accounts.
	pubReceipt := types.NewReceipt([]byte{}, failed, *usedGas)
	pubReceipt.TxHash = tx.Hash()
	pubReceipt.GasUsed = gas
	// if the transaction created a contract, store the creation address in the pubReceipt.
	if msg.To() == nil {
		pubReceipt.ContractAddress = crypto.CreateAddress(vmenv.Context.Origin, tx.Nonce())
	}
	// Set the pubReceipt logs and create a bloom for filtering
	pubReceipt.Logs = pubStateDb.GetLogs(tx.Hash())
	pubReceipt.Bloom = types.CreateBloom(types.Receipts{pubReceipt})

	var privReceipt *types.Receipt
	// For private tx, it should process its real private tx payload in participant's node. If account manager is nil,
	// doesn't process private tx. If the node does not support private transaction, skip it.
	if tx.IsPrivate() && accm != nil && SupportPrivateTx(bc) {
		privReceipt, err = tryApplyPrivateTx(config, bc, author, gp, privateStateDb, remoteDB, header, tx, cfg, accm)
		if err != nil {
			if err == NoPermissionError {
				log.Info("No permission to process the transaction.")
				return pubReceipt, privReceipt, gas, nil
			} else {
				log.Error("Cannot process the transaction.", err)
				return pubReceipt, privReceipt, 0, err
			}
		}
	}

	return pubReceipt, privReceipt, gas, err
}

// applyPrivateTx attempts to apply a private transaction to the given state database
func tryApplyPrivateTx(config *configs.ChainConfig, bc ChainContext, author *common.Address, gp *GasPool, privateStateDb *state.StateDB,
	remoteDB database.RemoteDatabase, header *types.Header, tx *types.Transaction, cfg vm.Config, accm *accounts.Manager) (*types.Receipt, error) {
	msg, err := tx.AsMessage(types.MakeSigner(config))
	if err != nil {
		return nil, err
	}

	if remoteDB == nil {
		return nil, RemoteDBAbsenceError
	}

	payload, hasPermission, err := private.RetrieveAndDecryptPayload(tx.Data(), tx.Nonce(), remoteDB, accm)
	if err != nil {
		return nil, err
	}
	if !hasPermission {
		return nil, NoPermissionError
	}

	// Replace with the real payload decrypted from remote database.
	msg.SetData(payload)
	msg.GasPrice().SetUint64(0)
	privateStateDb.SetNonce(msg.From(), msg.Nonce())

	// Create a new context to be used in the EVM environment
	context := NewEVMContext(msg, header, bc, author)
	// Create a new environment which holds all relevant information
	// about the transaction and calling mechanisms.
	vmenv := vm.NewEVM(context, privateStateDb, config, cfg)
	// Apply the transaction to the current state (included in the env)
	_, _, failed, err := ApplyMessage(vmenv, msg, gp)
	if err != nil {
		return nil, err
	}

	root := privateStateDb.IntermediateRoot(true).Bytes()

	// Create a new receipt for the transaction, storing the intermediate root and gas used by the tx
	// based on the eip phase, we're passing wether the root touch-delete accounts.
	receipt := types.NewReceipt(root, failed, 0)
	receipt.TxHash = tx.Hash()
	receipt.GasUsed = 0 // for private tx, consume no gas.
	// if the transaction created a contract, store the creation address in the receipt.
	if msg.To() == nil {
		receipt.ContractAddress = crypto.CreateAddress(vmenv.Context.Origin, tx.Nonce())
	}
	// Set the receipt logs and create a bloom for filtering
	receipt.Logs = privateStateDb.GetLogs(tx.Hash())
	receipt.Bloom = types.CreateBloom(types.Receipts{receipt})

	return receipt, nil
}

// SupportPrivateTx returns a bool value indicating whether it supports private transaction
func SupportPrivateTx(bc ChainContext) bool {
	eng := bc.Engine()
	if eng != nil {
		if d, ok := eng.(*dpor.Dpor); ok {
			return (!d.IsValidator()) && private.SupportPrivateTxFlag // validator node cannot handle private tx
		}
	}

	return private.SupportPrivateTxFlag
}
