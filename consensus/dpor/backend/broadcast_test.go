package backend

import (
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/consensus"
	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/signer_register"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

func TestHandler_PendingBlockBroadcastLoop(t *testing.T) {
	type fields struct {
		epochIdx           uint64
		epochLength        uint64
		nodeId             string
		coinbase           common.Address
		server             *p2p.Server
		rsaKey             *rsakey.RsaKey
		contractAddress    common.Address
		contractCaller     *ContractCaller
		contractInstance   *contract.SignerConnectionRegister
		contractTransactor *bind.TransactOpts
		signers            map[common.Address]*Signer
		snap               *consensus.PbftStatus
		statusFn           StatusFn
		statusUpdateFn     StatusUpdateFn
		getEmptyBlockFn    GetEmptyBlockFn
		verifyHeaderFn     VerifyHeaderFn
		verifyBlockFn      ValidateBlockFn
		signHeaderFn       SignHeaderFn
		insertChainFn      InsertChainFn
		broadcastBlockFn   BroadcastBlockFn
		validateSignerFn   ValidateSignerFn
		pendingBlockCh     chan *types.Block
		quitSync           chan struct{}
		dialed             bool
		available          bool
	}
	tests := []struct {
		name   string
		fields fields
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			h := &Handler{
				term:               tt.fields.epochIdx,
				termLen:            tt.fields.epochLength,
				nodeId:             tt.fields.nodeId,
				coinbase:           tt.fields.coinbase,
				server:             tt.fields.server,
				rsaKey:             tt.fields.rsaKey,
				contractAddress:    tt.fields.contractAddress,
				contractCaller:     tt.fields.contractCaller,
				contractInstance:   tt.fields.contractInstance,
				contractTransactor: tt.fields.contractTransactor,
				signers:            tt.fields.signers,
				snap:               tt.fields.snap,
				statusFn:           tt.fields.statusFn,
				statusUpdateFn:     tt.fields.statusUpdateFn,
				getEmptyBlockFn:    tt.fields.getEmptyBlockFn,
				verifyHeaderFn:     tt.fields.verifyHeaderFn,
				validateBlockFn:    tt.fields.verifyBlockFn,
				signHeaderFn:       tt.fields.signHeaderFn,
				insertChainFn:      tt.fields.insertChainFn,
				broadcastBlockFn:   tt.fields.broadcastBlockFn,
				validateSignerFn:   tt.fields.validateSignerFn,
				pendingBlockCh:     tt.fields.pendingBlockCh,
				quitSync:           tt.fields.quitSync,
				dialed:             tt.fields.dialed,
				available:          tt.fields.available,
			}
			// TODO: this is wrong, fix this
			h.PendingBlockBroadcastLoop()
		})
	}
}
