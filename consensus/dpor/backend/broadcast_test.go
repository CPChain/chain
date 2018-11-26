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

func TestHandler_BroadcastMinedBlock(t *testing.T) {
	type fields struct {
		mode               HandlerMode
		term               uint64
		termLen            uint64
		maxInitNumber      uint64
		nodeId             string
		coinbase           common.Address
		server             *p2p.Server
		rsaKey             *rsakey.RsaKey
		knownBlocks        *RecentBlocks
		contractAddress    common.Address
		contractCaller     *ContractCaller
		contractInstance   *contract.SignerConnectionRegister
		contractTransactor *bind.TransactOpts
		remoteValidators   map[common.Address]*RemoteValidator
		snap               *consensus.PbftStatus
		dpor               DporService
		pendingBlockCh     chan *types.Block
		quitSync           chan struct{}
		dialed             bool
		available          bool
	}
	type args struct {
		block *types.Block
	}
	tests := []struct {
		name   string
		fields fields
		args   args
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			h := &Handler{
				mode:               tt.fields.mode,
				term:               tt.fields.term,
				termLen:            tt.fields.termLen,
				maxInitNumber:      tt.fields.maxInitNumber,
				nodeId:             tt.fields.nodeId,
				coinbase:           tt.fields.coinbase,
				server:             tt.fields.server,
				rsaKey:             tt.fields.rsaKey,
				knownBlocks:        tt.fields.knownBlocks,
				contractAddress:    tt.fields.contractAddress,
				contractCaller:     tt.fields.contractCaller,
				contractInstance:   tt.fields.contractInstance,
				contractTransactor: tt.fields.contractTransactor,
				remoteValidators:   tt.fields.remoteValidators,
				snap:               tt.fields.snap,
				dpor:               tt.fields.dpor,
				pendingBlockCh:     tt.fields.pendingBlockCh,
				quitSync:           tt.fields.quitSync,
				dialed:             tt.fields.dialed,
				available:          tt.fields.available,
			}
			h.BroadcastMinedBlock(tt.args.block)
		})
	}
}
