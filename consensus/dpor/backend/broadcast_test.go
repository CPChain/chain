package backend

import (
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

func TestHandler_BroadcastMinedBlock(t *testing.T) {
	type fields struct {
		mode           HandlerMode
		config         *configs.DporConfig
		available      bool
		isProposer     bool
		isValidator    bool
		coinbase       common.Address
		dialer         *Dialer
		snap           *consensus.PbftStatus
		dpor           DporService
		knownBlocks    *RecentBlocks
		pendingBlockCh chan *types.Block
		quitSync       chan struct{}
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
				mode:           tt.fields.mode,
				config:         tt.fields.config,
				available:      tt.fields.available,
				isProposer:     tt.fields.isProposer,
				isValidator:    tt.fields.isValidator,
				coinbase:       tt.fields.coinbase,
				dialer:         tt.fields.dialer,
				snap:           tt.fields.snap,
				dpor:           tt.fields.dpor,
				knownBlocks:    tt.fields.knownBlocks,
				pendingBlockCh: tt.fields.pendingBlockCh,
				quitCh:         tt.fields.quitSync,
			}
			h.BroadcastPreprepareBlock(tt.args.block)
		})
	}
}
