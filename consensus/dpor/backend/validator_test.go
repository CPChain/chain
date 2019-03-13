package backend

import (
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

func TestHandler_handleLbft2Msg(t *testing.T) {
	type fields struct {
		mode           HandlerMode
		config         *configs.DporConfig
		available      bool
		coinbase       common.Address
		dialer         *Dialer
		snap           *consensus.PbftStatus
		fsm            ConsensusStateMachine
		lbft           *LBFT
		dpor           DporService
		knownBlocks    *RecentBlocks
		pendingBlockCh chan *types.Block
		quitCh         chan struct{}
	}
	type args struct {
		msg p2p.Msg
		p   *RemoteSigner
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			vh := &Handler{
				mode:           tt.fields.mode,
				config:         tt.fields.config,
				available:      tt.fields.available,
				coinbase:       tt.fields.coinbase,
				dialer:         tt.fields.dialer,
				fsm:            tt.fields.fsm,
				lbft:           tt.fields.lbft,
				dpor:           tt.fields.dpor,
				knownBlocks:    tt.fields.knownBlocks,
				pendingBlockCh: tt.fields.pendingBlockCh,
				quitCh:         tt.fields.quitCh,
			}
			if err := vh.handleLBFT2Msg(tt.args.msg, tt.args.p); (err != nil) != tt.wantErr {
				t.Errorf("Handler.handleLbft2Msg() error = %v, wantErr %v", err, tt.wantErr)
			}
		})
	}
}
