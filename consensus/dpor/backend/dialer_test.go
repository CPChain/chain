package backend

import (
	"testing"

	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/signer_register"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

func TestSigner_fetchPubkey(t *testing.T) {
	type fields struct {
		Peer                *p2p.Peer
		rw                  p2p.MsgReadWriter
		version             int
		epochIdx            uint64
		pubkey              []byte
		nodeID              string
		address             common.Address
		dialed              bool
		pubkeyFetched       bool
		nodeIDFetched       bool
		nodeIDUpdated       bool
		queuedPendingBlocks chan *types.Block
		queuedPrepareSigs   chan *types.Header
		queuedCommitSigs    chan *types.Header
		term                chan struct{}
	}
	type args struct {
		contractInstance *contract.SignerConnectionRegister
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
			s := &Signer{
				Peer:                tt.fields.Peer,
				rw:                  tt.fields.rw,
				version:             tt.fields.version,
				epochIdx:            tt.fields.epochIdx,
				pubkey:              tt.fields.pubkey,
				nodeID:              tt.fields.nodeID,
				address:             tt.fields.address,
				dialed:              tt.fields.dialed,
				pubkeyFetched:       tt.fields.pubkeyFetched,
				nodeIDFetched:       tt.fields.nodeIDFetched,
				nodeIDUpdated:       tt.fields.nodeIDUpdated,
				queuedPendingBlocks: tt.fields.queuedPendingBlocks,
				queuedPrepareSigs:   tt.fields.queuedPrepareSigs,
				queuedCommitSigs:    tt.fields.queuedCommitSigs,
				term:                tt.fields.term,
			}
			if err := s.fetchPubkey(tt.args.contractInstance); (err != nil) != tt.wantErr {
				t.Errorf("Signer.fetchPubkey() error = %v, wantErr %v", err, tt.wantErr)
			}
		})
	}
}
