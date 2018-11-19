package backend

import (
	"crypto/rand"
	"reflect"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
)

// newTestPeer creates a new peer and a message pipe for testing.
func newTestPeer(name string) (*p2p.Peer, p2p.MsgReadWriter) {
	// Create a message pipe to communicate through
	_, net := p2p.MsgPipe()

	// Generate a random id and create the peer
	var id discover.NodeID
	rand.Read(id[:])

	peer := p2p.NewPeer(id, name, nil)
	return peer, net
}

func fakeValidateSignerFn(signer common.Address) (bool, error) {
	return true, nil
}
func TestHandshake(t *testing.T) {
	type args struct {
		p               *p2p.Peer
		rw              p2p.MsgReadWriter
		etherbase       common.Address
		signerValidator ValidateSignerFn
	}
	testPeer, testNet := newTestPeer("peer_1")
	tests := []struct {
		name         string
		args         args
		wantIsSigner bool
		wantAddress  common.Address
		wantErr      bool
	}{
		{"test_HandShake",
			args{
				testPeer,
				testNet,
				common.Address{},
				fakeValidateSignerFn,
			},
			true,
			common.Address{},
			false,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			gotIsSigner, gotAddress, err := Handshake(tt.args.p, tt.args.rw, tt.args.etherbase, tt.args.signerValidator)
			if (err != nil) != tt.wantErr {
				t.Errorf("Handshake() error = %v, wantErr %v", err, tt.wantErr)
				return
			}
			if gotIsSigner != tt.wantIsSigner {
				t.Errorf("Handshake() gotIsSigner = %v, want %v", gotIsSigner, tt.wantIsSigner)
			}
			if !reflect.DeepEqual(gotAddress, tt.wantAddress) {
				t.Errorf("Handshake() gotAddress = %v, want %v", gotAddress, tt.wantAddress)
			}
		})
	}
}
