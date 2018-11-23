package backend

import (
	"reflect"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

func TestHandshake(t *testing.T) {
	type args struct {
		p               *p2p.Peer
		rw              p2p.MsgReadWriter
		etherbase       common.Address
		signerValidator VerifyRemoteValidatorFn
	}
	tests := []struct {
		name         string
		args         args
		wantIsSigner bool
		wantAddress  common.Address
		wantErr      bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			gotIsSigner, gotAddress, err := VVHandshake(tt.args.p, tt.args.rw, tt.args.etherbase, tt.args.signerValidator)
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
