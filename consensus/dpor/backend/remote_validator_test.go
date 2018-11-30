package backend

import (
	"testing"
)

func TestValidatorHandshake(t *testing.T) {
	// TODO: @AC need to redesign
	// type args struct {
	// 	p                       *p2p.Peer
	// 	rw                      p2p.MsgReadWriter
	// 	coinbase                common.Address
	// 	verifyRemoteValidatorFn VerifyRemoteValidatorFn
	// }
	// tests := []struct {
	// 	name            string
	// 	args            args
	// 	wantIsValidator bool
	// 	wantAddress     common.Address
	// 	wantErr         bool
	// }{
	// 	// TODO: Add test cases.
	// }
	// for _, tt := range tests {
	// 	t.Run(tt.name, func(t *testing.T) {
	// 		gotIsValidator, gotAddress, err := ValidatorHandshake(tt.args.p, tt.args.rw, tt.args.coinbase, tt.args.verifyRemoteValidatorFn)
	// 		if (err != nil) != tt.wantErr {
	// 			t.Errorf("ValidatorHandshake() error = %v, wantErr %v", err, tt.wantErr)
	// 			return
	// 		}
	// 		if gotIsValidator != tt.wantIsValidator {
	// 			t.Errorf("ValidatorHandshake() gotIsValidator = %v, want %v", gotIsValidator, tt.wantIsValidator)
	// 		}
	// 		if !reflect.DeepEqual(gotAddress, tt.wantAddress) {
	// 			t.Errorf("ValidatorHandshake() gotAddress = %v, want %v", gotAddress, tt.wantAddress)
	// 		}
	// 	})
	// }
}
