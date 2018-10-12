package eth

import (
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/p2p"
	"github.com/ethereum/go-ethereum/common"
)

// launch the chain
// new a committee_network_handler
// build the network.

func TestNewBasicCommitteeNetworkHandler(t *testing.T) {
	type args struct {
		epochLength     uint64
		ownAddress      common.Address
		contractAddress common.Address
		server          *p2p.Server
	}
	tests := []struct {
		name    string
		args    args
		want    *BasicCommitteeNetworkHandler
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := NewBasicCommitteeNetworkHandler(tt.args.epochLength, tt.args.ownAddress, tt.args.contractAddress, tt.args.server)
			if (err != nil) != tt.wantErr {
				t.Errorf("NewBasicCommitteeNetworkHandler() error = %v, wantErr %v", err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("NewBasicCommitteeNetworkHandler() = %v, want %v", got, tt.want)
			}
		})
	}
}
