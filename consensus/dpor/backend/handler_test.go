package backend

import (
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"github.com/ethereum/go-ethereum/common"
)

// launch the chain
// new a committee_network_handler
// build the network.

func TestNewHandler(t *testing.T) {
	type args struct {
		config    *configs.DporConfig
		etherbase common.Address
	}
	tests := []struct {
		name string
		args args
		want *Handler
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := NewHandler(tt.args.config, tt.args.etherbase); !reflect.DeepEqual(got, tt.want) {
				t.Errorf("NewHandler() = %v, want %v", got, tt.want)
			}
		})
	}
}
