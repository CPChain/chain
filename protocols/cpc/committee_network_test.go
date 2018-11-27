// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package cpc

import (
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"github.com/ethereum/go-ethereum/common"
)

// launch the chain
// new a committee_network_handler
// build the network.

func TestNewBasicCommitteeNetworkHandler(t *testing.T) {
	type args struct {
		config   *configs.DporConfig
		coinbase common.Address
	}
	tests := []struct {
		name    string
		args    args
		want    *BasicCommitteeHandler
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := NewBasicCommitteeNetworkHandler(tt.args.config, tt.args.coinbase)
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
