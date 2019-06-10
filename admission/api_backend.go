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

package admission

import (
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/consensus"
	contracts "bitbucket.org/cpchain/chain/contracts/dpor/campaign/tests"
	"github.com/ethereum/go-ethereum/common"
)

type AdmissionApiBackend struct {
	admissionControl *AdmissionControl
}

func NewAdmissionApiBackend(chain consensus.ChainReader, address common.Address, admissionContractAddr common.Address,
	campaignContractAddr common.Address, rNodeContractAddr common.Address, networkContractAddr common.Address) ApiBackend {
	return &AdmissionApiBackend{
		admissionControl: NewAdmissionControl(chain, address, admissionContractAddr, campaignContractAddr, rNodeContractAddr, networkContractAddr),
	}
}

// APIs returns the collection of RPC services the admission package offers.
func (b *AdmissionApiBackend) Apis() []rpc.API {
	return []rpc.API{
		{
			Namespace: "admission",
			Version:   "1.0",
			Service:   b,
			Public:    false,
		},
	}
}

func (b *AdmissionApiBackend) IgnoreNetworkCheck() {
	b.admissionControl.IgnoreNetworkCheck()
}

func (b *AdmissionApiBackend) CheckNetworkStatus() bool {
	return b.admissionControl.CheckNetworkStatus()
}

func (b *AdmissionApiBackend) FundForRNode() error {
	return b.admissionControl.FundForRNode()
}

func (b *AdmissionApiBackend) IsRNode() (bool, error) {
	return b.admissionControl.IsRNode()
}

func (b *AdmissionApiBackend) Campaign(terms uint64) error {
	return b.admissionControl.Campaign(terms)
}

func (b *AdmissionApiBackend) Abort() {
	b.admissionControl.Abort()
}

func (b *AdmissionApiBackend) GetStatus() (workStatus, error) {
	return b.admissionControl.GetStatus()
}

func (b *AdmissionApiBackend) GetResult() map[string]Result {
	return b.admissionControl.GetResult()
}

func (b *AdmissionApiBackend) SetAdmissionKey(key *keystore.Key) {
	b.admissionControl.SetAdmissionKey(key)
}

func (b *AdmissionApiBackend) AdmissionKey() *keystore.Key {
	return b.admissionControl.key
}

// RegisterInProcHandler registers the rpc.Server, handles RPC request to process the API requests in process
func (b *AdmissionApiBackend) RegisterInProcHandler(localRPCServer *rpc.Server) {
	client := rpc.DialInProc(localRPCServer)
	b.admissionControl.setClientBackend(cpclient.NewClient(client))
}

func (b *AdmissionApiBackend) SetContractBackend(contractBackend contracts.Backend) {
	b.admissionControl.SetSimulateBackend(contractBackend)
}
