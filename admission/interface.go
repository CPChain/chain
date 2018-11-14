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
	"sync"

	"bitbucket.org/cpchain/chain/api/rpc"
	"github.com/ethereum/go-ethereum/common"
)

// go:generate abigen --sol contract/admission/campaign.sol --pkg contract --out contract/admission/campaign.go

// APIBackend interface provides the common JSON-RPC API.
type APIBackend interface {
	// APIs returns the collection of RPC services the admission package offers.
	APIs() []rpc.API

	// Campaign starts running all the proof work to generate the campaign information and waits all proof work done, send msg
	Campaign()

	// Abort cancels all the proof work associated to the workType.
	Abort()

	// GetStatus gets status of campaign
	GetStatus() (workStatus, error)

	// GetProofInfo gets all work proofInfo
	GetProofInfo() ProofInfo

	// VerifyEthash returns true if memory's nonce is valid
	VerifyEthash(number, nonce uint64, signer common.Address) bool
}

// ProofWorkBackend common API for proof work.
type ProofWorkBackend interface {
	// prove starts memory pow work.
	prove(abort chan struct{}, wg *sync.WaitGroup)

	// isOk returns true if work successful
	isOk() bool

	// getError returns err if proof work is abnormal
	getError() error

	// proof returns the work proof result
	getProofInfo() uint64
}
