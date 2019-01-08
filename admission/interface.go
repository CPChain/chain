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

	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/rpc"
)

// ApiBackend interface provides the common JSON-RPC API.
type ApiBackend interface {
	// APIs returns the collection of RPC services the admission package offers.
	Apis() []rpc.API

	// Campaign starts running all the proof work to generate the campaign information and waits all proof work done, send msg
	Campaign(times uint64)

	// Abort cancels all the proof work associated to the workType.
	Abort()

	// GetStatus gets status of campaign
	GetStatus() (workStatus, error)

	// getResult returns the work proof result
	GetResult() map[string]Result

	// SetAdmissionKey sets the key for admission control to participate campaign
	SetAdmissionKey(key *keystore.Key)

	// RegisterInProcHandler registers the rpc.Server, handles RPC request to process the API requests in process
	RegisterInProcHandler(localRPCServer *rpc.Server)
}

// ProofWork represent a proof work
type ProofWork interface {
	// prove starts memory/cpu/... POW work.
	prove(abort chan interface{}, wg *sync.WaitGroup)

	// error returns err if proof work is abnormal
	error() error

	// result returns the work proof result
	result() Result
}
