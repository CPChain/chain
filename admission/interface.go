package admission

import (
	"sync"

	"bitbucket.org/cpchain/chain/core/types"
	"bitbucket.org/cpchain/chain/rpc"
)

//Backend interface provides the common JSON-RPC API.
type Backend interface {
	CurrentBlock() *types.Block
}

//APIBackend interface provides the common JSON-RPC API.
type APIBackend interface {
	//APIs returns the collection of RPC services the admission package offers.
	APIs() []rpc.API

	//Campaign starts running all the proof work to generate the campaign information and waits all proof work done, send msg
	Campaign()

	//Abort cancels all the proof work associated to the workType.
	Abort()

	// GetStatus gets status of campaign
	GetStatus() (workStatus, error)

	// GetProofInfo gets all work proofInfo
	GetProofInfo() ProofInfo
}

//ProofWorkBackend common API for proof work.
type ProofWorkBackend interface {
	//prove starts memory pow work.
	prove(abort chan struct{}, wg *sync.WaitGroup)

	// isOk returns true if work successful
	isOk() bool

	// getError returns err if proof work is abnormal
	getError() error

	// proof returns the work proof result
	getProofInfo() interface{}
}
