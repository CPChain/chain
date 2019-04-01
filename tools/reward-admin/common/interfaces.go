package common

import (
	"math/big"

	"github.com/ethereum/go-ethereum/common"
)

// Output data
type Output interface {
	Info(msg string, params ...interface{})
	Error(msg string, params ...interface{})
	Fatal(msg string, params ...interface{})
	Warn(msg string, params ...interface{})
}

// Manager manage the cpchain node
type Manager interface {
	IsLocked()
	GetMessage() error
	ContractAccountBalance()
	StartNewRound() error
	StartNewRaise() error
}

// RewardBalance is balance of contract namded reward
type InvestorInfo struct {
	FreeBalance   *big.Int
	LockedBalance *big.Int
	IsToRenew     bool
	Account       common.Address
}
