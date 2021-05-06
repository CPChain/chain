package configs_test

import (
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

func showContractAddress(t *testing.T, owner common.Address, name string, nonce uint64) {
	c := crypto.CreateAddress(owner, nonce)
	t.Log(name+": ", c.Hex())
}

func TestGenerateContractsOfMiniMode(t *testing.T) {
	// use the validator as the admin to deploy the contracts
	validator := common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")
	// the order of all to be deployed contracts
	// RNode
	// Admission
	// Campaign
	// Rpt
	// Network
	showContractAddress(t, validator, "RNode", 0)
	showContractAddress(t, validator, "Admission", 1)
	showContractAddress(t, validator, "Campaign", 2)
	showContractAddress(t, validator, "Rpt", 3)
	showContractAddress(t, validator, "Network", 4)
}
