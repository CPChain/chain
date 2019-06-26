package main

import (
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/stretchr/testify/assert"
)

func TestContractAddress(t *testing.T) {
	aa := crypto.CreateAddress(common.HexToAddress("0x0020511a8d7fd0dc831610a8c2d41c99e2cc9a51"), 0) //ContractRnode
	assert.Equal(t, "0x76dBCA2CED6D81E2f26A6657b436d340bb924874", aa.Hex())
	aa = crypto.CreateAddress(common.HexToAddress("0x0020511a8d7fd0dc831610a8c2d41c99e2cc9a51"), 1) //ContractAdmission
	assert.Equal(t, "0x45621603C070b051C0FC337294cAa7b4a21a8b79", aa.Hex())
	aa = crypto.CreateAddress(common.HexToAddress("0x0020511a8d7fd0dc831610a8c2d41c99e2cc9a51"), 2) //ContractCampaign
	assert.Equal(t, "0x4E0AB103714c14d2e3b3A4D9d7355f6A01534242", aa.Hex())
	aa = crypto.CreateAddress(common.HexToAddress("0x0020511a8d7fd0dc831610a8c2d41c99e2cc9a51"), 3) //ContractRpt
	assert.Equal(t, "0x3feA6e441d9dBAfB80f20333bD16d00e49179b33", aa.Hex())
	aa = crypto.CreateAddress(common.HexToAddress("0x0020511a8d7fd0dc831610a8c2d41c99e2cc9a51"), 4) //ContractNetwork
	assert.Equal(t, "0x951C57619aD1f7DCf2Eb5f7078eE7264c9cF8ef8", aa.Hex())

}
