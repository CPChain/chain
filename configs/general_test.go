// Copyright 2018 The cpchain authors

package configs

import (
	"encoding/json"
	"fmt"
	"math/big"
	"testing"

	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/assert"
)

func TestDporConfig(t *testing.T) {
	contracts := map[string]common.Address{}
	contracts["t1"] = common.HexToAddress("0x01")
	contracts["t2"] = common.HexToAddress("0x02")
	dc := &DporConfig{Contracts: contracts}
	s, err := json.Marshal(dc)
	if err != nil {
		t.Error("marshal json error")
	}
	fmt.Println("s:", string(s))
}

func TestCandidates(t *testing.T) {
	SetRunMode(Dev)
	addr := Candidates()
	assert.Equal(t, devDefaultCandidates, addr)
}

func TestProposers(t *testing.T) {
	SetRunMode(Dev)
	props := Proposers()
	assert.Equal(t, devProposers, props)
}

func TestValidators(t *testing.T) {
	SetRunMode(Dev)
	validators := Validators()
	assert.Equal(t, devValidators, validators)
}

func TestBootnodes(t *testing.T) {
	SetRunMode(Dev)
	assert.Equal(t, devBootnodes, Bootnodes())

	SetRunMode(Testnet)
	assert.Equal(t, testnetBootnodes, Bootnodes())

	SetRunMode(Mainnet)
	assert.Equal(t, mainnetBootnodes, Bootnodes())
}

func TestDeposit(t *testing.T) {
	SetRunMode(Dev)
	deposit := Deposit()
	assert.Equal(t, devDeposit, deposit)
}

func TestGetDefaultValidators(t *testing.T) {
	urls := GetDefaultValidators()
	assert.Nil(t, urls)
}

func TestGetDefaultValidatorsByRunMode(t *testing.T) {
	SetRunMode(Dev)
	InitDefaultValidators(nil)
	urls := GetDefaultValidators()
	assert.Equal(t, defaultDevValidatorNodes, urls)

	SetRunMode(Mainnet)
	InitDefaultValidators(nil)
	urls = GetDefaultValidators()
	assert.Equal(t, len(defaultMainnetValidatorNodes), len(urls))

	SetRunMode(Testnet)
	InitDefaultValidators(nil)
	urls = GetDefaultValidators()
	assert.Equal(t, defaultTestnetValidatorNodes, urls)
}

func TestInitDefaultValidators(t *testing.T) {
	InitDefaultValidators(defaultDevValidatorNodes)
	url := GetDefaultValidators()
	assert.Equal(t, defaultDevValidatorNodes, url)
}

func TestDporConfig_String(t *testing.T) {
	contracts := map[string]common.Address{}
	contracts["t1"] = common.HexToAddress("0x01")
	contracts["t2"] = common.HexToAddress("0x02")
	dc := &DporConfig{Contracts: contracts}
	assert.Equal(t, "dpor", dc.String())
}

func TestChainConfigString(t *testing.T) {
	cc := ChainConfig{Dpor: nil, ChainID: big.NewInt(10)}
	assert.Equal(t, "{ChainID: 10 Engine: unknown}", cc.String())
}

func TestChainConfigString1(t *testing.T) {
	contracts := map[string]common.Address{}
	contracts["t1"] = common.HexToAddress("0x01")
	cc := ChainConfig{Dpor: &DporConfig{Contracts: contracts}, ChainID: big.NewInt(10)}
	assert.Equal(t, "{ChainID: 10 Engine: dpor}", cc.String())
}

func TestIsCpchainTrue(t *testing.T) {
	cc := ChainConfig{Dpor: nil, ChainID: big.NewInt(MainnetChainId)}
	assert.True(t, cc.IsCpchain())
}

func TestIsCpchainFalse(t *testing.T) {
	cc := ChainConfig{Dpor: nil, ChainID: big.NewInt(10)}
	assert.False(t, cc.IsCpchain())
}

func TestIsCpchainFalse1(t *testing.T) {
	cc := ChainConfig{Dpor: nil, ChainID: nil}
	assert.False(t, cc.IsCpchain())
}

func TestGasTable(t *testing.T) {
	SetRunMode(Dev)
	cc := ChainConfig{Dpor: nil, ChainID: nil}
	assert.Equal(t, GasTableCep1, cc.GasTable(big.NewInt(0)))
}

func TestConfigCompatError(t *testing.T) {
	err := ConfigCompatError{What: "xxx", StoredConfig: nil, NewConfig: nil, RewindTo: 1}
	assert.Equal(t, "mismatching xxx in database (have <nil>, want <nil>, rewindto 1)", err.Error())
}

func TestRulesIsNotCpchain(t *testing.T) {
	cc := ChainConfig{Dpor: nil, ChainID: nil}
	rule := cc.Rules(nil)
	assert.False(t, rule.IsCpchain)
}

func TestRulesIsCpchain(t *testing.T) {
	cc := ChainConfig{Dpor: nil, ChainID: big.NewInt(MainnetChainId)}
	rule := cc.Rules(nil)
	assert.True(t, rule.IsCpchain)
}

func TestChainConfigInfo(t *testing.T) {
	SetRunMode(Dev)
	chainConfigInfo := ChainConfigInfo()
	assert.Equal(t, devChainConfig, chainConfigInfo)

	SetRunMode(Testnet)
	chainConfigInfo = ChainConfigInfo()
	assert.Equal(t, testnetChainConfig, chainConfigInfo)

	SetRunMode(Mainnet)
	chainConfigInfo = ChainConfigInfo()
	assert.Equal(t, mainnetChainConfig, chainConfigInfo)
}

func TestConvertDomainNodeWithIpOK(t *testing.T) {
	address, err := convertDomainNode("enode://2ddfb534019e6b446fb4465742f266d04fae661089e3dac6a4c841ad0fcf5569f8d049203079bb64e20d1a32fc84b584920839a2120cd5e8886744719452d936@127.0.0.1:30317")
	assert.Nil(t, err)
	assert.Equal(t, "enode://2ddfb534019e6b446fb4465742f266d04fae661089e3dac6a4c841ad0fcf5569f8d049203079bb64e20d1a32fc84b584920839a2120cd5e8886744719452d936@127.0.0.1:30317", address)
}

func TestConvertDomainNodeWithDomainOK(t *testing.T) {
	address, err := convertDomainNode("enode://2ddfb534019e6b446fb4465742f266d04fae661089e3dac6a4c841ad0fcf5569f8d049203079bb64e20d1a32fc84b584920839a2120cd5e8886744719452d936@www.baidu.com:30317")
	fmt.Println(address)
	assert.Nil(t, err)
	assert.NotEqual(t, "enode://2ddfb534019e6b446fb4465742f266d04fae661089e3dac6a4c841ad0fcf5569f8d049203079bb64e20d1a32fc84b584920839a2120cd5e8886744719452d936@www.baidu.com:30317", address)
}

func TestConvertDomainNodeWithDomainFail(t *testing.T) {
	_, err := convertDomainNode("enode://2ddfb534019e6b446fb4465742f266d04fae661089e3dac6a4c841ad0fcf5569f8d049203079bb64e20d1a32fc84b584920839a2120cd5e8886744719452d936@www.notexistwebsite111.com:30317")
	assert.NotNil(t, err)
}

func TestConvertValidators(t *testing.T) {
	validators := []string{"enode://2ddfb534019e6b446fb4465742f266d04fae661089e3dac6a4c841ad0fcf5569f8d049203079bb64e20d1a32fc84b584920839a2120cd5e8886744719452d936@www.baidu.com:30317",
		"enode://2ddfb534019e6b446fb4465742f266d04fae661089e3dac6a4c841ad0fcf5569f8d049203079bb64e20d1a32fc84b584920839a2120cd5e8886744719452d936@192.111.222.3:30317",
		"enode://2ddfb534019e6b446fb4465742f266d04fae661089e3dac6a4c841ad0fcf5569f8d049203079bb64e20d1a32fc84b584920839a2120cd5e8886744719452d936@127.3.1.2:30317"}
	newValidators, err := ConvertNodeURL(validators)
	fmt.Println(newValidators)
	assert.Nil(t, err)
	assert.Equal(t, 3, len(newValidators))
}

func TestResolveDomain(t *testing.T) {
	_, err := resolveDomain("v01.mainnet.cpc-servers.com:8533")
	fmt.Println("err", err)
	assert.NotNil(t, err)
}

func TestResolveDomain1(t *testing.T) {
	host, err := resolveDomain("v01.mainnet.cpc-servers.com")
	fmt.Println("host", host)
	fmt.Println("err", err)
	if err != nil {
		t.Skip("skip if no hosts mapping")
	}
}

func TestResolveUrl(t *testing.T) {
	endPoint := "http://v01.mainnet.cpc-servers.com:8533"
	url, err := ResolveUrl(endPoint)
	fmt.Println("host", url)
	fmt.Println("err", err)
	if err != nil {
		t.Skip("skip if no hosts mapping")
	}
}
