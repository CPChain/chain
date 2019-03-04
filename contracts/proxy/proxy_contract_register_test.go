package proxy_test

import (
	"crypto/ecdsa"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/contracts/proxy"
	"bitbucket.org/cpchain/chain/core"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	key, _      = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	addr        = crypto.PubkeyToAddress(key.PublicKey)
	numPerRound = 12

	realaddr  = common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87")
	proxyaddr = common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d86")
)

func deploy(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, *bind.TransactOpts, *proxy.ProxyContractRegister, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	proxyaddr, _, instance, err := proxy.DeployProxyContractRegister(deployTransactor, backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	backend.Commit()
	return proxyaddr, deployTransactor, instance, nil
}

func TestProxyContractRegister_GetRealContract(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	_, _, instance, err := deploy(key, big.NewInt(0), contractBackend)
	checkError(t, "deploy contract: expected no error, got %v", err)

	_, err = instance.RegisterPublicKey(proxyaddr, realaddr)
	contractBackend.Commit()
	checkError(t, "RegisterPublicKey : expected no error, got %v ", err)

	addr, err := instance.GetRealContract(proxyaddr)
	checkError(t, "GetRealContract : expected no error, got %v ", err)
	if addr != realaddr {
		t.Fatal("get wrong address", "get addr:", addr, "real address", realaddr)
	}

	version, err := instance.GetContractVersion(proxyaddr)
	checkError(t, "GetContractVersion : expected no error, got %v ", err)
	if version.Uint64() != uint64(1) {
		t.Fatal("get wrong version", "get version", version, "we want", 1)
	}

	addrByversion, err := instance.GetOldContract(proxyaddr, big.NewInt(1))
	checkError(t, "GetOldContract : expected no error, got %v ", err)
	if addrByversion != realaddr {
		t.Fatal("get wrong address", "get addr:", addrByversion, "real address", realaddr)
	}
}

func checkError(t *testing.T, msg string, err error) {
	if err != nil {
		t.Fatalf(msg, err)
	}
}
