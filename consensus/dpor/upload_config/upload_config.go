package upload_config

import (
	"context"
	"crypto/ecdsa"
	"fmt"
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/register"
	"bitbucket.org/cpchain/chain/core"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/crypto/sha3"
	"github.com/ethereum/go-ethereum/rlp"
)

var (
	Testkey, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	Addr       = crypto.PubkeyToAddress(Testkey.PublicKey)
)
var (
	ContractBackend           = backends.NewDporSimulatedBackend(core.GenesisAlloc{Addr: {Balance: big.NewInt(1000000000000)}})
	RegisterContractAddr, err = Deploy(Testkey, big.NewInt(0), ContractBackend)
)

type file struct {
	fileName string
	fileHash [32]byte
	fileSize *big.Int
}

func sigHash(testfile file) (hash common.Hash) {
	hasher := sha3.NewKeccak256()

	rlp.Encode(hasher, []interface{}{
		testfile.fileName,
		testfile.fileSize,
	})
	hasher.Sum(hash[:0])
	return hash
}

func Deploy(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	deployTransactor.Value = amount
	addr, _, _, err := register.DeployRegister(deployTransactor, backend)
	if err != nil {
		return common.Address{}, err
	}
	backend.Commit()
	return addr, nil
}

func DeployRegister() {

	Fakeregister, err := register.NewRegister(RegisterContractAddr, ContractBackend)
	ContractBackend.Commit()
	printBalance(ContractBackend)

	fakefile1 := file{
		fileName: ",cpchian,cpchian,cpchian good",
		fileSize: big.NewInt(88),
	}
	copy(fakefile1.fileHash[:], sigHash(fakefile1).Bytes())

	fakefile2 := file{
		fileName: ",cpchian,cpchian,cpchian best",
		fileSize: big.NewInt(88),
	}
	copy(fakefile2.fileHash[:], sigHash(fakefile2).Bytes())

	fakefile3 := file{
		fileName: ",cpchian,cpchian,cpchian Especially good",
		fileSize: big.NewInt(88),
	}
	copy(fakefile3.fileHash[:], sigHash(fakefile3).Bytes())

	transactOpts := bind.NewKeyedTransactor(Testkey)
	_, err1 := Fakeregister.ClaimRegister(transactOpts, fakefile1.fileName, fakefile1.fileHash, fakefile1.fileSize)
	if err1 != nil {
		log.Warn("ClaimRegister,error", Addr, err)
	}
	ContractBackend.Commit()
	printBalance(ContractBackend)
	_, err2 := Fakeregister.ClaimRegister(transactOpts, fakefile2.fileName, fakefile2.fileHash, fakefile2.fileSize)
	if err2 != nil {
		log.Warn("ClaimRegister,error", Addr, err)
	}
	ContractBackend.Commit()
	printBalance(ContractBackend)
	_, err3 := Fakeregister.ClaimRegister(transactOpts, fakefile3.fileName, fakefile3.fileHash, fakefile3.fileSize)
	if err3 != nil {
		log.Warn("ClaimRegister,error", Addr, err)
	}
	ContractBackend.Commit()
	printBalance(ContractBackend)

}

func printBalance(contractBackend *backends.SimulatedBackend) {
	addrBalance, _ := contractBackend.BalanceAt(context.Background(), Addr, nil)
	fmt.Println("==== addrBalance ==== ", addrBalance)
}
