package rpt_test

import (
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/register"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/crypto/sha3"
	"fmt"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/stretchr/testify/assert"
	"testing"

	"bitbucket.org/cpchain/chain/crypto"
	"context"
	"crypto/ecdsa"
	"github.com/ethereum/go-ethereum/common"
	"math/big"
)

var (
	key, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	addr   = crypto.PubkeyToAddress(key.PublicKey)
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

func deploy(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	deployTransactor.Value = amount
	addr, _, _, err := register.DeployRegister(deployTransactor, backend)
	if err != nil {
		return common.Address{}, err
	}
	backend.Commit()
	return addr, nil
}

func TestDeployRegister(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	contractAddr, err := deploy(key, big.NewInt(0), contractBackend)
	checkError(t, "deploy contract: expected no error, got %v", err)

	Fakeregister, err := register.NewRegister(contractAddr, contractBackend)
	checkError(t, "NewRegister, got %v", err)
	contractBackend.Commit()
	printBalance(contractBackend)

	fakefile := file{
		fileName: ",cpchian,cpchian,cpchian",
		fileSize: big.NewInt(88),
	}
	copy(fakefile.fileHash[:], sigHash(fakefile).Bytes())
	transactOpts := bind.NewKeyedTransactor(key)
	_, err1 := Fakeregister.ClaimRegister(transactOpts, fakefile.fileName, fakefile.fileHash, fakefile.fileSize)
	if err1 != nil {
		log.Warn("ClaimRegister,error", addr, err)
	}
	contractBackend.Commit()
	printBalance(contractBackend)

	filenumber, err2 := Fakeregister.GetUploadCount(nil, addr)
	if err2 != nil {
		log.Warn("GetUploadCount err", addr, err)
	}
	fmt.Println(err)
	assert.Equal(t, float64(1), float64(filenumber.Int64()))

	file, err3 := Fakeregister.UploadHistory(nil, addr, big.NewInt(int64(0)))
	if err3 != nil {
		log.Warn("GetUploadCount err", addr, err)
	}
	assert.Equal(t, fakefile.fileName, file.FileName)
	contractBackend.Commit()
	printBalance(contractBackend)
}

func checkError(t *testing.T, msg string, err error) {
	if err != nil {
		t.Fatalf(msg, err)
	}
}

func printBalance(contractBackend *backends.SimulatedBackend) {
	addrBalance, _ := contractBackend.BalanceAt(context.Background(), addr, nil)
	fmt.Println("==== addrBalance ==== ", addrBalance)
}
