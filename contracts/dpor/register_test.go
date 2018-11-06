package dpor

import (
	"crypto/ecdsa"
	"fmt"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/core"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto/sha3"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/stretchr/testify/assert"
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

func deployTestRegister(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, *Register, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	addr, instance, err := DeployRegister(deployTransactor, backend)

	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
		return common.Address{}, nil, err
	}
	backend.Commit()
	return addr, instance, nil
}

func TestRegister(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	_, register, err := deployTestRegister(key, big.NewInt(0), contractBackend)
	checkError(t, "can't deploy root registry: %v", err)
	contractBackend.Commit()

	fakefile := file{
		fileName: ",cpchian,cpchian,cpchian",
		fileSize: big.NewInt(88),
	}
	copy(fakefile.fileHash[:], sigHash(fakefile).Bytes())

	transactOpts := bind.NewKeyedTransactor(key)
	_, err = register.ClaimRegister(transactOpts, fakefile.fileName, fakefile.fileHash, fakefile.fileSize)
	if err != nil {
		fmt.Println("ClainRegister error :", err)
		log.Warn("ClaimRegister error", err)
	}
	contractBackend.Commit()

	filenumber, err := register.GetUploadCount(nil, addr)
	if err != nil {
		log.Warn("GetUploadCount err", addr, err)
	}
	fmt.Println(err)
	assert.Equal(t, float64(1), float64(filenumber.Int64()))

	file, err := register.UploadHistory(addr, big.NewInt(int64(0)))
	if err != nil {
		log.Warn("GetUploadCount err", addr, err)
	}
	assert.Equal(t, fakefile.fileName, file.FileName)

}
