package rpt_test

import (
	"context"
	"crypto/ecdsa"
	"fmt"
	"math/big"
	"os"
	"path/filepath"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/register"
	"bitbucket.org/cpchain/chain/crypto"
	"bitbucket.org/cpchain/chain/crypto/sha3"
	"bitbucket.org/cpchain/chain/ethclient"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/stretchr/testify/assert"
)

type filestruck struct {
	fileName string
	fileHash [32]byte
	fileSize *big.Int
}

func sigHash(testfile filestruck) (hash common.Hash) {
	hasher := sha3.NewKeccak256()

	rlp.Encode(hasher, []interface{}{
		testfile.fileName,
		testfile.fileSize,
	})
	hasher.Sum(hash[:0])
	return hash
}

func TestDeployRegister(t *testing.T) {
	t.Skip("we shall use a simulated backend.")

	// create client.
	// client, err := ethclient.Dial("https://rinkeby.infura.io")
	client, err := ethclient.Dial("http://localhost:8501") // local
	if err != nil {
		log.Fatal(err.Error())
	}

	file, _ := os.Open("../../../examples/cpchain/data/dd1/keystore/")
	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	kst := keystore.NewKeyStore(keyPath, 2, 1)
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, "password")
	privateKey := key.PrivateKey

	if err != nil {
		log.Fatal(err.Error())
	}

	publicKey := privateKey.Public()
	publicKeyECDSA, ok := publicKey.(*ecdsa.PublicKey)
	if !ok {
		log.Fatal("error casting public key to ECDSA")
	}

	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)
	fmt.Println("from address:", fromAddress.Hex()) // 0x96216849c49358B10257cb55b28eA603c874b05E

	bal, err := client.BalanceAt(context.Background(), fromAddress, nil)
	fmt.Println("bal:", bal)
	gasLimit := 3000000
	gasPrice, err := client.SuggestGasPrice(context.Background())
	fmt.Println("gasPrice:", gasPrice)
	if err != nil {
		log.Fatal(err.Error())
	}

	auth := bind.NewKeyedTransactor(privateKey)
	//auth.Nonce = big.NewInt(int64(nonce)) // not necessary
	auth.Value = big.NewInt(0)       // in wei
	auth.GasLimit = uint64(gasLimit) // in units
	auth.GasPrice = gasPrice

	contractAddress, _, _, err := register.DeployRegister(auth, client)

	Fakeregister, err := register.NewRegister(contractAddress, client)
	checkError(t, "NewRegister, got %v", err)

	fakefile := filestruck{
		fileName: ",cpchian,cpchian,cpchian",
		fileSize: big.NewInt(88),
	}
	copy(fakefile.fileHash[:], sigHash(fakefile).Bytes())

	_, err1 := Fakeregister.ClaimRegister(auth, fakefile.fileName, fakefile.fileHash, fakefile.fileSize)
	if err1 != nil {
		log.Warn("ClaimRegister,error", fromAddress, err)
	}

	filenumber, err := Fakeregister.GetUploadCount(nil, fromAddress)
	if err != nil {
		log.Warn("GetUploadCount err", fromAddress, err)
	}
	fmt.Println(err)
	assert.Equal(t, float64(1), float64(filenumber.Int64()))

	fileHistory, err := Fakeregister.UploadHistory(nil, fromAddress, big.NewInt(int64(0)))
	if err != nil {
		log.Warn("GetUploadCount err", fromAddress, err)
	}
	assert.Equal(t, fakefile.fileName, fileHistory.FileName)
}

func checkError(t *testing.T, msg string, err error) {
	if err != nil {
		t.Fatalf(msg, err)
	}
}
