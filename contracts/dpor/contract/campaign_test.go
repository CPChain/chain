package contract

import (
	"context"
	"crypto/ecdsa"
	"fmt"
	"log"
	"math/big"
	"os"
	"path/filepath"

	"testing"

	"time"

	"bytes"

	"github.com/ethereum/go-ethereum/accounts/abi/bind"
	"github.com/ethereum/go-ethereum/accounts/keystore"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/ethclient"
)

func TestCampaign(t *testing.T) {
	t.Skip("we shall use a simulated backend.")

	// create client.
	// client, err := ethclient.Dial("https://rinkeby.infura.io")
	client, err := ethclient.Dial("http://localhost:8501") // local
	if err != nil {
		log.Fatal(err)
	}

	// create account.
	// privateKey, err := crypto.HexToECDSA("fad9c8855b740a0b7ed4c221dbad0f33a83a49cad6b3fe8d5817ac83d38b6a19")
	file, _ := os.Open("../../../examples/cpchain/data/dd1/keystore/")
	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	kst := keystore.NewKeyStore(keyPath, 2, 1)
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, "password")
	privateKey := key.PrivateKey

	if err != nil {
		log.Fatal(err)
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
		log.Fatal(err)
	}

	auth := bind.NewKeyedTransactor(privateKey)
	//auth.Nonce = big.NewInt(int64(nonce)) // not necessary
	auth.Value = big.NewInt(0)       // in wei
	auth.GasLimit = uint64(gasLimit) // in units
	auth.GasPrice = gasPrice

	// launch contract deploy transaction.
	address, tx, instance, err := DeployCampaign(auth, client)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Printf("Contract pending deploy: 0x%x\n", address)
	fmt.Printf("Transaction waiting to be mined: 0x%x\n\n", tx.Hash())

	startTime := time.Now()
	fmt.Printf("TX start @:%s", time.Now())
	ctx := context.Background()
	addressAfterMined, err := bind.WaitDeployed(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	if !bytes.Equal(address.Bytes(), addressAfterMined.Bytes()) {
		log.Fatalf("mined address :%s,before mined address:%s", addressAfterMined, address)
	}

	fmt.Println("*******************************************************")
	numOfCampaign, deposit, _ := ClaimCampaign(privateKey, gasLimit, gasPrice, err, instance, startTime, ctx, client, fromAddress)
	assert(1, 50, numOfCampaign, deposit, t)

	fmt.Println("*******************************************************")
	numOfCampaign, deposit, _ = ClaimCampaign(privateKey, gasLimit, gasPrice, err, instance, startTime, ctx, client, fromAddress)
	assert(2, 100, numOfCampaign, deposit, t)
}

func assert(expectNum int64, expectDeposit int64, numOfCampaign *big.Int, deposit *big.Int, t *testing.T) {
	if numOfCampaign.Cmp(big.NewInt(expectNum)) != 0 || deposit.Cmp(big.NewInt(expectDeposit)) != 0 {
		t.Fatal("unexpected numOfCampaign, deposit:", numOfCampaign, deposit)
	}
}

func ClaimCampaign(privateKey *ecdsa.PrivateKey, gasLimit int, gasPrice *big.Int, err error, instance *Campaign, startTime time.Time, ctx context.Context, client *ethclient.Client, fromAddress common.Address) (*big.Int, *big.Int, *big.Int) {
	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(50)
	// in wei
	auth.GasLimit = uint64(gasLimit)
	// in units
	auth.GasPrice = gasPrice
	claimtx, err := instance.ClaimCampaign(auth, big.NewInt(int64(1)), big.NewInt(int64(60)))
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("TX:", claimtx.Hash().Hex())
	startTime = time.Now()
	receipt, err := bind.WaitMined(ctx, client, claimtx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	fmt.Println("receipt.Status:", receipt.Status)
	// test contract state variable call.
	x, err := instance.MinimumRpt(nil)
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("minimum reputation: ", x)
	// test contract map variable call.
	numOfCampaign, deposit, timestamp, err := instance.CandidateInfoOf(nil, fromAddress)
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("candidate info of", fromAddress.Hex(), ":", numOfCampaign, deposit, timestamp)
	// see candidates of view zero.
	candidates, err := instance.CandidatesOf(nil, big.NewInt(0))
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("candidates of first view:")
	for i := 0; i < len(candidates); i++ {
		fmt.Println("number", i, candidates[i].Hex())
	}
	return numOfCampaign, deposit, timestamp
}
