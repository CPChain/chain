package contract

import (
	"context"
	"crypto/ecdsa"
	"fmt"
	"log"
	"math/big"

	"testing"

	"time"

	"github.com/ethereum/go-ethereum/accounts/abi/bind"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/ethclient"
)

func TestCampaign(t *testing.T) {
	//t.Skip("we shall use a simulated backend.")

	// create client.
	client, err := ethclient.Dial("https://rinkeby.infura.io")
	// client, err := ethclient.Dial("http://localhost:8545") // local
	if err != nil {
		log.Fatal(err)
	}

	// create account.
	privateKey, err := crypto.HexToECDSA("fad9c8855b740a0b7ed4c221dbad0f33a83a49cad6b3fe8d5817ac83d38b6a19")
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

	// create contract deploy transaction.
	//nonce, err := client.PendingNonceAt(context.Background(), fromAddress)
	//fmt.Println("nonce:", nonce)
	//if err != nil {
	//	log.Fatal(err)
	//}

	gasLimit := 3000000
	gasPrice, err := client.SuggestGasPrice(context.Background())
	fmt.Println("gasPrice:", gasPrice)
	if err != nil {
		log.Fatal(err)
	}

	auth := bind.NewKeyedTransactor(privateKey)
	//auth.Nonce = big.NewInt(int64(nonce))
	auth.Value = big.NewInt(0)       // in wei
	auth.GasLimit = uint64(gasLimit) // in units
	auth.GasPrice = gasPrice

	// launch contract deploy transaction.
	address, tx, instance, err := DeployCampaign(auth, client)
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("contract address:", address.Hex())
	fmt.Println(tx.Hash().Hex())

	// wait until tx receipt status becomes 1.
	tx, isPending, err := client.TransactionByHash(context.Background(), tx.Hash())
	if isPending {
		fmt.Println("DeployCampaign is Pending...", tx.Hash().Hex())
	}
	for isPending {
		time.Sleep(time.Second * 2)

		tx, isPending, err = client.TransactionByHash(context.Background(), tx.Hash())
		if err != nil {
			log.Fatal(err)
		}

	}
	receipt, err := client.TransactionReceipt(context.Background(), tx.Hash())
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("deploy contract transaction receipt status:", receipt.Status)

	// load contract from address
	// address := common.HexToAddress("0x6eC85AC61684e5250257B27FDEfFDE79246fADb1")
	// instance, err := NewCampaign(address, client)

	// launch claimCampaign contract func call transaction.
	//nonce, err = client.PendingNonceAt(context.Background(), fromAddress)
	//fmt.Println("nonce:", nonce)
	//if err != nil {
	//	log.Fatal(err)
	//}

	auth = bind.NewKeyedTransactor(privateKey)
	//auth.Nonce = big.NewInt(int64(nonce))
	auth.Value = big.NewInt(50)      // in wei
	auth.GasLimit = uint64(gasLimit) // in units
	auth.GasPrice = gasPrice

	claimtx, err := instance.ClaimCampaign(auth, big.NewInt(int64(1)), big.NewInt(int64(60)))
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println(claimtx.Hash().Hex())

	// wait until tx receipt status becomes 1.
	claimtx, claimIsPending, err := client.TransactionByHash(context.Background(), claimtx.Hash())
	if claimIsPending {
		fmt.Println("call claimCampaign is Pending...", claimtx.Hash().Hex())
	}
	for claimIsPending {

		time.Sleep(time.Second * 2)

		claimtx, claimIsPending, err = client.TransactionByHash(context.Background(), claimtx.Hash())
		if err != nil {
			log.Fatal(err)
		}

	}
	claimReceipt, err := client.TransactionReceipt(context.Background(), claimtx.Hash())
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("claimCampaign call transaction receipt status:", claimReceipt.Status)

	// test contract state variable call.
	x, err := instance.MinimumRpt(nil)
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("minimum reputation: ", x)

	// test contract map variable call.
	x, y, z, err := instance.CandidateInfoOf(nil, fromAddress)
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("candidate info of", fromAddress.Hex(), ":", x, y, z)

	// see candidates of view zero.
	candidates, err := instance.CandidatesOf(nil, big.NewInt(0))
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("candidates of first view:")
	for i := 0; i < len(candidates); i++ {
		fmt.Println("number", i, candidates[i].Hex())
	}
}
