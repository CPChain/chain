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

func TestRegisterSigner(t *testing.T) {
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
	address, tx, instance, err := DeploySignerConnectionRegister(auth, client)
	if err != nil {
		log.Fatal(err)
	}
	ctx := context.Background()

	receipt, err := bind.WaitMined(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Println("receipt.Status:", receipt.Status)

	fmt.Printf("Contract pending deploy: 0x%x\n", address)
	fmt.Printf("Transaction waiting to be mined: 0x%x\n\n", tx.Hash())

	startTime := time.Now()
	fmt.Printf("TX start @:%s", time.Now())
	addressAfterMined, err := bind.WaitDeployed(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	if !bytes.Equal(address.Bytes(), addressAfterMined.Bytes()) {
		log.Fatalf("mined address :%s,before mined address:%s", addressAfterMined, address)
	}

	fmt.Println("*******************************************************")
	RegisterSigner(privateKey, gasLimit, gasPrice, err, instance, startTime, ctx, client, fromAddress)
	fmt.Println("*******************************************************")
}

func RegisterSigner(privateKey *ecdsa.PrivateKey, gasLimit int, gasPrice *big.Int, err error, instance *SignerConnectionRegister, startTime time.Time, ctx context.Context, client *ethclient.Client, fromAddress common.Address) {
	// =================== register public key =======================
	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(500)
	// in wei
	auth.GasLimit = uint64(gasLimit)
	// in units
	auth.GasPrice = gasPrice
	transaction, err := instance.RegisterPublicKey(auth, []byte("ssss"))
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("TX:", transaction.Hash().Hex())
	startTime = time.Now()
	receipt, err := bind.WaitMined(ctx, client, transaction)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	fmt.Println("receipt.Status:", receipt.Status)

	// ====================== get publickey ======================
	// test contract map variable call.
	publicKey, err := instance.GetPublicKey(nil, fromAddress)

	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("publicKey of", fromAddress.Hex(), ":", publicKey)

	// ====================== add nodeinfo ======================
	auth = bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(500)
	// in wei
	auth.GasLimit = uint64(gasLimit)
	// in units
	auth.GasPrice = gasPrice
	transaction, err = instance.AddNodeInfo(auth, big.NewInt(1), fromAddress, []byte("encryptedNodeInfo"))

	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("TX:", transaction.Hash().Hex())
	startTime = time.Now()
	receipt, err = bind.WaitMined(ctx, client, transaction)
	if err != nil {
		log.Fatalf("failed to AddNodeInfo when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	fmt.Println("receipt.Status:", receipt.Status)

	// ====================== GetNodeInfo ======================
	rsaPublicKey, err := instance.GetNodeInfo(nil, big.NewInt(1), fromAddress)
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("rsaPublicKey of", fromAddress.Hex(), ":", string(rsaPublicKey))
}
