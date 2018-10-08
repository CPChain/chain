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

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/crypto"
	"bitbucket.org/cpchain/chain/ethclient"
	"github.com/ethereum/go-ethereum/common"
)

func TestProxyContractRegister(t *testing.T) {
	t.Skip("we shall use a simulated backend.")

	client, privateKey, fromAddress, gasLimit, gasPrice, instance, ctx, contractAddress := deployProxyContract()

	fmt.Println("*******************************************************")
	registerProxyAndGet(t, privateKey, gasLimit, gasPrice, instance, ctx, client, fromAddress, contractAddress)
	fmt.Println("*******************************************************")
}

func deployProxyContract() (*ethclient.Client, *ecdsa.PrivateKey, common.Address, int, *big.Int, *ProxyContractRegister, context.Context, common.Address) {
	client, err := ethclient.Dial("http://localhost:8501")
	// local
	if err != nil {
		log.Fatal(err)
	}
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
	fmt.Println("from address:", fromAddress.Hex())
	bal, err := client.BalanceAt(context.Background(), fromAddress, nil)
	fmt.Println("bal:", bal)
	gasLimit := 3000000
	gasPrice, err := client.SuggestGasPrice(context.Background())
	fmt.Println("gasPrice:", gasPrice)
	if err != nil {
		log.Fatal(err)
	}
	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(0)
	auth.GasLimit = uint64(gasLimit)
	auth.GasPrice = gasPrice
	address, tx, instance, err := DeployProxyContractRegister(auth, client)
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
	return client, privateKey, fromAddress, gasLimit, gasPrice, instance, ctx, address
}

func registerProxyAndGet(t *testing.T, privateKey *ecdsa.PrivateKey, gasLimit int, gasPrice *big.Int, instance *ProxyContractRegister, ctx context.Context, client *ethclient.Client, fromAddress, contractAddress common.Address) {

	// 2. register node2 public key on chain (claim campaign)
	fmt.Println("2.RegisterProxyContract")
	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(500)
	// in wei
	auth.GasLimit = uint64(gasLimit)
	// in units
	auth.GasPrice = gasPrice

	proxyAddr := common.HexToAddress("0x1a9fae75908752d0abf4dca45ebcac311c376290")
	realAddr := common.HexToAddress("0bd6a2b982fc58e80a50beac02349871e2d016df")
	transaction, err := instance.RegisterProxyContract(auth, proxyAddr, realAddr)
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("TX:", transaction.Hash().Hex())
	startTime := time.Now()
	receipt, err := bind.WaitMined(ctx, client, transaction)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	fmt.Println("receipt.Status:", receipt.Status)

	// 3. node1 get public key with other's(node2) address
	fmt.Println("3.GetRealContract")
	realAddrOnChain, err := instance.GetRealContract(nil, proxyAddr)

	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("realAddr:", realAddrOnChain.Hex(),
		" of proxyAddr:", proxyAddr.Hex())

	if !bytes.Equal(realAddr.Bytes(), realAddrOnChain.Bytes()) {
		t.Errorf("expected enode:%v,got %v", realAddr, realAddrOnChain)
	}

	// register proxy contract address as proxy should be invalid
	proxyAddr = contractAddress
	realAddr = common.HexToAddress("0bd6a2b982fc58e80a50beac02349871e2d016df")
	transaction, err = instance.RegisterProxyContract(auth, proxyAddr, realAddr)
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("TX:", transaction.Hash().Hex())
	startTime = time.Now()
	receipt, err = bind.WaitMined(ctx, client, transaction)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	fmt.Println("receipt.Status:", receipt.Status)

	// 4. GetRealContract
	fmt.Println("4.GetRealContract")
	realAddrOnChain, err = instance.GetRealContract(nil, proxyAddr)

	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("realAddr:", realAddrOnChain.Hex(), "of proxyAddr:", proxyAddr.Hex())

	empty := common.Address{}
	if !bytes.Equal(empty.Bytes(), realAddrOnChain.Bytes()) {
		t.Errorf("expected enode:%v,got %v", empty, realAddrOnChain)
	}
}
