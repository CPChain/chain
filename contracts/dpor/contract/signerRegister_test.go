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
	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/crypto"
	"bitbucket.org/cpchain/chain/crypto/rsa_"
	"bitbucket.org/cpchain/chain/ethclient"
)

func TestSignerRegister(t *testing.T) {
	t.Skip("we shall use a simulated backend.")

	client, privateKey, fromAddress, gasLimit, gasPrice, instance, ctx := deployContract()

	fmt.Println("*******************************************************")
	registerSignerAndGet(t, privateKey, gasLimit, gasPrice, instance, ctx, client, fromAddress)
	fmt.Println("*******************************************************")
}

func deployContract() (*ethclient.Client, *ecdsa.PrivateKey, common.Address, int, *big.Int, *SignerConnectionRegister, context.Context) {
	// create client.
	// client, err := ethclient.Dial("https://rinkeby.infura.io")
	client, err := ethclient.Dial("http://localhost:8501")
	// local
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
	fmt.Println("from address:", fromAddress.Hex())
	// 0x96216849c49358B10257cb55b28eA603c874b05E
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
	auth.Value = big.NewInt(0)
	// in wei
	auth.GasLimit = uint64(gasLimit)
	// in units
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
	return client, privateKey, fromAddress, gasLimit, gasPrice, instance, ctx
}

func registerSignerAndGet(t *testing.T, privateKey *ecdsa.PrivateKey, gasLimit int, gasPrice *big.Int, instance *SignerConnectionRegister, ctx context.Context, client *ethclient.Client, fromAddress common.Address) {
	// 1. load RsaPublicKey/PrivateKey
	fmt.Println("1.load RsaPublicKey/PrivateKey")
	//publicKey1, privateKey1, pubBytes1, priBytes1, _ := rsa_.LoadRsaKey("./testdata/rsa_pub.pem", "./testdata/rsa_pri.pem")
	publicKey2, privateKey2, pubBytes2, _, _ := rsa_.LoadRsaKey("../testdata/rsa_pub1.pem", "../testdata/rsa_pri1.pem")
	_ = publicKey2

	// 2. register node2 public key on chain (claim campaign)
	fmt.Println("2.register node2 public key on chain")
	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(500)
	// in wei
	auth.GasLimit = uint64(gasLimit)
	// in units
	auth.GasPrice = gasPrice
	transaction, err := instance.RegisterPublicKey(auth, pubBytes2)
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
	fmt.Println("3.node1 get public key with other's(node2) address")
	publicKeyBytes, err := instance.GetPublicKey(nil, fromAddress)

	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("publicKeyBytes of", fromAddress.Hex(), ":", publicKeyBytes)

	// 4. node1 encrypt enode with node2's public key
	fmt.Println("4.node1 encrypt enode with node2's public key")

	enodeBytes := []byte("enode://abc:127.0.0.1:444")
	publicKeyFromChain, _ := rsa_.Bytes2PublicKey(publicKeyBytes)
	//if publicKey2 != publicKeyFromChain {
	//	t.Errorf("publicKey2 != publicKeyFromChain")
	//}
	encryptedEnodeBytes, err := rsa_.RsaEncrypt(enodeBytes, publicKeyFromChain)
	fmt.Println("hex(encryptedEnodeBytes):", common.Bytes2Hex(encryptedEnodeBytes))

	// 5. node1 add encrypted enode(node2) on chain
	fmt.Println("5.node1 add encrypted enode(node2) on chain")

	auth = bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(500)
	// in wei
	auth.GasLimit = uint64(gasLimit)
	// in units
	auth.GasPrice = gasPrice
	transaction, err = instance.AddNodeInfo(auth, big.NewInt(1), fromAddress, encryptedEnodeBytes)

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

	// 6. node2 get enode from chain
	fmt.Println("6.node2 get enode from chain")
	rsaPublicKey, err := instance.GetNodeInfo(nil, big.NewInt(1), fromAddress)
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("rsaPublicKey of", fromAddress.Hex(), ":", common.Bytes2Hex(rsaPublicKey))

	// 7. decrypt with node2 private key
	fmt.Println("7.decrypt with node2 private key")
	enode, err := rsa_.RsaDecrypt(rsaPublicKey, privateKey2)
	fmt.Println("enode:", string(enode))

	if !bytes.Equal(enodeBytes, enode) {
		t.Errorf("expected enode:%v,got %v", enodeBytes, enode)
	}
}
