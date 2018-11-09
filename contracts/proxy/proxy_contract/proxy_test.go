package contract

import (
	"context"
	"crypto/ecdsa"
	"fmt"
	"math/big"
	"os"
	"path/filepath"

	"testing"

	"time"

	"bytes"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/campaign"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

func TestSignerRegisterProxyContractRegister(t *testing.T) {
	t.Skip("we shall use a simulated backend.")

	fmt.Println("*******************************************************")
	// 1. deploy proxy contract
	client, privateKey, _, gasLimit, gasPrice, _, ctx, proxyAddress := deploySignerRegisterProxyContract()
	fmt.Println("proxyAddress:", proxyAddress.Hex())

	// 3. register proxy -> real contract
	// load existing proxyContract register proxy mapping
	fmt.Println("2.RegisterProxyContract")
	proxyContratAddress := common.HexToAddress("0x7900dd1d71fc5c57ba56e4b768de3c2264253335")
	proxyContractRegister, _ := NewProxyContractRegister(proxyContratAddress, client)

	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(500)
	auth.GasLimit = uint64(gasLimit)
	gasPrice, err := client.SuggestGasPrice(context.Background())
	fmt.Println("gasPrice:", gasPrice)
	auth.GasPrice = gasPrice

	proxyAddr := proxyAddress // common.HexToAddress("0x1a9fae75908752d0abf4dca45ebcac311c376290")
	realAddr := common.HexToAddress("0x482fdcd02cd9bc79ccb69644cbdec46ff365f50b")
	tx, err := proxyContractRegister.RegisterProxyContract(auth, proxyAddr, realAddr)
	if err != nil {
		log.Fatal(err.Error())
	}
	fmt.Println("TX:", tx.Hash().Hex())
	startTime := time.Now()
	receipt, err := bind.WaitMined(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	fmt.Println("receipt.Status:", receipt.Status)

	realContractAddress, err := proxyContractRegister.GetRealContract(nil, proxyAddr)
	fmt.Println("realContractAddress:", realContractAddress.Hex())

	// 4. invoke real contract
	auth = bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(0)       // in wei
	auth.GasLimit = uint64(gasLimit) // in units
	auth.GasPrice = gasPrice

	campaignIns, err := contract.NewCampaign(realAddr, client)
	newMaxNoc, err := campaignIns.MaximumNoc(nil)
	fmt.Println("newMaxNoc:", newMaxNoc)

	// 5. replace real contract address with proxy contract
	proxyCampaignIns, err := contract.NewCampaign(proxyAddress, client)
	proxyNewMaxNoc, err := proxyCampaignIns.MaximumNoc(nil)
	fmt.Println("proxy newMaxNoc:", proxyNewMaxNoc)

	if newMaxNoc.Cmp(proxyNewMaxNoc) != 0 {
		t.Errorf("MaxNoc in proxyCampaignIns not match realCampaignIns")
	}
}

func deploySignerRegisterProxyContract() (*cpclient.Client, *ecdsa.PrivateKey, common.Address, int, *big.Int, *Proxy, context.Context, common.Address) {
	client, err := cpclient.Dial("http://localhost:8501")
	// local
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
	fmt.Println("from address:", fromAddress.Hex())
	bal, err := client.BalanceAt(context.Background(), fromAddress, nil)
	fmt.Println("bal:", bal)
	gasLimit := 3000000
	gasPrice, err := client.SuggestGasPrice(context.Background())
	fmt.Println("gasPrice:", gasPrice)
	if err != nil {
		log.Fatal(err.Error())
	}
	auth := bind.NewKeyedTransactor(privateKey)
	auth.Value = big.NewInt(0)
	auth.GasLimit = uint64(gasLimit)
	auth.GasPrice = gasPrice
	address, tx, instance, err := DeployProxy(auth, client)
	if err != nil {
		log.Fatal(err.Error())
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
