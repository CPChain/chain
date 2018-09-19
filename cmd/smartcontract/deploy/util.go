package deploy

import (
	"bytes"
	"context"
	"fmt"
	"log"
	"time"

	"github.com/ethereum/go-ethereum/accounts/abi/bind"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/ethclient"
)

func printTx(tx *types.Transaction, err error, client *ethclient.Client, contractAddress common.Address) context.Context {
	ctx := context.Background()
	fmt.Printf("Transaction: 0x%x\n", tx.Hash())
	startTime := time.Now()
	fmt.Printf("TX start @:%s", time.Now())
	addressAfterMined, err := bind.WaitDeployed(ctx, client, tx)
	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
	}
	fmt.Printf("tx mining take time:%s\n", time.Since(startTime))
	if !bytes.Equal(contractAddress.Bytes(), addressAfterMined.Bytes()) {
		log.Fatalf("mined contractAddress :%s,before mined contractAddress:%s", addressAfterMined, contractAddress)
	}
	return ctx
}

func printBalance(client *ethclient.Client, fromAddress common.Address) {
	// Check balance.
	bal, _ := client.BalanceAt(context.Background(), fromAddress, nil)
	fmt.Println("balance:", bal)
}

func PrintContract(address common.Address) {
	fmt.Println("================================================================")
	fmt.Printf("Contract Address: 0x%x\n", address)
	fmt.Println("================================================================")
}

func FormatPrint(msg string) {
	fmt.Println("\n\n================================================================")
	fmt.Println(msg)
	fmt.Println("================================================================")
}
