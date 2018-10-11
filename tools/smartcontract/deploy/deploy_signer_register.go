package deploy

import (
	"log"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/contracts/dpor"
	"bitbucket.org/cpchain/chain/tools/smartcontract/config"
	"github.com/ethereum/go-ethereum/common"
)

func DeploySignerConnectionRegister() common.Address {
	client, err, privateKey, _, fromAddress := config.Connect()
	printBalance(client, fromAddress)
	// launch contract deploy transaction.
	auth := bind.NewKeyedTransactor(privateKey)
	contractAddress, tx, _, err := dpor.DeploySignerConnectionRegister(auth, client)
	if err != nil {
		log.Fatal(err)
	}
	printTx(tx, err, client, contractAddress)
	return contractAddress
}
