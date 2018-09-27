package deploy

import (
	"log"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/cmd/smartcontract/config"
	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/contracts/dpor"
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
