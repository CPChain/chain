package deploy

import (
	"log"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/cmd/smartcontract/config"
	"bitbucket.org/cpchain/chain/contracts/dpor/contract"
	"github.com/ethereum/go-ethereum/common"
)

func DeployCampaign() common.Address {
	client, err, privateKey, _, fromAddress := config.Connect()
	printBalance(client, fromAddress)
	// Launch contract deploy transaction.
	auth := bind.NewKeyedTransactor(privateKey)
	contractAddress, tx, _, err := contract.DeployCampaign(auth, client)
	if err != nil {
		log.Fatal(err)
	}
	printTx(tx, err, client, contractAddress)
	return contractAddress
}
