package deploy

import (
	"bitbucket.org/cpchain/chain/commons/log"
	rpt "bitbucket.org/cpchain/chain/contracts/dpor/contracts"
	"bitbucket.org/cpchain/chain/tools/smartcontract/config"
	"github.com/ethereum/go-ethereum/common"
)

func DeployRpt() common.Address {
	client, err, privateKey, _, fromAddress := config.Connect()
	printBalance(client, fromAddress)
	// Launch contract deploy transaction.
	auth := newAuth(client, privateKey, fromAddress)
	contractAddress, tx, _, err := rpt.DeployRpt(auth, client)
	if err != nil {
		log.Fatal(err.Error())
	}
	printTx(tx, err, client, contractAddress)
	return contractAddress
}
