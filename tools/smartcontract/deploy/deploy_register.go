package deploy

import (
	"bitbucket.org/cpchain/chain/commons/log"
	register "bitbucket.org/cpchain/chain/contracts/pdash/sol"
	"bitbucket.org/cpchain/chain/tools/smartcontract/config"
	"github.com/ethereum/go-ethereum/common"
)

func DeployRegister(password string) common.Address {
	client, err, privateKey, _, fromAddress := config.Connect(password)
	printBalance(client, fromAddress)
	// Launch contract deploy transaction.
	auth := newAuth(client, privateKey, fromAddress)
	contractAddress, tx, _, err := register.DeployRegister(auth, client)
	if err != nil {
		log.Fatal(err.Error())
	}
	printTx(tx, err, client, contractAddress)
	return contractAddress
}
