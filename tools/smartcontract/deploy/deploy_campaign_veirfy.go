package deploy

import (
	"log"
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/contracts/admission"
	"bitbucket.org/cpchain/chain/tools/smartcontract/config"
	"github.com/ethereum/go-ethereum/common"
)

func DeployCampaignVerify() common.Address {
	client, err, privateKey, _, fromAddress := config.Connect()
	printBalance(client, fromAddress)
	// Launch contract deploy transaction.
	auth := bind.NewKeyedTransactor(privateKey)
	contractAddress, tx, _, err := campaignVerify.DeployAdmission(auth, client, new(big.Int).SetUint64(config.DefaultCPUDifficulty), new(big.Int).SetUint64(config.DefaultMemoryDifficulty))
	if err != nil {
		log.Fatal(err)
	}
	printTx(tx, err, client, contractAddress)
	return contractAddress
}
