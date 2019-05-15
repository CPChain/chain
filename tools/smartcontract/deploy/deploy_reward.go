package deploy

import (
	"math/big"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/reward"
	"bitbucket.org/cpchain/chain/tools/smartcontract/config"
	"github.com/ethereum/go-ethereum/common"
)

func DeployReward(password string, nonce uint64) common.Address {
	client, err, privateKey, _, fromAddress := config.Connect(password)
	printBalance(client, fromAddress)
	// Launch contract deploy transaction.
	auth := newTransactor(privateKey, new(big.Int).SetUint64(nonce))
	contractAddress, tx, _, err := reward.DeployReward(auth, client)
	if err != nil {
		log.Fatal(err.Error())
	}
	printTx(tx, err, client, contractAddress)
	return contractAddress
}

func StartNewRaise(rewardAddr common.Address, password string, nonce uint64) {
	client, _, privateKey, _, _ := config.Connect(password)
	reward, _ := reward.NewReward(rewardAddr, client)
	auth := newTransactor(privateKey, new(big.Int).SetUint64(nonce))
	tx, _ := reward.NewRaise(auth)
	log.Info("started new raise", "txhash", tx.Hash().Hex())

}
