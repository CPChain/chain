package deploy

import (
	"math/big"

	"bitbucket.org/cpchain/chain/commons/log"
	pdash "bitbucket.org/cpchain/chain/contracts/pdash/pdash_contract"
	"bitbucket.org/cpchain/chain/tools/smartcontract/config"
	"github.com/ethereum/go-ethereum/common"
)

// addr is proxy_register address
func DeployPdashProxy(password string, nonce uint64, addr common.Address) common.Address {
	client, err, privateKey, _, fromAddress := config.Connect(password)
	printBalance(client, fromAddress)
	// Launch contract deploy transaction.
	auth := newTransactor(privateKey, new(big.Int).SetUint64(nonce))
	contractAddress, tx, _, err := pdash.DeployPdashProxy(auth, client, addr)
	if err != nil {
		log.Fatal(err.Error())
	}
	printTx(tx, err, client, contractAddress)
	return contractAddress
}
