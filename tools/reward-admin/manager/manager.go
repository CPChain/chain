package manager

import (
	"context"
	"crypto/ecdsa"
	"math/big"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/reward"
	cm "bitbucket.org/cpchain/chain/tools/console/common"
	rm "bitbucket.org/cpchain/chain/tools/reward-admin/common"
	cc "bitbucket.org/cpchain/chain/tools/utility"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/urfave/cli"
)

// Console manage apis
type Console struct {
	rpc    string
	output rm.Output
	ctx    *context.Context
	client *cpclient.Client
	prvKey *ecdsa.PrivateKey
	pubKey *ecdsa.PublicKey
	addr   common.Address
}

var gasPrice *big.Int

var gasLimit int64

func init() {
	gasPrice = big.NewInt(0)
	gasLimit = int64(200000)
}

// NewConsole build a console
func NewConsole(ctx *context.Context, rpc string, keystore string, passwordFile string, output rm.Output) *Console {
	password, err := cc.ReadPasswordByFile(passwordFile)
	if err != nil {
		output.Fatal(err.Error())
	}
	client, prvkey, pubkey, fromAddress, err := cm.NewCpcClient(rpc, keystore, *password)
	if err != nil {
		output.Fatal(err.Error())
	}
	console := Console{
		rpc,
		output,
		ctx,
		client,
		prvkey,
		pubkey,
		fromAddress,
	}
	return &console
}

func (c *Console) IsLocked() bool {
	addr := getContractAddress(configs.ContractReward)
	instance, err := reward.NewReward(addr, c.client)
	if err != nil {
		c.output.Error(err.Error())
	}
	locked, err := instance.IsLocked(nil)
	if err != nil {
		c.output.Error(err.Error())
	}
	return locked
}

func (c *Console) TotalInvestorsAmount() *big.Int {
	addr := getContractAddress(configs.ContractReward)
	instance, err := reward.NewReward(addr, c.client)
	if err != nil {
		c.output.Error(err.Error())
	}
	balanceAmount, _ := instance.TotalInvestAmount(nil)
	return balanceAmount

}

// GetBalanceOnReward get balance on reward contract
func (c *Console) GetInvestorList(ctx *cli.Context) ([]rm.InvestorInfo, error) {
	addr := getContractAddress(configs.ContractReward)
	instance, err := reward.NewReward(addr, c.client)
	if err != nil {
		return nil, err
	}
	investors, _ := instance.GetInvestors(nil)
	slice := make([]rm.InvestorInfo, len(investors))
	for i, v := range investors {
		freeB, _ := instance.GetFreeBalance(nil, v)
		lockedB, _ := instance.GetLockedBalance(nil, v)
		toRenewB, _ := instance.IsToRenew(nil, v)
		investorItem := rm.InvestorInfo{
			FreeBalance:   freeB,
			LockedBalance: lockedB,
			IsToRenew:     toRenewB,
			Account:       v,
		}
		slice[i] = investorItem
	}
	return slice, nil
}

// Get balance from reward contract
func (c *Console) ContractAccountBalance() *big.Int {
	addr := getContractAddress(configs.ContractReward)
	balance, _ := c.client.BalanceAt(context.Background(), addr, nil)
	return balance
}

func (c *Console) buildTransactOpts(value *big.Int) *bind.TransactOpts {
	transactOpts := bind.NewKeyedTransactor(c.prvKey)
	transactOpts.Value = value
	transactOpts.GasPrice = gasPrice
	transactOpts.GasLimit = uint64(gasLimit)
	return transactOpts
}

// Want StartNewRound
func (c *Console) StartNewRound() error {
	c.output.Info("Want Startnewround...")
	if c.IsLocked() {
		c.output.Warn("Sorry, the reward contract is locked now.")
		return nil
	}
	addr := getContractAddress(configs.ContractReward)

	instance, err := reward.NewReward(addr, c.client)
	if err != nil {
		return err
	}
	// Want Startnewround
	transactOpts := c.buildTransactOpts(big.NewInt(0))
	tx, err := instance.StartNewRound(transactOpts)
	if err != nil {
		return err
	}
	var count = 0
	for i := 0; i < 20; i++ {
		time.Sleep(500 * time.Millisecond)
		r, err := c.client.TransactionReceipt(context.Background(), tx.Hash())
		if err == nil {
			c.checkNewRoundLockStatus(r, instance)
			break
		}
		count++
	}
	if count == 20 {
		c.output.Info("The transation is not Successful.")
	}
	return err
}

func (c *Console) checkNewRoundLockStatus(r *types.Receipt, instance *reward.Reward) {
	if r.Status == 1 {
		locked, err := instance.IsLocked(nil)
		if err != nil {
			c.output.Error(err.Error())
		}
		if locked == true {
			c.output.Info("Successful")
		} else {
			c.output.Info("The state of this node is incorrect.")
		}
	} else {
		c.output.Info("The transation is not Successful.")
	}
}

/// Want StartNewRaise
func (c *Console) StartNewRaise() error {
	c.output.Info("Want Startnewraise...")
	if c.IsLocked() {
		c.output.Warn("Sorry, the reward contract is locked now.")
		return nil
	}
	addr := getContractAddress(configs.ContractReward)

	instance, err := reward.NewReward(addr, c.client)
	if err != nil {
		return err
	}
	// Want Startnewraise
	transactOpts := c.buildTransactOpts(big.NewInt(0))

	tx, err := instance.NewRaise(transactOpts)
	if err != nil {
		return err
	}

	var count = 0
	for i := 0; i < 20; i++ {
		time.Sleep(500 * time.Millisecond)
		r, err := c.client.TransactionReceipt(context.Background(), tx.Hash())
		if err == nil {
			c.checkNewRaiseLockStatus(r, instance)
			break
		}
		count++
	}
	if count == 20 {
		c.output.Info("The transation is not Successful.")
	}

	return err
}

func (c *Console) checkNewRaiseLockStatus(r *types.Receipt, instance *reward.Reward) {
	if r.Status == 1 {
		locked, err := instance.IsLocked(nil)
		if err != nil {
			c.output.Error(err.Error())
		}
		if locked == false {
			c.output.Info("Successful")
		} else {
			c.output.Info("The state of this node is incorrect.")
		}
	} else {
		c.output.Info("The transation is not Successful.")
	}
}

// getContractAddress get contract address by name
func getContractAddress(name string) common.Address {
	return configs.MainnetContractAddressMap[name]
}
