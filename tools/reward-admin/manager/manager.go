package manager

import (
	"context"
	"crypto/ecdsa"
	"math/big"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/reward"
	cm "bitbucket.org/cpchain/chain/tools/console/common"
	rm "bitbucket.org/cpchain/chain/tools/reward-admin/common"
	cc "bitbucket.org/cpchain/chain/tools/utility"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
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
	transactOpts.GasPrice = big.NewInt(3000000)
	transactOpts.GasLimit = uint64(5000000)
	return transactOpts
}

func (c *Console) SetPeriod() error {
	addr := getContractAddress(configs.ContractReward)
	instance, err := reward.NewReward(addr, c.client)
	if err != nil {
		return err
	}
	transactOpts := c.buildTransactOpts(big.NewInt(0))
	instance.SetPeriod(transactOpts, big.NewInt(0))
	time.Sleep(20 * time.Second)
	return err
}

// Want StartNewRound
func (c *Console) StartNewRound() error {
	c.output.Info("Want Startnewround...")
	if c.IsLocked() {
		mark:="Sorry, the reward contract is locked now, to startnewround is failed."
		log.Info(mark)
		c.output.Warn(mark)
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

	if err != nil {
		return err
	}

	r, err := bind.WaitMined(context.Background(), c.client, tx)
	if err != nil {
		errmark:="wait mined failed,to startnewround is failed."
		log.Info(errmark, "err", err)
		c.output.Error(errmark, "err", err)
		return err
	}
	c.checkNewRoundLockStatus(r, instance)
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
			mark := "The state of this node should be locked,but it is incorrect,to startnewround is failed."
			c.output.Info(mark)
			log.Info(mark)
		}
	} else {
		mark:="The StatusReceipt of this transation is not Successful,to startnewround is failed."
		c.output.Info(mark)
		log.Info(mark)
	}
}

/// Want StartNewRaise
func (c *Console) StartNewRaise() error {
	c.output.Info("Want Startnewraise...")
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

	r, err := bind.WaitMined(context.Background(), c.client, tx)
	if err != nil {
		mark:="wait mined failed,to startnewraise is failed."
		log.Info(mark, "err", err)
		c.output.Error(mark, "err", err)
		return err
	}
	c.checkNewRaiseLockStatus(r, instance)

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
			mark:="The state of this node should be unlocked,but it is incorrect,to startnewraise is failed."
			c.output.Info(mark)
			log.Info(mark)
		}
	} else {
		mark:="The StatusReceipt of this transation is not Successful,to startnewraise is failed."
		c.output.Info(mark)
		log.Info(mark)
	}
}

// getContractAddress get contract address by name
func getContractAddress(name string) common.Address {
	return configs.MainnetContractAddressMap[name]
}
