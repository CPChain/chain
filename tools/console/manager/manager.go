package manager

import (
	"context"
	"crypto/ecdsa"
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/reward"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/rnode"
	cm "bitbucket.org/cpchain/chain/tools/console/common"
	cc "bitbucket.org/cpchain/chain/tools/utility"
	"github.com/ethereum/go-ethereum/common"
)

// Console manage apis
type Console struct {
	rpc    string
	output cm.Output
	ctx    *context.Context
	client *cpclient.Client
	prvKey *ecdsa.PrivateKey
	pubKey *ecdsa.PublicKey
	addr   common.Address
}

var gasPrice *big.Int

var gasLimit uint64

func init() {
	gasPrice = nil
	gasLimit = uint64(200000)
}

// SetGasConfig set gas price and limit
func SetGasConfig(price *big.Int, limit uint64) {
	gasPrice = price
	gasLimit = limit
}

// NewConsole build a console
func NewConsole(ctx *context.Context, rpc string, keystore string, passwordFile string, output cm.Output) (*Console, error) {
	password, err := cc.ReadPasswordByFile(passwordFile)
	if err != nil {
		output.Fatal(err.Error())
		return nil, err
	}
	client, prvkey, pubkey, fromAddress, err := cm.NewCpcClient(rpc, keystore, *password)
	if err != nil {
		output.Fatal(err.Error())
		return nil, err
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
	return &console, nil
}

func (c *Console) isMining() bool {
	client, err := rpc.DialContext(*c.ctx, c.rpc)
	if err != nil {
		c.output.Error(err.Error())
	}
	var result bool
	client.CallContext(*c.ctx, &result, "eth_mining")
	return result
}

func (c *Console) isRNode() bool {
	addr := cm.GetContractAddress(configs.ContractRnode)
	// instance, err := reward.NewReward(addr, c.client)
	instance, err := rnode.NewRnode(addr, c.client)
	if err != nil {
		c.output.Error(err.Error())
	}
	// ISRNode
	isRNode, err := instance.IsRnode(nil, c.addr)
	if err != nil {
		c.output.Error(err.Error())
	}
	return isRNode
}

func (c *Console) isLocked() bool {
	addr := cm.GetContractAddress(configs.ContractReward)
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

// GetStatus get status of cpchain node
func (c *Console) GetStatus() (*cm.Status, error) {
	// Mining
	mining := c.isMining()

	// RNode
	rnode := c.isRNode()

	// Proposer
	head, err := c.client.HeaderByNumber(*c.ctx, nil)
	if err != nil {
		c.output.Error(err.Error())
	}
	paddrs := head.Dpor.Proposers
	var proposer = false
	for _, addr := range paddrs {
		if c.addr == addr {
			proposer = true
		}
		log.Info("proposer", "addr", addr.Hex(), "c.addr", c.addr.Hex())
	}
	blockNumber := big.NewInt(0)
	if proposer {
		block, err := c.client.BlockByNumber(*c.ctx, nil)
		if err != nil {
			c.output.Error(err.Error())
		}
		blockNumber = block.Number()
	}
	locked := c.isLocked()
	supportPrivate, _ := c.client.SupportPrivateTx(context.Background())
	status := cm.Status{
		Mining:           mining,
		RNode:            rnode,
		ENode:            true,
		Proposer:         proposer,
		Locked:           locked,
		NextNumber:       blockNumber,
		SupportPrivateTx: supportPrivate,
	}
	return &status, nil
}

// StartMining start mining
func (c *Console) StartMining() error {
	c.output.Info("Start Mining...")
	client, err := rpc.DialContext(*c.ctx, c.rpc)
	if err != nil {
		return err
	}
	// Start Mining
	err = client.CallContext(*c.ctx, nil, "miner_start", 1)
	if err != nil {
		return err
	}

	c.output.Info("Start Success.")
	return nil
}

// StopMining stop mining
func (c *Console) StopMining() error {
	c.output.Info("Stop Mining...")
	client, err := rpc.DialContext(*c.ctx, c.rpc)
	if err != nil {
		return err
	}
	// Start Mining
	err = client.CallContext(*c.ctx, nil, "miner_stop")
	if err != nil {
		return err
	}
	c.output.Info("Stop Success.")
	return nil
}

// GetBalance get balance of user's account
func (c *Console) GetBalance() (*cm.Balance, error) {
	// balance
	balance, err := c.client.BalanceAt(*c.ctx, c.addr, nil)
	if err != nil {
		return nil, err
	}
	// reward balance
	reward, err := c.GetBalanceOnReward()
	if err != nil {
		return nil, err
	}
	b := cm.Balance{
		Balance: *balance,
		Reward:  *reward,
	}
	return &b, nil
}

// GetBalanceOnReward get balance on reward contract
func (c *Console) GetBalanceOnReward() (*cm.RewardBalance, error) {
	addr := cm.GetContractAddress(configs.ContractReward)
	instance, err := reward.NewReward(addr, c.client)
	if err != nil {
		return nil, err
	}
	// GetLockedBalance
	totalBalance, err := instance.GetTotalBalance(nil, c.addr)
	if err != nil {
		return nil, err
	}

	// GetFreeBalance
	freeBalance, err := instance.GetFreeBalance(nil, c.addr)
	if err != nil {
		return nil, err
	}

	// GetLockedBalance
	lockedBalance, err := instance.GetLockedBalance(nil, c.addr)
	if err != nil {
		return nil, err
	}
	reward := cm.RewardBalance{
		TotalBalance:  totalBalance,
		FreeBalance:   freeBalance,
		LockedBalance: lockedBalance,
	}
	return &reward, nil
}

// Withdraw money from reward contract
func (c *Console) Withdraw(value *big.Int) error {
	c.output.Info("Withdraw...")
	addr := cm.GetContractAddress(configs.ContractReward)
	instance, err := reward.NewReward(addr, c.client)
	if err != nil {
		return err
	}

	// Withdraw
	transactOpts := c.buildTransactOpts(big.NewInt(0))
	c.output.Info("create transaction options successfully")
	_, err = instance.Withdraw(transactOpts, value)
	if err != nil {
		return err
	}
	c.output.Info("withdraw successfully")
	return nil
}

func (c *Console) buildTransactOpts(value *big.Int) *bind.TransactOpts {
	transactOpts := bind.NewKeyedTransactor(c.prvKey)
	transactOpts.Value = value
	transactOpts.GasPrice = gasPrice
	transactOpts.GasLimit = uint64(gasLimit)
	return transactOpts
}

// SubmitDeposit submit deposit
func (c *Console) SubmitDeposit(value *big.Int) error {
	c.output.Info("Submit Deposit...")
	if c.isLocked() {
		c.output.Warn("Sorry, the reward contract is locked now.")
		return nil
	}
	addr := cm.GetContractAddress(configs.ContractReward)
	instance, err := reward.NewReward(addr, c.client)
	if err != nil {
		return err
	}

	// Deposit
	participantInvest := value
	transactOpts := c.buildTransactOpts(participantInvest)
	c.output.Info("create transaction options successfully")
	_, err = instance.SubmitDeposit(transactOpts)
	if err != nil {
		return err
	}
	c.output.Info("submit successfully")
	return nil
}

// WantRenew want renew
func (c *Console) WantRenew() error {
	c.output.Info("Want Renew...")
	if c.isLocked() {
		c.output.Warn("Sorry, the reward contract is locked now.")
		return nil
	}
	addr := cm.GetContractAddress(configs.ContractReward)

	instance, err := reward.NewReward(addr, c.client)
	if err != nil {
		return err
	}

	// Want Renew
	transactOpts := c.buildTransactOpts(big.NewInt(0))
	_, err = instance.WantRenew(transactOpts)
	if err != nil {
		return err
	}
	c.output.Info("Successful")
	return err
}

// QuitRenew quit renew
func (c *Console) QuitRenew() error {
	c.output.Info("Quit Renew...")
	if c.isLocked() {
		c.output.Warn("Sorry, the reward contract is locked now.")
		return nil
	}
	addr := cm.GetContractAddress(configs.ContractReward)

	instance, err := reward.NewReward(addr, c.client)
	if err != nil {
		return err
	}

	// Want Renew
	transactOpts := c.buildTransactOpts(big.NewInt(0))
	_, err = instance.QuitRenew(transactOpts)
	if err != nil {
		return err
	}
	c.output.Info("Successful")
	return err
}
