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
	"bitbucket.org/cpchain/chain/contracts/dpor/rnode"
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
	//gasPrice = big.NewInt(1000000)
	gasPrice =nil
	gasLimit = uint64(2000000)
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

	status := cm.Status{
		Mining:           mining,
		RNode:            rnode,
		Proposer:         proposer,
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


func (c *Console) JoinRnode() error {
	c.output.Info("Join Rnode...")
	addr := cm.GetContractAddress(configs.ContractRnode)
	instance, err := rnode.NewRnode(addr, c.client)
	if err != nil {
		return err
	}
	// Withdraw
	transactOpts := c.buildTransactOpts(big.NewInt(210000))
	c.output.Info("create transaction options successfully")
	tx, err:= instance.QuitRnode(transactOpts)
	if err != nil {
		return err
	}
	_, err = bind.WaitMined(context.Background(), c.client, tx)
	if err != nil {
		c.output.Error("wait mined failed,to startnewround is failed.", "err", err)
		log.Error(err.Error())
	}
	c.output.Info("join successfully")
	return nil
}


func (c *Console) QuitRnode() error {
	c.output.Info("Quit Rnode...")
	addr := cm.GetContractAddress(configs.ContractRnode)
	instance, err := rnode.NewRnode(addr, c.client)
	if err != nil {
		return err
	}
	// Quit...
	transactOpts := c.buildTransactOpts(big.NewInt(0))
	c.output.Info("create transaction options successfully")
	tx, err:= instance.QuitRnode(transactOpts)
	if err != nil {
		return err
	}
	_, err = bind.WaitMined(context.Background(), c.client, tx)
	if err != nil {
		c.output.Error("wait mined failed,to startnewround is failed.", "err", err)
		log.Error(err.Error())
	}
	c.output.Info("quit successfully")
	return nil

}



func (c *Console) buildTransactOpts(value *big.Int) *bind.TransactOpts {
	transactOpts := bind.NewKeyedTransactor(c.prvKey)
	transactOpts.Value = value
	transactOpts.GasPrice = gasPrice
	transactOpts.GasLimit = uint64(gasLimit)
	return transactOpts
}
