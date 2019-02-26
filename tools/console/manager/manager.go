package manager

import (
	"context"
	"crypto/ecdsa"
	"math/big"

	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/api/rpc"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/reward"
	cm "bitbucket.org/cpchain/chain/tools/console/common"
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

// NewConsole build a console
func NewConsole(ctx *context.Context, rpc string, keystore string, passwordFile string, output cm.Output) *Console {
	password, err := cm.ReadPasswordByFile(passwordFile)
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
	addr := cm.GetContractAddress(cm.ContractReward)
	instance, err := reward.NewReward(addr, c.client)
	if err != nil {
		c.output.Error(err.Error())
	}
	// ISRNode
	isRNode, err := instance.IsRNode(nil, c.addr)
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
	}
	blockNumber := big.NewInt(0)
	if proposer {
		block, err := c.client.BlockByNumber(*c.ctx, nil)
		if err != nil {
			c.output.Error(err.Error())
		}
		blockNumber = block.Number()
	}
	status := cm.Status{
		mining,
		rnode,
		true,
		proposer,
		blockNumber,
	}
	return &status, nil
}

// StartMining start mining
func (c *Console) StartMining() error {
	return nil
}

// StopMining stop mining
func (c *Console) StopMining() error {
	return nil
}

// GetBalance get balance of user's account
func (c *Console) GetBalance() (*cm.Balance, error) {
	return nil, nil
}

// GetBalanceOnReward get balance on reward contract
func (c *Console) GetBalanceOnReward() (*cm.RewardBalance, error) {
	return nil, nil
}

// Withdraw money from reward contract
func (c *Console) Withdraw() error {
	return nil
}

// SubmitDeposit submit deposit
func (c *Console) SubmitDeposit() error {
	return nil
}

// WantRenew want renew
func (c *Console) WantRenew() error {
	return nil
}

// QuitRenew quit renew
func (c *Console) QuitRenew() error {
	return nil
}
