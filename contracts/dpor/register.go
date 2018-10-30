package dpor

import (
	"context"
	"fmt"
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts/register"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

type RegisterBackend interface {
	bind.ContractBackend
	TransactionReceipt(ctx context.Context, txHash common.Hash) (*types.Receipt, error)
	BalanceAt(ctx context.Context, address common.Address, blockNum *big.Int) (*big.Int, error)
}

type Register struct {
	*register.RegisterSession
	contractBackend bind.ContractBackend
}

func NewRegister(transactOpts *bind.TransactOpts, contractAddr common.Address, contractBackend Backend) (*Register, error) {
	c, err := register.NewRegister(contractAddr, contractBackend)
	if err != nil {
		return nil, err
	}

	return &Register{
		&register.RegisterSession{
			Contract:     c,
			TransactOpts: *transactOpts,
		},
		contractBackend,
	}, nil
}

func DeployRegister(transactOpts *bind.TransactOpts, contractBackend RegisterBackend) (common.Address, *Register, error) {
	contractAddr, _, _, err := register.DeployRegister(transactOpts, contractBackend)
	if err != nil {
		return contractAddr, nil, err
	}
	register, err := NewRegister(transactOpts, contractAddr, contractBackend)
	if err != nil {
		return contractAddr, nil, err
	}

	return contractAddr, register, err

}

func (self *Register) ClaimRegister(transactOpts *bind.TransactOpts, fileName string, fileHash [32]byte, fileSize *big.Int) (*types.Transaction, error) {
	fmt.Println("ClainRegister is called:")
	return self.Contract.ClaimRegister(transactOpts, fileName, fileHash, fileSize)
}

func (self *Register) GetUploadCount(CallOpts *bind.CallOpts, address common.Address) (*big.Int, error) {
	fmt.Println("GetUploadCount is call:")
	return self.Contract.GetUploadCount(CallOpts, address)
}
