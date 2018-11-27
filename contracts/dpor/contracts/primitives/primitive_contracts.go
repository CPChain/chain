// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package primitives

import (
	"strings"

	"bitbucket.org/cpchain/chain/accounts/abi"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// PrimitiveContractsInterfaceABI is the input ABI used to generate the binding from.
const PrimitiveContractsInterfaceABI = "[]"

// PrimitiveContractsInterfaceBin is the compiled bytecode used for deploying new contracts.
const PrimitiveContractsInterfaceBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a72305820c10985a8ec8cbb1362c9a1db0859203a02b216e46d6d4775c1f26baa4c969c090029`

// DeployPrimitiveContractsInterface deploys a new cpchain contract, binding an instance of PrimitiveContractsInterface to it.
func DeployPrimitiveContractsInterface(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *PrimitiveContractsInterface, error) {
	parsed, err := abi.JSON(strings.NewReader(PrimitiveContractsInterfaceABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(PrimitiveContractsInterfaceBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &PrimitiveContractsInterface{PrimitiveContractsInterfaceCaller: PrimitiveContractsInterfaceCaller{contract: contract}, PrimitiveContractsInterfaceTransactor: PrimitiveContractsInterfaceTransactor{contract: contract}, PrimitiveContractsInterfaceFilterer: PrimitiveContractsInterfaceFilterer{contract: contract}}, nil
}

// PrimitiveContractsInterface is an auto generated Go binding around an cpchain contract.
type PrimitiveContractsInterface struct {
	PrimitiveContractsInterfaceCaller     // Read-only binding to the contract
	PrimitiveContractsInterfaceTransactor // Write-only binding to the contract
	PrimitiveContractsInterfaceFilterer   // Log filterer for contract events
}

// PrimitiveContractsInterfaceCaller is an auto generated read-only Go binding around an cpchain contract.
type PrimitiveContractsInterfaceCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// PrimitiveContractsInterfaceTransactor is an auto generated write-only Go binding around an cpchain contract.
type PrimitiveContractsInterfaceTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// PrimitiveContractsInterfaceFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type PrimitiveContractsInterfaceFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// PrimitiveContractsInterfaceSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type PrimitiveContractsInterfaceSession struct {
	Contract     *PrimitiveContractsInterface // Generic contract binding to set the session for
	CallOpts     bind.CallOpts                // Call options to use throughout this session
	TransactOpts bind.TransactOpts            // Transaction auth options to use throughout this session
}

// PrimitiveContractsInterfaceCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type PrimitiveContractsInterfaceCallerSession struct {
	Contract *PrimitiveContractsInterfaceCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts                      // Call options to use throughout this session
}

// PrimitiveContractsInterfaceTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type PrimitiveContractsInterfaceTransactorSession struct {
	Contract     *PrimitiveContractsInterfaceTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts                      // Transaction auth options to use throughout this session
}

// PrimitiveContractsInterfaceRaw is an auto generated low-level Go binding around an cpchain contract.
type PrimitiveContractsInterfaceRaw struct {
	Contract *PrimitiveContractsInterface // Generic contract binding to access the raw methods on
}

// PrimitiveContractsInterfaceCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type PrimitiveContractsInterfaceCallerRaw struct {
	Contract *PrimitiveContractsInterfaceCaller // Generic read-only contract binding to access the raw methods on
}

// PrimitiveContractsInterfaceTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type PrimitiveContractsInterfaceTransactorRaw struct {
	Contract *PrimitiveContractsInterfaceTransactor // Generic write-only contract binding to access the raw methods on
}

// NewPrimitiveContractsInterface creates a new instance of PrimitiveContractsInterface, bound to a specific deployed contract.
func NewPrimitiveContractsInterface(address common.Address, backend bind.ContractBackend) (*PrimitiveContractsInterface, error) {
	contract, err := bindPrimitiveContractsInterface(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &PrimitiveContractsInterface{PrimitiveContractsInterfaceCaller: PrimitiveContractsInterfaceCaller{contract: contract}, PrimitiveContractsInterfaceTransactor: PrimitiveContractsInterfaceTransactor{contract: contract}, PrimitiveContractsInterfaceFilterer: PrimitiveContractsInterfaceFilterer{contract: contract}}, nil
}

// NewPrimitiveContractsInterfaceCaller creates a new read-only instance of PrimitiveContractsInterface, bound to a specific deployed contract.
func NewPrimitiveContractsInterfaceCaller(address common.Address, caller bind.ContractCaller) (*PrimitiveContractsInterfaceCaller, error) {
	contract, err := bindPrimitiveContractsInterface(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &PrimitiveContractsInterfaceCaller{contract: contract}, nil
}

// NewPrimitiveContractsInterfaceTransactor creates a new write-only instance of PrimitiveContractsInterface, bound to a specific deployed contract.
func NewPrimitiveContractsInterfaceTransactor(address common.Address, transactor bind.ContractTransactor) (*PrimitiveContractsInterfaceTransactor, error) {
	contract, err := bindPrimitiveContractsInterface(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &PrimitiveContractsInterfaceTransactor{contract: contract}, nil
}

// NewPrimitiveContractsInterfaceFilterer creates a new log filterer instance of PrimitiveContractsInterface, bound to a specific deployed contract.
func NewPrimitiveContractsInterfaceFilterer(address common.Address, filterer bind.ContractFilterer) (*PrimitiveContractsInterfaceFilterer, error) {
	contract, err := bindPrimitiveContractsInterface(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &PrimitiveContractsInterfaceFilterer{contract: contract}, nil
}

// bindPrimitiveContractsInterface binds a generic wrapper to an already deployed contract.
func bindPrimitiveContractsInterface(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(PrimitiveContractsInterfaceABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_PrimitiveContractsInterface *PrimitiveContractsInterfaceRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _PrimitiveContractsInterface.Contract.PrimitiveContractsInterfaceCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_PrimitiveContractsInterface *PrimitiveContractsInterfaceRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _PrimitiveContractsInterface.Contract.PrimitiveContractsInterfaceTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_PrimitiveContractsInterface *PrimitiveContractsInterfaceRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _PrimitiveContractsInterface.Contract.PrimitiveContractsInterfaceTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_PrimitiveContractsInterface *PrimitiveContractsInterfaceCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _PrimitiveContractsInterface.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_PrimitiveContractsInterface *PrimitiveContractsInterfaceTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _PrimitiveContractsInterface.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_PrimitiveContractsInterface *PrimitiveContractsInterfaceTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _PrimitiveContractsInterface.Contract.contract.Transact(opts, method, params...)
}
