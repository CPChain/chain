// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package primitives_test

import (
	"math/big"
	"strings"

	"bitbucket.org/cpchain/chain/accounts/abi"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// PrimitiveContractsInterfaceABI is the input ABI used to generate the binding from.
const PrimitiveContractsInterfaceABI = "[]"

// PrimitiveContractsInterfaceBin is the compiled bytecode used for deploying new contracts.
const PrimitiveContractsInterfaceBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a72305820c8ba6eda6f13a305e166080c4f075a76ed90de6888258732356962ae9b6df0090029`

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

// PrimitiveContractsTestABI is the input ABI used to generate the binding from.
const PrimitiveContractsTestABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"},{\"name\":\"blockNum\",\"type\":\"uint256\"}],\"name\":\"getMaintenance\",\"outputs\":[{\"name\":\"b\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"},{\"name\":\"blockNum\",\"type\":\"uint256\"}],\"name\":\"getTxVolume\",\"outputs\":[{\"name\":\"b\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"},{\"name\":\"blockNum\",\"type\":\"uint256\"}],\"name\":\"getProxyCount\",\"outputs\":[{\"name\":\"b\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"},{\"name\":\"blockNum\",\"type\":\"uint256\"}],\"name\":\"getUploadInfo\",\"outputs\":[{\"name\":\"b\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"},{\"name\":\"blockNum\",\"type\":\"uint256\"}],\"name\":\"getRank\",\"outputs\":[{\"name\":\"b\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"},{\"name\":\"blockNum\",\"type\":\"uint256\"}],\"name\":\"isProxy\",\"outputs\":[{\"name\":\"b\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"}]"

// PrimitiveContractsTestBin is the compiled bytecode used for deploying new contracts.
const PrimitiveContractsTestBin = `0x608060405234801561001057600080fd5b50610321806100206000396000f3006080604052600436106100775763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166337cdbe7f811461007c578063435f8a27146100b257806398c9c279146100d6578063b68d0d43146100fa578063f79359691461011e578063fae4a1e114610142575b600080fd5b34801561008857600080fd5b506100a0600160a060020a0360043516602435610166565b60408051918252519081900360200190f35b3480156100be57600080fd5b506100a0600160a060020a0360043516602435610188565b3480156100e257600080fd5b506100a0600160a060020a03600435166024356101a3565b34801561010657600080fd5b506100a0600160a060020a03600435166024356101be565b34801561012a57600080fd5b506100a0600160a060020a03600435166024356101d9565b34801561014e57600080fd5b506100a0600160a060020a03600435166024356101f4565b6000610181600160a060020a0384168363ffffffff61020f16565b9392505050565b6000610181600160a060020a0384168363ffffffff61023c16565b6000610181600160a060020a0384168363ffffffff61026116565b6000610181600160a060020a0384168363ffffffff61028616565b6000610181600160a060020a0384168363ffffffff6102ab16565b6000610181600160a060020a0384168363ffffffff6102d016565b60006040518381528260208201526020816040836065600019fa151561023457600080fd5b519392505050565b60006040518381528260208201526020816040836068600019fa151561023457600080fd5b60006040518381528260208201526020816040836066600019fa151561023457600080fd5b60006040518381528260208201526020816040836067600019fa151561023457600080fd5b60006040518381528260208201526020816040836064600019fa151561023457600080fd5b60006040518381528260208201526020816040836069600019fa151561023457600080fd00a165627a7a7230582098c522e835b0669774d7f7b7db740998311af31c8574790f9cb484b045071f2b0029`

// DeployPrimitiveContractsTest deploys a new cpchain contract, binding an instance of PrimitiveContractsTest to it.
func DeployPrimitiveContractsTest(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *PrimitiveContractsTest, error) {
	parsed, err := abi.JSON(strings.NewReader(PrimitiveContractsTestABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(PrimitiveContractsTestBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &PrimitiveContractsTest{PrimitiveContractsTestCaller: PrimitiveContractsTestCaller{contract: contract}, PrimitiveContractsTestTransactor: PrimitiveContractsTestTransactor{contract: contract}, PrimitiveContractsTestFilterer: PrimitiveContractsTestFilterer{contract: contract}}, nil
}

// PrimitiveContractsTest is an auto generated Go binding around an cpchain contract.
type PrimitiveContractsTest struct {
	PrimitiveContractsTestCaller     // Read-only binding to the contract
	PrimitiveContractsTestTransactor // Write-only binding to the contract
	PrimitiveContractsTestFilterer   // Log filterer for contract events
}

// PrimitiveContractsTestCaller is an auto generated read-only Go binding around an cpchain contract.
type PrimitiveContractsTestCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// PrimitiveContractsTestTransactor is an auto generated write-only Go binding around an cpchain contract.
type PrimitiveContractsTestTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// PrimitiveContractsTestFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type PrimitiveContractsTestFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// PrimitiveContractsTestSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type PrimitiveContractsTestSession struct {
	Contract     *PrimitiveContractsTest // Generic contract binding to set the session for
	CallOpts     bind.CallOpts           // Call options to use throughout this session
	TransactOpts bind.TransactOpts       // Transaction auth options to use throughout this session
}

// PrimitiveContractsTestCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type PrimitiveContractsTestCallerSession struct {
	Contract *PrimitiveContractsTestCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts                 // Call options to use throughout this session
}

// PrimitiveContractsTestTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type PrimitiveContractsTestTransactorSession struct {
	Contract     *PrimitiveContractsTestTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts                 // Transaction auth options to use throughout this session
}

// PrimitiveContractsTestRaw is an auto generated low-level Go binding around an cpchain contract.
type PrimitiveContractsTestRaw struct {
	Contract *PrimitiveContractsTest // Generic contract binding to access the raw methods on
}

// PrimitiveContractsTestCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type PrimitiveContractsTestCallerRaw struct {
	Contract *PrimitiveContractsTestCaller // Generic read-only contract binding to access the raw methods on
}

// PrimitiveContractsTestTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type PrimitiveContractsTestTransactorRaw struct {
	Contract *PrimitiveContractsTestTransactor // Generic write-only contract binding to access the raw methods on
}

// NewPrimitiveContractsTest creates a new instance of PrimitiveContractsTest, bound to a specific deployed contract.
func NewPrimitiveContractsTest(address common.Address, backend bind.ContractBackend) (*PrimitiveContractsTest, error) {
	contract, err := bindPrimitiveContractsTest(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &PrimitiveContractsTest{PrimitiveContractsTestCaller: PrimitiveContractsTestCaller{contract: contract}, PrimitiveContractsTestTransactor: PrimitiveContractsTestTransactor{contract: contract}, PrimitiveContractsTestFilterer: PrimitiveContractsTestFilterer{contract: contract}}, nil
}

// NewPrimitiveContractsTestCaller creates a new read-only instance of PrimitiveContractsTest, bound to a specific deployed contract.
func NewPrimitiveContractsTestCaller(address common.Address, caller bind.ContractCaller) (*PrimitiveContractsTestCaller, error) {
	contract, err := bindPrimitiveContractsTest(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &PrimitiveContractsTestCaller{contract: contract}, nil
}

// NewPrimitiveContractsTestTransactor creates a new write-only instance of PrimitiveContractsTest, bound to a specific deployed contract.
func NewPrimitiveContractsTestTransactor(address common.Address, transactor bind.ContractTransactor) (*PrimitiveContractsTestTransactor, error) {
	contract, err := bindPrimitiveContractsTest(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &PrimitiveContractsTestTransactor{contract: contract}, nil
}

// NewPrimitiveContractsTestFilterer creates a new log filterer instance of PrimitiveContractsTest, bound to a specific deployed contract.
func NewPrimitiveContractsTestFilterer(address common.Address, filterer bind.ContractFilterer) (*PrimitiveContractsTestFilterer, error) {
	contract, err := bindPrimitiveContractsTest(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &PrimitiveContractsTestFilterer{contract: contract}, nil
}

// bindPrimitiveContractsTest binds a generic wrapper to an already deployed contract.
func bindPrimitiveContractsTest(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(PrimitiveContractsTestABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_PrimitiveContractsTest *PrimitiveContractsTestRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _PrimitiveContractsTest.Contract.PrimitiveContractsTestCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_PrimitiveContractsTest *PrimitiveContractsTestRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _PrimitiveContractsTest.Contract.PrimitiveContractsTestTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_PrimitiveContractsTest *PrimitiveContractsTestRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _PrimitiveContractsTest.Contract.PrimitiveContractsTestTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_PrimitiveContractsTest *PrimitiveContractsTestCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _PrimitiveContractsTest.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_PrimitiveContractsTest *PrimitiveContractsTestTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _PrimitiveContractsTest.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_PrimitiveContractsTest *PrimitiveContractsTestTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _PrimitiveContractsTest.Contract.contract.Transact(opts, method, params...)
}

// GetMaintenance is a free data retrieval call binding the contract method 0x37cdbe7f.
//
// Solidity: function getMaintenance(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestCaller) GetMaintenance(opts *bind.CallOpts, addr common.Address, blockNum *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _PrimitiveContractsTest.contract.Call(opts, out, "getMaintenance", addr, blockNum)
	return *ret0, err
}

// GetMaintenance is a free data retrieval call binding the contract method 0x37cdbe7f.
//
// Solidity: function getMaintenance(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestSession) GetMaintenance(addr common.Address, blockNum *big.Int) (*big.Int, error) {
	return _PrimitiveContractsTest.Contract.GetMaintenance(&_PrimitiveContractsTest.CallOpts, addr, blockNum)
}

// GetMaintenance is a free data retrieval call binding the contract method 0x37cdbe7f.
//
// Solidity: function getMaintenance(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestCallerSession) GetMaintenance(addr common.Address, blockNum *big.Int) (*big.Int, error) {
	return _PrimitiveContractsTest.Contract.GetMaintenance(&_PrimitiveContractsTest.CallOpts, addr, blockNum)
}

// GetProxyCount is a free data retrieval call binding the contract method 0x98c9c279.
//
// Solidity: function getProxyCount(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestCaller) GetProxyCount(opts *bind.CallOpts, addr common.Address, blockNum *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _PrimitiveContractsTest.contract.Call(opts, out, "getProxyCount", addr, blockNum)
	return *ret0, err
}

// GetProxyCount is a free data retrieval call binding the contract method 0x98c9c279.
//
// Solidity: function getProxyCount(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestSession) GetProxyCount(addr common.Address, blockNum *big.Int) (*big.Int, error) {
	return _PrimitiveContractsTest.Contract.GetProxyCount(&_PrimitiveContractsTest.CallOpts, addr, blockNum)
}

// GetProxyCount is a free data retrieval call binding the contract method 0x98c9c279.
//
// Solidity: function getProxyCount(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestCallerSession) GetProxyCount(addr common.Address, blockNum *big.Int) (*big.Int, error) {
	return _PrimitiveContractsTest.Contract.GetProxyCount(&_PrimitiveContractsTest.CallOpts, addr, blockNum)
}

// GetRank is a free data retrieval call binding the contract method 0xf7935969.
//
// Solidity: function getRank(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestCaller) GetRank(opts *bind.CallOpts, addr common.Address, blockNum *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _PrimitiveContractsTest.contract.Call(opts, out, "getRank", addr, blockNum)
	return *ret0, err
}

// GetRank is a free data retrieval call binding the contract method 0xf7935969.
//
// Solidity: function getRank(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestSession) GetRank(addr common.Address, blockNum *big.Int) (*big.Int, error) {
	return _PrimitiveContractsTest.Contract.GetRank(&_PrimitiveContractsTest.CallOpts, addr, blockNum)
}

// GetRank is a free data retrieval call binding the contract method 0xf7935969.
//
// Solidity: function getRank(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestCallerSession) GetRank(addr common.Address, blockNum *big.Int) (*big.Int, error) {
	return _PrimitiveContractsTest.Contract.GetRank(&_PrimitiveContractsTest.CallOpts, addr, blockNum)
}

// GetTxVolume is a free data retrieval call binding the contract method 0x435f8a27.
//
// Solidity: function getTxVolume(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestCaller) GetTxVolume(opts *bind.CallOpts, addr common.Address, blockNum *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _PrimitiveContractsTest.contract.Call(opts, out, "getTxVolume", addr, blockNum)
	return *ret0, err
}

// GetTxVolume is a free data retrieval call binding the contract method 0x435f8a27.
//
// Solidity: function getTxVolume(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestSession) GetTxVolume(addr common.Address, blockNum *big.Int) (*big.Int, error) {
	return _PrimitiveContractsTest.Contract.GetTxVolume(&_PrimitiveContractsTest.CallOpts, addr, blockNum)
}

// GetTxVolume is a free data retrieval call binding the contract method 0x435f8a27.
//
// Solidity: function getTxVolume(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestCallerSession) GetTxVolume(addr common.Address, blockNum *big.Int) (*big.Int, error) {
	return _PrimitiveContractsTest.Contract.GetTxVolume(&_PrimitiveContractsTest.CallOpts, addr, blockNum)
}

// GetUploadInfo is a free data retrieval call binding the contract method 0xb68d0d43.
//
// Solidity: function getUploadInfo(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestCaller) GetUploadInfo(opts *bind.CallOpts, addr common.Address, blockNum *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _PrimitiveContractsTest.contract.Call(opts, out, "getUploadInfo", addr, blockNum)
	return *ret0, err
}

// GetUploadInfo is a free data retrieval call binding the contract method 0xb68d0d43.
//
// Solidity: function getUploadInfo(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestSession) GetUploadInfo(addr common.Address, blockNum *big.Int) (*big.Int, error) {
	return _PrimitiveContractsTest.Contract.GetUploadInfo(&_PrimitiveContractsTest.CallOpts, addr, blockNum)
}

// GetUploadInfo is a free data retrieval call binding the contract method 0xb68d0d43.
//
// Solidity: function getUploadInfo(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestCallerSession) GetUploadInfo(addr common.Address, blockNum *big.Int) (*big.Int, error) {
	return _PrimitiveContractsTest.Contract.GetUploadInfo(&_PrimitiveContractsTest.CallOpts, addr, blockNum)
}

// IsProxy is a free data retrieval call binding the contract method 0xfae4a1e1.
//
// Solidity: function isProxy(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestCaller) IsProxy(opts *bind.CallOpts, addr common.Address, blockNum *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _PrimitiveContractsTest.contract.Call(opts, out, "isProxy", addr, blockNum)
	return *ret0, err
}

// IsProxy is a free data retrieval call binding the contract method 0xfae4a1e1.
//
// Solidity: function isProxy(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestSession) IsProxy(addr common.Address, blockNum *big.Int) (*big.Int, error) {
	return _PrimitiveContractsTest.Contract.IsProxy(&_PrimitiveContractsTest.CallOpts, addr, blockNum)
}

// IsProxy is a free data retrieval call binding the contract method 0xfae4a1e1.
//
// Solidity: function isProxy(addr address, blockNum uint256) constant returns(b uint256)
func (_PrimitiveContractsTest *PrimitiveContractsTestCallerSession) IsProxy(addr common.Address, blockNum *big.Int) (*big.Int, error) {
	return _PrimitiveContractsTest.Contract.IsProxy(&_PrimitiveContractsTest.CallOpts, addr, blockNum)
}
