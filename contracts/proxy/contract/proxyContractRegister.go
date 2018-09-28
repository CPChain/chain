// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package contract

import (
	"strings"

	"bitbucket.org/cpchain/chain/accounts/abi"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/core/types"
)

// ProxyContractRegisterABI is the input ABI used to generate the binding from.
const ProxyContractRegisterABI = "[{\"constant\":false,\"inputs\":[{\"name\":\"proxyAddress\",\"type\":\"address\"},{\"name\":\"realAddress\",\"type\":\"address\"}],\"name\":\"registerProxyContract\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"}],\"name\":\"contractAddresses\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"getRealContract\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]"

// ProxyContractRegisterBin is the compiled bytecode used for deploying new contracts.
const ProxyContractRegisterBin = `0x608060405234801561001057600080fd5b5060008054600160a060020a0319163317905561019d806100326000396000f3006080604052600436106100565763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416630e0bee3e811461005b5780634661ac95146100775780638099b681146100b4575b600080fd5b610075600160a060020a03600435811690602435166100d5565b005b34801561008357600080fd5b50610098600160a060020a0360043516610138565b60408051600160a060020a039092168252519081900360200190f35b3480156100c057600080fd5b50610098600160a060020a0360043516610153565b600054600160a060020a031633141561013457600160a060020a038216301461013457600160a060020a038281166000908152600160205260409020805473ffffffffffffffffffffffffffffffffffffffff19169183169190911790555b5050565b600160205260009081526040902054600160a060020a031681565b600160a060020a0390811660009081526001602052604090205416905600a165627a7a7230582074e67f4a93cc07a31309e743c4dbe9090f5c56cd237a8e51265a367d56d4d68b0029`

// DeployProxyContractRegister deploys a new Ethereum contract, binding an instance of ProxyContractRegister to it.
func DeployProxyContractRegister(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *ProxyContractRegister, error) {
	parsed, err := abi.JSON(strings.NewReader(ProxyContractRegisterABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(ProxyContractRegisterBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &ProxyContractRegister{ProxyContractRegisterCaller: ProxyContractRegisterCaller{contract: contract}, ProxyContractRegisterTransactor: ProxyContractRegisterTransactor{contract: contract}, ProxyContractRegisterFilterer: ProxyContractRegisterFilterer{contract: contract}}, nil
}

// ProxyContractRegister is an auto generated Go binding around an Ethereum contract.
type ProxyContractRegister struct {
	ProxyContractRegisterCaller     // Read-only binding to the contract
	ProxyContractRegisterTransactor // Write-only binding to the contract
	ProxyContractRegisterFilterer   // Log filterer for contract events
}

// ProxyContractRegisterCaller is an auto generated read-only Go binding around an Ethereum contract.
type ProxyContractRegisterCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProxyContractRegisterTransactor is an auto generated write-only Go binding around an Ethereum contract.
type ProxyContractRegisterTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProxyContractRegisterFilterer is an auto generated log filtering Go binding around an Ethereum contract events.
type ProxyContractRegisterFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProxyContractRegisterSession is an auto generated Go binding around an Ethereum contract,
// with pre-set call and transact options.
type ProxyContractRegisterSession struct {
	Contract     *ProxyContractRegister // Generic contract binding to set the session for
	CallOpts     bind.CallOpts          // Call options to use throughout this session
	TransactOpts bind.TransactOpts      // Transaction auth options to use throughout this session
}

// ProxyContractRegisterCallerSession is an auto generated read-only Go binding around an Ethereum contract,
// with pre-set call options.
type ProxyContractRegisterCallerSession struct {
	Contract *ProxyContractRegisterCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts                // Call options to use throughout this session
}

// ProxyContractRegisterTransactorSession is an auto generated write-only Go binding around an Ethereum contract,
// with pre-set transact options.
type ProxyContractRegisterTransactorSession struct {
	Contract     *ProxyContractRegisterTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts                // Transaction auth options to use throughout this session
}

// ProxyContractRegisterRaw is an auto generated low-level Go binding around an Ethereum contract.
type ProxyContractRegisterRaw struct {
	Contract *ProxyContractRegister // Generic contract binding to access the raw methods on
}

// ProxyContractRegisterCallerRaw is an auto generated low-level read-only Go binding around an Ethereum contract.
type ProxyContractRegisterCallerRaw struct {
	Contract *ProxyContractRegisterCaller // Generic read-only contract binding to access the raw methods on
}

// ProxyContractRegisterTransactorRaw is an auto generated low-level write-only Go binding around an Ethereum contract.
type ProxyContractRegisterTransactorRaw struct {
	Contract *ProxyContractRegisterTransactor // Generic write-only contract binding to access the raw methods on
}

// NewProxyContractRegister creates a new instance of ProxyContractRegister, bound to a specific deployed contract.
func NewProxyContractRegister(address common.Address, backend bind.ContractBackend) (*ProxyContractRegister, error) {
	contract, err := bindProxyContractRegister(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &ProxyContractRegister{ProxyContractRegisterCaller: ProxyContractRegisterCaller{contract: contract}, ProxyContractRegisterTransactor: ProxyContractRegisterTransactor{contract: contract}, ProxyContractRegisterFilterer: ProxyContractRegisterFilterer{contract: contract}}, nil
}

// NewProxyContractRegisterCaller creates a new read-only instance of ProxyContractRegister, bound to a specific deployed contract.
func NewProxyContractRegisterCaller(address common.Address, caller bind.ContractCaller) (*ProxyContractRegisterCaller, error) {
	contract, err := bindProxyContractRegister(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &ProxyContractRegisterCaller{contract: contract}, nil
}

// NewProxyContractRegisterTransactor creates a new write-only instance of ProxyContractRegister, bound to a specific deployed contract.
func NewProxyContractRegisterTransactor(address common.Address, transactor bind.ContractTransactor) (*ProxyContractRegisterTransactor, error) {
	contract, err := bindProxyContractRegister(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &ProxyContractRegisterTransactor{contract: contract}, nil
}

// NewProxyContractRegisterFilterer creates a new log filterer instance of ProxyContractRegister, bound to a specific deployed contract.
func NewProxyContractRegisterFilterer(address common.Address, filterer bind.ContractFilterer) (*ProxyContractRegisterFilterer, error) {
	contract, err := bindProxyContractRegister(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &ProxyContractRegisterFilterer{contract: contract}, nil
}

// bindProxyContractRegister binds a generic wrapper to an already deployed contract.
func bindProxyContractRegister(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(ProxyContractRegisterABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_ProxyContractRegister *ProxyContractRegisterRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _ProxyContractRegister.Contract.ProxyContractRegisterCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_ProxyContractRegister *ProxyContractRegisterRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _ProxyContractRegister.Contract.ProxyContractRegisterTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_ProxyContractRegister *ProxyContractRegisterRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _ProxyContractRegister.Contract.ProxyContractRegisterTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_ProxyContractRegister *ProxyContractRegisterCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _ProxyContractRegister.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_ProxyContractRegister *ProxyContractRegisterTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _ProxyContractRegister.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_ProxyContractRegister *ProxyContractRegisterTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _ProxyContractRegister.Contract.contract.Transact(opts, method, params...)
}

// ContractAddresses is a free data retrieval call binding the contract method 0x4661ac95.
//
// Solidity: function contractAddresses( address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCaller) ContractAddresses(opts *bind.CallOpts, arg0 common.Address) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _ProxyContractRegister.contract.Call(opts, out, "contractAddresses", arg0)
	return *ret0, err
}

// ContractAddresses is a free data retrieval call binding the contract method 0x4661ac95.
//
// Solidity: function contractAddresses( address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterSession) ContractAddresses(arg0 common.Address) (common.Address, error) {
	return _ProxyContractRegister.Contract.ContractAddresses(&_ProxyContractRegister.CallOpts, arg0)
}

// ContractAddresses is a free data retrieval call binding the contract method 0x4661ac95.
//
// Solidity: function contractAddresses( address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCallerSession) ContractAddresses(arg0 common.Address) (common.Address, error) {
	return _ProxyContractRegister.Contract.ContractAddresses(&_ProxyContractRegister.CallOpts, arg0)
}

// GetRealContract is a free data retrieval call binding the contract method 0x8099b681.
//
// Solidity: function getRealContract(addr address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCaller) GetRealContract(opts *bind.CallOpts, addr common.Address) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _ProxyContractRegister.contract.Call(opts, out, "getRealContract", addr)
	return *ret0, err
}

// GetRealContract is a free data retrieval call binding the contract method 0x8099b681.
//
// Solidity: function getRealContract(addr address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterSession) GetRealContract(addr common.Address) (common.Address, error) {
	return _ProxyContractRegister.Contract.GetRealContract(&_ProxyContractRegister.CallOpts, addr)
}

// GetRealContract is a free data retrieval call binding the contract method 0x8099b681.
//
// Solidity: function getRealContract(addr address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCallerSession) GetRealContract(addr common.Address) (common.Address, error) {
	return _ProxyContractRegister.Contract.GetRealContract(&_ProxyContractRegister.CallOpts, addr)
}

// RegisterProxyContract is a paid mutator transaction binding the contract method 0x0e0bee3e.
//
// Solidity: function registerProxyContract(proxyAddress address, realAddress address) returns()
func (_ProxyContractRegister *ProxyContractRegisterTransactor) RegisterProxyContract(opts *bind.TransactOpts, proxyAddress common.Address, realAddress common.Address) (*types.Transaction, error) {
	return _ProxyContractRegister.contract.Transact(opts, "registerProxyContract", proxyAddress, realAddress)
}

// RegisterProxyContract is a paid mutator transaction binding the contract method 0x0e0bee3e.
//
// Solidity: function registerProxyContract(proxyAddress address, realAddress address) returns()
func (_ProxyContractRegister *ProxyContractRegisterSession) RegisterProxyContract(proxyAddress common.Address, realAddress common.Address) (*types.Transaction, error) {
	return _ProxyContractRegister.Contract.RegisterProxyContract(&_ProxyContractRegister.TransactOpts, proxyAddress, realAddress)
}

// RegisterProxyContract is a paid mutator transaction binding the contract method 0x0e0bee3e.
//
// Solidity: function registerProxyContract(proxyAddress address, realAddress address) returns()
func (_ProxyContractRegister *ProxyContractRegisterTransactorSession) RegisterProxyContract(proxyAddress common.Address, realAddress common.Address) (*types.Transaction, error) {
	return _ProxyContractRegister.Contract.RegisterProxyContract(&_ProxyContractRegister.TransactOpts, proxyAddress, realAddress)
}
