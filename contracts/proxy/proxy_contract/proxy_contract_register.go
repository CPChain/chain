// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package contract

import (
	"strings"

	"bitbucket.org/cpchain/chain/accounts/abi"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// ProxyContractRegisterABI is the input ABI used to generate the binding from.
const ProxyContractRegisterABI = "[{\"constant\":false,\"inputs\":[{\"name\":\"_proxyAddress\",\"type\":\"address\"},{\"name\":\"_realAddress\",\"type\":\"address\"}],\"name\":\"registerProxyContract\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"}],\"name\":\"contractAddresses\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"}],\"name\":\"proxyContractAddress\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"getRealContract\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"getProxyContract\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]"

// ProxyContractRegisterBin is the compiled bytecode used for deploying new contracts.
const ProxyContractRegisterBin = `0x608060405234801561001057600080fd5b5060008054600160a060020a03191633179055610243806100326000396000f30060806040526004361061006c5763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416630e0bee3e81146100715780634661ac951461008d5780637dadbe99146100ca5780638099b681146100eb578063fc4fdd3d1461010c575b600080fd5b61008b600160a060020a036004358116906024351661012d565b005b34801561009957600080fd5b506100ae600160a060020a03600435166101a5565b60408051600160a060020a039092168252519081900360200190f35b3480156100d657600080fd5b506100ae600160a060020a03600435166101c0565b3480156100f757600080fd5b506100ae600160a060020a03600435166101db565b34801561011857600080fd5b506100ae600160a060020a03600435166101f9565b600054600160a060020a03163314156101a157600160a060020a03821630146101a157600160a060020a038083166000818152600160209081526040808320805495871673ffffffffffffffffffffffffffffffffffffffff19968716811790915583526002909152902080549092161790555b5050565b600160205260009081526040902054600160a060020a031681565b600260205260009081526040902054600160a060020a031681565b600160a060020a039081166000908152600160205260409020541690565b600160a060020a0390811660009081526002602052604090205416905600a165627a7a7230582053f87cc6ab01dd4ada7eefb9be52ca3348fa3edd405d60777d5a3e623a27abd10029`

// DeployProxyContractRegister deploys a new cpchain contract, binding an instance of ProxyContractRegister to it.
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

// ProxyContractRegister is an auto generated Go binding around an cpchain contract.
type ProxyContractRegister struct {
	ProxyContractRegisterCaller     // Read-only binding to the contract
	ProxyContractRegisterTransactor // Write-only binding to the contract
	ProxyContractRegisterFilterer   // Log filterer for contract events
}

// ProxyContractRegisterCaller is an auto generated read-only Go binding around an cpchain contract.
type ProxyContractRegisterCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProxyContractRegisterTransactor is an auto generated write-only Go binding around an cpchain contract.
type ProxyContractRegisterTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProxyContractRegisterFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type ProxyContractRegisterFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProxyContractRegisterSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type ProxyContractRegisterSession struct {
	Contract     *ProxyContractRegister // Generic contract binding to set the session for
	CallOpts     bind.CallOpts          // Call options to use throughout this session
	TransactOpts bind.TransactOpts      // Transaction auth options to use throughout this session
}

// ProxyContractRegisterCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type ProxyContractRegisterCallerSession struct {
	Contract *ProxyContractRegisterCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts                // Call options to use throughout this session
}

// ProxyContractRegisterTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type ProxyContractRegisterTransactorSession struct {
	Contract     *ProxyContractRegisterTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts                // Transaction auth options to use throughout this session
}

// ProxyContractRegisterRaw is an auto generated low-level Go binding around an cpchain contract.
type ProxyContractRegisterRaw struct {
	Contract *ProxyContractRegister // Generic contract binding to access the raw methods on
}

// ProxyContractRegisterCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type ProxyContractRegisterCallerRaw struct {
	Contract *ProxyContractRegisterCaller // Generic read-only contract binding to access the raw methods on
}

// ProxyContractRegisterTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
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

// GetProxyContract is a free data retrieval call binding the contract method 0xfc4fdd3d.
//
// Solidity: function getProxyContract(_addr address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCaller) GetProxyContract(opts *bind.CallOpts, _addr common.Address) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _ProxyContractRegister.contract.Call(opts, out, "getProxyContract", _addr)
	return *ret0, err
}

// GetProxyContract is a free data retrieval call binding the contract method 0xfc4fdd3d.
//
// Solidity: function getProxyContract(_addr address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterSession) GetProxyContract(_addr common.Address) (common.Address, error) {
	return _ProxyContractRegister.Contract.GetProxyContract(&_ProxyContractRegister.CallOpts, _addr)
}

// GetProxyContract is a free data retrieval call binding the contract method 0xfc4fdd3d.
//
// Solidity: function getProxyContract(_addr address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCallerSession) GetProxyContract(_addr common.Address) (common.Address, error) {
	return _ProxyContractRegister.Contract.GetProxyContract(&_ProxyContractRegister.CallOpts, _addr)
}

// GetRealContract is a free data retrieval call binding the contract method 0x8099b681.
//
// Solidity: function getRealContract(_addr address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCaller) GetRealContract(opts *bind.CallOpts, _addr common.Address) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _ProxyContractRegister.contract.Call(opts, out, "getRealContract", _addr)
	return *ret0, err
}

// GetRealContract is a free data retrieval call binding the contract method 0x8099b681.
//
// Solidity: function getRealContract(_addr address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterSession) GetRealContract(_addr common.Address) (common.Address, error) {
	return _ProxyContractRegister.Contract.GetRealContract(&_ProxyContractRegister.CallOpts, _addr)
}

// GetRealContract is a free data retrieval call binding the contract method 0x8099b681.
//
// Solidity: function getRealContract(_addr address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCallerSession) GetRealContract(_addr common.Address) (common.Address, error) {
	return _ProxyContractRegister.Contract.GetRealContract(&_ProxyContractRegister.CallOpts, _addr)
}

// ProxyContractAddress is a free data retrieval call binding the contract method 0x7dadbe99.
//
// Solidity: function proxyContractAddress( address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCaller) ProxyContractAddress(opts *bind.CallOpts, arg0 common.Address) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _ProxyContractRegister.contract.Call(opts, out, "proxyContractAddress", arg0)
	return *ret0, err
}

// ProxyContractAddress is a free data retrieval call binding the contract method 0x7dadbe99.
//
// Solidity: function proxyContractAddress( address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterSession) ProxyContractAddress(arg0 common.Address) (common.Address, error) {
	return _ProxyContractRegister.Contract.ProxyContractAddress(&_ProxyContractRegister.CallOpts, arg0)
}

// ProxyContractAddress is a free data retrieval call binding the contract method 0x7dadbe99.
//
// Solidity: function proxyContractAddress( address) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCallerSession) ProxyContractAddress(arg0 common.Address) (common.Address, error) {
	return _ProxyContractRegister.Contract.ProxyContractAddress(&_ProxyContractRegister.CallOpts, arg0)
}

// RegisterProxyContract is a paid mutator transaction binding the contract method 0x0e0bee3e.
//
// Solidity: function registerProxyContract(_proxyAddress address, _realAddress address) returns()
func (_ProxyContractRegister *ProxyContractRegisterTransactor) RegisterProxyContract(opts *bind.TransactOpts, _proxyAddress common.Address, _realAddress common.Address) (*types.Transaction, error) {
	return _ProxyContractRegister.contract.Transact(opts, "registerProxyContract", _proxyAddress, _realAddress)
}

// RegisterProxyContract is a paid mutator transaction binding the contract method 0x0e0bee3e.
//
// Solidity: function registerProxyContract(_proxyAddress address, _realAddress address) returns()
func (_ProxyContractRegister *ProxyContractRegisterSession) RegisterProxyContract(_proxyAddress common.Address, _realAddress common.Address) (*types.Transaction, error) {
	return _ProxyContractRegister.Contract.RegisterProxyContract(&_ProxyContractRegister.TransactOpts, _proxyAddress, _realAddress)
}

// RegisterProxyContract is a paid mutator transaction binding the contract method 0x0e0bee3e.
//
// Solidity: function registerProxyContract(_proxyAddress address, _realAddress address) returns()
func (_ProxyContractRegister *ProxyContractRegisterTransactorSession) RegisterProxyContract(_proxyAddress common.Address, _realAddress common.Address) (*types.Transaction, error) {
	return _ProxyContractRegister.Contract.RegisterProxyContract(&_ProxyContractRegister.TransactOpts, _proxyAddress, _realAddress)
}
