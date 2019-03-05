// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package contract

import (
	"math/big"
	"strings"

	cpchain "bitbucket.org/cpchain/chain"
	"bitbucket.org/cpchain/chain/accounts/abi"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/event"
)

// ProxyContractRegisterABI is the input ABI used to generate the binding from.
const ProxyContractRegisterABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"},{\"name\":\"\",\"type\":\"uint256\"}],\"name\":\"histroyContract\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_proxyAddress\",\"type\":\"address\"},{\"name\":\"_realAddress\",\"type\":\"address\"}],\"name\":\"registerProxyContract\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"}],\"name\":\"contractAddresses\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"},{\"name\":\"_version\",\"type\":\"uint256\"}],\"name\":\"getOldContract\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"}],\"name\":\"proxyContractAddress\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"getRealContract\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"}],\"name\":\"proxyContractAddressVersion\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_proxyAddress\",\"type\":\"address\"}],\"name\":\"getContractVersion\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"getProxyContract\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"_proxy\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"_real\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"_version\",\"type\":\"uint256\"}],\"name\":\"ProxyContractAddressVersion\",\"type\":\"event\"}]"

// ProxyContractRegisterBin is the compiled bytecode used for deploying new contracts.
const ProxyContractRegisterBin = `0x608060405234801561001057600080fd5b5060008054600160a060020a031916331790556103f8806100326000396000f3006080604052600436106100985763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416630d100b03811461009d5780630e0bee3e146100dd5780634661ac95146100f95780634c9150c81461011a5780637dadbe991461013e5780638099b6811461015f578063810d816a14610180578063c4b9d89d146101b3578063fc4fdd3d146101d4575b600080fd5b3480156100a957600080fd5b506100c1600160a060020a03600435166024356101f5565b60408051600160a060020a039092168252519081900360200190f35b6100f7600160a060020a036004358116906024351661021b565b005b34801561010557600080fd5b506100c1600160a060020a0360043516610305565b34801561012657600080fd5b506100c1600160a060020a0360043516602435610320565b34801561014a57600080fd5b506100c1600160a060020a0360043516610348565b34801561016b57600080fd5b506100c1600160a060020a0360043516610363565b34801561018c57600080fd5b506101a1600160a060020a0360043516610381565b60408051918252519081900360200190f35b3480156101bf57600080fd5b506101a1600160a060020a0360043516610393565b3480156101e057600080fd5b506100c1600160a060020a03600435166103ae565b6004602090815260009283526040808420909152908252902054600160a060020a031681565b600054600160a060020a031633141561030157600160a060020a038216301461030157600160a060020a038083166000818152600160208181526040808420805496881673ffffffffffffffffffffffffffffffffffffffff19978816811790915580855260028352818520805488168717905585855260038084528286208054909501808655600485528387209087528452828620805490981682179097559385905294815290548451938452908301919091528183015290517f9d57b1c7a777e15a03e127c41649b8c7d8d0d63df11ad3750bb52634544f9f319181900360600190a15b5050565b600160205260009081526040902054600160a060020a031681565b600160a060020a03918216600090815260046020908152604080832093835292905220541690565b600260205260009081526040902054600160a060020a031681565b600160a060020a039081166000908152600160205260409020541690565b60036020526000908152604090205481565b600160a060020a031660009081526003602052604090205490565b600160a060020a0390811660009081526002602052604090205416905600a165627a7a72305820368b5f5f99f2eb4a4c2b52d7de2e385ccfd1840a0955bab6ae776312c0f6e81c0029`

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

// GetContractVersion is a free data retrieval call binding the contract method 0xc4b9d89d.
//
// Solidity: function getContractVersion(_proxyAddress address) constant returns(uint256)
func (_ProxyContractRegister *ProxyContractRegisterCaller) GetContractVersion(opts *bind.CallOpts, _proxyAddress common.Address) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _ProxyContractRegister.contract.Call(opts, out, "getContractVersion", _proxyAddress)
	return *ret0, err
}

// GetContractVersion is a free data retrieval call binding the contract method 0xc4b9d89d.
//
// Solidity: function getContractVersion(_proxyAddress address) constant returns(uint256)
func (_ProxyContractRegister *ProxyContractRegisterSession) GetContractVersion(_proxyAddress common.Address) (*big.Int, error) {
	return _ProxyContractRegister.Contract.GetContractVersion(&_ProxyContractRegister.CallOpts, _proxyAddress)
}

// GetContractVersion is a free data retrieval call binding the contract method 0xc4b9d89d.
//
// Solidity: function getContractVersion(_proxyAddress address) constant returns(uint256)
func (_ProxyContractRegister *ProxyContractRegisterCallerSession) GetContractVersion(_proxyAddress common.Address) (*big.Int, error) {
	return _ProxyContractRegister.Contract.GetContractVersion(&_ProxyContractRegister.CallOpts, _proxyAddress)
}

// GetOldContract is a free data retrieval call binding the contract method 0x4c9150c8.
//
// Solidity: function getOldContract(_addr address, _version uint256) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCaller) GetOldContract(opts *bind.CallOpts, _addr common.Address, _version *big.Int) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _ProxyContractRegister.contract.Call(opts, out, "getOldContract", _addr, _version)
	return *ret0, err
}

// GetOldContract is a free data retrieval call binding the contract method 0x4c9150c8.
//
// Solidity: function getOldContract(_addr address, _version uint256) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterSession) GetOldContract(_addr common.Address, _version *big.Int) (common.Address, error) {
	return _ProxyContractRegister.Contract.GetOldContract(&_ProxyContractRegister.CallOpts, _addr, _version)
}

// GetOldContract is a free data retrieval call binding the contract method 0x4c9150c8.
//
// Solidity: function getOldContract(_addr address, _version uint256) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCallerSession) GetOldContract(_addr common.Address, _version *big.Int) (common.Address, error) {
	return _ProxyContractRegister.Contract.GetOldContract(&_ProxyContractRegister.CallOpts, _addr, _version)
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

// HistroyContract is a free data retrieval call binding the contract method 0x0d100b03.
//
// Solidity: function histroyContract( address,  uint256) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCaller) HistroyContract(opts *bind.CallOpts, arg0 common.Address, arg1 *big.Int) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _ProxyContractRegister.contract.Call(opts, out, "histroyContract", arg0, arg1)
	return *ret0, err
}

// HistroyContract is a free data retrieval call binding the contract method 0x0d100b03.
//
// Solidity: function histroyContract( address,  uint256) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterSession) HistroyContract(arg0 common.Address, arg1 *big.Int) (common.Address, error) {
	return _ProxyContractRegister.Contract.HistroyContract(&_ProxyContractRegister.CallOpts, arg0, arg1)
}

// HistroyContract is a free data retrieval call binding the contract method 0x0d100b03.
//
// Solidity: function histroyContract( address,  uint256) constant returns(address)
func (_ProxyContractRegister *ProxyContractRegisterCallerSession) HistroyContract(arg0 common.Address, arg1 *big.Int) (common.Address, error) {
	return _ProxyContractRegister.Contract.HistroyContract(&_ProxyContractRegister.CallOpts, arg0, arg1)
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

// ProxyContractAddressVersion is a free data retrieval call binding the contract method 0x810d816a.
//
// Solidity: function proxyContractAddressVersion( address) constant returns(uint256)
func (_ProxyContractRegister *ProxyContractRegisterCaller) ProxyContractAddressVersion(opts *bind.CallOpts, arg0 common.Address) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _ProxyContractRegister.contract.Call(opts, out, "proxyContractAddressVersion", arg0)
	return *ret0, err
}

// ProxyContractAddressVersion is a free data retrieval call binding the contract method 0x810d816a.
//
// Solidity: function proxyContractAddressVersion( address) constant returns(uint256)
func (_ProxyContractRegister *ProxyContractRegisterSession) ProxyContractAddressVersion(arg0 common.Address) (*big.Int, error) {
	return _ProxyContractRegister.Contract.ProxyContractAddressVersion(&_ProxyContractRegister.CallOpts, arg0)
}

// ProxyContractAddressVersion is a free data retrieval call binding the contract method 0x810d816a.
//
// Solidity: function proxyContractAddressVersion( address) constant returns(uint256)
func (_ProxyContractRegister *ProxyContractRegisterCallerSession) ProxyContractAddressVersion(arg0 common.Address) (*big.Int, error) {
	return _ProxyContractRegister.Contract.ProxyContractAddressVersion(&_ProxyContractRegister.CallOpts, arg0)
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

// ProxyContractRegisterProxyContractAddressVersionIterator is returned from FilterProxyContractAddressVersion and is used to iterate over the raw logs and unpacked data for ProxyContractAddressVersion events raised by the ProxyContractRegister contract.
type ProxyContractRegisterProxyContractAddressVersionIterator struct {
	Event *ProxyContractRegisterProxyContractAddressVersion // Event containing the contract specifics and raw log

	contract *bind.BoundContract // Generic contract to use for unpacking event data
	event    string              // Event name to use for unpacking event data

	logs chan types.Log       // Log channel receiving the found contract events
	sub  cpchain.Subscription // Subscription for errors, completion and termination
	done bool                 // Whether the subscription completed delivering logs
	fail error                // Occurred error to stop iteration
}

// Next advances the iterator to the subsequent event, returning whether there
// are any more events found. In case of a retrieval or parsing error, false is
// returned and Error() can be queried for the exact failure.
func (it *ProxyContractRegisterProxyContractAddressVersionIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(ProxyContractRegisterProxyContractAddressVersion)
			if err := it.contract.UnpackLog(it.Event, it.event, log); err != nil {
				it.fail = err
				return false
			}
			it.Event.Raw = log
			return true

		default:
			return false
		}
	}
	// Iterator still in progress, wait for either a data or an error event
	select {
	case log := <-it.logs:
		it.Event = new(ProxyContractRegisterProxyContractAddressVersion)
		if err := it.contract.UnpackLog(it.Event, it.event, log); err != nil {
			it.fail = err
			return false
		}
		it.Event.Raw = log
		return true

	case err := <-it.sub.Err():
		it.done = true
		it.fail = err
		return it.Next()
	}
}

// Error returns any retrieval or parsing error occurred during filtering.
func (it *ProxyContractRegisterProxyContractAddressVersionIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *ProxyContractRegisterProxyContractAddressVersionIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// ProxyContractRegisterProxyContractAddressVersion represents a ProxyContractAddressVersion event raised by the ProxyContractRegister contract.
type ProxyContractRegisterProxyContractAddressVersion struct {
	Proxy   common.Address
	Real    common.Address
	Version *big.Int
	Raw     types.Log // Blockchain specific contextual infos
}

// FilterProxyContractAddressVersion is a free log retrieval operation binding the contract event 0x9d57b1c7a777e15a03e127c41649b8c7d8d0d63df11ad3750bb52634544f9f31.
//
// Solidity: e ProxyContractAddressVersion(_proxy address, _real address, _version uint256)
func (_ProxyContractRegister *ProxyContractRegisterFilterer) FilterProxyContractAddressVersion(opts *bind.FilterOpts) (*ProxyContractRegisterProxyContractAddressVersionIterator, error) {

	logs, sub, err := _ProxyContractRegister.contract.FilterLogs(opts, "ProxyContractAddressVersion")
	if err != nil {
		return nil, err
	}
	return &ProxyContractRegisterProxyContractAddressVersionIterator{contract: _ProxyContractRegister.contract, event: "ProxyContractAddressVersion", logs: logs, sub: sub}, nil
}

// WatchProxyContractAddressVersion is a free log subscription operation binding the contract event 0x9d57b1c7a777e15a03e127c41649b8c7d8d0d63df11ad3750bb52634544f9f31.
//
// Solidity: e ProxyContractAddressVersion(_proxy address, _real address, _version uint256)
func (_ProxyContractRegister *ProxyContractRegisterFilterer) WatchProxyContractAddressVersion(opts *bind.WatchOpts, sink chan<- *ProxyContractRegisterProxyContractAddressVersion) (event.Subscription, error) {

	logs, sub, err := _ProxyContractRegister.contract.WatchLogs(opts, "ProxyContractAddressVersion")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(ProxyContractRegisterProxyContractAddressVersion)
				if err := _ProxyContractRegister.contract.UnpackLog(event, "ProxyContractAddressVersion", log); err != nil {
					return err
				}
				event.Raw = log

				select {
				case sink <- event:
				case err := <-sub.Err():
					return err
				case <-quit:
					return nil
				}
			case err := <-sub.Err():
				return err
			case <-quit:
				return nil
			}
		}
	}), nil
}
