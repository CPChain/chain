// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package pdash_contract

import (
	"math/big"
	"strings"

	"bitbucket.org/cpchain/chain/accounts/abi"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// PdashProxyABI is the input ABI used to generate the binding from.
const PdashProxyABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"proxy\",\"type\":\"address\"}],\"name\":\"getProxyFileNumber\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"user\",\"type\":\"address\"},{\"name\":\"block_num\",\"type\":\"uint256\"}],\"name\":\"getProxyFileNumberInBlock\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"updatePdashAddress\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"fileName\",\"type\":\"string\"},{\"name\":\"fileHash\",\"type\":\"bytes32\"},{\"name\":\"fileSize\",\"type\":\"uint256\"}],\"name\":\"proxyRegister\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"setAdmissionAddr\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"},{\"name\":\"\",\"type\":\"uint256\"}],\"name\":\"proxyHistory\",\"outputs\":[{\"name\":\"fileName\",\"type\":\"string\"},{\"name\":\"fileHash\",\"type\":\"bytes32\"},{\"name\":\"fileSize\",\"type\":\"uint256\"},{\"name\":\"timeStamp\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"pdash\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]"

// PdashProxyBin is the compiled bytecode used for deploying new contracts.
const PdashProxyBin = `0x608060405234801561001057600080fd5b50604051602080610766833981016040525160008054600160a060020a0319908116331790915560018054821673d81ab6b1e656550f90b2d874926b949fde97096d17905560028054600160a060020a03909316929091169190911790556106e98061007d6000396000f3006080604052600436106100825763ffffffff7c0100000000000000000000000000000000000000000000000000000000600035041663122de578811461008757806355a20afc146100ba57806384b0c302146100de578063ac50f81514610101578063c0e9e35e14610163578063c642648d14610184578063c946286d14610236575b600080fd5b34801561009357600080fd5b506100a8600160a060020a0360043516610267565b60408051918252519081900360200190f35b3480156100c657600080fd5b506100a8600160a060020a0360043516602435610282565b3480156100ea57600080fd5b506100ff600160a060020a03600435166102fd565b005b34801561010d57600080fd5b506040805160206004803580820135601f81018490048402850184019095528484526100ff9436949293602493928401919081908401838280828437509497505084359550505060209092013591506103439050565b34801561016f57600080fd5b506100ff600160a060020a03600435166104fd565b34801561019057600080fd5b506101a8600160a060020a0360043516602435610543565b60408051602080820186905291810184905260608101839052608080825286519082015285519091829160a083019188019080838360005b838110156101f85781810151838201526020016101e0565b50505050905090810190601f1680156102255780820380516001836020036101000a031916815260200191505b509550505050505060405180910390f35b34801561024257600080fd5b5061024b610613565b60408051600160a060020a039092168252519081900360200190f35b600160a060020a031660009081526003602052604090205490565b600080805b600160a060020a0385166000908152600360205260409020548110156102f557600160a060020a03851660009081526003602052604090208054859190839081106102ce57fe5b90600052602060002090600402016003015414156102ed576001909101905b600101610287565b509392505050565b600054600160a060020a0316331461031457600080fd5b6001805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a0392909216919091179055565b600254604080517ffc4fdd3d0000000000000000000000000000000000000000000000000000000081523360048201529051600160a060020a039092169163fc4fdd3d916024808201926020929091908290030181600087803b1580156103a957600080fd5b505af11580156103bd573d6000803e3d6000fd5b505050506040513d60208110156103d357600080fd5b5051600154600160a060020a0390811691161461047757604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602160248201527f6f6e6c792070646173682063616e2063616c6c2070726f78795265676973746560448201527f7200000000000000000000000000000000000000000000000000000000000000606482015290519081900360840190fd5b33600090815260036020908152604080832081516080810183528781528084018790529182018590524360608301528054600181018083559185529383902082518051929593946004909402909101926104d692849290910190610622565b50602082015160018201556040820151600282015560609091015160039091015550505050565b600054600160a060020a0316331461051457600080fd5b6002805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a0392909216919091179055565b60036020528160005260406000208181548110151561055e57fe5b60009182526020918290206004919091020180546040805160026001841615610100026000190190931692909204601f8101859004850283018501909152808252919450925083918301828280156105f75780601f106105cc576101008083540402835291602001916105f7565b820191906000526020600020905b8154815290600101906020018083116105da57829003601f168201915b5050505050908060010154908060020154908060030154905084565b600154600160a060020a031681565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f1061066357805160ff1916838001178555610690565b82800160010185558215610690579182015b82811115610690578251825591602001919060010190610675565b5061069c9291506106a0565b5090565b6106ba91905b8082111561069c57600081556001016106a6565b905600a165627a7a72305820a44a90576e98fd9e5c71f95b5b4cc65bf9a08c5d9caa920e16bcd6fe139f00c20029`

// DeployPdashProxy deploys a new cpchain contract, binding an instance of PdashProxy to it.
func DeployPdashProxy(auth *bind.TransactOpts, backend bind.ContractBackend, _addr common.Address) (common.Address, *types.Transaction, *PdashProxy, error) {
	parsed, err := abi.JSON(strings.NewReader(PdashProxyABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(PdashProxyBin), backend, _addr)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &PdashProxy{PdashProxyCaller: PdashProxyCaller{contract: contract}, PdashProxyTransactor: PdashProxyTransactor{contract: contract}, PdashProxyFilterer: PdashProxyFilterer{contract: contract}}, nil
}

// PdashProxy is an auto generated Go binding around an cpchain contract.
type PdashProxy struct {
	PdashProxyCaller     // Read-only binding to the contract
	PdashProxyTransactor // Write-only binding to the contract
	PdashProxyFilterer   // Log filterer for contract events
}

// PdashProxyCaller is an auto generated read-only Go binding around an cpchain contract.
type PdashProxyCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// PdashProxyTransactor is an auto generated write-only Go binding around an cpchain contract.
type PdashProxyTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// PdashProxyFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type PdashProxyFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// PdashProxySession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type PdashProxySession struct {
	Contract     *PdashProxy       // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// PdashProxyCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type PdashProxyCallerSession struct {
	Contract *PdashProxyCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts     // Call options to use throughout this session
}

// PdashProxyTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type PdashProxyTransactorSession struct {
	Contract     *PdashProxyTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts     // Transaction auth options to use throughout this session
}

// PdashProxyRaw is an auto generated low-level Go binding around an cpchain contract.
type PdashProxyRaw struct {
	Contract *PdashProxy // Generic contract binding to access the raw methods on
}

// PdashProxyCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type PdashProxyCallerRaw struct {
	Contract *PdashProxyCaller // Generic read-only contract binding to access the raw methods on
}

// PdashProxyTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type PdashProxyTransactorRaw struct {
	Contract *PdashProxyTransactor // Generic write-only contract binding to access the raw methods on
}

// NewPdashProxy creates a new instance of PdashProxy, bound to a specific deployed contract.
func NewPdashProxy(address common.Address, backend bind.ContractBackend) (*PdashProxy, error) {
	contract, err := bindPdashProxy(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &PdashProxy{PdashProxyCaller: PdashProxyCaller{contract: contract}, PdashProxyTransactor: PdashProxyTransactor{contract: contract}, PdashProxyFilterer: PdashProxyFilterer{contract: contract}}, nil
}

// NewPdashProxyCaller creates a new read-only instance of PdashProxy, bound to a specific deployed contract.
func NewPdashProxyCaller(address common.Address, caller bind.ContractCaller) (*PdashProxyCaller, error) {
	contract, err := bindPdashProxy(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &PdashProxyCaller{contract: contract}, nil
}

// NewPdashProxyTransactor creates a new write-only instance of PdashProxy, bound to a specific deployed contract.
func NewPdashProxyTransactor(address common.Address, transactor bind.ContractTransactor) (*PdashProxyTransactor, error) {
	contract, err := bindPdashProxy(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &PdashProxyTransactor{contract: contract}, nil
}

// NewPdashProxyFilterer creates a new log filterer instance of PdashProxy, bound to a specific deployed contract.
func NewPdashProxyFilterer(address common.Address, filterer bind.ContractFilterer) (*PdashProxyFilterer, error) {
	contract, err := bindPdashProxy(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &PdashProxyFilterer{contract: contract}, nil
}

// bindPdashProxy binds a generic wrapper to an already deployed contract.
func bindPdashProxy(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(PdashProxyABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_PdashProxy *PdashProxyRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _PdashProxy.Contract.PdashProxyCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_PdashProxy *PdashProxyRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _PdashProxy.Contract.PdashProxyTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_PdashProxy *PdashProxyRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _PdashProxy.Contract.PdashProxyTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_PdashProxy *PdashProxyCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _PdashProxy.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_PdashProxy *PdashProxyTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _PdashProxy.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_PdashProxy *PdashProxyTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _PdashProxy.Contract.contract.Transact(opts, method, params...)
}

// GetProxyFileNumber is a free data retrieval call binding the contract method 0x122de578.
//
// Solidity: function getProxyFileNumber(proxy address) constant returns(uint256)
func (_PdashProxy *PdashProxyCaller) GetProxyFileNumber(opts *bind.CallOpts, proxy common.Address) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _PdashProxy.contract.Call(opts, out, "getProxyFileNumber", proxy)
	return *ret0, err
}

// GetProxyFileNumber is a free data retrieval call binding the contract method 0x122de578.
//
// Solidity: function getProxyFileNumber(proxy address) constant returns(uint256)
func (_PdashProxy *PdashProxySession) GetProxyFileNumber(proxy common.Address) (*big.Int, error) {
	return _PdashProxy.Contract.GetProxyFileNumber(&_PdashProxy.CallOpts, proxy)
}

// GetProxyFileNumber is a free data retrieval call binding the contract method 0x122de578.
//
// Solidity: function getProxyFileNumber(proxy address) constant returns(uint256)
func (_PdashProxy *PdashProxyCallerSession) GetProxyFileNumber(proxy common.Address) (*big.Int, error) {
	return _PdashProxy.Contract.GetProxyFileNumber(&_PdashProxy.CallOpts, proxy)
}

// GetProxyFileNumberInBlock is a free data retrieval call binding the contract method 0x55a20afc.
//
// Solidity: function getProxyFileNumberInBlock(user address, block_num uint256) constant returns(uint256)
func (_PdashProxy *PdashProxyCaller) GetProxyFileNumberInBlock(opts *bind.CallOpts, user common.Address, block_num *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _PdashProxy.contract.Call(opts, out, "getProxyFileNumberInBlock", user, block_num)
	return *ret0, err
}

// GetProxyFileNumberInBlock is a free data retrieval call binding the contract method 0x55a20afc.
//
// Solidity: function getProxyFileNumberInBlock(user address, block_num uint256) constant returns(uint256)
func (_PdashProxy *PdashProxySession) GetProxyFileNumberInBlock(user common.Address, block_num *big.Int) (*big.Int, error) {
	return _PdashProxy.Contract.GetProxyFileNumberInBlock(&_PdashProxy.CallOpts, user, block_num)
}

// GetProxyFileNumberInBlock is a free data retrieval call binding the contract method 0x55a20afc.
//
// Solidity: function getProxyFileNumberInBlock(user address, block_num uint256) constant returns(uint256)
func (_PdashProxy *PdashProxyCallerSession) GetProxyFileNumberInBlock(user common.Address, block_num *big.Int) (*big.Int, error) {
	return _PdashProxy.Contract.GetProxyFileNumberInBlock(&_PdashProxy.CallOpts, user, block_num)
}

// Pdash is a free data retrieval call binding the contract method 0xc946286d.
//
// Solidity: function pdash() constant returns(address)
func (_PdashProxy *PdashProxyCaller) Pdash(opts *bind.CallOpts) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _PdashProxy.contract.Call(opts, out, "pdash")
	return *ret0, err
}

// Pdash is a free data retrieval call binding the contract method 0xc946286d.
//
// Solidity: function pdash() constant returns(address)
func (_PdashProxy *PdashProxySession) Pdash() (common.Address, error) {
	return _PdashProxy.Contract.Pdash(&_PdashProxy.CallOpts)
}

// Pdash is a free data retrieval call binding the contract method 0xc946286d.
//
// Solidity: function pdash() constant returns(address)
func (_PdashProxy *PdashProxyCallerSession) Pdash() (common.Address, error) {
	return _PdashProxy.Contract.Pdash(&_PdashProxy.CallOpts)
}

// ProxyHistory is a free data retrieval call binding the contract method 0xc642648d.
//
// Solidity: function proxyHistory( address,  uint256) constant returns(fileName string, fileHash bytes32, fileSize uint256, timeStamp uint256)
func (_PdashProxy *PdashProxyCaller) ProxyHistory(opts *bind.CallOpts, arg0 common.Address, arg1 *big.Int) (struct {
	FileName  string
	FileHash  [32]byte
	FileSize  *big.Int
	TimeStamp *big.Int
}, error) {
	ret := new(struct {
		FileName  string
		FileHash  [32]byte
		FileSize  *big.Int
		TimeStamp *big.Int
	})
	out := ret
	err := _PdashProxy.contract.Call(opts, out, "proxyHistory", arg0, arg1)
	return *ret, err
}

// ProxyHistory is a free data retrieval call binding the contract method 0xc642648d.
//
// Solidity: function proxyHistory( address,  uint256) constant returns(fileName string, fileHash bytes32, fileSize uint256, timeStamp uint256)
func (_PdashProxy *PdashProxySession) ProxyHistory(arg0 common.Address, arg1 *big.Int) (struct {
	FileName  string
	FileHash  [32]byte
	FileSize  *big.Int
	TimeStamp *big.Int
}, error) {
	return _PdashProxy.Contract.ProxyHistory(&_PdashProxy.CallOpts, arg0, arg1)
}

// ProxyHistory is a free data retrieval call binding the contract method 0xc642648d.
//
// Solidity: function proxyHistory( address,  uint256) constant returns(fileName string, fileHash bytes32, fileSize uint256, timeStamp uint256)
func (_PdashProxy *PdashProxyCallerSession) ProxyHistory(arg0 common.Address, arg1 *big.Int) (struct {
	FileName  string
	FileHash  [32]byte
	FileSize  *big.Int
	TimeStamp *big.Int
}, error) {
	return _PdashProxy.Contract.ProxyHistory(&_PdashProxy.CallOpts, arg0, arg1)
}

// ProxyRegister is a paid mutator transaction binding the contract method 0xac50f815.
//
// Solidity: function proxyRegister(fileName string, fileHash bytes32, fileSize uint256) returns()
func (_PdashProxy *PdashProxyTransactor) ProxyRegister(opts *bind.TransactOpts, fileName string, fileHash [32]byte, fileSize *big.Int) (*types.Transaction, error) {
	return _PdashProxy.contract.Transact(opts, "proxyRegister", fileName, fileHash, fileSize)
}

// ProxyRegister is a paid mutator transaction binding the contract method 0xac50f815.
//
// Solidity: function proxyRegister(fileName string, fileHash bytes32, fileSize uint256) returns()
func (_PdashProxy *PdashProxySession) ProxyRegister(fileName string, fileHash [32]byte, fileSize *big.Int) (*types.Transaction, error) {
	return _PdashProxy.Contract.ProxyRegister(&_PdashProxy.TransactOpts, fileName, fileHash, fileSize)
}

// ProxyRegister is a paid mutator transaction binding the contract method 0xac50f815.
//
// Solidity: function proxyRegister(fileName string, fileHash bytes32, fileSize uint256) returns()
func (_PdashProxy *PdashProxyTransactorSession) ProxyRegister(fileName string, fileHash [32]byte, fileSize *big.Int) (*types.Transaction, error) {
	return _PdashProxy.Contract.ProxyRegister(&_PdashProxy.TransactOpts, fileName, fileHash, fileSize)
}

// SetAdmissionAddr is a paid mutator transaction binding the contract method 0xc0e9e35e.
//
// Solidity: function setAdmissionAddr(_addr address) returns()
func (_PdashProxy *PdashProxyTransactor) SetAdmissionAddr(opts *bind.TransactOpts, _addr common.Address) (*types.Transaction, error) {
	return _PdashProxy.contract.Transact(opts, "setAdmissionAddr", _addr)
}

// SetAdmissionAddr is a paid mutator transaction binding the contract method 0xc0e9e35e.
//
// Solidity: function setAdmissionAddr(_addr address) returns()
func (_PdashProxy *PdashProxySession) SetAdmissionAddr(_addr common.Address) (*types.Transaction, error) {
	return _PdashProxy.Contract.SetAdmissionAddr(&_PdashProxy.TransactOpts, _addr)
}

// SetAdmissionAddr is a paid mutator transaction binding the contract method 0xc0e9e35e.
//
// Solidity: function setAdmissionAddr(_addr address) returns()
func (_PdashProxy *PdashProxyTransactorSession) SetAdmissionAddr(_addr common.Address) (*types.Transaction, error) {
	return _PdashProxy.Contract.SetAdmissionAddr(&_PdashProxy.TransactOpts, _addr)
}

// UpdatePdashAddress is a paid mutator transaction binding the contract method 0x84b0c302.
//
// Solidity: function updatePdashAddress(addr address) returns()
func (_PdashProxy *PdashProxyTransactor) UpdatePdashAddress(opts *bind.TransactOpts, addr common.Address) (*types.Transaction, error) {
	return _PdashProxy.contract.Transact(opts, "updatePdashAddress", addr)
}

// UpdatePdashAddress is a paid mutator transaction binding the contract method 0x84b0c302.
//
// Solidity: function updatePdashAddress(addr address) returns()
func (_PdashProxy *PdashProxySession) UpdatePdashAddress(addr common.Address) (*types.Transaction, error) {
	return _PdashProxy.Contract.UpdatePdashAddress(&_PdashProxy.TransactOpts, addr)
}

// UpdatePdashAddress is a paid mutator transaction binding the contract method 0x84b0c302.
//
// Solidity: function updatePdashAddress(addr address) returns()
func (_PdashProxy *PdashProxyTransactorSession) UpdatePdashAddress(addr common.Address) (*types.Transaction, error) {
	return _PdashProxy.Contract.UpdatePdashAddress(&_PdashProxy.TransactOpts, addr)
}

// ProxyContractInterfaceABI is the input ABI used to generate the binding from.
const ProxyContractInterfaceABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"getProxyContract\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"}]"

// ProxyContractInterfaceBin is the compiled bytecode used for deploying new contracts.
const ProxyContractInterfaceBin = `0x`

// DeployProxyContractInterface deploys a new cpchain contract, binding an instance of ProxyContractInterface to it.
func DeployProxyContractInterface(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *ProxyContractInterface, error) {
	parsed, err := abi.JSON(strings.NewReader(ProxyContractInterfaceABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(ProxyContractInterfaceBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &ProxyContractInterface{ProxyContractInterfaceCaller: ProxyContractInterfaceCaller{contract: contract}, ProxyContractInterfaceTransactor: ProxyContractInterfaceTransactor{contract: contract}, ProxyContractInterfaceFilterer: ProxyContractInterfaceFilterer{contract: contract}}, nil
}

// ProxyContractInterface is an auto generated Go binding around an cpchain contract.
type ProxyContractInterface struct {
	ProxyContractInterfaceCaller     // Read-only binding to the contract
	ProxyContractInterfaceTransactor // Write-only binding to the contract
	ProxyContractInterfaceFilterer   // Log filterer for contract events
}

// ProxyContractInterfaceCaller is an auto generated read-only Go binding around an cpchain contract.
type ProxyContractInterfaceCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProxyContractInterfaceTransactor is an auto generated write-only Go binding around an cpchain contract.
type ProxyContractInterfaceTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProxyContractInterfaceFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type ProxyContractInterfaceFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProxyContractInterfaceSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type ProxyContractInterfaceSession struct {
	Contract     *ProxyContractInterface // Generic contract binding to set the session for
	CallOpts     bind.CallOpts           // Call options to use throughout this session
	TransactOpts bind.TransactOpts       // Transaction auth options to use throughout this session
}

// ProxyContractInterfaceCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type ProxyContractInterfaceCallerSession struct {
	Contract *ProxyContractInterfaceCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts                 // Call options to use throughout this session
}

// ProxyContractInterfaceTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type ProxyContractInterfaceTransactorSession struct {
	Contract     *ProxyContractInterfaceTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts                 // Transaction auth options to use throughout this session
}

// ProxyContractInterfaceRaw is an auto generated low-level Go binding around an cpchain contract.
type ProxyContractInterfaceRaw struct {
	Contract *ProxyContractInterface // Generic contract binding to access the raw methods on
}

// ProxyContractInterfaceCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type ProxyContractInterfaceCallerRaw struct {
	Contract *ProxyContractInterfaceCaller // Generic read-only contract binding to access the raw methods on
}

// ProxyContractInterfaceTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type ProxyContractInterfaceTransactorRaw struct {
	Contract *ProxyContractInterfaceTransactor // Generic write-only contract binding to access the raw methods on
}

// NewProxyContractInterface creates a new instance of ProxyContractInterface, bound to a specific deployed contract.
func NewProxyContractInterface(address common.Address, backend bind.ContractBackend) (*ProxyContractInterface, error) {
	contract, err := bindProxyContractInterface(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &ProxyContractInterface{ProxyContractInterfaceCaller: ProxyContractInterfaceCaller{contract: contract}, ProxyContractInterfaceTransactor: ProxyContractInterfaceTransactor{contract: contract}, ProxyContractInterfaceFilterer: ProxyContractInterfaceFilterer{contract: contract}}, nil
}

// NewProxyContractInterfaceCaller creates a new read-only instance of ProxyContractInterface, bound to a specific deployed contract.
func NewProxyContractInterfaceCaller(address common.Address, caller bind.ContractCaller) (*ProxyContractInterfaceCaller, error) {
	contract, err := bindProxyContractInterface(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &ProxyContractInterfaceCaller{contract: contract}, nil
}

// NewProxyContractInterfaceTransactor creates a new write-only instance of ProxyContractInterface, bound to a specific deployed contract.
func NewProxyContractInterfaceTransactor(address common.Address, transactor bind.ContractTransactor) (*ProxyContractInterfaceTransactor, error) {
	contract, err := bindProxyContractInterface(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &ProxyContractInterfaceTransactor{contract: contract}, nil
}

// NewProxyContractInterfaceFilterer creates a new log filterer instance of ProxyContractInterface, bound to a specific deployed contract.
func NewProxyContractInterfaceFilterer(address common.Address, filterer bind.ContractFilterer) (*ProxyContractInterfaceFilterer, error) {
	contract, err := bindProxyContractInterface(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &ProxyContractInterfaceFilterer{contract: contract}, nil
}

// bindProxyContractInterface binds a generic wrapper to an already deployed contract.
func bindProxyContractInterface(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(ProxyContractInterfaceABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_ProxyContractInterface *ProxyContractInterfaceRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _ProxyContractInterface.Contract.ProxyContractInterfaceCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_ProxyContractInterface *ProxyContractInterfaceRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _ProxyContractInterface.Contract.ProxyContractInterfaceTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_ProxyContractInterface *ProxyContractInterfaceRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _ProxyContractInterface.Contract.ProxyContractInterfaceTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_ProxyContractInterface *ProxyContractInterfaceCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _ProxyContractInterface.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_ProxyContractInterface *ProxyContractInterfaceTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _ProxyContractInterface.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_ProxyContractInterface *ProxyContractInterfaceTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _ProxyContractInterface.Contract.contract.Transact(opts, method, params...)
}

// GetProxyContract is a free data retrieval call binding the contract method 0xfc4fdd3d.
//
// Solidity: function getProxyContract(addr address) constant returns(address)
func (_ProxyContractInterface *ProxyContractInterfaceCaller) GetProxyContract(opts *bind.CallOpts, addr common.Address) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _ProxyContractInterface.contract.Call(opts, out, "getProxyContract", addr)
	return *ret0, err
}

// GetProxyContract is a free data retrieval call binding the contract method 0xfc4fdd3d.
//
// Solidity: function getProxyContract(addr address) constant returns(address)
func (_ProxyContractInterface *ProxyContractInterfaceSession) GetProxyContract(addr common.Address) (common.Address, error) {
	return _ProxyContractInterface.Contract.GetProxyContract(&_ProxyContractInterface.CallOpts, addr)
}

// GetProxyContract is a free data retrieval call binding the contract method 0xfc4fdd3d.
//
// Solidity: function getProxyContract(addr address) constant returns(address)
func (_ProxyContractInterface *ProxyContractInterfaceCallerSession) GetProxyContract(addr common.Address) (common.Address, error) {
	return _ProxyContractInterface.Contract.GetProxyContract(&_ProxyContractInterface.CallOpts, addr)
}
