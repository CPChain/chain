// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package contracts

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

// RptABI is the input ABI used to generate the binding from.
const RptABI = "[{\"constant\":false,\"inputs\":[{\"name\":\"_alpha\",\"type\":\"uint256\"}],\"name\":\"updateAlpha\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"omega\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"window\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_gamma\",\"type\":\"uint256\"}],\"name\":\"updateGamma\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"randomLevel\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_randomLevel\",\"type\":\"uint256\"}],\"name\":\"updateRandomLevel\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"psi\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"owner\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"beta\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_omega\",\"type\":\"uint256\"}],\"name\":\"updateOmega\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_beta\",\"type\":\"uint256\"}],\"name\":\"updateBeta\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"gamma\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_psi\",\"type\":\"uint256\"}],\"name\":\"updatePsi\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_window\",\"type\":\"uint256\"}],\"name\":\"updateWindow\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_alpha\",\"type\":\"uint256\"},{\"name\":\"_beta\",\"type\":\"uint256\"},{\"name\":\"_gamma\",\"type\":\"uint256\"},{\"name\":\"_psi\",\"type\":\"uint256\"},{\"name\":\"_omega\",\"type\":\"uint256\"},{\"name\":\"_window\",\"type\":\"uint256\"},{\"name\":\"_randomLevel\",\"type\":\"uint256\"}],\"name\":\"updateConfigs\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"alpha\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"blockNumber\",\"type\":\"uint256\"}],\"name\":\"UpdateConfigs\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"blockNumber\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"configName\",\"type\":\"string\"},{\"indexed\":false,\"name\":\"configValue\",\"type\":\"uint256\"}],\"name\":\"UpdateOneConfig\",\"type\":\"event\"}]"

// RptBin is the compiled bytecode used for deploying new contracts.
const RptBin = `0x60806040526032600055600f600155600a600255600f600355600a6004556004600555600560065534801561003357600080fd5b5060078054600160a060020a031916331790556106eb806100556000396000f3006080604052600436106100e55763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166306d2d3dc81146100ea5780632262a1b314610104578063461645bf1461012b5780636d8004c5146101405780638070cb8e1461015857806381cfcb4f1461016d57806386f87fdd146101855780638da5cb5b1461019a5780639faa3c91146101cb578063a23f52b8146101e0578063ac7dabbc146101f8578063b137392914610210578063b2f801c414610225578063b98f00561461023d578063bd5c5f8614610255578063db1d0fd51461027f575b600080fd5b3480156100f657600080fd5b50610102600435610294565b005b34801561011057600080fd5b5061011961030f565b60408051918252519081900360200190f35b34801561013757600080fd5b50610119610315565b34801561014c57600080fd5b5061010260043561031b565b34801561016457600080fd5b50610119610396565b34801561017957600080fd5b5061010260043561039c565b34801561019157600080fd5b50610119610417565b3480156101a657600080fd5b506101af61041d565b60408051600160a060020a039092168252519081900360200190f35b3480156101d757600080fd5b5061011961042c565b3480156101ec57600080fd5b50610102600435610432565b34801561020457600080fd5b506101026004356104ad565b34801561021c57600080fd5b50610119610528565b34801561023157600080fd5b5061010260043561052e565b34801561024957600080fd5b506101026004356105a8565b34801561026157600080fd5b5061010260043560243560443560643560843560a43560c435610623565b34801561028b57600080fd5b50610119610699565b600754600160a060020a031633146102ab57600080fd5b6000819055604080514381528082018390526060602082018190526005908201527f616c706861000000000000000000000000000000000000000000000000000000608082015290516000805160206106a08339815191529181900360a00190a150565b60045481565b60055481565b600754600160a060020a0316331461033257600080fd5b6002819055604080514381528082018390526060602082018190526005908201527f67616d6d61000000000000000000000000000000000000000000000000000000608082015290516000805160206106a08339815191529181900360a00190a150565b60065481565b600754600160a060020a031633146103b357600080fd5b600681905560408051438152808201839052606060208201819052600b908201527f72616e646f6d4c6576656c000000000000000000000000000000000000000000608082015290516000805160206106a08339815191529181900360a00190a150565b60035481565b600754600160a060020a031681565b60015481565b600754600160a060020a0316331461044957600080fd5b6004819055604080514381528082018390526060602082018190526005908201527f6f6d656761000000000000000000000000000000000000000000000000000000608082015290516000805160206106a08339815191529181900360a00190a150565b600754600160a060020a031633146104c457600080fd5b6001819055604080514381528082018390526060602082018190526004908201527f6265746100000000000000000000000000000000000000000000000000000000608082015290516000805160206106a08339815191529181900360a00190a150565b60025481565b600754600160a060020a0316331461054557600080fd5b6003818155604080514381528082018490526060602082018190528101929092527f70736900000000000000000000000000000000000000000000000000000000006080830152516000805160206106a08339815191529181900360a00190a150565b600754600160a060020a031633146105bf57600080fd5b6005819055604080514381528082018390526060602082018190526006908201527f77696e646f770000000000000000000000000000000000000000000000000000608082015290516000805160206106a08339815191529181900360a00190a150565b600754600160a060020a0316331461063a57600080fd5b60008790556001869055600285905560038490556004839055600582905560068190556040805143815290517f78a3671679b68721aaad9eb74535be0be119bd34c0efa671eb6ab3210d1fe2579181900360200190a150505050505050565b6000548156007c2d85cf45868065466ed7df2e23f26349626794d112e41a734a4e34727fcb21a165627a7a72305820c62782755e007d008f9ee6ea04ed5ad95378f94403c7e010891306c8e15ca4680029`

// DeployRpt deploys a new cpchain contract, binding an instance of Rpt to it.
func DeployRpt(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *Rpt, error) {
	parsed, err := abi.JSON(strings.NewReader(RptABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(RptBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &Rpt{RptCaller: RptCaller{contract: contract}, RptTransactor: RptTransactor{contract: contract}, RptFilterer: RptFilterer{contract: contract}}, nil
}

// Rpt is an auto generated Go binding around an cpchain contract.
type Rpt struct {
	RptCaller     // Read-only binding to the contract
	RptTransactor // Write-only binding to the contract
	RptFilterer   // Log filterer for contract events
}

// RptCaller is an auto generated read-only Go binding around an cpchain contract.
type RptCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RptTransactor is an auto generated write-only Go binding around an cpchain contract.
type RptTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RptFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type RptFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RptSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type RptSession struct {
	Contract     *Rpt              // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// RptCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type RptCallerSession struct {
	Contract *RptCaller    // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts // Call options to use throughout this session
}

// RptTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type RptTransactorSession struct {
	Contract     *RptTransactor    // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// RptRaw is an auto generated low-level Go binding around an cpchain contract.
type RptRaw struct {
	Contract *Rpt // Generic contract binding to access the raw methods on
}

// RptCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type RptCallerRaw struct {
	Contract *RptCaller // Generic read-only contract binding to access the raw methods on
}

// RptTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type RptTransactorRaw struct {
	Contract *RptTransactor // Generic write-only contract binding to access the raw methods on
}

// NewRpt creates a new instance of Rpt, bound to a specific deployed contract.
func NewRpt(address common.Address, backend bind.ContractBackend) (*Rpt, error) {
	contract, err := bindRpt(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &Rpt{RptCaller: RptCaller{contract: contract}, RptTransactor: RptTransactor{contract: contract}, RptFilterer: RptFilterer{contract: contract}}, nil
}

// NewRptCaller creates a new read-only instance of Rpt, bound to a specific deployed contract.
func NewRptCaller(address common.Address, caller bind.ContractCaller) (*RptCaller, error) {
	contract, err := bindRpt(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &RptCaller{contract: contract}, nil
}

// NewRptTransactor creates a new write-only instance of Rpt, bound to a specific deployed contract.
func NewRptTransactor(address common.Address, transactor bind.ContractTransactor) (*RptTransactor, error) {
	contract, err := bindRpt(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &RptTransactor{contract: contract}, nil
}

// NewRptFilterer creates a new log filterer instance of Rpt, bound to a specific deployed contract.
func NewRptFilterer(address common.Address, filterer bind.ContractFilterer) (*RptFilterer, error) {
	contract, err := bindRpt(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &RptFilterer{contract: contract}, nil
}

// bindRpt binds a generic wrapper to an already deployed contract.
func bindRpt(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(RptABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Rpt *RptRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Rpt.Contract.RptCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Rpt *RptRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Rpt.Contract.RptTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Rpt *RptRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Rpt.Contract.RptTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Rpt *RptCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Rpt.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Rpt *RptTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Rpt.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Rpt *RptTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Rpt.Contract.contract.Transact(opts, method, params...)
}

// Alpha is a free data retrieval call binding the contract method 0xdb1d0fd5.
//
// Solidity: function alpha() constant returns(uint256)
func (_Rpt *RptCaller) Alpha(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "alpha")
	return *ret0, err
}

// Alpha is a free data retrieval call binding the contract method 0xdb1d0fd5.
//
// Solidity: function alpha() constant returns(uint256)
func (_Rpt *RptSession) Alpha() (*big.Int, error) {
	return _Rpt.Contract.Alpha(&_Rpt.CallOpts)
}

// Alpha is a free data retrieval call binding the contract method 0xdb1d0fd5.
//
// Solidity: function alpha() constant returns(uint256)
func (_Rpt *RptCallerSession) Alpha() (*big.Int, error) {
	return _Rpt.Contract.Alpha(&_Rpt.CallOpts)
}

// Beta is a free data retrieval call binding the contract method 0x9faa3c91.
//
// Solidity: function beta() constant returns(uint256)
func (_Rpt *RptCaller) Beta(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "beta")
	return *ret0, err
}

// Beta is a free data retrieval call binding the contract method 0x9faa3c91.
//
// Solidity: function beta() constant returns(uint256)
func (_Rpt *RptSession) Beta() (*big.Int, error) {
	return _Rpt.Contract.Beta(&_Rpt.CallOpts)
}

// Beta is a free data retrieval call binding the contract method 0x9faa3c91.
//
// Solidity: function beta() constant returns(uint256)
func (_Rpt *RptCallerSession) Beta() (*big.Int, error) {
	return _Rpt.Contract.Beta(&_Rpt.CallOpts)
}

// Gamma is a free data retrieval call binding the contract method 0xb1373929.
//
// Solidity: function gamma() constant returns(uint256)
func (_Rpt *RptCaller) Gamma(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "gamma")
	return *ret0, err
}

// Gamma is a free data retrieval call binding the contract method 0xb1373929.
//
// Solidity: function gamma() constant returns(uint256)
func (_Rpt *RptSession) Gamma() (*big.Int, error) {
	return _Rpt.Contract.Gamma(&_Rpt.CallOpts)
}

// Gamma is a free data retrieval call binding the contract method 0xb1373929.
//
// Solidity: function gamma() constant returns(uint256)
func (_Rpt *RptCallerSession) Gamma() (*big.Int, error) {
	return _Rpt.Contract.Gamma(&_Rpt.CallOpts)
}

// Omega is a free data retrieval call binding the contract method 0x2262a1b3.
//
// Solidity: function omega() constant returns(uint256)
func (_Rpt *RptCaller) Omega(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "omega")
	return *ret0, err
}

// Omega is a free data retrieval call binding the contract method 0x2262a1b3.
//
// Solidity: function omega() constant returns(uint256)
func (_Rpt *RptSession) Omega() (*big.Int, error) {
	return _Rpt.Contract.Omega(&_Rpt.CallOpts)
}

// Omega is a free data retrieval call binding the contract method 0x2262a1b3.
//
// Solidity: function omega() constant returns(uint256)
func (_Rpt *RptCallerSession) Omega() (*big.Int, error) {
	return _Rpt.Contract.Omega(&_Rpt.CallOpts)
}

// Owner is a free data retrieval call binding the contract method 0x8da5cb5b.
//
// Solidity: function owner() constant returns(address)
func (_Rpt *RptCaller) Owner(opts *bind.CallOpts) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "owner")
	return *ret0, err
}

// Owner is a free data retrieval call binding the contract method 0x8da5cb5b.
//
// Solidity: function owner() constant returns(address)
func (_Rpt *RptSession) Owner() (common.Address, error) {
	return _Rpt.Contract.Owner(&_Rpt.CallOpts)
}

// Owner is a free data retrieval call binding the contract method 0x8da5cb5b.
//
// Solidity: function owner() constant returns(address)
func (_Rpt *RptCallerSession) Owner() (common.Address, error) {
	return _Rpt.Contract.Owner(&_Rpt.CallOpts)
}

// Psi is a free data retrieval call binding the contract method 0x86f87fdd.
//
// Solidity: function psi() constant returns(uint256)
func (_Rpt *RptCaller) Psi(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "psi")
	return *ret0, err
}

// Psi is a free data retrieval call binding the contract method 0x86f87fdd.
//
// Solidity: function psi() constant returns(uint256)
func (_Rpt *RptSession) Psi() (*big.Int, error) {
	return _Rpt.Contract.Psi(&_Rpt.CallOpts)
}

// Psi is a free data retrieval call binding the contract method 0x86f87fdd.
//
// Solidity: function psi() constant returns(uint256)
func (_Rpt *RptCallerSession) Psi() (*big.Int, error) {
	return _Rpt.Contract.Psi(&_Rpt.CallOpts)
}

// RandomLevel is a free data retrieval call binding the contract method 0x8070cb8e.
//
// Solidity: function randomLevel() constant returns(uint256)
func (_Rpt *RptCaller) RandomLevel(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "randomLevel")
	return *ret0, err
}

// RandomLevel is a free data retrieval call binding the contract method 0x8070cb8e.
//
// Solidity: function randomLevel() constant returns(uint256)
func (_Rpt *RptSession) RandomLevel() (*big.Int, error) {
	return _Rpt.Contract.RandomLevel(&_Rpt.CallOpts)
}

// RandomLevel is a free data retrieval call binding the contract method 0x8070cb8e.
//
// Solidity: function randomLevel() constant returns(uint256)
func (_Rpt *RptCallerSession) RandomLevel() (*big.Int, error) {
	return _Rpt.Contract.RandomLevel(&_Rpt.CallOpts)
}

// Window is a free data retrieval call binding the contract method 0x461645bf.
//
// Solidity: function window() constant returns(uint256)
func (_Rpt *RptCaller) Window(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "window")
	return *ret0, err
}

// Window is a free data retrieval call binding the contract method 0x461645bf.
//
// Solidity: function window() constant returns(uint256)
func (_Rpt *RptSession) Window() (*big.Int, error) {
	return _Rpt.Contract.Window(&_Rpt.CallOpts)
}

// Window is a free data retrieval call binding the contract method 0x461645bf.
//
// Solidity: function window() constant returns(uint256)
func (_Rpt *RptCallerSession) Window() (*big.Int, error) {
	return _Rpt.Contract.Window(&_Rpt.CallOpts)
}

// UpdateAlpha is a paid mutator transaction binding the contract method 0x06d2d3dc.
//
// Solidity: function updateAlpha(_alpha uint256) returns()
func (_Rpt *RptTransactor) UpdateAlpha(opts *bind.TransactOpts, _alpha *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateAlpha", _alpha)
}

// UpdateAlpha is a paid mutator transaction binding the contract method 0x06d2d3dc.
//
// Solidity: function updateAlpha(_alpha uint256) returns()
func (_Rpt *RptSession) UpdateAlpha(_alpha *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateAlpha(&_Rpt.TransactOpts, _alpha)
}

// UpdateAlpha is a paid mutator transaction binding the contract method 0x06d2d3dc.
//
// Solidity: function updateAlpha(_alpha uint256) returns()
func (_Rpt *RptTransactorSession) UpdateAlpha(_alpha *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateAlpha(&_Rpt.TransactOpts, _alpha)
}

// UpdateBeta is a paid mutator transaction binding the contract method 0xac7dabbc.
//
// Solidity: function updateBeta(_beta uint256) returns()
func (_Rpt *RptTransactor) UpdateBeta(opts *bind.TransactOpts, _beta *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateBeta", _beta)
}

// UpdateBeta is a paid mutator transaction binding the contract method 0xac7dabbc.
//
// Solidity: function updateBeta(_beta uint256) returns()
func (_Rpt *RptSession) UpdateBeta(_beta *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateBeta(&_Rpt.TransactOpts, _beta)
}

// UpdateBeta is a paid mutator transaction binding the contract method 0xac7dabbc.
//
// Solidity: function updateBeta(_beta uint256) returns()
func (_Rpt *RptTransactorSession) UpdateBeta(_beta *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateBeta(&_Rpt.TransactOpts, _beta)
}

// UpdateConfigs is a paid mutator transaction binding the contract method 0xbd5c5f86.
//
// Solidity: function updateConfigs(_alpha uint256, _beta uint256, _gamma uint256, _psi uint256, _omega uint256, _window uint256, _randomLevel uint256) returns()
func (_Rpt *RptTransactor) UpdateConfigs(opts *bind.TransactOpts, _alpha *big.Int, _beta *big.Int, _gamma *big.Int, _psi *big.Int, _omega *big.Int, _window *big.Int, _randomLevel *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateConfigs", _alpha, _beta, _gamma, _psi, _omega, _window, _randomLevel)
}

// UpdateConfigs is a paid mutator transaction binding the contract method 0xbd5c5f86.
//
// Solidity: function updateConfigs(_alpha uint256, _beta uint256, _gamma uint256, _psi uint256, _omega uint256, _window uint256, _randomLevel uint256) returns()
func (_Rpt *RptSession) UpdateConfigs(_alpha *big.Int, _beta *big.Int, _gamma *big.Int, _psi *big.Int, _omega *big.Int, _window *big.Int, _randomLevel *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateConfigs(&_Rpt.TransactOpts, _alpha, _beta, _gamma, _psi, _omega, _window, _randomLevel)
}

// UpdateConfigs is a paid mutator transaction binding the contract method 0xbd5c5f86.
//
// Solidity: function updateConfigs(_alpha uint256, _beta uint256, _gamma uint256, _psi uint256, _omega uint256, _window uint256, _randomLevel uint256) returns()
func (_Rpt *RptTransactorSession) UpdateConfigs(_alpha *big.Int, _beta *big.Int, _gamma *big.Int, _psi *big.Int, _omega *big.Int, _window *big.Int, _randomLevel *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateConfigs(&_Rpt.TransactOpts, _alpha, _beta, _gamma, _psi, _omega, _window, _randomLevel)
}

// UpdateGamma is a paid mutator transaction binding the contract method 0x6d8004c5.
//
// Solidity: function updateGamma(_gamma uint256) returns()
func (_Rpt *RptTransactor) UpdateGamma(opts *bind.TransactOpts, _gamma *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateGamma", _gamma)
}

// UpdateGamma is a paid mutator transaction binding the contract method 0x6d8004c5.
//
// Solidity: function updateGamma(_gamma uint256) returns()
func (_Rpt *RptSession) UpdateGamma(_gamma *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateGamma(&_Rpt.TransactOpts, _gamma)
}

// UpdateGamma is a paid mutator transaction binding the contract method 0x6d8004c5.
//
// Solidity: function updateGamma(_gamma uint256) returns()
func (_Rpt *RptTransactorSession) UpdateGamma(_gamma *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateGamma(&_Rpt.TransactOpts, _gamma)
}

// UpdateOmega is a paid mutator transaction binding the contract method 0xa23f52b8.
//
// Solidity: function updateOmega(_omega uint256) returns()
func (_Rpt *RptTransactor) UpdateOmega(opts *bind.TransactOpts, _omega *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateOmega", _omega)
}

// UpdateOmega is a paid mutator transaction binding the contract method 0xa23f52b8.
//
// Solidity: function updateOmega(_omega uint256) returns()
func (_Rpt *RptSession) UpdateOmega(_omega *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateOmega(&_Rpt.TransactOpts, _omega)
}

// UpdateOmega is a paid mutator transaction binding the contract method 0xa23f52b8.
//
// Solidity: function updateOmega(_omega uint256) returns()
func (_Rpt *RptTransactorSession) UpdateOmega(_omega *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateOmega(&_Rpt.TransactOpts, _omega)
}

// UpdatePsi is a paid mutator transaction binding the contract method 0xb2f801c4.
//
// Solidity: function updatePsi(_psi uint256) returns()
func (_Rpt *RptTransactor) UpdatePsi(opts *bind.TransactOpts, _psi *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updatePsi", _psi)
}

// UpdatePsi is a paid mutator transaction binding the contract method 0xb2f801c4.
//
// Solidity: function updatePsi(_psi uint256) returns()
func (_Rpt *RptSession) UpdatePsi(_psi *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdatePsi(&_Rpt.TransactOpts, _psi)
}

// UpdatePsi is a paid mutator transaction binding the contract method 0xb2f801c4.
//
// Solidity: function updatePsi(_psi uint256) returns()
func (_Rpt *RptTransactorSession) UpdatePsi(_psi *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdatePsi(&_Rpt.TransactOpts, _psi)
}

// UpdateRandomLevel is a paid mutator transaction binding the contract method 0x81cfcb4f.
//
// Solidity: function updateRandomLevel(_randomLevel uint256) returns()
func (_Rpt *RptTransactor) UpdateRandomLevel(opts *bind.TransactOpts, _randomLevel *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateRandomLevel", _randomLevel)
}

// UpdateRandomLevel is a paid mutator transaction binding the contract method 0x81cfcb4f.
//
// Solidity: function updateRandomLevel(_randomLevel uint256) returns()
func (_Rpt *RptSession) UpdateRandomLevel(_randomLevel *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateRandomLevel(&_Rpt.TransactOpts, _randomLevel)
}

// UpdateRandomLevel is a paid mutator transaction binding the contract method 0x81cfcb4f.
//
// Solidity: function updateRandomLevel(_randomLevel uint256) returns()
func (_Rpt *RptTransactorSession) UpdateRandomLevel(_randomLevel *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateRandomLevel(&_Rpt.TransactOpts, _randomLevel)
}

// UpdateWindow is a paid mutator transaction binding the contract method 0xb98f0056.
//
// Solidity: function updateWindow(_window uint256) returns()
func (_Rpt *RptTransactor) UpdateWindow(opts *bind.TransactOpts, _window *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateWindow", _window)
}

// UpdateWindow is a paid mutator transaction binding the contract method 0xb98f0056.
//
// Solidity: function updateWindow(_window uint256) returns()
func (_Rpt *RptSession) UpdateWindow(_window *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateWindow(&_Rpt.TransactOpts, _window)
}

// UpdateWindow is a paid mutator transaction binding the contract method 0xb98f0056.
//
// Solidity: function updateWindow(_window uint256) returns()
func (_Rpt *RptTransactorSession) UpdateWindow(_window *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateWindow(&_Rpt.TransactOpts, _window)
}

// RptUpdateConfigsIterator is returned from FilterUpdateConfigs and is used to iterate over the raw logs and unpacked data for UpdateConfigs events raised by the Rpt contract.
type RptUpdateConfigsIterator struct {
	Event *RptUpdateConfigs // Event containing the contract specifics and raw log

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
func (it *RptUpdateConfigsIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RptUpdateConfigs)
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
		it.Event = new(RptUpdateConfigs)
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
func (it *RptUpdateConfigsIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RptUpdateConfigsIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RptUpdateConfigs represents a UpdateConfigs event raised by the Rpt contract.
type RptUpdateConfigs struct {
	BlockNumber *big.Int
	Raw         types.Log // Blockchain specific contextual infos
}

// FilterUpdateConfigs is a free log retrieval operation binding the contract event 0x78a3671679b68721aaad9eb74535be0be119bd34c0efa671eb6ab3210d1fe257.
//
// Solidity: e UpdateConfigs(blockNumber uint256)
func (_Rpt *RptFilterer) FilterUpdateConfigs(opts *bind.FilterOpts) (*RptUpdateConfigsIterator, error) {

	logs, sub, err := _Rpt.contract.FilterLogs(opts, "UpdateConfigs")
	if err != nil {
		return nil, err
	}
	return &RptUpdateConfigsIterator{contract: _Rpt.contract, event: "UpdateConfigs", logs: logs, sub: sub}, nil
}

// WatchUpdateConfigs is a free log subscription operation binding the contract event 0x78a3671679b68721aaad9eb74535be0be119bd34c0efa671eb6ab3210d1fe257.
//
// Solidity: e UpdateConfigs(blockNumber uint256)
func (_Rpt *RptFilterer) WatchUpdateConfigs(opts *bind.WatchOpts, sink chan<- *RptUpdateConfigs) (event.Subscription, error) {

	logs, sub, err := _Rpt.contract.WatchLogs(opts, "UpdateConfigs")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RptUpdateConfigs)
				if err := _Rpt.contract.UnpackLog(event, "UpdateConfigs", log); err != nil {
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

// RptUpdateOneConfigIterator is returned from FilterUpdateOneConfig and is used to iterate over the raw logs and unpacked data for UpdateOneConfig events raised by the Rpt contract.
type RptUpdateOneConfigIterator struct {
	Event *RptUpdateOneConfig // Event containing the contract specifics and raw log

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
func (it *RptUpdateOneConfigIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RptUpdateOneConfig)
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
		it.Event = new(RptUpdateOneConfig)
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
func (it *RptUpdateOneConfigIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RptUpdateOneConfigIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RptUpdateOneConfig represents a UpdateOneConfig event raised by the Rpt contract.
type RptUpdateOneConfig struct {
	BlockNumber *big.Int
	ConfigName  string
	ConfigValue *big.Int
	Raw         types.Log // Blockchain specific contextual infos
}

// FilterUpdateOneConfig is a free log retrieval operation binding the contract event 0x7c2d85cf45868065466ed7df2e23f26349626794d112e41a734a4e34727fcb21.
//
// Solidity: e UpdateOneConfig(blockNumber uint256, configName string, configValue uint256)
func (_Rpt *RptFilterer) FilterUpdateOneConfig(opts *bind.FilterOpts) (*RptUpdateOneConfigIterator, error) {

	logs, sub, err := _Rpt.contract.FilterLogs(opts, "UpdateOneConfig")
	if err != nil {
		return nil, err
	}
	return &RptUpdateOneConfigIterator{contract: _Rpt.contract, event: "UpdateOneConfig", logs: logs, sub: sub}, nil
}

// WatchUpdateOneConfig is a free log subscription operation binding the contract event 0x7c2d85cf45868065466ed7df2e23f26349626794d112e41a734a4e34727fcb21.
//
// Solidity: e UpdateOneConfig(blockNumber uint256, configName string, configValue uint256)
func (_Rpt *RptFilterer) WatchUpdateOneConfig(opts *bind.WatchOpts, sink chan<- *RptUpdateOneConfig) (event.Subscription, error) {

	logs, sub, err := _Rpt.contract.WatchLogs(opts, "UpdateOneConfig")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RptUpdateOneConfig)
				if err := _Rpt.contract.UnpackLog(event, "UpdateOneConfig", log); err != nil {
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
