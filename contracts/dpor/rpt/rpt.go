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
const RptABI = "[{\"constant\":false,\"inputs\":[{\"name\":\"_alpha\",\"type\":\"uint256\"}],\"name\":\"updateAlpha\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"totalSeats\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"omega\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_lowRptPercentage\",\"type\":\"uint256\"}],\"name\":\"updateLowRptPercentage\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"window\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_lowRptSeats\",\"type\":\"uint256\"}],\"name\":\"updateLowRptSeats\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_gamma\",\"type\":\"uint256\"}],\"name\":\"updateGamma\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_lowRptPercentage\",\"type\":\"uint256\"},{\"name\":\"_totalSeats\",\"type\":\"uint256\"},{\"name\":\"_lowRptSeats\",\"type\":\"uint256\"}],\"name\":\"updateElectionConfigs\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"psi\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_totalSeats\",\"type\":\"uint256\"}],\"name\":\"updateTotalSeats\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"beta\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_omega\",\"type\":\"uint256\"}],\"name\":\"updateOmega\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_beta\",\"type\":\"uint256\"}],\"name\":\"updateBeta\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"gamma\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_psi\",\"type\":\"uint256\"}],\"name\":\"updatePsi\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_window\",\"type\":\"uint256\"}],\"name\":\"updateWindow\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"alpha\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_alpha\",\"type\":\"uint256\"},{\"name\":\"_beta\",\"type\":\"uint256\"},{\"name\":\"_gamma\",\"type\":\"uint256\"},{\"name\":\"_psi\",\"type\":\"uint256\"},{\"name\":\"_omega\",\"type\":\"uint256\"},{\"name\":\"_window\",\"type\":\"uint256\"}],\"name\":\"updateWeightConfigs\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"lowRptPercentage\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"lowRptSeats\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"blockNumber\",\"type\":\"uint256\"}],\"name\":\"UpdateWeightConfigs\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"blockNumber\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"configName\",\"type\":\"string\"},{\"indexed\":false,\"name\":\"configValue\",\"type\":\"uint256\"}],\"name\":\"UpdateOneConfig\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"blockNumber\",\"type\":\"uint256\"}],\"name\":\"UpdateElectionConfigs\",\"type\":\"event\"}]"

// RptBin is the compiled bytecode used for deploying new contracts.
const RptBin = `0x60806040526032600055600f600155600a600255600f600355600a600455606460055560466006556008600755600260085534801561003d57600080fd5b5060098054600160a060020a031916331790556109ce8061005f6000396000f3006080604052600436106101115763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166306d2d3dc81146101165780631ffc615e146101305780632262a1b314610157578063255c45901461016c578063461645bf146101845780636479b8e6146101995780636d8004c5146101b1578063854c42c5146101c957806386f87fdd146101e757806390530bf0146101fc5780639faa3c9114610214578063a23f52b814610229578063ac7dabbc14610241578063b137392914610259578063b2f801c41461026e578063b98f005614610286578063db1d0fd51461029e578063f182c59c146102b3578063f75ca7ff146102da578063fb2eb7f6146102ef575b600080fd5b34801561012257600080fd5b5061012e600435610304565b005b34801561013c57600080fd5b5061014561038d565b60408051918252519081900360200190f35b34801561016357600080fd5b50610145610393565b34801561017857600080fd5b5061012e600435610399565b34801561019057600080fd5b50610145610422565b3480156101a557600080fd5b5061012e600435610428565b3480156101bd57600080fd5b5061012e6004356104b2565b3480156101d557600080fd5b5061012e60043560243560443561053b565b3480156101f357600080fd5b506101456105c2565b34801561020857600080fd5b5061012e6004356105c8565b34801561022057600080fd5b50610145610661565b34801561023557600080fd5b5061012e600435610667565b34801561024d57600080fd5b5061012e6004356106f0565b34801561026557600080fd5b50610145610779565b34801561027a57600080fd5b5061012e60043561077f565b34801561029257600080fd5b5061012e600435610807565b3480156102aa57600080fd5b5061014561089f565b3480156102bf57600080fd5b5061012e60043560243560443560643560843560a4356108a5565b3480156102e657600080fd5b50610145610976565b3480156102fb57600080fd5b5061014561097c565b600954600160a060020a0316331461031b57600080fd5b606481111561032957600080fd5b6000819055604080514381528082018390526060602082018190526005908201527f616c706861000000000000000000000000000000000000000000000000000000608082015290516000805160206109838339815191529181900360a00190a150565b60075481565b60045481565b600954600160a060020a031633146103b057600080fd5b60648111156103be57600080fd5b6006819055604080514381528082018390526060602082018190526010908201527f6c6f7752707450657263656e7461676500000000000000000000000000000000608082015290516000805160206109838339815191529181900360a00190a150565b60055481565b600954600160a060020a0316331461043f57600080fd5b60075481111561044e57600080fd5b600881905560408051438152808201839052606060208201819052600b908201527f6c6f775270745365617473000000000000000000000000000000000000000000608082015290516000805160206109838339815191529181900360a00190a150565b600954600160a060020a031633146104c957600080fd5b60648111156104d757600080fd5b6002819055604080514381528082018390526060602082018190526005908201527f67616d6d61000000000000000000000000000000000000000000000000000000608082015290516000805160206109838339815191529181900360a00190a150565b600954600160a060020a0316331461055257600080fd5b60648311158015610564575060088211155b80156105705750818111155b151561057b57600080fd5b6006839055600782905560088190556040805143815290517f09e649367469a85db638685b74f92f1ef17cdebb4610b4c42b7da19c2f1b189c9181900360200190a1505050565b60035481565b600954600160a060020a031633146105df57600080fd5b600881111580156105f257506008548110155b15156105fd57600080fd5b600781905560408051438152808201839052606060208201819052600a908201527f746f74616c536561747300000000000000000000000000000000000000000000608082015290516000805160206109838339815191529181900360a00190a150565b60015481565b600954600160a060020a0316331461067e57600080fd5b606481111561068c57600080fd5b6004819055604080514381528082018390526060602082018190526005908201527f6f6d656761000000000000000000000000000000000000000000000000000000608082015290516000805160206109838339815191529181900360a00190a150565b600954600160a060020a0316331461070757600080fd5b606481111561071557600080fd5b6001819055604080514381528082018390526060602082018190526004908201527f6265746100000000000000000000000000000000000000000000000000000000608082015290516000805160206109838339815191529181900360a00190a150565b60025481565b600954600160a060020a0316331461079657600080fd5b60648111156107a457600080fd5b6003818155604080514381528082018490526060602082018190528101929092527f70736900000000000000000000000000000000000000000000000000000000006080830152516000805160206109838339815191529181900360a00190a150565b600954600160a060020a0316331461081e57600080fd5b600a8110158015610830575060648111155b151561083b57600080fd5b6005819055604080514381528082018390526060602082018190526006908201527f77696e646f770000000000000000000000000000000000000000000000000000608082015290516000805160206109838339815191529181900360a00190a150565b60005481565b600954600160a060020a031633146108bc57600080fd5b600a81101580156108ce575060648111155b15156108d957600080fd5b606486111580156108eb575060648511155b80156108f8575060648411155b8015610905575060648311155b8015610912575060648211155b151561091d57600080fd5b6000869055600185905560028490556003839055600482905560058190556040805143815290517f94cb95e42d1f9f5b3e73da8fddc18ba25b0c89408eb91f64e417c59c6833a82b9181900360200190a1505050505050565b60065481565b6008548156007c2d85cf45868065466ed7df2e23f26349626794d112e41a734a4e34727fcb21a165627a7a723058208e10c9f426cb2dc3a0c2d3031469c57a795df23d94f67433dfcf056e8daa5d5a0029`

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

// LowRptPercentage is a free data retrieval call binding the contract method 0xf75ca7ff.
//
// Solidity: function lowRptPercentage() constant returns(uint256)
func (_Rpt *RptCaller) LowRptPercentage(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "lowRptPercentage")
	return *ret0, err
}

// LowRptPercentage is a free data retrieval call binding the contract method 0xf75ca7ff.
//
// Solidity: function lowRptPercentage() constant returns(uint256)
func (_Rpt *RptSession) LowRptPercentage() (*big.Int, error) {
	return _Rpt.Contract.LowRptPercentage(&_Rpt.CallOpts)
}

// LowRptPercentage is a free data retrieval call binding the contract method 0xf75ca7ff.
//
// Solidity: function lowRptPercentage() constant returns(uint256)
func (_Rpt *RptCallerSession) LowRptPercentage() (*big.Int, error) {
	return _Rpt.Contract.LowRptPercentage(&_Rpt.CallOpts)
}

// LowRptSeats is a free data retrieval call binding the contract method 0xfb2eb7f6.
//
// Solidity: function lowRptSeats() constant returns(uint256)
func (_Rpt *RptCaller) LowRptSeats(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "lowRptSeats")
	return *ret0, err
}

// LowRptSeats is a free data retrieval call binding the contract method 0xfb2eb7f6.
//
// Solidity: function lowRptSeats() constant returns(uint256)
func (_Rpt *RptSession) LowRptSeats() (*big.Int, error) {
	return _Rpt.Contract.LowRptSeats(&_Rpt.CallOpts)
}

// LowRptSeats is a free data retrieval call binding the contract method 0xfb2eb7f6.
//
// Solidity: function lowRptSeats() constant returns(uint256)
func (_Rpt *RptCallerSession) LowRptSeats() (*big.Int, error) {
	return _Rpt.Contract.LowRptSeats(&_Rpt.CallOpts)
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

// TotalSeats is a free data retrieval call binding the contract method 0x1ffc615e.
//
// Solidity: function totalSeats() constant returns(uint256)
func (_Rpt *RptCaller) TotalSeats(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "totalSeats")
	return *ret0, err
}

// TotalSeats is a free data retrieval call binding the contract method 0x1ffc615e.
//
// Solidity: function totalSeats() constant returns(uint256)
func (_Rpt *RptSession) TotalSeats() (*big.Int, error) {
	return _Rpt.Contract.TotalSeats(&_Rpt.CallOpts)
}

// TotalSeats is a free data retrieval call binding the contract method 0x1ffc615e.
//
// Solidity: function totalSeats() constant returns(uint256)
func (_Rpt *RptCallerSession) TotalSeats() (*big.Int, error) {
	return _Rpt.Contract.TotalSeats(&_Rpt.CallOpts)
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

// UpdateElectionConfigs is a paid mutator transaction binding the contract method 0x854c42c5.
//
// Solidity: function updateElectionConfigs(_lowRptPercentage uint256, _totalSeats uint256, _lowRptSeats uint256) returns()
func (_Rpt *RptTransactor) UpdateElectionConfigs(opts *bind.TransactOpts, _lowRptPercentage *big.Int, _totalSeats *big.Int, _lowRptSeats *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateElectionConfigs", _lowRptPercentage, _totalSeats, _lowRptSeats)
}

// UpdateElectionConfigs is a paid mutator transaction binding the contract method 0x854c42c5.
//
// Solidity: function updateElectionConfigs(_lowRptPercentage uint256, _totalSeats uint256, _lowRptSeats uint256) returns()
func (_Rpt *RptSession) UpdateElectionConfigs(_lowRptPercentage *big.Int, _totalSeats *big.Int, _lowRptSeats *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateElectionConfigs(&_Rpt.TransactOpts, _lowRptPercentage, _totalSeats, _lowRptSeats)
}

// UpdateElectionConfigs is a paid mutator transaction binding the contract method 0x854c42c5.
//
// Solidity: function updateElectionConfigs(_lowRptPercentage uint256, _totalSeats uint256, _lowRptSeats uint256) returns()
func (_Rpt *RptTransactorSession) UpdateElectionConfigs(_lowRptPercentage *big.Int, _totalSeats *big.Int, _lowRptSeats *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateElectionConfigs(&_Rpt.TransactOpts, _lowRptPercentage, _totalSeats, _lowRptSeats)
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

// UpdateLowRptPercentage is a paid mutator transaction binding the contract method 0x255c4590.
//
// Solidity: function updateLowRptPercentage(_lowRptPercentage uint256) returns()
func (_Rpt *RptTransactor) UpdateLowRptPercentage(opts *bind.TransactOpts, _lowRptPercentage *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateLowRptPercentage", _lowRptPercentage)
}

// UpdateLowRptPercentage is a paid mutator transaction binding the contract method 0x255c4590.
//
// Solidity: function updateLowRptPercentage(_lowRptPercentage uint256) returns()
func (_Rpt *RptSession) UpdateLowRptPercentage(_lowRptPercentage *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateLowRptPercentage(&_Rpt.TransactOpts, _lowRptPercentage)
}

// UpdateLowRptPercentage is a paid mutator transaction binding the contract method 0x255c4590.
//
// Solidity: function updateLowRptPercentage(_lowRptPercentage uint256) returns()
func (_Rpt *RptTransactorSession) UpdateLowRptPercentage(_lowRptPercentage *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateLowRptPercentage(&_Rpt.TransactOpts, _lowRptPercentage)
}

// UpdateLowRptSeats is a paid mutator transaction binding the contract method 0x6479b8e6.
//
// Solidity: function updateLowRptSeats(_lowRptSeats uint256) returns()
func (_Rpt *RptTransactor) UpdateLowRptSeats(opts *bind.TransactOpts, _lowRptSeats *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateLowRptSeats", _lowRptSeats)
}

// UpdateLowRptSeats is a paid mutator transaction binding the contract method 0x6479b8e6.
//
// Solidity: function updateLowRptSeats(_lowRptSeats uint256) returns()
func (_Rpt *RptSession) UpdateLowRptSeats(_lowRptSeats *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateLowRptSeats(&_Rpt.TransactOpts, _lowRptSeats)
}

// UpdateLowRptSeats is a paid mutator transaction binding the contract method 0x6479b8e6.
//
// Solidity: function updateLowRptSeats(_lowRptSeats uint256) returns()
func (_Rpt *RptTransactorSession) UpdateLowRptSeats(_lowRptSeats *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateLowRptSeats(&_Rpt.TransactOpts, _lowRptSeats)
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

// UpdateTotalSeats is a paid mutator transaction binding the contract method 0x90530bf0.
//
// Solidity: function updateTotalSeats(_totalSeats uint256) returns()
func (_Rpt *RptTransactor) UpdateTotalSeats(opts *bind.TransactOpts, _totalSeats *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateTotalSeats", _totalSeats)
}

// UpdateTotalSeats is a paid mutator transaction binding the contract method 0x90530bf0.
//
// Solidity: function updateTotalSeats(_totalSeats uint256) returns()
func (_Rpt *RptSession) UpdateTotalSeats(_totalSeats *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateTotalSeats(&_Rpt.TransactOpts, _totalSeats)
}

// UpdateTotalSeats is a paid mutator transaction binding the contract method 0x90530bf0.
//
// Solidity: function updateTotalSeats(_totalSeats uint256) returns()
func (_Rpt *RptTransactorSession) UpdateTotalSeats(_totalSeats *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateTotalSeats(&_Rpt.TransactOpts, _totalSeats)
}

// UpdateWeightConfigs is a paid mutator transaction binding the contract method 0xf182c59c.
//
// Solidity: function updateWeightConfigs(_alpha uint256, _beta uint256, _gamma uint256, _psi uint256, _omega uint256, _window uint256) returns()
func (_Rpt *RptTransactor) UpdateWeightConfigs(opts *bind.TransactOpts, _alpha *big.Int, _beta *big.Int, _gamma *big.Int, _psi *big.Int, _omega *big.Int, _window *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateWeightConfigs", _alpha, _beta, _gamma, _psi, _omega, _window)
}

// UpdateWeightConfigs is a paid mutator transaction binding the contract method 0xf182c59c.
//
// Solidity: function updateWeightConfigs(_alpha uint256, _beta uint256, _gamma uint256, _psi uint256, _omega uint256, _window uint256) returns()
func (_Rpt *RptSession) UpdateWeightConfigs(_alpha *big.Int, _beta *big.Int, _gamma *big.Int, _psi *big.Int, _omega *big.Int, _window *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateWeightConfigs(&_Rpt.TransactOpts, _alpha, _beta, _gamma, _psi, _omega, _window)
}

// UpdateWeightConfigs is a paid mutator transaction binding the contract method 0xf182c59c.
//
// Solidity: function updateWeightConfigs(_alpha uint256, _beta uint256, _gamma uint256, _psi uint256, _omega uint256, _window uint256) returns()
func (_Rpt *RptTransactorSession) UpdateWeightConfigs(_alpha *big.Int, _beta *big.Int, _gamma *big.Int, _psi *big.Int, _omega *big.Int, _window *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateWeightConfigs(&_Rpt.TransactOpts, _alpha, _beta, _gamma, _psi, _omega, _window)
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

// RptUpdateElectionConfigsIterator is returned from FilterUpdateElectionConfigs and is used to iterate over the raw logs and unpacked data for UpdateElectionConfigs events raised by the Rpt contract.
type RptUpdateElectionConfigsIterator struct {
	Event *RptUpdateElectionConfigs // Event containing the contract specifics and raw log

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
func (it *RptUpdateElectionConfigsIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RptUpdateElectionConfigs)
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
		it.Event = new(RptUpdateElectionConfigs)
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
func (it *RptUpdateElectionConfigsIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RptUpdateElectionConfigsIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RptUpdateElectionConfigs represents a UpdateElectionConfigs event raised by the Rpt contract.
type RptUpdateElectionConfigs struct {
	BlockNumber *big.Int
	Raw         types.Log // Blockchain specific contextual infos
}

// FilterUpdateElectionConfigs is a free log retrieval operation binding the contract event 0x09e649367469a85db638685b74f92f1ef17cdebb4610b4c42b7da19c2f1b189c.
//
// Solidity: e UpdateElectionConfigs(blockNumber uint256)
func (_Rpt *RptFilterer) FilterUpdateElectionConfigs(opts *bind.FilterOpts) (*RptUpdateElectionConfigsIterator, error) {

	logs, sub, err := _Rpt.contract.FilterLogs(opts, "UpdateElectionConfigs")
	if err != nil {
		return nil, err
	}
	return &RptUpdateElectionConfigsIterator{contract: _Rpt.contract, event: "UpdateElectionConfigs", logs: logs, sub: sub}, nil
}

// WatchUpdateElectionConfigs is a free log subscription operation binding the contract event 0x09e649367469a85db638685b74f92f1ef17cdebb4610b4c42b7da19c2f1b189c.
//
// Solidity: e UpdateElectionConfigs(blockNumber uint256)
func (_Rpt *RptFilterer) WatchUpdateElectionConfigs(opts *bind.WatchOpts, sink chan<- *RptUpdateElectionConfigs) (event.Subscription, error) {

	logs, sub, err := _Rpt.contract.WatchLogs(opts, "UpdateElectionConfigs")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RptUpdateElectionConfigs)
				if err := _Rpt.contract.UnpackLog(event, "UpdateElectionConfigs", log); err != nil {
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

// RptUpdateWeightConfigsIterator is returned from FilterUpdateWeightConfigs and is used to iterate over the raw logs and unpacked data for UpdateWeightConfigs events raised by the Rpt contract.
type RptUpdateWeightConfigsIterator struct {
	Event *RptUpdateWeightConfigs // Event containing the contract specifics and raw log

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
func (it *RptUpdateWeightConfigsIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RptUpdateWeightConfigs)
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
		it.Event = new(RptUpdateWeightConfigs)
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
func (it *RptUpdateWeightConfigsIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RptUpdateWeightConfigsIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RptUpdateWeightConfigs represents a UpdateWeightConfigs event raised by the Rpt contract.
type RptUpdateWeightConfigs struct {
	BlockNumber *big.Int
	Raw         types.Log // Blockchain specific contextual infos
}

// FilterUpdateWeightConfigs is a free log retrieval operation binding the contract event 0x94cb95e42d1f9f5b3e73da8fddc18ba25b0c89408eb91f64e417c59c6833a82b.
//
// Solidity: e UpdateWeightConfigs(blockNumber uint256)
func (_Rpt *RptFilterer) FilterUpdateWeightConfigs(opts *bind.FilterOpts) (*RptUpdateWeightConfigsIterator, error) {

	logs, sub, err := _Rpt.contract.FilterLogs(opts, "UpdateWeightConfigs")
	if err != nil {
		return nil, err
	}
	return &RptUpdateWeightConfigsIterator{contract: _Rpt.contract, event: "UpdateWeightConfigs", logs: logs, sub: sub}, nil
}

// WatchUpdateWeightConfigs is a free log subscription operation binding the contract event 0x94cb95e42d1f9f5b3e73da8fddc18ba25b0c89408eb91f64e417c59c6833a82b.
//
// Solidity: e UpdateWeightConfigs(blockNumber uint256)
func (_Rpt *RptFilterer) WatchUpdateWeightConfigs(opts *bind.WatchOpts, sink chan<- *RptUpdateWeightConfigs) (event.Subscription, error) {

	logs, sub, err := _Rpt.contract.WatchLogs(opts, "UpdateWeightConfigs")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RptUpdateWeightConfigs)
				if err := _Rpt.contract.UnpackLog(event, "UpdateWeightConfigs", log); err != nil {
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
