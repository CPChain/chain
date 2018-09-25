// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package admissionContract

import (
	"math/big"
	"strings"

	"bitbucket.org/cpchain/chain/accounts/abi"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/core/types"
)

// AdmissionABI is the input ABI used to generate the binding from.
const AdmissionABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"_nonce\",\"type\":\"uint64\"},{\"name\":\"_blockNumber\",\"type\":\"uint256\"}],\"name\":\"verifyCPU\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_nonce\",\"type\":\"uint64\"},{\"name\":\"_blockNumber\",\"type\":\"uint256\"}],\"name\":\"verifyMemory\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_cpuNonce\",\"type\":\"uint64\"},{\"name\":\"_cpuBlockNumber\",\"type\":\"uint256\"},{\"name\":\"_memoryNonce\",\"type\":\"uint64\"},{\"name\":\"_memoryBlockNumber\",\"type\":\"uint256\"}],\"name\":\"verify\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_difficulty\",\"type\":\"uint256\"}],\"name\":\"updateCPUDifficulty\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_difficulty\",\"type\":\"uint256\"}],\"name\":\"updateMemoryDifficulty\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[{\"name\":\"_cpuDifficulty\",\"type\":\"uint256\"},{\"name\":\"_memoryDifficulty\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]"

// AdmissionBin is the compiled bytecode used for deploying new contracts.
const AdmissionBin = `0x608060405234801561001057600080fd5b5060405160408061036a833981016040528051602090910151610100908103600290810a600155919003900a60005561031c8061004e6000396000f30060806040526004361061006c5763ffffffff7c0100000000000000000000000000000000000000000000000000000000600035041663502e7f4881146100715780635e0870b2146100aa578063702656af146100cf578063be981db8146100fe578063e171894614610118575b600080fd5b34801561007d57600080fd5b5061009667ffffffffffffffff60043516602435610130565b604080519115158252519081900360200190f35b3480156100b657600080fd5b5061009667ffffffffffffffff600435166024356102aa565b3480156100db57600080fd5b5061009667ffffffffffffffff60043581169060243590604435166064356102b2565b34801561010a57600080fd5b506101166004356102d8565b005b34801561012457600080fd5b506101166004356102e4565b60006014824303111580156101485750600082430310155b15156101b557604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601460248201527f6d7573742077697468696e20323020626c6f636b000000000000000000000000604482015290519081900360640190fd5b600054604080516c01000000000000000000000000410260208083019190915285406034830152780100000000000000000000000000000000000000000000000067ffffffffffffffff88160260548301528251603c818403018152605c909201928390528151600293918291908401908083835b602083106102495780518252601f19909201916020918201910161022a565b51815160209384036101000a600019018019909216911617905260405191909301945091925050808303816000865af115801561028a573d6000803e3d6000fd5b5050506040513d602081101561029f57600080fd5b505111159392505050565b600192915050565b60006102be8585610130565b80156102cf57506102cf83836102aa565b95945050505050565b6101000360020a600055565b6101000360020a6001555600a165627a7a72305820004245be6173ddc5d197056ba366f4fa6cdc3cfcbf4abaad8029d8a18242a6620029`

// DeployAdmission deploys a new Ethereum contract, binding an instance of Admission to it.
func DeployAdmission(auth *bind.TransactOpts, backend bind.ContractBackend, _cpuDifficulty *big.Int, _memoryDifficulty *big.Int) (common.Address, *types.Transaction, *Admission, error) {
	parsed, err := abi.JSON(strings.NewReader(AdmissionABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(AdmissionBin), backend, _cpuDifficulty, _memoryDifficulty)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &Admission{AdmissionCaller: AdmissionCaller{contract: contract}, AdmissionTransactor: AdmissionTransactor{contract: contract}, AdmissionFilterer: AdmissionFilterer{contract: contract}}, nil
}

// Admission is an auto generated Go binding around an Ethereum contract.
type Admission struct {
	AdmissionCaller     // Read-only binding to the contract
	AdmissionTransactor // Write-only binding to the contract
	AdmissionFilterer   // Log filterer for contract events
}

// AdmissionCaller is an auto generated read-only Go binding around an Ethereum contract.
type AdmissionCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// AdmissionTransactor is an auto generated write-only Go binding around an Ethereum contract.
type AdmissionTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// AdmissionFilterer is an auto generated log filtering Go binding around an Ethereum contract events.
type AdmissionFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// AdmissionSession is an auto generated Go binding around an Ethereum contract,
// with pre-set call and transact options.
type AdmissionSession struct {
	Contract     *Admission        // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// AdmissionCallerSession is an auto generated read-only Go binding around an Ethereum contract,
// with pre-set call options.
type AdmissionCallerSession struct {
	Contract *AdmissionCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts    // Call options to use throughout this session
}

// AdmissionTransactorSession is an auto generated write-only Go binding around an Ethereum contract,
// with pre-set transact options.
type AdmissionTransactorSession struct {
	Contract     *AdmissionTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts    // Transaction auth options to use throughout this session
}

// AdmissionRaw is an auto generated low-level Go binding around an Ethereum contract.
type AdmissionRaw struct {
	Contract *Admission // Generic contract binding to access the raw methods on
}

// AdmissionCallerRaw is an auto generated low-level read-only Go binding around an Ethereum contract.
type AdmissionCallerRaw struct {
	Contract *AdmissionCaller // Generic read-only contract binding to access the raw methods on
}

// AdmissionTransactorRaw is an auto generated low-level write-only Go binding around an Ethereum contract.
type AdmissionTransactorRaw struct {
	Contract *AdmissionTransactor // Generic write-only contract binding to access the raw methods on
}

// NewAdmission creates a new instance of Admission, bound to a specific deployed contract.
func NewAdmission(address common.Address, backend bind.ContractBackend) (*Admission, error) {
	contract, err := bindAdmission(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &Admission{AdmissionCaller: AdmissionCaller{contract: contract}, AdmissionTransactor: AdmissionTransactor{contract: contract}, AdmissionFilterer: AdmissionFilterer{contract: contract}}, nil
}

// NewAdmissionCaller creates a new read-only instance of Admission, bound to a specific deployed contract.
func NewAdmissionCaller(address common.Address, caller bind.ContractCaller) (*AdmissionCaller, error) {
	contract, err := bindAdmission(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &AdmissionCaller{contract: contract}, nil
}

// NewAdmissionTransactor creates a new write-only instance of Admission, bound to a specific deployed contract.
func NewAdmissionTransactor(address common.Address, transactor bind.ContractTransactor) (*AdmissionTransactor, error) {
	contract, err := bindAdmission(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &AdmissionTransactor{contract: contract}, nil
}

// NewAdmissionFilterer creates a new log filterer instance of Admission, bound to a specific deployed contract.
func NewAdmissionFilterer(address common.Address, filterer bind.ContractFilterer) (*AdmissionFilterer, error) {
	contract, err := bindAdmission(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &AdmissionFilterer{contract: contract}, nil
}

// bindAdmission binds a generic wrapper to an already deployed contract.
func bindAdmission(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(AdmissionABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Admission *AdmissionRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Admission.Contract.AdmissionCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Admission *AdmissionRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Admission.Contract.AdmissionTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Admission *AdmissionRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Admission.Contract.AdmissionTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Admission *AdmissionCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Admission.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Admission *AdmissionTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Admission.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Admission *AdmissionTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Admission.Contract.contract.Transact(opts, method, params...)
}

// Verify is a free data retrieval call binding the contract method 0x702656af.
//
// Solidity: function verify(_cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256) constant returns(bool)
func (_Admission *AdmissionCaller) Verify(opts *bind.CallOpts, _cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Admission.contract.Call(opts, out, "verify", _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber)
	return *ret0, err
}

// Verify is a free data retrieval call binding the contract method 0x702656af.
//
// Solidity: function verify(_cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256) constant returns(bool)
func (_Admission *AdmissionSession) Verify(_cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int) (bool, error) {
	return _Admission.Contract.Verify(&_Admission.CallOpts, _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber)
}

// Verify is a free data retrieval call binding the contract method 0x702656af.
//
// Solidity: function verify(_cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256) constant returns(bool)
func (_Admission *AdmissionCallerSession) Verify(_cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int) (bool, error) {
	return _Admission.Contract.Verify(&_Admission.CallOpts, _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber)
}

// VerifyCPU is a free data retrieval call binding the contract method 0x502e7f48.
//
// Solidity: function verifyCPU(_nonce uint64, _blockNumber uint256) constant returns(bool)
func (_Admission *AdmissionCaller) VerifyCPU(opts *bind.CallOpts, _nonce uint64, _blockNumber *big.Int) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Admission.contract.Call(opts, out, "verifyCPU", _nonce, _blockNumber)
	return *ret0, err
}

// VerifyCPU is a free data retrieval call binding the contract method 0x502e7f48.
//
// Solidity: function verifyCPU(_nonce uint64, _blockNumber uint256) constant returns(bool)
func (_Admission *AdmissionSession) VerifyCPU(_nonce uint64, _blockNumber *big.Int) (bool, error) {
	return _Admission.Contract.VerifyCPU(&_Admission.CallOpts, _nonce, _blockNumber)
}

// VerifyCPU is a free data retrieval call binding the contract method 0x502e7f48.
//
// Solidity: function verifyCPU(_nonce uint64, _blockNumber uint256) constant returns(bool)
func (_Admission *AdmissionCallerSession) VerifyCPU(_nonce uint64, _blockNumber *big.Int) (bool, error) {
	return _Admission.Contract.VerifyCPU(&_Admission.CallOpts, _nonce, _blockNumber)
}

// VerifyMemory is a free data retrieval call binding the contract method 0x5e0870b2.
//
// Solidity: function verifyMemory(_nonce uint64, _blockNumber uint256) constant returns(bool)
func (_Admission *AdmissionCaller) VerifyMemory(opts *bind.CallOpts, _nonce uint64, _blockNumber *big.Int) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Admission.contract.Call(opts, out, "verifyMemory", _nonce, _blockNumber)
	return *ret0, err
}

// VerifyMemory is a free data retrieval call binding the contract method 0x5e0870b2.
//
// Solidity: function verifyMemory(_nonce uint64, _blockNumber uint256) constant returns(bool)
func (_Admission *AdmissionSession) VerifyMemory(_nonce uint64, _blockNumber *big.Int) (bool, error) {
	return _Admission.Contract.VerifyMemory(&_Admission.CallOpts, _nonce, _blockNumber)
}

// VerifyMemory is a free data retrieval call binding the contract method 0x5e0870b2.
//
// Solidity: function verifyMemory(_nonce uint64, _blockNumber uint256) constant returns(bool)
func (_Admission *AdmissionCallerSession) VerifyMemory(_nonce uint64, _blockNumber *big.Int) (bool, error) {
	return _Admission.Contract.VerifyMemory(&_Admission.CallOpts, _nonce, _blockNumber)
}

// UpdateCPUDifficulty is a paid mutator transaction binding the contract method 0xbe981db8.
//
// Solidity: function updateCPUDifficulty(_difficulty uint256) returns()
func (_Admission *AdmissionTransactor) UpdateCPUDifficulty(opts *bind.TransactOpts, _difficulty *big.Int) (*types.Transaction, error) {
	return _Admission.contract.Transact(opts, "updateCPUDifficulty", _difficulty)
}

// UpdateCPUDifficulty is a paid mutator transaction binding the contract method 0xbe981db8.
//
// Solidity: function updateCPUDifficulty(_difficulty uint256) returns()
func (_Admission *AdmissionSession) UpdateCPUDifficulty(_difficulty *big.Int) (*types.Transaction, error) {
	return _Admission.Contract.UpdateCPUDifficulty(&_Admission.TransactOpts, _difficulty)
}

// UpdateCPUDifficulty is a paid mutator transaction binding the contract method 0xbe981db8.
//
// Solidity: function updateCPUDifficulty(_difficulty uint256) returns()
func (_Admission *AdmissionTransactorSession) UpdateCPUDifficulty(_difficulty *big.Int) (*types.Transaction, error) {
	return _Admission.Contract.UpdateCPUDifficulty(&_Admission.TransactOpts, _difficulty)
}

// UpdateMemoryDifficulty is a paid mutator transaction binding the contract method 0xe1718946.
//
// Solidity: function updateMemoryDifficulty(_difficulty uint256) returns()
func (_Admission *AdmissionTransactor) UpdateMemoryDifficulty(opts *bind.TransactOpts, _difficulty *big.Int) (*types.Transaction, error) {
	return _Admission.contract.Transact(opts, "updateMemoryDifficulty", _difficulty)
}

// UpdateMemoryDifficulty is a paid mutator transaction binding the contract method 0xe1718946.
//
// Solidity: function updateMemoryDifficulty(_difficulty uint256) returns()
func (_Admission *AdmissionSession) UpdateMemoryDifficulty(_difficulty *big.Int) (*types.Transaction, error) {
	return _Admission.Contract.UpdateMemoryDifficulty(&_Admission.TransactOpts, _difficulty)
}

// UpdateMemoryDifficulty is a paid mutator transaction binding the contract method 0xe1718946.
//
// Solidity: function updateMemoryDifficulty(_difficulty uint256) returns()
func (_Admission *AdmissionTransactorSession) UpdateMemoryDifficulty(_difficulty *big.Int) (*types.Transaction, error) {
	return _Admission.Contract.UpdateMemoryDifficulty(&_Admission.TransactOpts, _difficulty)
}
