// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package admission

import (
	"math/big"
	"strings"

	"bitbucket.org/cpchain/chain/accounts/abi"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// AdmissionABI is the input ABI used to generate the binding from.
const AdmissionABI = "[{\"constant\":true,\"inputs\":[],\"name\":\"memoryDifficulty\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_cpuNonce\",\"type\":\"uint64\"},{\"name\":\"_cpuBlockNumber\",\"type\":\"uint256\"},{\"name\":\"_memoryNonce\",\"type\":\"uint64\"},{\"name\":\"_memoryBlockNumber\",\"type\":\"uint256\"},{\"name\":\"_sender\",\"type\":\"address\"}],\"name\":\"verify\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_sender\",\"type\":\"address\"},{\"name\":\"_nonce\",\"type\":\"uint64\"},{\"name\":\"_blockNumber\",\"type\":\"uint256\"},{\"name\":\"_difficulty\",\"type\":\"uint256\"}],\"name\":\"verifyMemory\",\"outputs\":[{\"name\":\"b\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_sender\",\"type\":\"address\"},{\"name\":\"_nonce\",\"type\":\"uint64\"},{\"name\":\"_blockNumber\",\"type\":\"uint256\"},{\"name\":\"_difficulty\",\"type\":\"uint256\"}],\"name\":\"verifyCPU\",\"outputs\":[{\"name\":\"b\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"cpuDifficulty\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"owner\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_difficulty\",\"type\":\"uint256\"}],\"name\":\"updateCPUDifficulty\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_difficulty\",\"type\":\"uint256\"}],\"name\":\"updateMemoryDifficulty\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[{\"name\":\"_cpuDifficulty\",\"type\":\"uint256\"},{\"name\":\"_memoryDifficulty\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]"

// AdmissionBin is the compiled bytecode used for deploying new contracts.
const AdmissionBin = `0x608060405234801561001057600080fd5b506040516040806105ca83398101604052805160209091015160048054600160a060020a0319163317905561004d82640100000000610066810204565b61005f816401000000006100f9810204565b505061018a565b6101008111801590610079575060008110155b15156100e657604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601d60248201527f446966666963756c7479206d757374206c657373207468616e20323536000000604482015290519081900360640190fd5b600281815561010091909103900a600055565b610100811180159061010c575060008110155b151561017957604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601d60248201527f446966666963756c7479206d757374206c657373207468616e20323536000000604482015290519081900360640190fd5b60038190556101000360020a600155565b610431806101996000396000f30060806040526004361061008d5763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166317e6b96681146100925780633395492e146100b95780634bda8957146101155780636ac03dcc146101565780638b654613146101975780638da5cb5b146101ac578063be981db8146101ea578063e171894614610204575b600080fd5b34801561009e57600080fd5b506100a761021c565b60408051918252519081900360200190f35b3480156100c557600080fd5b5061010167ffffffffffffffff600435811690602435906044351660643573ffffffffffffffffffffffffffffffffffffffff60843516610222565b604080519115158252519081900360200190f35b34801561012157600080fd5b5061010173ffffffffffffffffffffffffffffffffffffffff6004351667ffffffffffffffff60243516604435606435610251565b34801561016257600080fd5b5061010173ffffffffffffffffffffffffffffffffffffffff6004351667ffffffffffffffff6024351660443560643561028d565b3480156101a357600080fd5b506100a76102bf565b3480156101b857600080fd5b506101c16102c5565b6040805173ffffffffffffffffffffffffffffffffffffffff9092168252519081900360200190f35b3480156101f657600080fd5b506102026004356102e1565b005b34801561021057600080fd5b50610202600435610374565b60035481565b600061023282878760025461028d565b80156102475750610247828585600354610251565b9695505050505050565b600060405185815284602082015283406040820152826060820152602081608083606b600019fa151561028357600080fd5b5195945050505050565b600060405185815284602082015283406040820152826060820152602081608083606a600019fa151561028357600080fd5b60025481565b60045473ffffffffffffffffffffffffffffffffffffffff1681565b61010081118015906102f4575060008110155b151561036157604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601d60248201527f446966666963756c7479206d757374206c657373207468616e20323536000000604482015290519081900360640190fd5b600281815561010091909103900a600055565b6101008111801590610387575060008110155b15156103f457604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601d60248201527f446966666963756c7479206d757374206c657373207468616e20323536000000604482015290519081900360640190fd5b60038190556101000360020a6001555600a165627a7a7230582042729ab17fafe469ce34ba7ecaa83be4a5bbad45240f85b57963b88538ccf7450029`

// DeployAdmission deploys a new cpchain contract, binding an instance of Admission to it.
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

// Admission is an auto generated Go binding around an cpchain contract.
type Admission struct {
	AdmissionCaller     // Read-only binding to the contract
	AdmissionTransactor // Write-only binding to the contract
	AdmissionFilterer   // Log filterer for contract events
}

// AdmissionCaller is an auto generated read-only Go binding around an cpchain contract.
type AdmissionCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// AdmissionTransactor is an auto generated write-only Go binding around an cpchain contract.
type AdmissionTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// AdmissionFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type AdmissionFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// AdmissionSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type AdmissionSession struct {
	Contract     *Admission        // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// AdmissionCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type AdmissionCallerSession struct {
	Contract *AdmissionCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts    // Call options to use throughout this session
}

// AdmissionTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type AdmissionTransactorSession struct {
	Contract     *AdmissionTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts    // Transaction auth options to use throughout this session
}

// AdmissionRaw is an auto generated low-level Go binding around an cpchain contract.
type AdmissionRaw struct {
	Contract *Admission // Generic contract binding to access the raw methods on
}

// AdmissionCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type AdmissionCallerRaw struct {
	Contract *AdmissionCaller // Generic read-only contract binding to access the raw methods on
}

// AdmissionTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
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

// CpuDifficulty is a free data retrieval call binding the contract method 0x8b654613.
//
// Solidity: function cpuDifficulty() constant returns(uint256)
func (_Admission *AdmissionCaller) CpuDifficulty(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Admission.contract.Call(opts, out, "cpuDifficulty")
	return *ret0, err
}

// CpuDifficulty is a free data retrieval call binding the contract method 0x8b654613.
//
// Solidity: function cpuDifficulty() constant returns(uint256)
func (_Admission *AdmissionSession) CpuDifficulty() (*big.Int, error) {
	return _Admission.Contract.CpuDifficulty(&_Admission.CallOpts)
}

// CpuDifficulty is a free data retrieval call binding the contract method 0x8b654613.
//
// Solidity: function cpuDifficulty() constant returns(uint256)
func (_Admission *AdmissionCallerSession) CpuDifficulty() (*big.Int, error) {
	return _Admission.Contract.CpuDifficulty(&_Admission.CallOpts)
}

// MemoryDifficulty is a free data retrieval call binding the contract method 0x17e6b966.
//
// Solidity: function memoryDifficulty() constant returns(uint256)
func (_Admission *AdmissionCaller) MemoryDifficulty(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Admission.contract.Call(opts, out, "memoryDifficulty")
	return *ret0, err
}

// MemoryDifficulty is a free data retrieval call binding the contract method 0x17e6b966.
//
// Solidity: function memoryDifficulty() constant returns(uint256)
func (_Admission *AdmissionSession) MemoryDifficulty() (*big.Int, error) {
	return _Admission.Contract.MemoryDifficulty(&_Admission.CallOpts)
}

// MemoryDifficulty is a free data retrieval call binding the contract method 0x17e6b966.
//
// Solidity: function memoryDifficulty() constant returns(uint256)
func (_Admission *AdmissionCallerSession) MemoryDifficulty() (*big.Int, error) {
	return _Admission.Contract.MemoryDifficulty(&_Admission.CallOpts)
}

// Owner is a free data retrieval call binding the contract method 0x8da5cb5b.
//
// Solidity: function owner() constant returns(address)
func (_Admission *AdmissionCaller) Owner(opts *bind.CallOpts) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _Admission.contract.Call(opts, out, "owner")
	return *ret0, err
}

// Owner is a free data retrieval call binding the contract method 0x8da5cb5b.
//
// Solidity: function owner() constant returns(address)
func (_Admission *AdmissionSession) Owner() (common.Address, error) {
	return _Admission.Contract.Owner(&_Admission.CallOpts)
}

// Owner is a free data retrieval call binding the contract method 0x8da5cb5b.
//
// Solidity: function owner() constant returns(address)
func (_Admission *AdmissionCallerSession) Owner() (common.Address, error) {
	return _Admission.Contract.Owner(&_Admission.CallOpts)
}

// Verify is a free data retrieval call binding the contract method 0x3395492e.
//
// Solidity: function verify(_cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256, _sender address) constant returns(bool)
func (_Admission *AdmissionCaller) Verify(opts *bind.CallOpts, _cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int, _sender common.Address) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Admission.contract.Call(opts, out, "verify", _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber, _sender)
	return *ret0, err
}

// Verify is a free data retrieval call binding the contract method 0x3395492e.
//
// Solidity: function verify(_cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256, _sender address) constant returns(bool)
func (_Admission *AdmissionSession) Verify(_cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int, _sender common.Address) (bool, error) {
	return _Admission.Contract.Verify(&_Admission.CallOpts, _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber, _sender)
}

// Verify is a free data retrieval call binding the contract method 0x3395492e.
//
// Solidity: function verify(_cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256, _sender address) constant returns(bool)
func (_Admission *AdmissionCallerSession) Verify(_cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int, _sender common.Address) (bool, error) {
	return _Admission.Contract.Verify(&_Admission.CallOpts, _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber, _sender)
}

// VerifyCPU is a free data retrieval call binding the contract method 0x6ac03dcc.
//
// Solidity: function verifyCPU(_sender address, _nonce uint64, _blockNumber uint256, _difficulty uint256) constant returns(b bool)
func (_Admission *AdmissionCaller) VerifyCPU(opts *bind.CallOpts, _sender common.Address, _nonce uint64, _blockNumber *big.Int, _difficulty *big.Int) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Admission.contract.Call(opts, out, "verifyCPU", _sender, _nonce, _blockNumber, _difficulty)
	return *ret0, err
}

// VerifyCPU is a free data retrieval call binding the contract method 0x6ac03dcc.
//
// Solidity: function verifyCPU(_sender address, _nonce uint64, _blockNumber uint256, _difficulty uint256) constant returns(b bool)
func (_Admission *AdmissionSession) VerifyCPU(_sender common.Address, _nonce uint64, _blockNumber *big.Int, _difficulty *big.Int) (bool, error) {
	return _Admission.Contract.VerifyCPU(&_Admission.CallOpts, _sender, _nonce, _blockNumber, _difficulty)
}

// VerifyCPU is a free data retrieval call binding the contract method 0x6ac03dcc.
//
// Solidity: function verifyCPU(_sender address, _nonce uint64, _blockNumber uint256, _difficulty uint256) constant returns(b bool)
func (_Admission *AdmissionCallerSession) VerifyCPU(_sender common.Address, _nonce uint64, _blockNumber *big.Int, _difficulty *big.Int) (bool, error) {
	return _Admission.Contract.VerifyCPU(&_Admission.CallOpts, _sender, _nonce, _blockNumber, _difficulty)
}

// VerifyMemory is a free data retrieval call binding the contract method 0x4bda8957.
//
// Solidity: function verifyMemory(_sender address, _nonce uint64, _blockNumber uint256, _difficulty uint256) constant returns(b bool)
func (_Admission *AdmissionCaller) VerifyMemory(opts *bind.CallOpts, _sender common.Address, _nonce uint64, _blockNumber *big.Int, _difficulty *big.Int) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Admission.contract.Call(opts, out, "verifyMemory", _sender, _nonce, _blockNumber, _difficulty)
	return *ret0, err
}

// VerifyMemory is a free data retrieval call binding the contract method 0x4bda8957.
//
// Solidity: function verifyMemory(_sender address, _nonce uint64, _blockNumber uint256, _difficulty uint256) constant returns(b bool)
func (_Admission *AdmissionSession) VerifyMemory(_sender common.Address, _nonce uint64, _blockNumber *big.Int, _difficulty *big.Int) (bool, error) {
	return _Admission.Contract.VerifyMemory(&_Admission.CallOpts, _sender, _nonce, _blockNumber, _difficulty)
}

// VerifyMemory is a free data retrieval call binding the contract method 0x4bda8957.
//
// Solidity: function verifyMemory(_sender address, _nonce uint64, _blockNumber uint256, _difficulty uint256) constant returns(b bool)
func (_Admission *AdmissionCallerSession) VerifyMemory(_sender common.Address, _nonce uint64, _blockNumber *big.Int, _difficulty *big.Int) (bool, error) {
	return _Admission.Contract.VerifyMemory(&_Admission.CallOpts, _sender, _nonce, _blockNumber, _difficulty)
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
