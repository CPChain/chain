// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package sol

import (
	"math/big"
	"strings"

	"bitbucket.org/cpchain/chain/accounts/abi"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// RegisterABI is the input ABI used to generate the binding from.
const RegisterABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"},{\"name\":\"\",\"type\":\"uint256\"}],\"name\":\"uploadHistory\",\"outputs\":[{\"name\":\"fileName\",\"type\":\"string\"},{\"name\":\"fileHash\",\"type\":\"bytes32\"},{\"name\":\"fileSize\",\"type\":\"uint256\"},{\"name\":\"timeStamp\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"fileName\",\"type\":\"string\"},{\"name\":\"fileHash\",\"type\":\"bytes32\"},{\"name\":\"fileSize\",\"type\":\"uint256\"}],\"name\":\"claimRegister\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"user\",\"type\":\"address\"}],\"name\":\"getUploadCount\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"user\",\"type\":\"address\"},{\"name\":\"block_num\",\"type\":\"uint256\"}],\"name\":\"getUploadCountAfterBlock\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]"

// RegisterBin is the compiled bytecode used for deploying new contracts.
const RegisterBin = `0x608060405234801561001057600080fd5b5060008054600160a060020a031916331790556104a0806100326000396000f3006080604052600436106100615763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166326cea7378114610066578063d44fd26114610118578063f1227d361461017c578063fcf197b2146101af575b600080fd5b34801561007257600080fd5b5061008a600160a060020a03600435166024356101d3565b60408051602080820186905291810184905260608101839052608080825286519082015285519091829160a083019188019080838360005b838110156100da5781810151838201526020016100c2565b50505050905090810190601f1680156101075780820380516001836020036101000a031916815260200191505b509550505050505060405180910390f35b34801561012457600080fd5b506040805160206004803580820135601f810184900484028501840190955284845261017a9436949293602493928401919081908401838280828437509497505084359550505060209092013591506102a39050565b005b34801561018857600080fd5b5061019d600160a060020a0360043516610324565b60408051918252519081900360200190f35b3480156101bb57600080fd5b5061019d600160a060020a036004351660243561033f565b6001602052816000526040600020818154811015156101ee57fe5b60009182526020918290206004919091020180546040805160026001841615610100026000190190931692909204601f8101859004850283018501909152808252919450925083918301828280156102875780601f1061025c57610100808354040283529160200191610287565b820191906000526020600020905b81548152906001019060200180831161026a57829003601f168201915b5050505050908060010154908060020154908060030154905084565b3360009081526001602081815260408084208151608081018352888152808401889052918201869052436060830152805493840180825590855293829020815180519294600402909101926102fd928492909101906103d9565b50602082015160018201556040820151600282015560609091015160039091015550505050565b600160a060020a031660009081526001602052604090205490565b600080805b600160a060020a0385166000908152600160205260409020548110156103b357600160a060020a038516600090815260016020526040902080548591908390811061038b57fe5b90600052602060002090600402016003015411156103ab578091506103b3565b600101610344565b600160a060020a0385166000908152600160205260409020548290039250505092915050565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f1061041a57805160ff1916838001178555610447565b82800160010185558215610447579182015b8281111561044757825182559160200191906001019061042c565b50610453929150610457565b5090565b61047191905b80821115610453576000815560010161045d565b905600a165627a7a723058202fd997a69260de9a087c90515379be6e132ecb713d014c6bfcd6ce458fc073e50029`

// DeployRegister deploys a new cpchain contract, binding an instance of Register to it.
func DeployRegister(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *Register, error) {
	parsed, err := abi.JSON(strings.NewReader(RegisterABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(RegisterBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &Register{RegisterCaller: RegisterCaller{contract: contract}, RegisterTransactor: RegisterTransactor{contract: contract}, RegisterFilterer: RegisterFilterer{contract: contract}}, nil
}

// Register is an auto generated Go binding around an cpchain contract.
type Register struct {
	RegisterCaller     // Read-only binding to the contract
	RegisterTransactor // Write-only binding to the contract
	RegisterFilterer   // Log filterer for contract events
}

// RegisterCaller is an auto generated read-only Go binding around an cpchain contract.
type RegisterCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RegisterTransactor is an auto generated write-only Go binding around an cpchain contract.
type RegisterTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RegisterFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type RegisterFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RegisterSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type RegisterSession struct {
	Contract     *Register         // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// RegisterCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type RegisterCallerSession struct {
	Contract *RegisterCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts   // Call options to use throughout this session
}

// RegisterTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type RegisterTransactorSession struct {
	Contract     *RegisterTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts   // Transaction auth options to use throughout this session
}

// RegisterRaw is an auto generated low-level Go binding around an cpchain contract.
type RegisterRaw struct {
	Contract *Register // Generic contract binding to access the raw methods on
}

// RegisterCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type RegisterCallerRaw struct {
	Contract *RegisterCaller // Generic read-only contract binding to access the raw methods on
}

// RegisterTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type RegisterTransactorRaw struct {
	Contract *RegisterTransactor // Generic write-only contract binding to access the raw methods on
}

// NewRegister creates a new instance of Register, bound to a specific deployed contract.
func NewRegister(address common.Address, backend bind.ContractBackend) (*Register, error) {
	contract, err := bindRegister(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &Register{RegisterCaller: RegisterCaller{contract: contract}, RegisterTransactor: RegisterTransactor{contract: contract}, RegisterFilterer: RegisterFilterer{contract: contract}}, nil
}

// NewRegisterCaller creates a new read-only instance of Register, bound to a specific deployed contract.
func NewRegisterCaller(address common.Address, caller bind.ContractCaller) (*RegisterCaller, error) {
	contract, err := bindRegister(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &RegisterCaller{contract: contract}, nil
}

// NewRegisterTransactor creates a new write-only instance of Register, bound to a specific deployed contract.
func NewRegisterTransactor(address common.Address, transactor bind.ContractTransactor) (*RegisterTransactor, error) {
	contract, err := bindRegister(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &RegisterTransactor{contract: contract}, nil
}

// NewRegisterFilterer creates a new log filterer instance of Register, bound to a specific deployed contract.
func NewRegisterFilterer(address common.Address, filterer bind.ContractFilterer) (*RegisterFilterer, error) {
	contract, err := bindRegister(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &RegisterFilterer{contract: contract}, nil
}

// bindRegister binds a generic wrapper to an already deployed contract.
func bindRegister(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(RegisterABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Register *RegisterRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Register.Contract.RegisterCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Register *RegisterRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Register.Contract.RegisterTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Register *RegisterRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Register.Contract.RegisterTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Register *RegisterCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Register.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Register *RegisterTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Register.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Register *RegisterTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Register.Contract.contract.Transact(opts, method, params...)
}

// GetUploadCount is a free data retrieval call binding the contract method 0xf1227d36.
//
// Solidity: function getUploadCount(user address) constant returns(uint256)
func (_Register *RegisterCaller) GetUploadCount(opts *bind.CallOpts, user common.Address) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Register.contract.Call(opts, out, "getUploadCount", user)
	return *ret0, err
}

// GetUploadCount is a free data retrieval call binding the contract method 0xf1227d36.
//
// Solidity: function getUploadCount(user address) constant returns(uint256)
func (_Register *RegisterSession) GetUploadCount(user common.Address) (*big.Int, error) {
	return _Register.Contract.GetUploadCount(&_Register.CallOpts, user)
}

// GetUploadCount is a free data retrieval call binding the contract method 0xf1227d36.
//
// Solidity: function getUploadCount(user address) constant returns(uint256)
func (_Register *RegisterCallerSession) GetUploadCount(user common.Address) (*big.Int, error) {
	return _Register.Contract.GetUploadCount(&_Register.CallOpts, user)
}

// GetUploadCountAfterBlock is a free data retrieval call binding the contract method 0xfcf197b2.
//
// Solidity: function getUploadCountAfterBlock(user address, block_num uint256) constant returns(uint256)
func (_Register *RegisterCaller) GetUploadCountAfterBlock(opts *bind.CallOpts, user common.Address, block_num *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Register.contract.Call(opts, out, "getUploadCountAfterBlock", user, block_num)
	return *ret0, err
}

// GetUploadCountAfterBlock is a free data retrieval call binding the contract method 0xfcf197b2.
//
// Solidity: function getUploadCountAfterBlock(user address, block_num uint256) constant returns(uint256)
func (_Register *RegisterSession) GetUploadCountAfterBlock(user common.Address, block_num *big.Int) (*big.Int, error) {
	return _Register.Contract.GetUploadCountAfterBlock(&_Register.CallOpts, user, block_num)
}

// GetUploadCountAfterBlock is a free data retrieval call binding the contract method 0xfcf197b2.
//
// Solidity: function getUploadCountAfterBlock(user address, block_num uint256) constant returns(uint256)
func (_Register *RegisterCallerSession) GetUploadCountAfterBlock(user common.Address, block_num *big.Int) (*big.Int, error) {
	return _Register.Contract.GetUploadCountAfterBlock(&_Register.CallOpts, user, block_num)
}

// UploadHistory is a free data retrieval call binding the contract method 0x26cea737.
//
// Solidity: function uploadHistory( address,  uint256) constant returns(fileName string, fileHash bytes32, fileSize uint256, timeStamp uint256)
func (_Register *RegisterCaller) UploadHistory(opts *bind.CallOpts, arg0 common.Address, arg1 *big.Int) (struct {
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
	err := _Register.contract.Call(opts, out, "uploadHistory", arg0, arg1)
	return *ret, err
}

// UploadHistory is a free data retrieval call binding the contract method 0x26cea737.
//
// Solidity: function uploadHistory( address,  uint256) constant returns(fileName string, fileHash bytes32, fileSize uint256, timeStamp uint256)
func (_Register *RegisterSession) UploadHistory(arg0 common.Address, arg1 *big.Int) (struct {
	FileName  string
	FileHash  [32]byte
	FileSize  *big.Int
	TimeStamp *big.Int
}, error) {
	return _Register.Contract.UploadHistory(&_Register.CallOpts, arg0, arg1)
}

// UploadHistory is a free data retrieval call binding the contract method 0x26cea737.
//
// Solidity: function uploadHistory( address,  uint256) constant returns(fileName string, fileHash bytes32, fileSize uint256, timeStamp uint256)
func (_Register *RegisterCallerSession) UploadHistory(arg0 common.Address, arg1 *big.Int) (struct {
	FileName  string
	FileHash  [32]byte
	FileSize  *big.Int
	TimeStamp *big.Int
}, error) {
	return _Register.Contract.UploadHistory(&_Register.CallOpts, arg0, arg1)
}

// ClaimRegister is a paid mutator transaction binding the contract method 0xd44fd261.
//
// Solidity: function claimRegister(fileName string, fileHash bytes32, fileSize uint256) returns()
func (_Register *RegisterTransactor) ClaimRegister(opts *bind.TransactOpts, fileName string, fileHash [32]byte, fileSize *big.Int) (*types.Transaction, error) {
	return _Register.contract.Transact(opts, "claimRegister", fileName, fileHash, fileSize)
}

// ClaimRegister is a paid mutator transaction binding the contract method 0xd44fd261.
//
// Solidity: function claimRegister(fileName string, fileHash bytes32, fileSize uint256) returns()
func (_Register *RegisterSession) ClaimRegister(fileName string, fileHash [32]byte, fileSize *big.Int) (*types.Transaction, error) {
	return _Register.Contract.ClaimRegister(&_Register.TransactOpts, fileName, fileHash, fileSize)
}

// ClaimRegister is a paid mutator transaction binding the contract method 0xd44fd261.
//
// Solidity: function claimRegister(fileName string, fileHash bytes32, fileSize uint256) returns()
func (_Register *RegisterTransactorSession) ClaimRegister(fileName string, fileHash [32]byte, fileSize *big.Int) (*types.Transaction, error) {
	return _Register.Contract.ClaimRegister(&_Register.TransactOpts, fileName, fileHash, fileSize)
}
