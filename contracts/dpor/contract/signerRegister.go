// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package contract

import (
	"math/big"
	"strings"

	"github.com/ethereum/go-ethereum/accounts/abi"
	"github.com/ethereum/go-ethereum/accounts/abi/bind"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
)

// SignerConnectionRegisterABI is the input ABI used to generate the binding from.
const SignerConnectionRegisterABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"}],\"name\":\"_publicKeys\",\"outputs\":[{\"name\":\"\",\"type\":\"bytes\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"viewIndex\",\"type\":\"uint256\"},{\"name\":\"otherAddress\",\"type\":\"address\"}],\"name\":\"getNodeInfo\",\"outputs\":[{\"name\":\"\",\"type\":\"bytes\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"rsaPublicKey\",\"type\":\"bytes\"}],\"name\":\"registerPublicKey\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"getPublicKey\",\"outputs\":[{\"name\":\"\",\"type\":\"bytes\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"viewIndex\",\"type\":\"uint256\"},{\"name\":\"otherAddress\",\"type\":\"address\"},{\"name\":\"encrpytedNodeInfo\",\"type\":\"bytes\"}],\"name\":\"addNodeInfo\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]"

// SignerConnectionRegisterBin is the compiled bytecode used for deploying new contracts.
const SignerConnectionRegisterBin = `0x608060405234801561001057600080fd5b5060008054600160a060020a0319163317905561060e806100326000396000f3fe60806040526004361061006c5763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416632c76beff811461007157806336056b40146101195780638562359414610152578063857cdbb8146101fa578063f94389911461022d575b600080fd5b34801561007d57600080fd5b506100a46004803603602081101561009457600080fd5b5035600160a060020a03166102e8565b6040805160208082528351818301528351919283929083019185019080838360005b838110156100de5781810151838201526020016100c6565b50505050905090810190601f16801561010b5780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b34801561012557600080fd5b506100a46004803603604081101561013c57600080fd5b5080359060200135600160a060020a0316610382565b6101f86004803603602081101561016857600080fd5b81019060208101813564010000000081111561018357600080fd5b82018360208201111561019557600080fd5b803590602001918460018302840111640100000000831117156101b757600080fd5b91908080601f01602080910402602001604051908101604052809392919081815260200183838082843760009201919091525092955061043b945050505050565b005b34801561020657600080fd5b506100a46004803603602081101561021d57600080fd5b5035600160a060020a031661045f565b6101f86004803603606081101561024357600080fd5b813591600160a060020a036020820135169181019060608101604082013564010000000081111561027357600080fd5b82018360208201111561028557600080fd5b803590602001918460018302840111640100000000831117156102a757600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600092019190915250929550610509945050505050565b60016020818152600092835260409283902080548451600294821615610100026000190190911693909304601f810183900483028401830190945283835291929083018282801561037a5780601f1061034f5761010080835404028352916020019161037a565b820191906000526020600020905b81548152906001019060200180831161035d57829003601f168201915b505050505081565b60008281526002602081815260408084203385528252808420600160a060020a0386168552825292839020805484516001821615610100026000190190911693909304601f8101839004830284018301909452838352606093909183018282801561042e5780601f106104035761010080835404028352916020019161042e565b820191906000526020600020905b81548152906001019060200180831161041157829003601f168201915b5050505050905092915050565b336000908152600160209081526040909120825161045b92840190610547565b5050565b600160a060020a03811660009081526001602081815260409283902080548451600294821615610100026000190190911693909304601f810183900483028401830190945283835260609390918301828280156104fd5780601f106104d2576101008083540402835291602001916104fd565b820191906000526020600020905b8154815290600101906020018083116104e057829003601f168201915b50505050509050919050565b60008381526002602090815260408083203384528252808320600160a060020a03861684528252909120825161054192840190610547565b50505050565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f1061058857805160ff19168380011785556105b5565b828001600101855582156105b5579182015b828111156105b557825182559160200191906001019061059a565b506105c19291506105c5565b5090565b6105df91905b808211156105c157600081556001016105cb565b9056fea165627a7a72305820a55b5af736d8f3bb88c7606d8b7adb24cdc83df5e246c373b8e8f7028a40146a0029`

// DeploySignerConnectionRegister deploys a new Ethereum contract, binding an instance of SignerConnectionRegister to it.
func DeploySignerConnectionRegister(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *SignerConnectionRegister, error) {
	parsed, err := abi.JSON(strings.NewReader(SignerConnectionRegisterABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(SignerConnectionRegisterBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &SignerConnectionRegister{SignerConnectionRegisterCaller: SignerConnectionRegisterCaller{contract: contract}, SignerConnectionRegisterTransactor: SignerConnectionRegisterTransactor{contract: contract}, SignerConnectionRegisterFilterer: SignerConnectionRegisterFilterer{contract: contract}}, nil
}

// SignerConnectionRegister is an auto generated Go binding around an Ethereum contract.
type SignerConnectionRegister struct {
	SignerConnectionRegisterCaller     // Read-only binding to the contract
	SignerConnectionRegisterTransactor // Write-only binding to the contract
	SignerConnectionRegisterFilterer   // Log filterer for contract events
}

// SignerConnectionRegisterCaller is an auto generated read-only Go binding around an Ethereum contract.
type SignerConnectionRegisterCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SignerConnectionRegisterTransactor is an auto generated write-only Go binding around an Ethereum contract.
type SignerConnectionRegisterTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SignerConnectionRegisterFilterer is an auto generated log filtering Go binding around an Ethereum contract events.
type SignerConnectionRegisterFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SignerConnectionRegisterSession is an auto generated Go binding around an Ethereum contract,
// with pre-set call and transact options.
type SignerConnectionRegisterSession struct {
	Contract     *SignerConnectionRegister // Generic contract binding to set the session for
	CallOpts     bind.CallOpts             // Call options to use throughout this session
	TransactOpts bind.TransactOpts         // Transaction auth options to use throughout this session
}

// SignerConnectionRegisterCallerSession is an auto generated read-only Go binding around an Ethereum contract,
// with pre-set call options.
type SignerConnectionRegisterCallerSession struct {
	Contract *SignerConnectionRegisterCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts                   // Call options to use throughout this session
}

// SignerConnectionRegisterTransactorSession is an auto generated write-only Go binding around an Ethereum contract,
// with pre-set transact options.
type SignerConnectionRegisterTransactorSession struct {
	Contract     *SignerConnectionRegisterTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts                   // Transaction auth options to use throughout this session
}

// SignerConnectionRegisterRaw is an auto generated low-level Go binding around an Ethereum contract.
type SignerConnectionRegisterRaw struct {
	Contract *SignerConnectionRegister // Generic contract binding to access the raw methods on
}

// SignerConnectionRegisterCallerRaw is an auto generated low-level read-only Go binding around an Ethereum contract.
type SignerConnectionRegisterCallerRaw struct {
	Contract *SignerConnectionRegisterCaller // Generic read-only contract binding to access the raw methods on
}

// SignerConnectionRegisterTransactorRaw is an auto generated low-level write-only Go binding around an Ethereum contract.
type SignerConnectionRegisterTransactorRaw struct {
	Contract *SignerConnectionRegisterTransactor // Generic write-only contract binding to access the raw methods on
}

// NewSignerConnectionRegister creates a new instance of SignerConnectionRegister, bound to a specific deployed contract.
func NewSignerConnectionRegister(address common.Address, backend bind.ContractBackend) (*SignerConnectionRegister, error) {
	contract, err := bindSignerConnectionRegister(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &SignerConnectionRegister{SignerConnectionRegisterCaller: SignerConnectionRegisterCaller{contract: contract}, SignerConnectionRegisterTransactor: SignerConnectionRegisterTransactor{contract: contract}, SignerConnectionRegisterFilterer: SignerConnectionRegisterFilterer{contract: contract}}, nil
}

// NewSignerConnectionRegisterCaller creates a new read-only instance of SignerConnectionRegister, bound to a specific deployed contract.
func NewSignerConnectionRegisterCaller(address common.Address, caller bind.ContractCaller) (*SignerConnectionRegisterCaller, error) {
	contract, err := bindSignerConnectionRegister(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &SignerConnectionRegisterCaller{contract: contract}, nil
}

// NewSignerConnectionRegisterTransactor creates a new write-only instance of SignerConnectionRegister, bound to a specific deployed contract.
func NewSignerConnectionRegisterTransactor(address common.Address, transactor bind.ContractTransactor) (*SignerConnectionRegisterTransactor, error) {
	contract, err := bindSignerConnectionRegister(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &SignerConnectionRegisterTransactor{contract: contract}, nil
}

// NewSignerConnectionRegisterFilterer creates a new log filterer instance of SignerConnectionRegister, bound to a specific deployed contract.
func NewSignerConnectionRegisterFilterer(address common.Address, filterer bind.ContractFilterer) (*SignerConnectionRegisterFilterer, error) {
	contract, err := bindSignerConnectionRegister(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &SignerConnectionRegisterFilterer{contract: contract}, nil
}

// bindSignerConnectionRegister binds a generic wrapper to an already deployed contract.
func bindSignerConnectionRegister(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(SignerConnectionRegisterABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_SignerConnectionRegister *SignerConnectionRegisterRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _SignerConnectionRegister.Contract.SignerConnectionRegisterCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_SignerConnectionRegister *SignerConnectionRegisterRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _SignerConnectionRegister.Contract.SignerConnectionRegisterTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_SignerConnectionRegister *SignerConnectionRegisterRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _SignerConnectionRegister.Contract.SignerConnectionRegisterTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_SignerConnectionRegister *SignerConnectionRegisterCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _SignerConnectionRegister.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_SignerConnectionRegister *SignerConnectionRegisterTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _SignerConnectionRegister.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_SignerConnectionRegister *SignerConnectionRegisterTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _SignerConnectionRegister.Contract.contract.Transact(opts, method, params...)
}

// PublicKeys is a free data retrieval call binding the contract method 0x2c76beff.
//
// Solidity: function _publicKeys( address) constant returns(bytes)
func (_SignerConnectionRegister *SignerConnectionRegisterCaller) PublicKeys(opts *bind.CallOpts, arg0 common.Address) ([]byte, error) {
	var (
		ret0 = new([]byte)
	)
	out := ret0
	err := _SignerConnectionRegister.contract.Call(opts, out, "_publicKeys", arg0)
	return *ret0, err
}

// PublicKeys is a free data retrieval call binding the contract method 0x2c76beff.
//
// Solidity: function _publicKeys( address) constant returns(bytes)
func (_SignerConnectionRegister *SignerConnectionRegisterSession) PublicKeys(arg0 common.Address) ([]byte, error) {
	return _SignerConnectionRegister.Contract.PublicKeys(&_SignerConnectionRegister.CallOpts, arg0)
}

// PublicKeys is a free data retrieval call binding the contract method 0x2c76beff.
//
// Solidity: function _publicKeys( address) constant returns(bytes)
func (_SignerConnectionRegister *SignerConnectionRegisterCallerSession) PublicKeys(arg0 common.Address) ([]byte, error) {
	return _SignerConnectionRegister.Contract.PublicKeys(&_SignerConnectionRegister.CallOpts, arg0)
}

// GetNodeInfo is a free data retrieval call binding the contract method 0x36056b40.
//
// Solidity: function getNodeInfo(viewIndex uint256, otherAddress address) constant returns(bytes)
func (_SignerConnectionRegister *SignerConnectionRegisterCaller) GetNodeInfo(opts *bind.CallOpts, viewIndex *big.Int, otherAddress common.Address) ([]byte, error) {
	var (
		ret0 = new([]byte)
	)
	out := ret0
	err := _SignerConnectionRegister.contract.Call(opts, out, "getNodeInfo", viewIndex, otherAddress)
	return *ret0, err
}

// GetNodeInfo is a free data retrieval call binding the contract method 0x36056b40.
//
// Solidity: function getNodeInfo(viewIndex uint256, otherAddress address) constant returns(bytes)
func (_SignerConnectionRegister *SignerConnectionRegisterSession) GetNodeInfo(viewIndex *big.Int, otherAddress common.Address) ([]byte, error) {
	return _SignerConnectionRegister.Contract.GetNodeInfo(&_SignerConnectionRegister.CallOpts, viewIndex, otherAddress)
}

// GetNodeInfo is a free data retrieval call binding the contract method 0x36056b40.
//
// Solidity: function getNodeInfo(viewIndex uint256, otherAddress address) constant returns(bytes)
func (_SignerConnectionRegister *SignerConnectionRegisterCallerSession) GetNodeInfo(viewIndex *big.Int, otherAddress common.Address) ([]byte, error) {
	return _SignerConnectionRegister.Contract.GetNodeInfo(&_SignerConnectionRegister.CallOpts, viewIndex, otherAddress)
}

// GetPublicKey is a free data retrieval call binding the contract method 0x857cdbb8.
//
// Solidity: function getPublicKey(addr address) constant returns(bytes)
func (_SignerConnectionRegister *SignerConnectionRegisterCaller) GetPublicKey(opts *bind.CallOpts, addr common.Address) ([]byte, error) {
	var (
		ret0 = new([]byte)
	)
	out := ret0
	err := _SignerConnectionRegister.contract.Call(opts, out, "getPublicKey", addr)
	return *ret0, err
}

// GetPublicKey is a free data retrieval call binding the contract method 0x857cdbb8.
//
// Solidity: function getPublicKey(addr address) constant returns(bytes)
func (_SignerConnectionRegister *SignerConnectionRegisterSession) GetPublicKey(addr common.Address) ([]byte, error) {
	return _SignerConnectionRegister.Contract.GetPublicKey(&_SignerConnectionRegister.CallOpts, addr)
}

// GetPublicKey is a free data retrieval call binding the contract method 0x857cdbb8.
//
// Solidity: function getPublicKey(addr address) constant returns(bytes)
func (_SignerConnectionRegister *SignerConnectionRegisterCallerSession) GetPublicKey(addr common.Address) ([]byte, error) {
	return _SignerConnectionRegister.Contract.GetPublicKey(&_SignerConnectionRegister.CallOpts, addr)
}

// AddNodeInfo is a paid mutator transaction binding the contract method 0xf9438991.
//
// Solidity: function addNodeInfo(viewIndex uint256, otherAddress address, encrpytedNodeInfo bytes) returns()
func (_SignerConnectionRegister *SignerConnectionRegisterTransactor) AddNodeInfo(opts *bind.TransactOpts, viewIndex *big.Int, otherAddress common.Address, encrpytedNodeInfo []byte) (*types.Transaction, error) {
	return _SignerConnectionRegister.contract.Transact(opts, "addNodeInfo", viewIndex, otherAddress, encrpytedNodeInfo)
}

// AddNodeInfo is a paid mutator transaction binding the contract method 0xf9438991.
//
// Solidity: function addNodeInfo(viewIndex uint256, otherAddress address, encrpytedNodeInfo bytes) returns()
func (_SignerConnectionRegister *SignerConnectionRegisterSession) AddNodeInfo(viewIndex *big.Int, otherAddress common.Address, encrpytedNodeInfo []byte) (*types.Transaction, error) {
	return _SignerConnectionRegister.Contract.AddNodeInfo(&_SignerConnectionRegister.TransactOpts, viewIndex, otherAddress, encrpytedNodeInfo)
}

// AddNodeInfo is a paid mutator transaction binding the contract method 0xf9438991.
//
// Solidity: function addNodeInfo(viewIndex uint256, otherAddress address, encrpytedNodeInfo bytes) returns()
func (_SignerConnectionRegister *SignerConnectionRegisterTransactorSession) AddNodeInfo(viewIndex *big.Int, otherAddress common.Address, encrpytedNodeInfo []byte) (*types.Transaction, error) {
	return _SignerConnectionRegister.Contract.AddNodeInfo(&_SignerConnectionRegister.TransactOpts, viewIndex, otherAddress, encrpytedNodeInfo)
}

// RegisterPublicKey is a paid mutator transaction binding the contract method 0x85623594.
//
// Solidity: function registerPublicKey(rsaPublicKey bytes) returns()
func (_SignerConnectionRegister *SignerConnectionRegisterTransactor) RegisterPublicKey(opts *bind.TransactOpts, rsaPublicKey []byte) (*types.Transaction, error) {
	return _SignerConnectionRegister.contract.Transact(opts, "registerPublicKey", rsaPublicKey)
}

// RegisterPublicKey is a paid mutator transaction binding the contract method 0x85623594.
//
// Solidity: function registerPublicKey(rsaPublicKey bytes) returns()
func (_SignerConnectionRegister *SignerConnectionRegisterSession) RegisterPublicKey(rsaPublicKey []byte) (*types.Transaction, error) {
	return _SignerConnectionRegister.Contract.RegisterPublicKey(&_SignerConnectionRegister.TransactOpts, rsaPublicKey)
}

// RegisterPublicKey is a paid mutator transaction binding the contract method 0x85623594.
//
// Solidity: function registerPublicKey(rsaPublicKey bytes) returns()
func (_SignerConnectionRegister *SignerConnectionRegisterTransactorSession) RegisterPublicKey(rsaPublicKey []byte) (*types.Transaction, error) {
	return _SignerConnectionRegister.Contract.RegisterPublicKey(&_SignerConnectionRegister.TransactOpts, rsaPublicKey)
}
