// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package dpor

import (
	"math/big"
	"strings"

	"bitbucket.org/cpchain/chain/accounts/abi"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// ProposerRegisterABI is the input ABI used to generate the binding from.
const ProposerRegisterABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"}],\"name\":\"_validatorPublicKeys\",\"outputs\":[{\"name\":\"\",\"type\":\"bytes\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"term\",\"type\":\"uint256\"},{\"name\":\"proposer\",\"type\":\"address\"}],\"name\":\"getNodeInfo\",\"outputs\":[{\"name\":\"\",\"type\":\"bytes\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"rsaPublicKey\",\"type\":\"bytes\"}],\"name\":\"registerPublicKey\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"getPublicKey\",\"outputs\":[{\"name\":\"\",\"type\":\"bytes\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"term\",\"type\":\"uint256\"},{\"name\":\"validator\",\"type\":\"address\"},{\"name\":\"encrpytedNodeInfo\",\"type\":\"bytes\"}],\"name\":\"addNodeInfo\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]"

// ProposerRegisterBin is the compiled bytecode used for deploying new contracts.
const ProposerRegisterBin = `0x608060405234801561001057600080fd5b5060008054600160a060020a03191633179055610524806100326000396000f30060806040526004361061006c5763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416631e4fbc40811461007157806336056b4014610107578063856235941461012b578063857cdbb814610179578063f94389911461019a575b600080fd5b34801561007d57600080fd5b50610092600160a060020a03600435166101f6565b6040805160208082528351818301528351919283929083019185019080838360005b838110156100cc5781810151838201526020016100b4565b50505050905090810190601f1680156100f95780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b34801561011357600080fd5b50610092600435600160a060020a0360243516610290565b6040805160206004803580820135601f810184900484028501840190955284845261017794369492936024939284019190819084018382808284375094975061034f9650505050505050565b005b34801561018557600080fd5b50610092600160a060020a0360043516610373565b604080516020600460443581810135601f81018490048402850184019095528484526101779482359460248035600160a060020a03169536959460649492019190819084018382808284375094975061041d9650505050505050565b60016020818152600092835260409283902080548451600294821615610100026000190190911693909304601f81018390048302840183019094528383529192908301828280156102885780601f1061025d57610100808354040283529160200191610288565b820191906000526020600020905b81548152906001019060200180831161026b57829003601f168201915b505050505081565b6000828152600260208181526040808420600160a060020a038616855282528084203380865290835293819020805482516001821615610100026000190190911694909404601f810184900484028501840190925281845260609493929091908301828280156103415780601f1061031657610100808354040283529160200191610341565b820191906000526020600020905b81548152906001019060200180831161032457829003601f168201915b505050505091505092915050565b336000908152600160209081526040909120825161036f9284019061045d565b5050565b600160a060020a03811660009081526001602081815260409283902080548451600294821615610100026000190190911693909304601f810183900483028401830190945283835260609390918301828280156104115780601f106103e657610100808354040283529160200191610411565b820191906000526020600020905b8154815290600101906020018083116103f457829003601f168201915b50505050509050919050565b600083815260026020908152604080832033808552908352818420600160a060020a03871685528352922083516104569285019061045d565b5050505050565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f1061049e57805160ff19168380011785556104cb565b828001600101855582156104cb579182015b828111156104cb5782518255916020019190600101906104b0565b506104d79291506104db565b5090565b6104f591905b808211156104d757600081556001016104e1565b905600a165627a7a723058205144f7d2a45a2fa2c55d952b6be72030b357a9513c4f890f6dc8487f4142445b0029`

// DeployProposerRegister deploys a new Ethereum contract, binding an instance of ProposerRegister to it.
func DeployProposerRegister(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *ProposerRegister, error) {
	parsed, err := abi.JSON(strings.NewReader(ProposerRegisterABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(ProposerRegisterBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &ProposerRegister{ProposerRegisterCaller: ProposerRegisterCaller{contract: contract}, ProposerRegisterTransactor: ProposerRegisterTransactor{contract: contract}, ProposerRegisterFilterer: ProposerRegisterFilterer{contract: contract}}, nil
}

// ProposerRegister is an auto generated Go binding around an Ethereum contract.
type ProposerRegister struct {
	ProposerRegisterCaller     // Read-only binding to the contract
	ProposerRegisterTransactor // Write-only binding to the contract
	ProposerRegisterFilterer   // Log filterer for contract events
}

// ProposerRegisterCaller is an auto generated read-only Go binding around an Ethereum contract.
type ProposerRegisterCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProposerRegisterTransactor is an auto generated write-only Go binding around an Ethereum contract.
type ProposerRegisterTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProposerRegisterFilterer is an auto generated log filtering Go binding around an Ethereum contract events.
type ProposerRegisterFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProposerRegisterSession is an auto generated Go binding around an Ethereum contract,
// with pre-set call and transact options.
type ProposerRegisterSession struct {
	Contract     *ProposerRegister // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// ProposerRegisterCallerSession is an auto generated read-only Go binding around an Ethereum contract,
// with pre-set call options.
type ProposerRegisterCallerSession struct {
	Contract *ProposerRegisterCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts           // Call options to use throughout this session
}

// ProposerRegisterTransactorSession is an auto generated write-only Go binding around an Ethereum contract,
// with pre-set transact options.
type ProposerRegisterTransactorSession struct {
	Contract     *ProposerRegisterTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts           // Transaction auth options to use throughout this session
}

// ProposerRegisterRaw is an auto generated low-level Go binding around an Ethereum contract.
type ProposerRegisterRaw struct {
	Contract *ProposerRegister // Generic contract binding to access the raw methods on
}

// ProposerRegisterCallerRaw is an auto generated low-level read-only Go binding around an Ethereum contract.
type ProposerRegisterCallerRaw struct {
	Contract *ProposerRegisterCaller // Generic read-only contract binding to access the raw methods on
}

// ProposerRegisterTransactorRaw is an auto generated low-level write-only Go binding around an Ethereum contract.
type ProposerRegisterTransactorRaw struct {
	Contract *ProposerRegisterTransactor // Generic write-only contract binding to access the raw methods on
}

// NewProposerRegister creates a new instance of ProposerRegister, bound to a specific deployed contract.
func NewProposerRegister(address common.Address, backend bind.ContractBackend) (*ProposerRegister, error) {
	contract, err := bindProposerRegister(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &ProposerRegister{ProposerRegisterCaller: ProposerRegisterCaller{contract: contract}, ProposerRegisterTransactor: ProposerRegisterTransactor{contract: contract}, ProposerRegisterFilterer: ProposerRegisterFilterer{contract: contract}}, nil
}

// NewProposerRegisterCaller creates a new read-only instance of ProposerRegister, bound to a specific deployed contract.
func NewProposerRegisterCaller(address common.Address, caller bind.ContractCaller) (*ProposerRegisterCaller, error) {
	contract, err := bindProposerRegister(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &ProposerRegisterCaller{contract: contract}, nil
}

// NewProposerRegisterTransactor creates a new write-only instance of ProposerRegister, bound to a specific deployed contract.
func NewProposerRegisterTransactor(address common.Address, transactor bind.ContractTransactor) (*ProposerRegisterTransactor, error) {
	contract, err := bindProposerRegister(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &ProposerRegisterTransactor{contract: contract}, nil
}

// NewProposerRegisterFilterer creates a new log filterer instance of ProposerRegister, bound to a specific deployed contract.
func NewProposerRegisterFilterer(address common.Address, filterer bind.ContractFilterer) (*ProposerRegisterFilterer, error) {
	contract, err := bindProposerRegister(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &ProposerRegisterFilterer{contract: contract}, nil
}

// bindProposerRegister binds a generic wrapper to an already deployed contract.
func bindProposerRegister(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(ProposerRegisterABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_ProposerRegister *ProposerRegisterRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _ProposerRegister.Contract.ProposerRegisterCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_ProposerRegister *ProposerRegisterRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _ProposerRegister.Contract.ProposerRegisterTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_ProposerRegister *ProposerRegisterRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _ProposerRegister.Contract.ProposerRegisterTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_ProposerRegister *ProposerRegisterCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _ProposerRegister.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_ProposerRegister *ProposerRegisterTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _ProposerRegister.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_ProposerRegister *ProposerRegisterTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _ProposerRegister.Contract.contract.Transact(opts, method, params...)
}

// ValidatorPublicKeys is a free data retrieval call binding the contract method 0x1e4fbc40.
//
// Solidity: function _validatorPublicKeys( address) constant returns(bytes)
func (_ProposerRegister *ProposerRegisterCaller) ValidatorPublicKeys(opts *bind.CallOpts, arg0 common.Address) ([]byte, error) {
	var (
		ret0 = new([]byte)
	)
	out := ret0
	err := _ProposerRegister.contract.Call(opts, out, "_validatorPublicKeys", arg0)
	return *ret0, err
}

// ValidatorPublicKeys is a free data retrieval call binding the contract method 0x1e4fbc40.
//
// Solidity: function _validatorPublicKeys( address) constant returns(bytes)
func (_ProposerRegister *ProposerRegisterSession) ValidatorPublicKeys(arg0 common.Address) ([]byte, error) {
	return _ProposerRegister.Contract.ValidatorPublicKeys(&_ProposerRegister.CallOpts, arg0)
}

// ValidatorPublicKeys is a free data retrieval call binding the contract method 0x1e4fbc40.
//
// Solidity: function _validatorPublicKeys( address) constant returns(bytes)
func (_ProposerRegister *ProposerRegisterCallerSession) ValidatorPublicKeys(arg0 common.Address) ([]byte, error) {
	return _ProposerRegister.Contract.ValidatorPublicKeys(&_ProposerRegister.CallOpts, arg0)
}

// GetNodeInfo is a free data retrieval call binding the contract method 0x36056b40.
//
// Solidity: function getNodeInfo(term uint256, proposer address) constant returns(bytes)
func (_ProposerRegister *ProposerRegisterCaller) GetNodeInfo(opts *bind.CallOpts, term *big.Int, proposer common.Address) ([]byte, error) {
	var (
		ret0 = new([]byte)
	)
	out := ret0
	err := _ProposerRegister.contract.Call(opts, out, "getNodeInfo", term, proposer)
	return *ret0, err
}

// GetNodeInfo is a free data retrieval call binding the contract method 0x36056b40.
//
// Solidity: function getNodeInfo(term uint256, proposer address) constant returns(bytes)
func (_ProposerRegister *ProposerRegisterSession) GetNodeInfo(term *big.Int, proposer common.Address) ([]byte, error) {
	return _ProposerRegister.Contract.GetNodeInfo(&_ProposerRegister.CallOpts, term, proposer)
}

// GetNodeInfo is a free data retrieval call binding the contract method 0x36056b40.
//
// Solidity: function getNodeInfo(term uint256, proposer address) constant returns(bytes)
func (_ProposerRegister *ProposerRegisterCallerSession) GetNodeInfo(term *big.Int, proposer common.Address) ([]byte, error) {
	return _ProposerRegister.Contract.GetNodeInfo(&_ProposerRegister.CallOpts, term, proposer)
}

// GetPublicKey is a free data retrieval call binding the contract method 0x857cdbb8.
//
// Solidity: function getPublicKey(addr address) constant returns(bytes)
func (_ProposerRegister *ProposerRegisterCaller) GetPublicKey(opts *bind.CallOpts, addr common.Address) ([]byte, error) {
	var (
		ret0 = new([]byte)
	)
	out := ret0
	err := _ProposerRegister.contract.Call(opts, out, "getPublicKey", addr)
	return *ret0, err
}

// GetPublicKey is a free data retrieval call binding the contract method 0x857cdbb8.
//
// Solidity: function getPublicKey(addr address) constant returns(bytes)
func (_ProposerRegister *ProposerRegisterSession) GetPublicKey(addr common.Address) ([]byte, error) {
	return _ProposerRegister.Contract.GetPublicKey(&_ProposerRegister.CallOpts, addr)
}

// GetPublicKey is a free data retrieval call binding the contract method 0x857cdbb8.
//
// Solidity: function getPublicKey(addr address) constant returns(bytes)
func (_ProposerRegister *ProposerRegisterCallerSession) GetPublicKey(addr common.Address) ([]byte, error) {
	return _ProposerRegister.Contract.GetPublicKey(&_ProposerRegister.CallOpts, addr)
}

// AddNodeInfo is a paid mutator transaction binding the contract method 0xf9438991.
//
// Solidity: function addNodeInfo(term uint256, validator address, encrpytedNodeInfo bytes) returns()
func (_ProposerRegister *ProposerRegisterTransactor) AddNodeInfo(opts *bind.TransactOpts, term *big.Int, validator common.Address, encrpytedNodeInfo []byte) (*types.Transaction, error) {
	return _ProposerRegister.contract.Transact(opts, "addNodeInfo", term, validator, encrpytedNodeInfo)
}

// AddNodeInfo is a paid mutator transaction binding the contract method 0xf9438991.
//
// Solidity: function addNodeInfo(term uint256, validator address, encrpytedNodeInfo bytes) returns()
func (_ProposerRegister *ProposerRegisterSession) AddNodeInfo(term *big.Int, validator common.Address, encrpytedNodeInfo []byte) (*types.Transaction, error) {
	return _ProposerRegister.Contract.AddNodeInfo(&_ProposerRegister.TransactOpts, term, validator, encrpytedNodeInfo)
}

// AddNodeInfo is a paid mutator transaction binding the contract method 0xf9438991.
//
// Solidity: function addNodeInfo(term uint256, validator address, encrpytedNodeInfo bytes) returns()
func (_ProposerRegister *ProposerRegisterTransactorSession) AddNodeInfo(term *big.Int, validator common.Address, encrpytedNodeInfo []byte) (*types.Transaction, error) {
	return _ProposerRegister.Contract.AddNodeInfo(&_ProposerRegister.TransactOpts, term, validator, encrpytedNodeInfo)
}

// RegisterPublicKey is a paid mutator transaction binding the contract method 0x85623594.
//
// Solidity: function registerPublicKey(rsaPublicKey bytes) returns()
func (_ProposerRegister *ProposerRegisterTransactor) RegisterPublicKey(opts *bind.TransactOpts, rsaPublicKey []byte) (*types.Transaction, error) {
	return _ProposerRegister.contract.Transact(opts, "registerPublicKey", rsaPublicKey)
}

// RegisterPublicKey is a paid mutator transaction binding the contract method 0x85623594.
//
// Solidity: function registerPublicKey(rsaPublicKey bytes) returns()
func (_ProposerRegister *ProposerRegisterSession) RegisterPublicKey(rsaPublicKey []byte) (*types.Transaction, error) {
	return _ProposerRegister.Contract.RegisterPublicKey(&_ProposerRegister.TransactOpts, rsaPublicKey)
}

// RegisterPublicKey is a paid mutator transaction binding the contract method 0x85623594.
//
// Solidity: function registerPublicKey(rsaPublicKey bytes) returns()
func (_ProposerRegister *ProposerRegisterTransactorSession) RegisterPublicKey(rsaPublicKey []byte) (*types.Transaction, error) {
	return _ProposerRegister.Contract.RegisterPublicKey(&_ProposerRegister.TransactOpts, rsaPublicKey)
}
