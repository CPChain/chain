// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package signerRegister

import (
	"math/big"
	"strings"

	"bitbucket.org/cpchain/chain/accounts/abi"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

// SignerConnectionRegisterABI is the input ABI used to generate the binding from.
const SignerConnectionRegisterABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"}],\"name\":\"_publicKeys\",\"outputs\":[{\"name\":\"\",\"type\":\"bytes\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"viewIndex\",\"type\":\"uint256\"},{\"name\":\"otherAddress\",\"type\":\"address\"}],\"name\":\"getNodeInfo\",\"outputs\":[{\"name\":\"\",\"type\":\"bytes\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"rsaPublicKey\",\"type\":\"bytes\"}],\"name\":\"registerPublicKey\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"getPublicKey\",\"outputs\":[{\"name\":\"\",\"type\":\"bytes\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"viewIndex\",\"type\":\"uint256\"},{\"name\":\"otherAddress\",\"type\":\"address\"},{\"name\":\"encrpytedNodeInfo\",\"type\":\"bytes\"}],\"name\":\"addNodeInfo\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]"

// SignerConnectionRegisterBin is the compiled bytecode used for deploying new contracts.
const SignerConnectionRegisterBin = `0x608060405234801561001057600080fd5b5060008054600160a060020a0319163317905561051c806100326000396000f30060806040526004361061006c5763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416632c76beff811461007157806336056b4014610107578063856235941461012b578063857cdbb814610179578063f94389911461019a575b600080fd5b34801561007d57600080fd5b50610092600160a060020a03600435166101f6565b6040805160208082528351818301528351919283929083019185019080838360005b838110156100cc5781810151838201526020016100b4565b50505050905090810190601f1680156100f95780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b34801561011357600080fd5b50610092600435600160a060020a0360243516610290565b6040805160206004803580820135601f81018490048402850184019095528484526101779436949293602493928401919081908401838280828437509497506103499650505050505050565b005b34801561018557600080fd5b50610092600160a060020a036004351661036d565b604080516020600460443581810135601f81018490048402850184019095528484526101779482359460248035600160a060020a0316953695946064949201919081908401838280828437509497506104179650505050505050565b60016020818152600092835260409283902080548451600294821615610100026000190190911693909304601f81018390048302840183019094528383529192908301828280156102885780601f1061025d57610100808354040283529160200191610288565b820191906000526020600020905b81548152906001019060200180831161026b57829003601f168201915b505050505081565b60008281526002602081815260408084203385528252808420600160a060020a0386168552825292839020805484516001821615610100026000190190911693909304601f8101839004830284018301909452838352606093909183018282801561033c5780601f106103115761010080835404028352916020019161033c565b820191906000526020600020905b81548152906001019060200180831161031f57829003601f168201915b5050505050905092915050565b336000908152600160209081526040909120825161036992840190610455565b5050565b600160a060020a03811660009081526001602081815260409283902080548451600294821615610100026000190190911693909304601f8101839004830284018301909452838352606093909183018282801561040b5780601f106103e05761010080835404028352916020019161040b565b820191906000526020600020905b8154815290600101906020018083116103ee57829003601f168201915b50505050509050919050565b60008381526002602090815260408083203384528252808320600160a060020a03861684528252909120825161044f92840190610455565b50505050565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f1061049657805160ff19168380011785556104c3565b828001600101855582156104c3579182015b828111156104c35782518255916020019190600101906104a8565b506104cf9291506104d3565b5090565b6104ed91905b808211156104cf57600081556001016104d9565b905600a165627a7a72305820c6bbe77400414faed54ee6726f7d58e12706ab7155419799a83ad9ff2b113ac20029`

// DeploySignerConnectionRegister deploys a new cpchain contract, binding an instance of SignerConnectionRegister to it.
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

// SignerConnectionRegister is an auto generated Go binding around an cpchain contract.
type SignerConnectionRegister struct {
	SignerConnectionRegisterCaller     // Read-only binding to the contract
	SignerConnectionRegisterTransactor // Write-only binding to the contract
	SignerConnectionRegisterFilterer   // Log filterer for contract events
}

// SignerConnectionRegisterCaller is an auto generated read-only Go binding around an cpchain contract.
type SignerConnectionRegisterCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SignerConnectionRegisterTransactor is an auto generated write-only Go binding around an cpchain contract.
type SignerConnectionRegisterTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SignerConnectionRegisterFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type SignerConnectionRegisterFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SignerConnectionRegisterSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type SignerConnectionRegisterSession struct {
	Contract     *SignerConnectionRegister // Generic contract binding to set the session for
	CallOpts     bind.CallOpts             // Call options to use throughout this session
	TransactOpts bind.TransactOpts         // Transaction auth options to use throughout this session
}

// SignerConnectionRegisterCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type SignerConnectionRegisterCallerSession struct {
	Contract *SignerConnectionRegisterCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts                   // Call options to use throughout this session
}

// SignerConnectionRegisterTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type SignerConnectionRegisterTransactorSession struct {
	Contract     *SignerConnectionRegisterTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts                   // Transaction auth options to use throughout this session
}

// SignerConnectionRegisterRaw is an auto generated low-level Go binding around an cpchain contract.
type SignerConnectionRegisterRaw struct {
	Contract *SignerConnectionRegister // Generic contract binding to access the raw methods on
}

// SignerConnectionRegisterCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type SignerConnectionRegisterCallerRaw struct {
	Contract *SignerConnectionRegisterCaller // Generic read-only contract binding to access the raw methods on
}

// SignerConnectionRegisterTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
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
