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

// ProxyInterfaceABI is the input ABI used to generate the binding from.
const ProxyInterfaceABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"getProxyContract\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"}]"

// ProxyInterfaceBin is the compiled bytecode used for deploying new contracts.
const ProxyInterfaceBin = `0x`

// DeployProxyInterface deploys a new cpchain contract, binding an instance of ProxyInterface to it.
func DeployProxyInterface(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *ProxyInterface, error) {
	parsed, err := abi.JSON(strings.NewReader(ProxyInterfaceABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(ProxyInterfaceBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &ProxyInterface{ProxyInterfaceCaller: ProxyInterfaceCaller{contract: contract}, ProxyInterfaceTransactor: ProxyInterfaceTransactor{contract: contract}, ProxyInterfaceFilterer: ProxyInterfaceFilterer{contract: contract}}, nil
}

// ProxyInterface is an auto generated Go binding around an cpchain contract.
type ProxyInterface struct {
	ProxyInterfaceCaller     // Read-only binding to the contract
	ProxyInterfaceTransactor // Write-only binding to the contract
	ProxyInterfaceFilterer   // Log filterer for contract events
}

// ProxyInterfaceCaller is an auto generated read-only Go binding around an cpchain contract.
type ProxyInterfaceCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProxyInterfaceTransactor is an auto generated write-only Go binding around an cpchain contract.
type ProxyInterfaceTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProxyInterfaceFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type ProxyInterfaceFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ProxyInterfaceSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type ProxyInterfaceSession struct {
	Contract     *ProxyInterface   // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// ProxyInterfaceCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type ProxyInterfaceCallerSession struct {
	Contract *ProxyInterfaceCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts         // Call options to use throughout this session
}

// ProxyInterfaceTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type ProxyInterfaceTransactorSession struct {
	Contract     *ProxyInterfaceTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts         // Transaction auth options to use throughout this session
}

// ProxyInterfaceRaw is an auto generated low-level Go binding around an cpchain contract.
type ProxyInterfaceRaw struct {
	Contract *ProxyInterface // Generic contract binding to access the raw methods on
}

// ProxyInterfaceCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type ProxyInterfaceCallerRaw struct {
	Contract *ProxyInterfaceCaller // Generic read-only contract binding to access the raw methods on
}

// ProxyInterfaceTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type ProxyInterfaceTransactorRaw struct {
	Contract *ProxyInterfaceTransactor // Generic write-only contract binding to access the raw methods on
}

// NewProxyInterface creates a new instance of ProxyInterface, bound to a specific deployed contract.
func NewProxyInterface(address common.Address, backend bind.ContractBackend) (*ProxyInterface, error) {
	contract, err := bindProxyInterface(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &ProxyInterface{ProxyInterfaceCaller: ProxyInterfaceCaller{contract: contract}, ProxyInterfaceTransactor: ProxyInterfaceTransactor{contract: contract}, ProxyInterfaceFilterer: ProxyInterfaceFilterer{contract: contract}}, nil
}

// NewProxyInterfaceCaller creates a new read-only instance of ProxyInterface, bound to a specific deployed contract.
func NewProxyInterfaceCaller(address common.Address, caller bind.ContractCaller) (*ProxyInterfaceCaller, error) {
	contract, err := bindProxyInterface(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &ProxyInterfaceCaller{contract: contract}, nil
}

// NewProxyInterfaceTransactor creates a new write-only instance of ProxyInterface, bound to a specific deployed contract.
func NewProxyInterfaceTransactor(address common.Address, transactor bind.ContractTransactor) (*ProxyInterfaceTransactor, error) {
	contract, err := bindProxyInterface(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &ProxyInterfaceTransactor{contract: contract}, nil
}

// NewProxyInterfaceFilterer creates a new log filterer instance of ProxyInterface, bound to a specific deployed contract.
func NewProxyInterfaceFilterer(address common.Address, filterer bind.ContractFilterer) (*ProxyInterfaceFilterer, error) {
	contract, err := bindProxyInterface(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &ProxyInterfaceFilterer{contract: contract}, nil
}

// bindProxyInterface binds a generic wrapper to an already deployed contract.
func bindProxyInterface(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(ProxyInterfaceABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_ProxyInterface *ProxyInterfaceRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _ProxyInterface.Contract.ProxyInterfaceCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_ProxyInterface *ProxyInterfaceRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _ProxyInterface.Contract.ProxyInterfaceTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_ProxyInterface *ProxyInterfaceRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _ProxyInterface.Contract.ProxyInterfaceTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_ProxyInterface *ProxyInterfaceCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _ProxyInterface.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_ProxyInterface *ProxyInterfaceTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _ProxyInterface.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_ProxyInterface *ProxyInterfaceTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _ProxyInterface.Contract.contract.Transact(opts, method, params...)
}

// GetProxyContract is a free data retrieval call binding the contract method 0xfc4fdd3d.
//
// Solidity: function getProxyContract(addr address) constant returns(address)
func (_ProxyInterface *ProxyInterfaceCaller) GetProxyContract(opts *bind.CallOpts, addr common.Address) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _ProxyInterface.contract.Call(opts, out, "getProxyContract", addr)
	return *ret0, err
}

// GetProxyContract is a free data retrieval call binding the contract method 0xfc4fdd3d.
//
// Solidity: function getProxyContract(addr address) constant returns(address)
func (_ProxyInterface *ProxyInterfaceSession) GetProxyContract(addr common.Address) (common.Address, error) {
	return _ProxyInterface.Contract.GetProxyContract(&_ProxyInterface.CallOpts, addr)
}

// GetProxyContract is a free data retrieval call binding the contract method 0xfc4fdd3d.
//
// Solidity: function getProxyContract(addr address) constant returns(address)
func (_ProxyInterface *ProxyInterfaceCallerSession) GetProxyContract(addr common.Address) (common.Address, error) {
	return _ProxyInterface.Contract.GetProxyContract(&_ProxyInterface.CallOpts, addr)
}

// RegisterABI is the input ABI used to generate the binding from.
const RegisterABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"},{\"name\":\"\",\"type\":\"uint256\"}],\"name\":\"uploadHistory\",\"outputs\":[{\"name\":\"fileName\",\"type\":\"string\"},{\"name\":\"fileHash\",\"type\":\"bytes32\"},{\"name\":\"fileSize\",\"type\":\"uint256\"},{\"name\":\"timeStamp\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"updatePdashAddress\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"setAdmissionAddr\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"fileName\",\"type\":\"string\"},{\"name\":\"fileHash\",\"type\":\"bytes32\"},{\"name\":\"fileSize\",\"type\":\"uint256\"}],\"name\":\"claimRegister\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"user\",\"type\":\"address\"}],\"name\":\"getUploadCount\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"user\",\"type\":\"address\"},{\"name\":\"block_num\",\"type\":\"uint256\"}],\"name\":\"getUploadCountAfterBlock\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]"

// RegisterBin is the compiled bytecode used for deploying new contracts.
const RegisterBin = `0x608060405234801561001057600080fd5b5060405160208061073a833981016040525160008054600160a060020a0319908116331790915560018054821673d81ab6b1e656550f90b2d874926b949fde97096d17905560028054600160a060020a03909316929091169190911790556106bd8061007d6000396000f3006080604052600436106100775763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166326cea737811461007c57806384b0c3021461012e578063c0e9e35e14610151578063d44fd26114610172578063f1227d36146101d4578063fcf197b214610207575b600080fd5b34801561008857600080fd5b506100a0600160a060020a036004351660243561022b565b60408051602080820186905291810184905260608101839052608080825286519082015285519091829160a083019188019080838360005b838110156100f05781810151838201526020016100d8565b50505050905090810190601f16801561011d5780820380516001836020036101000a031916815260200191505b509550505050505060405180910390f35b34801561013a57600080fd5b5061014f600160a060020a03600435166102fb565b005b34801561015d57600080fd5b5061014f600160a060020a0360043516610341565b34801561017e57600080fd5b506040805160206004803580820135601f810184900484028501840190955284845261014f9436949293602493928401919081908401838280828437509497505084359550505060209092013591506103879050565b3480156101e057600080fd5b506101f5600160a060020a0360043516610541565b60408051918252519081900360200190f35b34801561021357600080fd5b506101f5600160a060020a036004351660243561055c565b60036020528160005260406000208181548110151561024657fe5b60009182526020918290206004919091020180546040805160026001841615610100026000190190931692909204601f8101859004850283018501909152808252919450925083918301828280156102df5780601f106102b4576101008083540402835291602001916102df565b820191906000526020600020905b8154815290600101906020018083116102c257829003601f168201915b5050505050908060010154908060020154908060030154905084565b600054600160a060020a0316331461031257600080fd5b6001805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a0392909216919091179055565b600054600160a060020a0316331461035857600080fd5b6002805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a0392909216919091179055565b600254604080517ffc4fdd3d0000000000000000000000000000000000000000000000000000000081523360048201529051600160a060020a039092169163fc4fdd3d916024808201926020929091908290030181600087803b1580156103ed57600080fd5b505af1158015610401573d6000803e3d6000fd5b505050506040513d602081101561041757600080fd5b5051600154600160a060020a039081169116146104bb57604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602160248201527f6f6e6c792070646173682063616e2063616c6c20636c61696d5265676973746560448201527f7200000000000000000000000000000000000000000000000000000000000000606482015290519081900360840190fd5b336000908152600360209081526040808320815160808101835287815280840187905291820185905243606083015280546001810180835591855293839020825180519295939460049094029091019261051a928492909101906105f6565b50602082015160018201556040820151600282015560609091015160039091015550505050565b600160a060020a031660009081526003602052604090205490565b600080805b600160a060020a0385166000908152600360205260409020548110156105d057600160a060020a03851660009081526003602052604090208054859190839081106105a857fe5b90600052602060002090600402016003015411156105c8578091506105d0565b600101610561565b600160a060020a0385166000908152600360205260409020548290039250505092915050565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f1061063757805160ff1916838001178555610664565b82800160010185558215610664579182015b82811115610664578251825591602001919060010190610649565b50610670929150610674565b5090565b61068e91905b80821115610670576000815560010161067a565b905600a165627a7a7230582028773477cc6e75859b5a4a6f9480b34918c029b236afe25f682fc712c6cb69380029`

// DeployRegister deploys a new cpchain contract, binding an instance of Register to it.
func DeployRegister(auth *bind.TransactOpts, backend bind.ContractBackend, _addr common.Address) (common.Address, *types.Transaction, *Register, error) {
	parsed, err := abi.JSON(strings.NewReader(RegisterABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(RegisterBin), backend, _addr)
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

// SetAdmissionAddr is a paid mutator transaction binding the contract method 0xc0e9e35e.
//
// Solidity: function setAdmissionAddr(_addr address) returns()
func (_Register *RegisterTransactor) SetAdmissionAddr(opts *bind.TransactOpts, _addr common.Address) (*types.Transaction, error) {
	return _Register.contract.Transact(opts, "setAdmissionAddr", _addr)
}

// SetAdmissionAddr is a paid mutator transaction binding the contract method 0xc0e9e35e.
//
// Solidity: function setAdmissionAddr(_addr address) returns()
func (_Register *RegisterSession) SetAdmissionAddr(_addr common.Address) (*types.Transaction, error) {
	return _Register.Contract.SetAdmissionAddr(&_Register.TransactOpts, _addr)
}

// SetAdmissionAddr is a paid mutator transaction binding the contract method 0xc0e9e35e.
//
// Solidity: function setAdmissionAddr(_addr address) returns()
func (_Register *RegisterTransactorSession) SetAdmissionAddr(_addr common.Address) (*types.Transaction, error) {
	return _Register.Contract.SetAdmissionAddr(&_Register.TransactOpts, _addr)
}

// UpdatePdashAddress is a paid mutator transaction binding the contract method 0x84b0c302.
//
// Solidity: function updatePdashAddress(addr address) returns()
func (_Register *RegisterTransactor) UpdatePdashAddress(opts *bind.TransactOpts, addr common.Address) (*types.Transaction, error) {
	return _Register.contract.Transact(opts, "updatePdashAddress", addr)
}

// UpdatePdashAddress is a paid mutator transaction binding the contract method 0x84b0c302.
//
// Solidity: function updatePdashAddress(addr address) returns()
func (_Register *RegisterSession) UpdatePdashAddress(addr common.Address) (*types.Transaction, error) {
	return _Register.Contract.UpdatePdashAddress(&_Register.TransactOpts, addr)
}

// UpdatePdashAddress is a paid mutator transaction binding the contract method 0x84b0c302.
//
// Solidity: function updatePdashAddress(addr address) returns()
func (_Register *RegisterTransactorSession) UpdatePdashAddress(addr common.Address) (*types.Transaction, error) {
	return _Register.Contract.UpdatePdashAddress(&_Register.TransactOpts, addr)
}
