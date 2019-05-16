// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package campaign

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

// AdmissionInterfaceABI is the input ABI used to generate the binding from.
const AdmissionInterfaceABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"_cpuNonce\",\"type\":\"uint64\"},{\"name\":\"_cpuBlockNumber\",\"type\":\"uint256\"},{\"name\":\"_memoryNonce\",\"type\":\"uint64\"},{\"name\":\"_memoryBlockNumber\",\"type\":\"uint256\"},{\"name\":\"_sender\",\"type\":\"address\"}],\"name\":\"verify\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"}]"

// AdmissionInterfaceBin is the compiled bytecode used for deploying new contracts.
const AdmissionInterfaceBin = `0x608060405260006001556003600255600c600355600254600354026004556001600555600a60065560006007556001600860006101000a81548160ff02191690831515021790555034801561005357600080fd5b5060405160408061178d8339810180604052810190808051906020019092919080519060200190929190505050336000806101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff16021790555081600b60006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff16021790555080600c60006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff16021790555061016760045460014303610174640100000000026113cd179091906401000000009004565b600781905550505061018f565b600080828481151561018257fe5b0490508091505092915050565b6115ef8061019e6000396000f3006080604052600436106100f1576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806314b5980e146100f357806314b90a021461011e5780631984ab001461017a57806335805726146101fc5780633a713e3714610227578063488b87e5146102525780634b6b164b1461027d57806368f237a1146102a85780638cb59532146102d3578063a7e1f08b14610300578063c0e9e35e1461032d578063c351d0a514610370578063cd60e2171461039d578063db438269146103ca578063e2b281581461042f578063f2aaabdd1461045a578063fcf503f81461049d575b005b3480156100ff57600080fd5b506101086104a7565b6040518082815260200191505060405180910390f35b61017860048036038101908080359060200190929190803567ffffffffffffffff16906020019092919080359060200190929190803567ffffffffffffffff169060200190929190803590602001909291905050506104ad565b005b34801561018657600080fd5b506101a560048036038101908080359060200190929190505050610c9c565b6040518080602001828103825283818151815260200191508051906020019060200280838360005b838110156101e85780820151818401526020810190506101cd565b505050509050019250505060405180910390f35b34801561020857600080fd5b50610211610d40565b6040518082815260200191505060405180910390f35b34801561023357600080fd5b5061023c610d46565b6040518082815260200191505060405180910390f35b34801561025e57600080fd5b50610267610d4c565b6040518082815260200191505060405180910390f35b34801561028957600080fd5b50610292610d52565b6040518082815260200191505060405180910390f35b3480156102b457600080fd5b506102bd610d58565b6040518082815260200191505060405180910390f35b3480156102df57600080fd5b506102fe60048036038101908080359060200190929190505050610d5e565b005b34801561030c57600080fd5b5061032b60048036038101908080359060200190929190505050610dc3565b005b34801561033957600080fd5b5061036e600480360381019080803573ffffffffffffffffffffffffffffffffffffffff169060200190929190505050610e28565b005b34801561037c57600080fd5b5061039b60048036038101908080359060200190929190505050610ec7565b005b3480156103a957600080fd5b506103c860048036038101908080359060200190929190505050610f40565b005b3480156103d657600080fd5b5061040b600480360381019080803573ffffffffffffffffffffffffffffffffffffffff169060200190929190505050610fb9565b60405180848152602001838152602001828152602001935050505060405180910390f35b34801561043b57600080fd5b50610444611094565b6040518082815260200191505060405180910390f35b34801561046657600080fd5b5061049b600480360381019080803573ffffffffffffffffffffffffffffffffffffffff16906020019092919050505061109a565b005b6104a5611139565b005b60035481565b600080600860009054906101000a900460ff161561050257600a6104df600454600143036113cd90919063ffffffff16565b036007819055506000600860006101000a81548160ff0219169083151502179055505b60011515600c60009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1663a8f07697336040518263ffffffff167c0100000000000000000000000000000000000000000000000000000000028152600401808273ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001915050602060405180830381600087803b1580156105c357600080fd5b505af11580156105d7573d6000803e3d6000fd5b505050506040513d60208110156105ed57600080fd5b81019080805190602001909291905050501515141515610675576040517f08c379a00000000000000000000000000000000000000000000000000000000081526004018080602001828103825260128152602001807f6e6f7420524e6f646520627920726e6f6465000000000000000000000000000081525060200191505060405180910390fd5b600b60009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16633395492e87878787336040518663ffffffff167c0100000000000000000000000000000000000000000000000000000000028152600401808667ffffffffffffffff1667ffffffffffffffff1681526020018581526020018467ffffffffffffffff1667ffffffffffffffff1681526020018381526020018273ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200195505050505050602060405180830381600087803b15801561077a57600080fd5b505af115801561078e573d6000803e3d6000fd5b505050506040513d60208110156107a457600080fd5b81019080805190602001909291905050501515610829576040517f08c379a00000000000000000000000000000000000000000000000000000000081526004018080602001828103825260198152602001807f637075206f72206d656d6f7279206e6f74207061737365642e0000000000000081525060200191505060405180910390fd5b600554871015801561083d57506006548711155b15156108b1576040517f08c379a000000000000000000000000000000000000000000000000000000000815260040180806020018281038252601d8152602001807f6e756d206f662063616d706169676e206f7574206f662072616e67652e00000081525060200191505060405180910390fd5b6108b9611139565b3391506000600960008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000015414151561099c576040517f08c379a00000000000000000000000000000000000000000000000000000000081526004018080602001828103825260378152602001807f706c6561736520776169746520756e74696c20796f7572206c61737420726f7581526020017f6e6420656e64656420616e642074727920616761696e2e00000000000000000081525060400191505060405180910390fd5b86600960008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600001819055506109f8600180546113e890919063ffffffff16565b600960008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060010181905550610a9387600960008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600101546113e890919063ffffffff16565b600960008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060020181905550600960008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206001015490505b600960008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060020154811015610b9c57610b8e82600a600084815260200190815260200160002061140690919063ffffffff16565b508080600101915050610b1f565b7f8d468194bdd18296bee5d126aa15cc492d26bdf22a0585c4a47ec4490d3a0fcf82600960008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060010154600960008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060020154604051808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001838152602001828152602001935050505060405180910390a150505050505050565b6060600a6000838152602001908152602001600020600101805480602002602001604051908101604052809291908181526020018280548015610d3457602002820191906000526020600020905b8160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019060010190808311610cea575b50505050509050919050565b60015481565b60055481565b60075481565b60045481565b60025481565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff16141515610db957600080fd5b8060068190555050565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff16141515610e1e57600080fd5b8060058190555050565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff16141515610e8357600080fd5b80600b60006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff16021790555050565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff16141515610f2257600080fd5b80600381905550610f37600354600254611532565b60048190555050565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff16141515610f9b57600080fd5b80600281905550610fb0600354600254611532565b60048190555050565b6000806000600960008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060000154600960008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060010154600960008773ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600201549250925092509193909250565b60065481565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff161415156110f557600080fd5b80600c60006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff16021790555050565b600080600061114661156d565b600154600754101515611158576113c8565b5b6001546007541115156113c757600a60006007548152602001908152602001600020600101805490509250600091505b828210156113b057600a60006007548152602001908152602001600020600101828154811015156111b657fe5b9060005260206000200160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1690506000600960008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600001541415611233576113a3565b611280600960008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000015460016115aa565b600960008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600001819055506000600960008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000015414156113a2576000600960008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600101819055506000600960008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600201819055505b5b8180600101925050611189565b600760008154809291906001019190505550611159565b5b505050565b60008082848115156113db57fe5b0490508091505092915050565b60008082840190508381101515156113fc57fe5b8091505092915050565b60008260000160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060009054906101000a900460ff1615611465576000905061152c565b60018360000160008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060006101000a81548160ff021916908315150217905550826001018290806001815401808255809150509060018203906000526020600020016000909192909190916101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff16021790555050600190505b92915050565b60008060008414156115475760009150611566565b828402905082848281151561155857fe5b0414151561156257fe5b8091505b5092915050565b600043905060008114156115885760006001819055506115a7565b6115a0600454600183036113cd90919063ffffffff16565b6001819055505b50565b60008282111515156115b857fe5b8183039050929150505600a165627a7a72305820ab2dbf5a53ee2fee4fa054381ef5667f2ed840810302612f54f18b2a8ca6b0980029`

// DeployAdmissionInterface deploys a new cpchain contract, binding an instance of AdmissionInterface to it.
func DeployAdmissionInterface(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *AdmissionInterface, error) {
	parsed, err := abi.JSON(strings.NewReader(AdmissionInterfaceABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(AdmissionInterfaceBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &AdmissionInterface{AdmissionInterfaceCaller: AdmissionInterfaceCaller{contract: contract}, AdmissionInterfaceTransactor: AdmissionInterfaceTransactor{contract: contract}, AdmissionInterfaceFilterer: AdmissionInterfaceFilterer{contract: contract}}, nil
}

// AdmissionInterface is an auto generated Go binding around an cpchain contract.
type AdmissionInterface struct {
	AdmissionInterfaceCaller     // Read-only binding to the contract
	AdmissionInterfaceTransactor // Write-only binding to the contract
	AdmissionInterfaceFilterer   // Log filterer for contract events
}

// AdmissionInterfaceCaller is an auto generated read-only Go binding around an cpchain contract.
type AdmissionInterfaceCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// AdmissionInterfaceTransactor is an auto generated write-only Go binding around an cpchain contract.
type AdmissionInterfaceTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// AdmissionInterfaceFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type AdmissionInterfaceFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// AdmissionInterfaceSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type AdmissionInterfaceSession struct {
	Contract     *AdmissionInterface // Generic contract binding to set the session for
	CallOpts     bind.CallOpts       // Call options to use throughout this session
	TransactOpts bind.TransactOpts   // Transaction auth options to use throughout this session
}

// AdmissionInterfaceCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type AdmissionInterfaceCallerSession struct {
	Contract *AdmissionInterfaceCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts             // Call options to use throughout this session
}

// AdmissionInterfaceTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type AdmissionInterfaceTransactorSession struct {
	Contract     *AdmissionInterfaceTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts             // Transaction auth options to use throughout this session
}

// AdmissionInterfaceRaw is an auto generated low-level Go binding around an cpchain contract.
type AdmissionInterfaceRaw struct {
	Contract *AdmissionInterface // Generic contract binding to access the raw methods on
}

// AdmissionInterfaceCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type AdmissionInterfaceCallerRaw struct {
	Contract *AdmissionInterfaceCaller // Generic read-only contract binding to access the raw methods on
}

// AdmissionInterfaceTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type AdmissionInterfaceTransactorRaw struct {
	Contract *AdmissionInterfaceTransactor // Generic write-only contract binding to access the raw methods on
}

// NewAdmissionInterface creates a new instance of AdmissionInterface, bound to a specific deployed contract.
func NewAdmissionInterface(address common.Address, backend bind.ContractBackend) (*AdmissionInterface, error) {
	contract, err := bindAdmissionInterface(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &AdmissionInterface{AdmissionInterfaceCaller: AdmissionInterfaceCaller{contract: contract}, AdmissionInterfaceTransactor: AdmissionInterfaceTransactor{contract: contract}, AdmissionInterfaceFilterer: AdmissionInterfaceFilterer{contract: contract}}, nil
}

// NewAdmissionInterfaceCaller creates a new read-only instance of AdmissionInterface, bound to a specific deployed contract.
func NewAdmissionInterfaceCaller(address common.Address, caller bind.ContractCaller) (*AdmissionInterfaceCaller, error) {
	contract, err := bindAdmissionInterface(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &AdmissionInterfaceCaller{contract: contract}, nil
}

// NewAdmissionInterfaceTransactor creates a new write-only instance of AdmissionInterface, bound to a specific deployed contract.
func NewAdmissionInterfaceTransactor(address common.Address, transactor bind.ContractTransactor) (*AdmissionInterfaceTransactor, error) {
	contract, err := bindAdmissionInterface(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &AdmissionInterfaceTransactor{contract: contract}, nil
}

// NewAdmissionInterfaceFilterer creates a new log filterer instance of AdmissionInterface, bound to a specific deployed contract.
func NewAdmissionInterfaceFilterer(address common.Address, filterer bind.ContractFilterer) (*AdmissionInterfaceFilterer, error) {
	contract, err := bindAdmissionInterface(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &AdmissionInterfaceFilterer{contract: contract}, nil
}

// bindAdmissionInterface binds a generic wrapper to an already deployed contract.
func bindAdmissionInterface(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(AdmissionInterfaceABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_AdmissionInterface *AdmissionInterfaceRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _AdmissionInterface.Contract.AdmissionInterfaceCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_AdmissionInterface *AdmissionInterfaceRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _AdmissionInterface.Contract.AdmissionInterfaceTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_AdmissionInterface *AdmissionInterfaceRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _AdmissionInterface.Contract.AdmissionInterfaceTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_AdmissionInterface *AdmissionInterfaceCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _AdmissionInterface.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_AdmissionInterface *AdmissionInterfaceTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _AdmissionInterface.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_AdmissionInterface *AdmissionInterfaceTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _AdmissionInterface.Contract.contract.Transact(opts, method, params...)
}

// Verify is a free data retrieval call binding the contract method 0x3395492e.
//
// Solidity: function verify(_cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256, _sender address) constant returns(bool)
func (_AdmissionInterface *AdmissionInterfaceCaller) Verify(opts *bind.CallOpts, _cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int, _sender common.Address) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _AdmissionInterface.contract.Call(opts, out, "verify", _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber, _sender)
	return *ret0, err
}

// Verify is a free data retrieval call binding the contract method 0x3395492e.
//
// Solidity: function verify(_cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256, _sender address) constant returns(bool)
func (_AdmissionInterface *AdmissionInterfaceSession) Verify(_cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int, _sender common.Address) (bool, error) {
	return _AdmissionInterface.Contract.Verify(&_AdmissionInterface.CallOpts, _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber, _sender)
}

// Verify is a free data retrieval call binding the contract method 0x3395492e.
//
// Solidity: function verify(_cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256, _sender address) constant returns(bool)
func (_AdmissionInterface *AdmissionInterfaceCallerSession) Verify(_cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int, _sender common.Address) (bool, error) {
	return _AdmissionInterface.Contract.Verify(&_AdmissionInterface.CallOpts, _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber, _sender)
}

// CampaignABI is the input ABI used to generate the binding from.
const CampaignABI = "[{\"constant\":true,\"inputs\":[],\"name\":\"termLen\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_termIdx\",\"type\":\"uint256\"}],\"name\":\"candidatesOf\",\"outputs\":[{\"name\":\"\",\"type\":\"address[]\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_numOfCampaign\",\"type\":\"uint256\"},{\"name\":\"_cpuNonce\",\"type\":\"uint64\"},{\"name\":\"_cpuBlockNumber\",\"type\":\"uint256\"},{\"name\":\"_memoryNonce\",\"type\":\"uint64\"},{\"name\":\"_memoryBlockNumber\",\"type\":\"uint256\"},{\"name\":\"version\",\"type\":\"uint256\"}],\"name\":\"claimCampaign\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"termIdx\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"minNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"numPerRound\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"viewLen\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"updatedTermIdx\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_supportedVersion\",\"type\":\"uint256\"}],\"name\":\"updateSupportedVersion\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_maxNoc\",\"type\":\"uint256\"}],\"name\":\"updateMaxNoc\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_minNoc\",\"type\":\"uint256\"}],\"name\":\"updateMinNoc\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"acceptableBlocks\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"setAdmissionAddr\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_termLen\",\"type\":\"uint256\"}],\"name\":\"updateTermLen\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_viewLen\",\"type\":\"uint256\"}],\"name\":\"updateViewLen\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"supportedVersion\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_acceptableBlocks\",\"type\":\"uint256\"}],\"name\":\"updateAcceptableBlocks\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_candidate\",\"type\":\"address\"}],\"name\":\"candidateInfoOf\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"maxNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"setRnodeInterface\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[{\"name\":\"_admissionAddr\",\"type\":\"address\"},{\"name\":\"_rnodeAddr\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"fallback\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"candidate\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"startTermIdx\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"stopTermIdx\",\"type\":\"uint256\"}],\"name\":\"ClaimCampaign\",\"type\":\"event\"}]"

// CampaignBin is the compiled bytecode used for deploying new contracts.
const CampaignBin = `0x60806040526000600181815560036002819055600c905560246004556005819055600a600681905560078190556008829055600992909255815460ff191617905534801561004c57600080fd5b50604051604080610e248339810160405280516020909101516000805433600160a060020a031991821617909155600d80548216600160a060020a0380861691909117909155600e80549092169083161790556004546100d1906100be4360016401000000006100dc8102610a781704565b90640100000000610a8f6100ee82021704565b600955506101059050565b6000828211156100e857fe5b50900390565b60008082848115156100fc57fe5b04949350505050565b610d10806101146000396000f3006080604052600436106101115763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166314b5980e81146101165780631984ab001461013d578063350cc724146101a557806335805726146101dc5780633a713e37146101f15780634b6b164b1461020657806368f237a11461021b57806370e580e5146102305780637dd604d6146102455780638cb595321461025d578063a7e1f08b14610275578063a9d1de481461028d578063c0e9e35e146102a2578063c351d0a5146102c3578063cd60e217146102db578063d5601e9f146102f3578063dae49ab214610308578063db43826914610320578063e2b281581461035f578063f2aaabdd14610374575b600080fd5b34801561012257600080fd5b5061012b610395565b60408051918252519081900360200190f35b34801561014957600080fd5b5061015560043561039b565b60408051602080825283518183015283519192839290830191858101910280838360005b83811015610191578181015183820152602001610179565b505050509050019250505060405180910390f35b3480156101b157600080fd5b506101da60043567ffffffffffffffff602435811690604435906064351660843560a43561040a565b005b3480156101e857600080fd5b5061012b6108cb565b3480156101fd57600080fd5b5061012b6108d1565b34801561021257600080fd5b5061012b6108d7565b34801561022757600080fd5b5061012b6108dd565b34801561023c57600080fd5b5061012b6108e3565b34801561025157600080fd5b506101da6004356108e9565b34801561026957600080fd5b506101da600435610905565b34801561028157600080fd5b506101da600435610921565b34801561029957600080fd5b5061012b61093d565b3480156102ae57600080fd5b506101da600160a060020a0360043516610943565b3480156102cf57600080fd5b506101da600435610989565b3480156102e757600080fd5b506101da6004356109b9565b3480156102ff57600080fd5b5061012b6109e2565b34801561031457600080fd5b506101da6004356109e8565b34801561032c57600080fd5b50610341600160a060020a0360043516610a04565b60408051938452602084019290925282820152519081900360600190f35b34801561036b57600080fd5b5061012b610a2c565b34801561038057600080fd5b506101da600160a060020a0360043516610a32565b60035481565b6000818152600c60209081526040918290206001018054835181840281018401909452808452606093928301828280156103fe57602002820191906000526020600020905b8154600160a060020a031681526001909101906020018083116103e0575b50505050509050919050565b600a54600090819060ff161561044c5760045461043e9061043243600163ffffffff610a7816565b9063ffffffff610a8f16565b600955600a805460ff191690555b60085483101561045b57600080fd5b60075461046f90439063ffffffff610a7816565b8610158015610491575060075461048d90439063ffffffff610a7816565b8410155b151561049c57600080fd5b600e54604080517fa8f076970000000000000000000000000000000000000000000000000000000081523360048201529051600160a060020a039092169163a8f07697916024808201926020929091908290030181600087803b15801561050257600080fd5b505af1158015610516573d6000803e3d6000fd5b505050506040513d602081101561052c57600080fd5b50511515600114610587576040805160e560020a62461bcd02815260206004820152601260248201527f6e6f7420524e6f646520627920726e6f64650000000000000000000000000000604482015290519081900360640190fd5b600d54604080517f3395492e00000000000000000000000000000000000000000000000000000000815267ffffffffffffffff808b166004830152602482018a905288166044820152606481018790523360848201529051600160a060020a0390921691633395492e9160a4808201926020929091908290030181600087803b15801561061357600080fd5b505af1158015610627573d6000803e3d6000fd5b505050506040513d602081101561063d57600080fd5b50511515610695576040805160e560020a62461bcd02815260206004820152601960248201527f637075206f72206d656d6f7279206e6f74207061737365642e00000000000000604482015290519081900360640190fd5b60055488101580156106a957506006548811155b15156106ff576040805160e560020a62461bcd02815260206004820152601d60248201527f6e756d206f662063616d706169676e206f7574206f662072616e67652e000000604482015290519081900360640190fd5b610707610aab565b336000818152600b602052604090205490925015610795576040805160e560020a62461bcd02815260206004820152603760248201527f706c6561736520776169746520756e74696c20796f7572206c61737420726f7560448201527f6e6420656e64656420616e642074727920616761696e2e000000000000000000606482015290519081900360840190fd5b600160a060020a0382166000908152600b60205260409020889055600180546107c39163ffffffff610bf216565b600160a060020a0383166000908152600b602052604090206001018190556107f1908963ffffffff610bf216565b600160a060020a0383166000908152600b6020526040902060028101919091556001015490505b600160a060020a0382166000908152600b6020526040902060020154811015610862576000818152600c60205260409020610859908363ffffffff610c0816565b50600101610818565b600160a060020a0382166000818152600b6020908152604091829020600181015460029091015483519485529184015282820152517f8d468194bdd18296bee5d126aa15cc492d26bdf22a0585c4a47ec4490d3a0fcf9181900360600190a15050505050505050565b60015481565b60055481565b60045481565b60025481565b60095481565b600054600160a060020a0316331461090057600080fd5b600855565b600054600160a060020a0316331461091c57600080fd5b600655565b600054600160a060020a0316331461093857600080fd5b600555565b60075481565b600054600160a060020a0316331461095a57600080fd5b600d805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a0392909216919091179055565b600054600160a060020a031633146109a057600080fd5b60038190556002546109b3908290610c88565b60045550565b600054600160a060020a031633146109d057600080fd5b60028190556003546109b39082610c88565b60085481565b600054600160a060020a031633146109ff57600080fd5b600755565b600160a060020a03166000908152600b60205260409020805460018201546002909201549092565b60065481565b600054600160a060020a03163314610a4957600080fd5b600e805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a0392909216919091179055565b600082821115610a8457fe5b508082035b92915050565b6000808284811515610a9d57fe5b0490508091505b5092915050565b6000806000806000610abb610cb3565b60015460095410610acb57610beb565b600954600154039450600092505b84831015610beb57600954610af590600163ffffffff610bf216565b60098190556000908152600c6020526040812060010154945091505b83821015610be0576009546000908152600c60205260409020600101805483908110610b3957fe5b6000918252602080832090910154600160a060020a0316808352600b9091526040909120549091501515610b6c57610bd5565b600160a060020a0381166000908152600b6020526040902054610b90906001610a78565b600160a060020a0382166000908152600b602052604090208190551515610bd557600160a060020a0381166000908152600b6020526040812060018101829055600201555b600190910190610b11565b600190920191610ad9565b5050505050565b600082820183811015610c0157fe5b9392505050565b600160a060020a03811660009081526020839052604081205460ff1615610c3157506000610a89565b50600160a060020a03166000818152602083815260408220805460ff1916600190811790915593840180548086018255908352912001805473ffffffffffffffffffffffffffffffffffffffff1916909117905590565b600080831515610c9b5760009150610aa4565b50828202828482811515610cab57fe5b0414610c0157fe5b43801515610cc5576000600155610ce1565b600454610cdd9061043283600163ffffffff610a7816565b6001555b505600a165627a7a723058202f4eb05794f5cb5864cd7e46eb7b45904ae03fd2074d8cc07cb755207f07e7760029`

// DeployCampaign deploys a new cpchain contract, binding an instance of Campaign to it.
func DeployCampaign(auth *bind.TransactOpts, backend bind.ContractBackend, _admissionAddr common.Address, _rnodeAddr common.Address) (common.Address, *types.Transaction, *Campaign, error) {
	parsed, err := abi.JSON(strings.NewReader(CampaignABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(CampaignBin), backend, _admissionAddr, _rnodeAddr)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &Campaign{CampaignCaller: CampaignCaller{contract: contract}, CampaignTransactor: CampaignTransactor{contract: contract}, CampaignFilterer: CampaignFilterer{contract: contract}}, nil
}

// Campaign is an auto generated Go binding around an cpchain contract.
type Campaign struct {
	CampaignCaller     // Read-only binding to the contract
	CampaignTransactor // Write-only binding to the contract
	CampaignFilterer   // Log filterer for contract events
}

// CampaignCaller is an auto generated read-only Go binding around an cpchain contract.
type CampaignCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// CampaignTransactor is an auto generated write-only Go binding around an cpchain contract.
type CampaignTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// CampaignFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type CampaignFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// CampaignSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type CampaignSession struct {
	Contract     *Campaign         // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// CampaignCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type CampaignCallerSession struct {
	Contract *CampaignCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts   // Call options to use throughout this session
}

// CampaignTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type CampaignTransactorSession struct {
	Contract     *CampaignTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts   // Transaction auth options to use throughout this session
}

// CampaignRaw is an auto generated low-level Go binding around an cpchain contract.
type CampaignRaw struct {
	Contract *Campaign // Generic contract binding to access the raw methods on
}

// CampaignCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type CampaignCallerRaw struct {
	Contract *CampaignCaller // Generic read-only contract binding to access the raw methods on
}

// CampaignTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type CampaignTransactorRaw struct {
	Contract *CampaignTransactor // Generic write-only contract binding to access the raw methods on
}

// NewCampaign creates a new instance of Campaign, bound to a specific deployed contract.
func NewCampaign(address common.Address, backend bind.ContractBackend) (*Campaign, error) {
	contract, err := bindCampaign(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &Campaign{CampaignCaller: CampaignCaller{contract: contract}, CampaignTransactor: CampaignTransactor{contract: contract}, CampaignFilterer: CampaignFilterer{contract: contract}}, nil
}

// NewCampaignCaller creates a new read-only instance of Campaign, bound to a specific deployed contract.
func NewCampaignCaller(address common.Address, caller bind.ContractCaller) (*CampaignCaller, error) {
	contract, err := bindCampaign(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &CampaignCaller{contract: contract}, nil
}

// NewCampaignTransactor creates a new write-only instance of Campaign, bound to a specific deployed contract.
func NewCampaignTransactor(address common.Address, transactor bind.ContractTransactor) (*CampaignTransactor, error) {
	contract, err := bindCampaign(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &CampaignTransactor{contract: contract}, nil
}

// NewCampaignFilterer creates a new log filterer instance of Campaign, bound to a specific deployed contract.
func NewCampaignFilterer(address common.Address, filterer bind.ContractFilterer) (*CampaignFilterer, error) {
	contract, err := bindCampaign(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &CampaignFilterer{contract: contract}, nil
}

// bindCampaign binds a generic wrapper to an already deployed contract.
func bindCampaign(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(CampaignABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Campaign *CampaignRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Campaign.Contract.CampaignCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Campaign *CampaignRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Campaign.Contract.CampaignTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Campaign *CampaignRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Campaign.Contract.CampaignTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Campaign *CampaignCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Campaign.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Campaign *CampaignTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Campaign.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Campaign *CampaignTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Campaign.Contract.contract.Transact(opts, method, params...)
}

// AcceptableBlocks is a free data retrieval call binding the contract method 0xa9d1de48.
//
// Solidity: function acceptableBlocks() constant returns(uint256)
func (_Campaign *CampaignCaller) AcceptableBlocks(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "acceptableBlocks")
	return *ret0, err
}

// AcceptableBlocks is a free data retrieval call binding the contract method 0xa9d1de48.
//
// Solidity: function acceptableBlocks() constant returns(uint256)
func (_Campaign *CampaignSession) AcceptableBlocks() (*big.Int, error) {
	return _Campaign.Contract.AcceptableBlocks(&_Campaign.CallOpts)
}

// AcceptableBlocks is a free data retrieval call binding the contract method 0xa9d1de48.
//
// Solidity: function acceptableBlocks() constant returns(uint256)
func (_Campaign *CampaignCallerSession) AcceptableBlocks() (*big.Int, error) {
	return _Campaign.Contract.AcceptableBlocks(&_Campaign.CallOpts)
}

// CandidateInfoOf is a free data retrieval call binding the contract method 0xdb438269.
//
// Solidity: function candidateInfoOf(_candidate address) constant returns(uint256, uint256, uint256)
func (_Campaign *CampaignCaller) CandidateInfoOf(opts *bind.CallOpts, _candidate common.Address) (*big.Int, *big.Int, *big.Int, error) {
	var (
		ret0 = new(*big.Int)
		ret1 = new(*big.Int)
		ret2 = new(*big.Int)
	)
	out := &[]interface{}{
		ret0,
		ret1,
		ret2,
	}
	err := _Campaign.contract.Call(opts, out, "candidateInfoOf", _candidate)
	return *ret0, *ret1, *ret2, err
}

// CandidateInfoOf is a free data retrieval call binding the contract method 0xdb438269.
//
// Solidity: function candidateInfoOf(_candidate address) constant returns(uint256, uint256, uint256)
func (_Campaign *CampaignSession) CandidateInfoOf(_candidate common.Address) (*big.Int, *big.Int, *big.Int, error) {
	return _Campaign.Contract.CandidateInfoOf(&_Campaign.CallOpts, _candidate)
}

// CandidateInfoOf is a free data retrieval call binding the contract method 0xdb438269.
//
// Solidity: function candidateInfoOf(_candidate address) constant returns(uint256, uint256, uint256)
func (_Campaign *CampaignCallerSession) CandidateInfoOf(_candidate common.Address) (*big.Int, *big.Int, *big.Int, error) {
	return _Campaign.Contract.CandidateInfoOf(&_Campaign.CallOpts, _candidate)
}

// CandidatesOf is a free data retrieval call binding the contract method 0x1984ab00.
//
// Solidity: function candidatesOf(_termIdx uint256) constant returns(address[])
func (_Campaign *CampaignCaller) CandidatesOf(opts *bind.CallOpts, _termIdx *big.Int) ([]common.Address, error) {
	var (
		ret0 = new([]common.Address)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "candidatesOf", _termIdx)
	return *ret0, err
}

// CandidatesOf is a free data retrieval call binding the contract method 0x1984ab00.
//
// Solidity: function candidatesOf(_termIdx uint256) constant returns(address[])
func (_Campaign *CampaignSession) CandidatesOf(_termIdx *big.Int) ([]common.Address, error) {
	return _Campaign.Contract.CandidatesOf(&_Campaign.CallOpts, _termIdx)
}

// CandidatesOf is a free data retrieval call binding the contract method 0x1984ab00.
//
// Solidity: function candidatesOf(_termIdx uint256) constant returns(address[])
func (_Campaign *CampaignCallerSession) CandidatesOf(_termIdx *big.Int) ([]common.Address, error) {
	return _Campaign.Contract.CandidatesOf(&_Campaign.CallOpts, _termIdx)
}

// MaxNoc is a free data retrieval call binding the contract method 0xe2b28158.
//
// Solidity: function maxNoc() constant returns(uint256)
func (_Campaign *CampaignCaller) MaxNoc(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "maxNoc")
	return *ret0, err
}

// MaxNoc is a free data retrieval call binding the contract method 0xe2b28158.
//
// Solidity: function maxNoc() constant returns(uint256)
func (_Campaign *CampaignSession) MaxNoc() (*big.Int, error) {
	return _Campaign.Contract.MaxNoc(&_Campaign.CallOpts)
}

// MaxNoc is a free data retrieval call binding the contract method 0xe2b28158.
//
// Solidity: function maxNoc() constant returns(uint256)
func (_Campaign *CampaignCallerSession) MaxNoc() (*big.Int, error) {
	return _Campaign.Contract.MaxNoc(&_Campaign.CallOpts)
}

// MinNoc is a free data retrieval call binding the contract method 0x3a713e37.
//
// Solidity: function minNoc() constant returns(uint256)
func (_Campaign *CampaignCaller) MinNoc(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "minNoc")
	return *ret0, err
}

// MinNoc is a free data retrieval call binding the contract method 0x3a713e37.
//
// Solidity: function minNoc() constant returns(uint256)
func (_Campaign *CampaignSession) MinNoc() (*big.Int, error) {
	return _Campaign.Contract.MinNoc(&_Campaign.CallOpts)
}

// MinNoc is a free data retrieval call binding the contract method 0x3a713e37.
//
// Solidity: function minNoc() constant returns(uint256)
func (_Campaign *CampaignCallerSession) MinNoc() (*big.Int, error) {
	return _Campaign.Contract.MinNoc(&_Campaign.CallOpts)
}

// NumPerRound is a free data retrieval call binding the contract method 0x4b6b164b.
//
// Solidity: function numPerRound() constant returns(uint256)
func (_Campaign *CampaignCaller) NumPerRound(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "numPerRound")
	return *ret0, err
}

// NumPerRound is a free data retrieval call binding the contract method 0x4b6b164b.
//
// Solidity: function numPerRound() constant returns(uint256)
func (_Campaign *CampaignSession) NumPerRound() (*big.Int, error) {
	return _Campaign.Contract.NumPerRound(&_Campaign.CallOpts)
}

// NumPerRound is a free data retrieval call binding the contract method 0x4b6b164b.
//
// Solidity: function numPerRound() constant returns(uint256)
func (_Campaign *CampaignCallerSession) NumPerRound() (*big.Int, error) {
	return _Campaign.Contract.NumPerRound(&_Campaign.CallOpts)
}

// SupportedVersion is a free data retrieval call binding the contract method 0xd5601e9f.
//
// Solidity: function supportedVersion() constant returns(uint256)
func (_Campaign *CampaignCaller) SupportedVersion(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "supportedVersion")
	return *ret0, err
}

// SupportedVersion is a free data retrieval call binding the contract method 0xd5601e9f.
//
// Solidity: function supportedVersion() constant returns(uint256)
func (_Campaign *CampaignSession) SupportedVersion() (*big.Int, error) {
	return _Campaign.Contract.SupportedVersion(&_Campaign.CallOpts)
}

// SupportedVersion is a free data retrieval call binding the contract method 0xd5601e9f.
//
// Solidity: function supportedVersion() constant returns(uint256)
func (_Campaign *CampaignCallerSession) SupportedVersion() (*big.Int, error) {
	return _Campaign.Contract.SupportedVersion(&_Campaign.CallOpts)
}

// TermIdx is a free data retrieval call binding the contract method 0x35805726.
//
// Solidity: function termIdx() constant returns(uint256)
func (_Campaign *CampaignCaller) TermIdx(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "termIdx")
	return *ret0, err
}

// TermIdx is a free data retrieval call binding the contract method 0x35805726.
//
// Solidity: function termIdx() constant returns(uint256)
func (_Campaign *CampaignSession) TermIdx() (*big.Int, error) {
	return _Campaign.Contract.TermIdx(&_Campaign.CallOpts)
}

// TermIdx is a free data retrieval call binding the contract method 0x35805726.
//
// Solidity: function termIdx() constant returns(uint256)
func (_Campaign *CampaignCallerSession) TermIdx() (*big.Int, error) {
	return _Campaign.Contract.TermIdx(&_Campaign.CallOpts)
}

// TermLen is a free data retrieval call binding the contract method 0x14b5980e.
//
// Solidity: function termLen() constant returns(uint256)
func (_Campaign *CampaignCaller) TermLen(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "termLen")
	return *ret0, err
}

// TermLen is a free data retrieval call binding the contract method 0x14b5980e.
//
// Solidity: function termLen() constant returns(uint256)
func (_Campaign *CampaignSession) TermLen() (*big.Int, error) {
	return _Campaign.Contract.TermLen(&_Campaign.CallOpts)
}

// TermLen is a free data retrieval call binding the contract method 0x14b5980e.
//
// Solidity: function termLen() constant returns(uint256)
func (_Campaign *CampaignCallerSession) TermLen() (*big.Int, error) {
	return _Campaign.Contract.TermLen(&_Campaign.CallOpts)
}

// UpdatedTermIdx is a free data retrieval call binding the contract method 0x70e580e5.
//
// Solidity: function updatedTermIdx() constant returns(uint256)
func (_Campaign *CampaignCaller) UpdatedTermIdx(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "updatedTermIdx")
	return *ret0, err
}

// UpdatedTermIdx is a free data retrieval call binding the contract method 0x70e580e5.
//
// Solidity: function updatedTermIdx() constant returns(uint256)
func (_Campaign *CampaignSession) UpdatedTermIdx() (*big.Int, error) {
	return _Campaign.Contract.UpdatedTermIdx(&_Campaign.CallOpts)
}

// UpdatedTermIdx is a free data retrieval call binding the contract method 0x70e580e5.
//
// Solidity: function updatedTermIdx() constant returns(uint256)
func (_Campaign *CampaignCallerSession) UpdatedTermIdx() (*big.Int, error) {
	return _Campaign.Contract.UpdatedTermIdx(&_Campaign.CallOpts)
}

// ViewLen is a free data retrieval call binding the contract method 0x68f237a1.
//
// Solidity: function viewLen() constant returns(uint256)
func (_Campaign *CampaignCaller) ViewLen(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "viewLen")
	return *ret0, err
}

// ViewLen is a free data retrieval call binding the contract method 0x68f237a1.
//
// Solidity: function viewLen() constant returns(uint256)
func (_Campaign *CampaignSession) ViewLen() (*big.Int, error) {
	return _Campaign.Contract.ViewLen(&_Campaign.CallOpts)
}

// ViewLen is a free data retrieval call binding the contract method 0x68f237a1.
//
// Solidity: function viewLen() constant returns(uint256)
func (_Campaign *CampaignCallerSession) ViewLen() (*big.Int, error) {
	return _Campaign.Contract.ViewLen(&_Campaign.CallOpts)
}

// ClaimCampaign is a paid mutator transaction binding the contract method 0x350cc724.
//
// Solidity: function claimCampaign(_numOfCampaign uint256, _cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256, version uint256) returns()
func (_Campaign *CampaignTransactor) ClaimCampaign(opts *bind.TransactOpts, _numOfCampaign *big.Int, _cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int, version *big.Int) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "claimCampaign", _numOfCampaign, _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber, version)
}

// ClaimCampaign is a paid mutator transaction binding the contract method 0x350cc724.
//
// Solidity: function claimCampaign(_numOfCampaign uint256, _cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256, version uint256) returns()
func (_Campaign *CampaignSession) ClaimCampaign(_numOfCampaign *big.Int, _cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int, version *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.ClaimCampaign(&_Campaign.TransactOpts, _numOfCampaign, _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber, version)
}

// ClaimCampaign is a paid mutator transaction binding the contract method 0x350cc724.
//
// Solidity: function claimCampaign(_numOfCampaign uint256, _cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256, version uint256) returns()
func (_Campaign *CampaignTransactorSession) ClaimCampaign(_numOfCampaign *big.Int, _cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int, version *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.ClaimCampaign(&_Campaign.TransactOpts, _numOfCampaign, _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber, version)
}

// SetAdmissionAddr is a paid mutator transaction binding the contract method 0xc0e9e35e.
//
// Solidity: function setAdmissionAddr(_addr address) returns()
func (_Campaign *CampaignTransactor) SetAdmissionAddr(opts *bind.TransactOpts, _addr common.Address) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "setAdmissionAddr", _addr)
}

// SetAdmissionAddr is a paid mutator transaction binding the contract method 0xc0e9e35e.
//
// Solidity: function setAdmissionAddr(_addr address) returns()
func (_Campaign *CampaignSession) SetAdmissionAddr(_addr common.Address) (*types.Transaction, error) {
	return _Campaign.Contract.SetAdmissionAddr(&_Campaign.TransactOpts, _addr)
}

// SetAdmissionAddr is a paid mutator transaction binding the contract method 0xc0e9e35e.
//
// Solidity: function setAdmissionAddr(_addr address) returns()
func (_Campaign *CampaignTransactorSession) SetAdmissionAddr(_addr common.Address) (*types.Transaction, error) {
	return _Campaign.Contract.SetAdmissionAddr(&_Campaign.TransactOpts, _addr)
}

// SetRnodeInterface is a paid mutator transaction binding the contract method 0xf2aaabdd.
//
// Solidity: function setRnodeInterface(_addr address) returns()
func (_Campaign *CampaignTransactor) SetRnodeInterface(opts *bind.TransactOpts, _addr common.Address) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "setRnodeInterface", _addr)
}

// SetRnodeInterface is a paid mutator transaction binding the contract method 0xf2aaabdd.
//
// Solidity: function setRnodeInterface(_addr address) returns()
func (_Campaign *CampaignSession) SetRnodeInterface(_addr common.Address) (*types.Transaction, error) {
	return _Campaign.Contract.SetRnodeInterface(&_Campaign.TransactOpts, _addr)
}

// SetRnodeInterface is a paid mutator transaction binding the contract method 0xf2aaabdd.
//
// Solidity: function setRnodeInterface(_addr address) returns()
func (_Campaign *CampaignTransactorSession) SetRnodeInterface(_addr common.Address) (*types.Transaction, error) {
	return _Campaign.Contract.SetRnodeInterface(&_Campaign.TransactOpts, _addr)
}

// UpdateAcceptableBlocks is a paid mutator transaction binding the contract method 0xdae49ab2.
//
// Solidity: function updateAcceptableBlocks(_acceptableBlocks uint256) returns()
func (_Campaign *CampaignTransactor) UpdateAcceptableBlocks(opts *bind.TransactOpts, _acceptableBlocks *big.Int) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "updateAcceptableBlocks", _acceptableBlocks)
}

// UpdateAcceptableBlocks is a paid mutator transaction binding the contract method 0xdae49ab2.
//
// Solidity: function updateAcceptableBlocks(_acceptableBlocks uint256) returns()
func (_Campaign *CampaignSession) UpdateAcceptableBlocks(_acceptableBlocks *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateAcceptableBlocks(&_Campaign.TransactOpts, _acceptableBlocks)
}

// UpdateAcceptableBlocks is a paid mutator transaction binding the contract method 0xdae49ab2.
//
// Solidity: function updateAcceptableBlocks(_acceptableBlocks uint256) returns()
func (_Campaign *CampaignTransactorSession) UpdateAcceptableBlocks(_acceptableBlocks *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateAcceptableBlocks(&_Campaign.TransactOpts, _acceptableBlocks)
}

// UpdateMaxNoc is a paid mutator transaction binding the contract method 0x8cb59532.
//
// Solidity: function updateMaxNoc(_maxNoc uint256) returns()
func (_Campaign *CampaignTransactor) UpdateMaxNoc(opts *bind.TransactOpts, _maxNoc *big.Int) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "updateMaxNoc", _maxNoc)
}

// UpdateMaxNoc is a paid mutator transaction binding the contract method 0x8cb59532.
//
// Solidity: function updateMaxNoc(_maxNoc uint256) returns()
func (_Campaign *CampaignSession) UpdateMaxNoc(_maxNoc *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateMaxNoc(&_Campaign.TransactOpts, _maxNoc)
}

// UpdateMaxNoc is a paid mutator transaction binding the contract method 0x8cb59532.
//
// Solidity: function updateMaxNoc(_maxNoc uint256) returns()
func (_Campaign *CampaignTransactorSession) UpdateMaxNoc(_maxNoc *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateMaxNoc(&_Campaign.TransactOpts, _maxNoc)
}

// UpdateMinNoc is a paid mutator transaction binding the contract method 0xa7e1f08b.
//
// Solidity: function updateMinNoc(_minNoc uint256) returns()
func (_Campaign *CampaignTransactor) UpdateMinNoc(opts *bind.TransactOpts, _minNoc *big.Int) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "updateMinNoc", _minNoc)
}

// UpdateMinNoc is a paid mutator transaction binding the contract method 0xa7e1f08b.
//
// Solidity: function updateMinNoc(_minNoc uint256) returns()
func (_Campaign *CampaignSession) UpdateMinNoc(_minNoc *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateMinNoc(&_Campaign.TransactOpts, _minNoc)
}

// UpdateMinNoc is a paid mutator transaction binding the contract method 0xa7e1f08b.
//
// Solidity: function updateMinNoc(_minNoc uint256) returns()
func (_Campaign *CampaignTransactorSession) UpdateMinNoc(_minNoc *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateMinNoc(&_Campaign.TransactOpts, _minNoc)
}

// UpdateSupportedVersion is a paid mutator transaction binding the contract method 0x7dd604d6.
//
// Solidity: function updateSupportedVersion(_supportedVersion uint256) returns()
func (_Campaign *CampaignTransactor) UpdateSupportedVersion(opts *bind.TransactOpts, _supportedVersion *big.Int) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "updateSupportedVersion", _supportedVersion)
}

// UpdateSupportedVersion is a paid mutator transaction binding the contract method 0x7dd604d6.
//
// Solidity: function updateSupportedVersion(_supportedVersion uint256) returns()
func (_Campaign *CampaignSession) UpdateSupportedVersion(_supportedVersion *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateSupportedVersion(&_Campaign.TransactOpts, _supportedVersion)
}

// UpdateSupportedVersion is a paid mutator transaction binding the contract method 0x7dd604d6.
//
// Solidity: function updateSupportedVersion(_supportedVersion uint256) returns()
func (_Campaign *CampaignTransactorSession) UpdateSupportedVersion(_supportedVersion *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateSupportedVersion(&_Campaign.TransactOpts, _supportedVersion)
}

// UpdateTermLen is a paid mutator transaction binding the contract method 0xc351d0a5.
//
// Solidity: function updateTermLen(_termLen uint256) returns()
func (_Campaign *CampaignTransactor) UpdateTermLen(opts *bind.TransactOpts, _termLen *big.Int) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "updateTermLen", _termLen)
}

// UpdateTermLen is a paid mutator transaction binding the contract method 0xc351d0a5.
//
// Solidity: function updateTermLen(_termLen uint256) returns()
func (_Campaign *CampaignSession) UpdateTermLen(_termLen *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateTermLen(&_Campaign.TransactOpts, _termLen)
}

// UpdateTermLen is a paid mutator transaction binding the contract method 0xc351d0a5.
//
// Solidity: function updateTermLen(_termLen uint256) returns()
func (_Campaign *CampaignTransactorSession) UpdateTermLen(_termLen *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateTermLen(&_Campaign.TransactOpts, _termLen)
}

// UpdateViewLen is a paid mutator transaction binding the contract method 0xcd60e217.
//
// Solidity: function updateViewLen(_viewLen uint256) returns()
func (_Campaign *CampaignTransactor) UpdateViewLen(opts *bind.TransactOpts, _viewLen *big.Int) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "updateViewLen", _viewLen)
}

// UpdateViewLen is a paid mutator transaction binding the contract method 0xcd60e217.
//
// Solidity: function updateViewLen(_viewLen uint256) returns()
func (_Campaign *CampaignSession) UpdateViewLen(_viewLen *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateViewLen(&_Campaign.TransactOpts, _viewLen)
}

// UpdateViewLen is a paid mutator transaction binding the contract method 0xcd60e217.
//
// Solidity: function updateViewLen(_viewLen uint256) returns()
func (_Campaign *CampaignTransactorSession) UpdateViewLen(_viewLen *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateViewLen(&_Campaign.TransactOpts, _viewLen)
}

// CampaignClaimCampaignIterator is returned from FilterClaimCampaign and is used to iterate over the raw logs and unpacked data for ClaimCampaign events raised by the Campaign contract.
type CampaignClaimCampaignIterator struct {
	Event *CampaignClaimCampaign // Event containing the contract specifics and raw log

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
func (it *CampaignClaimCampaignIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(CampaignClaimCampaign)
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
		it.Event = new(CampaignClaimCampaign)
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
func (it *CampaignClaimCampaignIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *CampaignClaimCampaignIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// CampaignClaimCampaign represents a ClaimCampaign event raised by the Campaign contract.
type CampaignClaimCampaign struct {
	Candidate    common.Address
	StartTermIdx *big.Int
	StopTermIdx  *big.Int
	Raw          types.Log // Blockchain specific contextual infos
}

// FilterClaimCampaign is a free log retrieval operation binding the contract event 0x8d468194bdd18296bee5d126aa15cc492d26bdf22a0585c4a47ec4490d3a0fcf.
//
// Solidity: e ClaimCampaign(candidate address, startTermIdx uint256, stopTermIdx uint256)
func (_Campaign *CampaignFilterer) FilterClaimCampaign(opts *bind.FilterOpts) (*CampaignClaimCampaignIterator, error) {

	logs, sub, err := _Campaign.contract.FilterLogs(opts, "ClaimCampaign")
	if err != nil {
		return nil, err
	}
	return &CampaignClaimCampaignIterator{contract: _Campaign.contract, event: "ClaimCampaign", logs: logs, sub: sub}, nil
}

// WatchClaimCampaign is a free log subscription operation binding the contract event 0x8d468194bdd18296bee5d126aa15cc492d26bdf22a0585c4a47ec4490d3a0fcf.
//
// Solidity: e ClaimCampaign(candidate address, startTermIdx uint256, stopTermIdx uint256)
func (_Campaign *CampaignFilterer) WatchClaimCampaign(opts *bind.WatchOpts, sink chan<- *CampaignClaimCampaign) (event.Subscription, error) {

	logs, sub, err := _Campaign.contract.WatchLogs(opts, "ClaimCampaign")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(CampaignClaimCampaign)
				if err := _Campaign.contract.UnpackLog(event, "ClaimCampaign", log); err != nil {
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

// RnodeInterfaceABI is the input ABI used to generate the binding from.
const RnodeInterfaceABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"isRnode\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"}]"

// RnodeInterfaceBin is the compiled bytecode used for deploying new contracts.
const RnodeInterfaceBin = `0x`

// DeployRnodeInterface deploys a new cpchain contract, binding an instance of RnodeInterface to it.
func DeployRnodeInterface(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *RnodeInterface, error) {
	parsed, err := abi.JSON(strings.NewReader(RnodeInterfaceABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(RnodeInterfaceBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &RnodeInterface{RnodeInterfaceCaller: RnodeInterfaceCaller{contract: contract}, RnodeInterfaceTransactor: RnodeInterfaceTransactor{contract: contract}, RnodeInterfaceFilterer: RnodeInterfaceFilterer{contract: contract}}, nil
}

// RnodeInterface is an auto generated Go binding around an cpchain contract.
type RnodeInterface struct {
	RnodeInterfaceCaller     // Read-only binding to the contract
	RnodeInterfaceTransactor // Write-only binding to the contract
	RnodeInterfaceFilterer   // Log filterer for contract events
}

// RnodeInterfaceCaller is an auto generated read-only Go binding around an cpchain contract.
type RnodeInterfaceCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RnodeInterfaceTransactor is an auto generated write-only Go binding around an cpchain contract.
type RnodeInterfaceTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RnodeInterfaceFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type RnodeInterfaceFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RnodeInterfaceSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type RnodeInterfaceSession struct {
	Contract     *RnodeInterface   // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// RnodeInterfaceCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type RnodeInterfaceCallerSession struct {
	Contract *RnodeInterfaceCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts         // Call options to use throughout this session
}

// RnodeInterfaceTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type RnodeInterfaceTransactorSession struct {
	Contract     *RnodeInterfaceTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts         // Transaction auth options to use throughout this session
}

// RnodeInterfaceRaw is an auto generated low-level Go binding around an cpchain contract.
type RnodeInterfaceRaw struct {
	Contract *RnodeInterface // Generic contract binding to access the raw methods on
}

// RnodeInterfaceCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type RnodeInterfaceCallerRaw struct {
	Contract *RnodeInterfaceCaller // Generic read-only contract binding to access the raw methods on
}

// RnodeInterfaceTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type RnodeInterfaceTransactorRaw struct {
	Contract *RnodeInterfaceTransactor // Generic write-only contract binding to access the raw methods on
}

// NewRnodeInterface creates a new instance of RnodeInterface, bound to a specific deployed contract.
func NewRnodeInterface(address common.Address, backend bind.ContractBackend) (*RnodeInterface, error) {
	contract, err := bindRnodeInterface(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &RnodeInterface{RnodeInterfaceCaller: RnodeInterfaceCaller{contract: contract}, RnodeInterfaceTransactor: RnodeInterfaceTransactor{contract: contract}, RnodeInterfaceFilterer: RnodeInterfaceFilterer{contract: contract}}, nil
}

// NewRnodeInterfaceCaller creates a new read-only instance of RnodeInterface, bound to a specific deployed contract.
func NewRnodeInterfaceCaller(address common.Address, caller bind.ContractCaller) (*RnodeInterfaceCaller, error) {
	contract, err := bindRnodeInterface(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &RnodeInterfaceCaller{contract: contract}, nil
}

// NewRnodeInterfaceTransactor creates a new write-only instance of RnodeInterface, bound to a specific deployed contract.
func NewRnodeInterfaceTransactor(address common.Address, transactor bind.ContractTransactor) (*RnodeInterfaceTransactor, error) {
	contract, err := bindRnodeInterface(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &RnodeInterfaceTransactor{contract: contract}, nil
}

// NewRnodeInterfaceFilterer creates a new log filterer instance of RnodeInterface, bound to a specific deployed contract.
func NewRnodeInterfaceFilterer(address common.Address, filterer bind.ContractFilterer) (*RnodeInterfaceFilterer, error) {
	contract, err := bindRnodeInterface(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &RnodeInterfaceFilterer{contract: contract}, nil
}

// bindRnodeInterface binds a generic wrapper to an already deployed contract.
func bindRnodeInterface(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(RnodeInterfaceABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_RnodeInterface *RnodeInterfaceRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _RnodeInterface.Contract.RnodeInterfaceCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_RnodeInterface *RnodeInterfaceRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _RnodeInterface.Contract.RnodeInterfaceTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_RnodeInterface *RnodeInterfaceRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _RnodeInterface.Contract.RnodeInterfaceTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_RnodeInterface *RnodeInterfaceCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _RnodeInterface.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_RnodeInterface *RnodeInterfaceTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _RnodeInterface.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_RnodeInterface *RnodeInterfaceTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _RnodeInterface.Contract.contract.Transact(opts, method, params...)
}

// IsRnode is a free data retrieval call binding the contract method 0xa8f07697.
//
// Solidity: function isRnode(_addr address) constant returns(bool)
func (_RnodeInterface *RnodeInterfaceCaller) IsRnode(opts *bind.CallOpts, _addr common.Address) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _RnodeInterface.contract.Call(opts, out, "isRnode", _addr)
	return *ret0, err
}

// IsRnode is a free data retrieval call binding the contract method 0xa8f07697.
//
// Solidity: function isRnode(_addr address) constant returns(bool)
func (_RnodeInterface *RnodeInterfaceSession) IsRnode(_addr common.Address) (bool, error) {
	return _RnodeInterface.Contract.IsRnode(&_RnodeInterface.CallOpts, _addr)
}

// IsRnode is a free data retrieval call binding the contract method 0xa8f07697.
//
// Solidity: function isRnode(_addr address) constant returns(bool)
func (_RnodeInterface *RnodeInterfaceCallerSession) IsRnode(_addr common.Address) (bool, error) {
	return _RnodeInterface.Contract.IsRnode(&_RnodeInterface.CallOpts, _addr)
}

// SafeMathABI is the input ABI used to generate the binding from.
const SafeMathABI = "[]"

// SafeMathBin is the compiled bytecode used for deploying new contracts.
const SafeMathBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a723058207fdab779613bc4529b3b9b247551040267c8e51666af67ff879c620bef07ab010029`

// DeploySafeMath deploys a new cpchain contract, binding an instance of SafeMath to it.
func DeploySafeMath(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *SafeMath, error) {
	parsed, err := abi.JSON(strings.NewReader(SafeMathABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(SafeMathBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &SafeMath{SafeMathCaller: SafeMathCaller{contract: contract}, SafeMathTransactor: SafeMathTransactor{contract: contract}, SafeMathFilterer: SafeMathFilterer{contract: contract}}, nil
}

// SafeMath is an auto generated Go binding around an cpchain contract.
type SafeMath struct {
	SafeMathCaller     // Read-only binding to the contract
	SafeMathTransactor // Write-only binding to the contract
	SafeMathFilterer   // Log filterer for contract events
}

// SafeMathCaller is an auto generated read-only Go binding around an cpchain contract.
type SafeMathCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SafeMathTransactor is an auto generated write-only Go binding around an cpchain contract.
type SafeMathTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SafeMathFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type SafeMathFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SafeMathSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type SafeMathSession struct {
	Contract     *SafeMath         // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// SafeMathCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type SafeMathCallerSession struct {
	Contract *SafeMathCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts   // Call options to use throughout this session
}

// SafeMathTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type SafeMathTransactorSession struct {
	Contract     *SafeMathTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts   // Transaction auth options to use throughout this session
}

// SafeMathRaw is an auto generated low-level Go binding around an cpchain contract.
type SafeMathRaw struct {
	Contract *SafeMath // Generic contract binding to access the raw methods on
}

// SafeMathCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type SafeMathCallerRaw struct {
	Contract *SafeMathCaller // Generic read-only contract binding to access the raw methods on
}

// SafeMathTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type SafeMathTransactorRaw struct {
	Contract *SafeMathTransactor // Generic write-only contract binding to access the raw methods on
}

// NewSafeMath creates a new instance of SafeMath, bound to a specific deployed contract.
func NewSafeMath(address common.Address, backend bind.ContractBackend) (*SafeMath, error) {
	contract, err := bindSafeMath(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &SafeMath{SafeMathCaller: SafeMathCaller{contract: contract}, SafeMathTransactor: SafeMathTransactor{contract: contract}, SafeMathFilterer: SafeMathFilterer{contract: contract}}, nil
}

// NewSafeMathCaller creates a new read-only instance of SafeMath, bound to a specific deployed contract.
func NewSafeMathCaller(address common.Address, caller bind.ContractCaller) (*SafeMathCaller, error) {
	contract, err := bindSafeMath(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &SafeMathCaller{contract: contract}, nil
}

// NewSafeMathTransactor creates a new write-only instance of SafeMath, bound to a specific deployed contract.
func NewSafeMathTransactor(address common.Address, transactor bind.ContractTransactor) (*SafeMathTransactor, error) {
	contract, err := bindSafeMath(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &SafeMathTransactor{contract: contract}, nil
}

// NewSafeMathFilterer creates a new log filterer instance of SafeMath, bound to a specific deployed contract.
func NewSafeMathFilterer(address common.Address, filterer bind.ContractFilterer) (*SafeMathFilterer, error) {
	contract, err := bindSafeMath(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &SafeMathFilterer{contract: contract}, nil
}

// bindSafeMath binds a generic wrapper to an already deployed contract.
func bindSafeMath(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(SafeMathABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_SafeMath *SafeMathRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _SafeMath.Contract.SafeMathCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_SafeMath *SafeMathRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _SafeMath.Contract.SafeMathTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_SafeMath *SafeMathRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _SafeMath.Contract.SafeMathTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_SafeMath *SafeMathCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _SafeMath.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_SafeMath *SafeMathTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _SafeMath.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_SafeMath *SafeMathTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _SafeMath.Contract.contract.Transact(opts, method, params...)
}

// SetABI is the input ABI used to generate the binding from.
const SetABI = "[]"

// SetBin is the compiled bytecode used for deploying new contracts.
const SetBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a723058203b76908c4e622c08a300d4ff93df65f3dd1f35df0071ee24d88b3224a32af4900029`

// DeploySet deploys a new cpchain contract, binding an instance of Set to it.
func DeploySet(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *Set, error) {
	parsed, err := abi.JSON(strings.NewReader(SetABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(SetBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &Set{SetCaller: SetCaller{contract: contract}, SetTransactor: SetTransactor{contract: contract}, SetFilterer: SetFilterer{contract: contract}}, nil
}

// Set is an auto generated Go binding around an cpchain contract.
type Set struct {
	SetCaller     // Read-only binding to the contract
	SetTransactor // Write-only binding to the contract
	SetFilterer   // Log filterer for contract events
}

// SetCaller is an auto generated read-only Go binding around an cpchain contract.
type SetCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SetTransactor is an auto generated write-only Go binding around an cpchain contract.
type SetTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SetFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type SetFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SetSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type SetSession struct {
	Contract     *Set              // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// SetCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type SetCallerSession struct {
	Contract *SetCaller    // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts // Call options to use throughout this session
}

// SetTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type SetTransactorSession struct {
	Contract     *SetTransactor    // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// SetRaw is an auto generated low-level Go binding around an cpchain contract.
type SetRaw struct {
	Contract *Set // Generic contract binding to access the raw methods on
}

// SetCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type SetCallerRaw struct {
	Contract *SetCaller // Generic read-only contract binding to access the raw methods on
}

// SetTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type SetTransactorRaw struct {
	Contract *SetTransactor // Generic write-only contract binding to access the raw methods on
}

// NewSet creates a new instance of Set, bound to a specific deployed contract.
func NewSet(address common.Address, backend bind.ContractBackend) (*Set, error) {
	contract, err := bindSet(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &Set{SetCaller: SetCaller{contract: contract}, SetTransactor: SetTransactor{contract: contract}, SetFilterer: SetFilterer{contract: contract}}, nil
}

// NewSetCaller creates a new read-only instance of Set, bound to a specific deployed contract.
func NewSetCaller(address common.Address, caller bind.ContractCaller) (*SetCaller, error) {
	contract, err := bindSet(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &SetCaller{contract: contract}, nil
}

// NewSetTransactor creates a new write-only instance of Set, bound to a specific deployed contract.
func NewSetTransactor(address common.Address, transactor bind.ContractTransactor) (*SetTransactor, error) {
	contract, err := bindSet(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &SetTransactor{contract: contract}, nil
}

// NewSetFilterer creates a new log filterer instance of Set, bound to a specific deployed contract.
func NewSetFilterer(address common.Address, filterer bind.ContractFilterer) (*SetFilterer, error) {
	contract, err := bindSet(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &SetFilterer{contract: contract}, nil
}

// bindSet binds a generic wrapper to an already deployed contract.
func bindSet(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(SetABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Set *SetRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Set.Contract.SetCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Set *SetRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Set.Contract.SetTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Set *SetRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Set.Contract.SetTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Set *SetCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Set.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Set *SetTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Set.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Set *SetTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Set.Contract.contract.Transact(opts, method, params...)
}
