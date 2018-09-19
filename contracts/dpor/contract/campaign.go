// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package contract

import (
	"math/big"
	"strings"

	"bitbucket.org/cpchain/chain/accounts/abi"
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/core/types"
)

// CampaignABI is the input ABI used to generate the binding from.
const CampaignABI = "[{\"constant\":true,\"inputs\":[],\"name\":\"minimumNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"view_idx\",\"type\":\"uint256\"}],\"name\":\"CandidatesOf\",\"outputs\":[{\"name\":\"\",\"type\":\"address[]\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"candidate\",\"type\":\"address\"}],\"name\":\"CandidateInfoOf\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"baseDeposit\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"maximumNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"viewIdx\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"ViewChange\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"minimumRpt\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"num_of_campaign\",\"type\":\"uint256\"},{\"name\":\"rpt\",\"type\":\"uint256\"}],\"name\":\"ClaimCampaign\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"QuitCampaign\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]"

// CampaignBin is the compiled bytecode used for deploying new contracts.
const CampaignBin = `0x60806040526000600155603260025560326003556001600455600a60055534801561002957600080fd5b5060008054600160a060020a03191633179055610a3d8061004b6000396000f3006080604052600436106100a35763ffffffff7c0100000000000000000000000000000000000000000000000000000000600035041663241ead3581146100a85780632d621bda146100cf578063684d9e1014610149578063694746251461019a578063ae3f11bf146101af578063b07eaaf0146101c4578063beff1476146101d9578063e41cf003146101e3578063ee1cfa08146101f8578063fdb297151461021b575b600080fd5b3480156100b457600080fd5b506100bd610223565b60408051918252519081900360200190f35b3480156100db57600080fd5b506100f9600480360360208110156100f257600080fd5b5035610229565b60408051602080825283518183015283519192839290830191858101910280838360005b8381101561013557818101518382015260200161011d565b505050509050019250505060405180910390f35b34801561015557600080fd5b5061017c6004803603602081101561016c57600080fd5b5035600160a060020a0316610298565b60408051938452602084019290925282820152519081900360600190f35b3480156101a657600080fd5b506100bd6102c0565b3480156101bb57600080fd5b506100bd6102c6565b3480156101d057600080fd5b506100bd6102cc565b6101e16102d2565b005b3480156101ef57600080fd5b506100bd6103b1565b6101e16004803603604081101561020e57600080fd5b50803590602001356103b7565b6101e1610670565b60045481565b60008181526007602090815260409182902060010180548351818402810184019094528084526060939283018282801561028c57602002820191906000526020600020905b8154600160a060020a0316815260019091019060200180831161026e575b50505050509050919050565b600160a060020a03166000908152600660205260409020805460018201546002909201549092565b60025481565b60055481565b60015481565b60005b60018054600090815260076020526040902001548110156103a65760018054600090815260076020526040812090910180548390811061031157fe5b6000918252602080832090910154600254600160a060020a0390911680845260069092526040909220600101549092501061039d5760028054600160a060020a03831660008181526006602052604080822060010180549490940390935592549151909282156108fc02929190818181858888f1935050505015801561039b573d6000803e3d6000fd5b505b506001016102d5565b506001805481019055565b60035481565b600354811015610411576040805160e560020a62461bcd02815260206004820152600c60248201527f746f6f206c6f77207270742e0000000000000000000000000000000000000000604482015290519081900360640190fd5b6002548202341461046c576040805160e560020a62461bcd02815260206004820152601460248201527f77726f6e67206465706f7369742076616c75652e000000000000000000000000604482015290519081900360640190fd5b33600081815260066020526040902054151561053b57600454831015801561049657506005548311155b15156104ec576040805160e560020a62461bcd02815260206004820152601d60248201527f6e756d206f662063616d706169676e206f7574206f662072616e67652e000000604482015290519081900360640190fd5b6040805160608101825284815234602080830191825260018054848601908152600160a060020a0387166000908152600690935294909120925183559051908201559051600290910155610601565b600454600160a060020a0382166000908152600660205260409020548401108015906105835750600554600160a060020a038216600090815260066020526040902054840111155b15156105d9576040805160e560020a62461bcd02815260206004820152601d60248201527f6e756d206f662063616d706169676e206f7574206f662072616e67652e000000604482015290519081900360640190fd5b600160a060020a03811660009081526006602052604090208054840181556001018054340190555b600160a060020a0381166000908152600660205260409020600201545b600160a060020a038216600090815260066020526040902060020154840181101561066a576000818152600760205260409020610661908363ffffffff6107be16565b5060010161061e565b50505050565b33600081815260066020526040812054116106d5576040805160e560020a62461bcd02815260206004820152601660248201527f616c726561647920717569742063616d706169676e2e00000000000000000000604482015290519081900360640190fd5b6001545b600160a060020a03821660009081526006602052604090208054600290910154018110156107a357600254600160a060020a0383166000908152600660205260409020600101541061077c5760028054600160a060020a03841660008181526006602052604080822060010180549490940390935592549151909282156108fc02929190818181858888f1935050505015801561077a573d6000803e3d6000fd5b505b600081815260076020526040902061079a908363ffffffff61084616565b506001016106d9565b50600160a060020a0316600090815260066020526040812055565b600160a060020a03811660009081526020839052604081205460ff16156107e757506000610840565b50600160a060020a0381166000818152602084815260408220805460ff19166001908117909155858101805480830182559084529190922001805473ffffffffffffffffffffffffffffffffffffffff19169092179091555b92915050565b600160a060020a03811660009081526020839052604081205460ff16151561087057506000610840565b600160a060020a0382166000908152602084905260408120805460ff191690555b60018401548110156109bd5782600160a060020a031684600101828154811015156108b857fe5b600091825260209091200154600160a060020a031614156109b557805b60018501546000190181101561095f5784600101816001018154811015156108f957fe5b600091825260209091200154600186018054600160a060020a03909216918390811061092157fe5b6000918252602090912001805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a03929092169190911790556001016108d5565b50600184018054600019810190811061097457fe5b6000918252602090912001805473ffffffffffffffffffffffffffffffffffffffff19169055600184018054906109af9060001983016109c7565b506109bd565b600101610891565b5060019392505050565b8154818355818111156109eb576000838152602090206109eb9181019083016109f0565b505050565b610a0e91905b80821115610a0a57600081556001016109f6565b5090565b905600a165627a7a7230582065697c5e144489f8affc6a19c4da133b6d34413b4629abada86b34c6005f62630029`

// DeployCampaign deploys a new Ethereum contract, binding an instance of Campaign to it.
func DeployCampaign(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *Campaign, error) {
	parsed, err := abi.JSON(strings.NewReader(CampaignABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(CampaignBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &Campaign{CampaignCaller: CampaignCaller{contract: contract}, CampaignTransactor: CampaignTransactor{contract: contract}, CampaignFilterer: CampaignFilterer{contract: contract}}, nil
}

// Campaign is an auto generated Go binding around an Ethereum contract.
type Campaign struct {
	CampaignCaller     // Read-only binding to the contract
	CampaignTransactor // Write-only binding to the contract
	CampaignFilterer   // Log filterer for contract events
}

// CampaignCaller is an auto generated read-only Go binding around an Ethereum contract.
type CampaignCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// CampaignTransactor is an auto generated write-only Go binding around an Ethereum contract.
type CampaignTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// CampaignFilterer is an auto generated log filtering Go binding around an Ethereum contract events.
type CampaignFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// CampaignSession is an auto generated Go binding around an Ethereum contract,
// with pre-set call and transact options.
type CampaignSession struct {
	Contract     *Campaign         // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// CampaignCallerSession is an auto generated read-only Go binding around an Ethereum contract,
// with pre-set call options.
type CampaignCallerSession struct {
	Contract *CampaignCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts   // Call options to use throughout this session
}

// CampaignTransactorSession is an auto generated write-only Go binding around an Ethereum contract,
// with pre-set transact options.
type CampaignTransactorSession struct {
	Contract     *CampaignTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts   // Transaction auth options to use throughout this session
}

// CampaignRaw is an auto generated low-level Go binding around an Ethereum contract.
type CampaignRaw struct {
	Contract *Campaign // Generic contract binding to access the raw methods on
}

// CampaignCallerRaw is an auto generated low-level read-only Go binding around an Ethereum contract.
type CampaignCallerRaw struct {
	Contract *CampaignCaller // Generic read-only contract binding to access the raw methods on
}

// CampaignTransactorRaw is an auto generated low-level write-only Go binding around an Ethereum contract.
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

// CandidateInfoOf is a free data retrieval call binding the contract method 0x684d9e10.
//
// Solidity: function CandidateInfoOf(candidate address) constant returns(uint256, uint256, uint256)
func (_Campaign *CampaignCaller) CandidateInfoOf(opts *bind.CallOpts, candidate common.Address) (*big.Int, *big.Int, *big.Int, error) {
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
	err := _Campaign.contract.Call(opts, out, "CandidateInfoOf", candidate)
	return *ret0, *ret1, *ret2, err
}

// CandidateInfoOf is a free data retrieval call binding the contract method 0x684d9e10.
//
// Solidity: function CandidateInfoOf(candidate address) constant returns(uint256, uint256, uint256)
func (_Campaign *CampaignSession) CandidateInfoOf(candidate common.Address) (*big.Int, *big.Int, *big.Int, error) {
	return _Campaign.Contract.CandidateInfoOf(&_Campaign.CallOpts, candidate)
}

// CandidateInfoOf is a free data retrieval call binding the contract method 0x684d9e10.
//
// Solidity: function CandidateInfoOf(candidate address) constant returns(uint256, uint256, uint256)
func (_Campaign *CampaignCallerSession) CandidateInfoOf(candidate common.Address) (*big.Int, *big.Int, *big.Int, error) {
	return _Campaign.Contract.CandidateInfoOf(&_Campaign.CallOpts, candidate)
}

// CandidatesOf is a free data retrieval call binding the contract method 0x2d621bda.
//
// Solidity: function CandidatesOf(view_idx uint256) constant returns(address[])
func (_Campaign *CampaignCaller) CandidatesOf(opts *bind.CallOpts, view_idx *big.Int) ([]common.Address, error) {
	var (
		ret0 = new([]common.Address)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "CandidatesOf", view_idx)
	return *ret0, err
}

// CandidatesOf is a free data retrieval call binding the contract method 0x2d621bda.
//
// Solidity: function CandidatesOf(view_idx uint256) constant returns(address[])
func (_Campaign *CampaignSession) CandidatesOf(view_idx *big.Int) ([]common.Address, error) {
	return _Campaign.Contract.CandidatesOf(&_Campaign.CallOpts, view_idx)
}

// CandidatesOf is a free data retrieval call binding the contract method 0x2d621bda.
//
// Solidity: function CandidatesOf(view_idx uint256) constant returns(address[])
func (_Campaign *CampaignCallerSession) CandidatesOf(view_idx *big.Int) ([]common.Address, error) {
	return _Campaign.Contract.CandidatesOf(&_Campaign.CallOpts, view_idx)
}

// BaseDeposit is a free data retrieval call binding the contract method 0x69474625.
//
// Solidity: function baseDeposit() constant returns(uint256)
func (_Campaign *CampaignCaller) BaseDeposit(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "baseDeposit")
	return *ret0, err
}

// BaseDeposit is a free data retrieval call binding the contract method 0x69474625.
//
// Solidity: function baseDeposit() constant returns(uint256)
func (_Campaign *CampaignSession) BaseDeposit() (*big.Int, error) {
	return _Campaign.Contract.BaseDeposit(&_Campaign.CallOpts)
}

// BaseDeposit is a free data retrieval call binding the contract method 0x69474625.
//
// Solidity: function baseDeposit() constant returns(uint256)
func (_Campaign *CampaignCallerSession) BaseDeposit() (*big.Int, error) {
	return _Campaign.Contract.BaseDeposit(&_Campaign.CallOpts)
}

// MaximumNoc is a free data retrieval call binding the contract method 0xae3f11bf.
//
// Solidity: function maximumNoc() constant returns(uint256)
func (_Campaign *CampaignCaller) MaximumNoc(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "maximumNoc")
	return *ret0, err
}

// MaximumNoc is a free data retrieval call binding the contract method 0xae3f11bf.
//
// Solidity: function maximumNoc() constant returns(uint256)
func (_Campaign *CampaignSession) MaximumNoc() (*big.Int, error) {
	return _Campaign.Contract.MaximumNoc(&_Campaign.CallOpts)
}

// MaximumNoc is a free data retrieval call binding the contract method 0xae3f11bf.
//
// Solidity: function maximumNoc() constant returns(uint256)
func (_Campaign *CampaignCallerSession) MaximumNoc() (*big.Int, error) {
	return _Campaign.Contract.MaximumNoc(&_Campaign.CallOpts)
}

// MinimumNoc is a free data retrieval call binding the contract method 0x241ead35.
//
// Solidity: function minimumNoc() constant returns(uint256)
func (_Campaign *CampaignCaller) MinimumNoc(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "minimumNoc")
	return *ret0, err
}

// MinimumNoc is a free data retrieval call binding the contract method 0x241ead35.
//
// Solidity: function minimumNoc() constant returns(uint256)
func (_Campaign *CampaignSession) MinimumNoc() (*big.Int, error) {
	return _Campaign.Contract.MinimumNoc(&_Campaign.CallOpts)
}

// MinimumNoc is a free data retrieval call binding the contract method 0x241ead35.
//
// Solidity: function minimumNoc() constant returns(uint256)
func (_Campaign *CampaignCallerSession) MinimumNoc() (*big.Int, error) {
	return _Campaign.Contract.MinimumNoc(&_Campaign.CallOpts)
}

// MinimumRpt is a free data retrieval call binding the contract method 0xe41cf003.
//
// Solidity: function minimumRpt() constant returns(uint256)
func (_Campaign *CampaignCaller) MinimumRpt(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "minimumRpt")
	return *ret0, err
}

// MinimumRpt is a free data retrieval call binding the contract method 0xe41cf003.
//
// Solidity: function minimumRpt() constant returns(uint256)
func (_Campaign *CampaignSession) MinimumRpt() (*big.Int, error) {
	return _Campaign.Contract.MinimumRpt(&_Campaign.CallOpts)
}

// MinimumRpt is a free data retrieval call binding the contract method 0xe41cf003.
//
// Solidity: function minimumRpt() constant returns(uint256)
func (_Campaign *CampaignCallerSession) MinimumRpt() (*big.Int, error) {
	return _Campaign.Contract.MinimumRpt(&_Campaign.CallOpts)
}

// ViewIdx is a free data retrieval call binding the contract method 0xb07eaaf0.
//
// Solidity: function viewIdx() constant returns(uint256)
func (_Campaign *CampaignCaller) ViewIdx(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "viewIdx")
	return *ret0, err
}

// ViewIdx is a free data retrieval call binding the contract method 0xb07eaaf0.
//
// Solidity: function viewIdx() constant returns(uint256)
func (_Campaign *CampaignSession) ViewIdx() (*big.Int, error) {
	return _Campaign.Contract.ViewIdx(&_Campaign.CallOpts)
}

// ViewIdx is a free data retrieval call binding the contract method 0xb07eaaf0.
//
// Solidity: function viewIdx() constant returns(uint256)
func (_Campaign *CampaignCallerSession) ViewIdx() (*big.Int, error) {
	return _Campaign.Contract.ViewIdx(&_Campaign.CallOpts)
}

// ClaimCampaign is a paid mutator transaction binding the contract method 0xee1cfa08.
//
// Solidity: function ClaimCampaign(num_of_campaign uint256, rpt uint256) returns()
func (_Campaign *CampaignTransactor) ClaimCampaign(opts *bind.TransactOpts, num_of_campaign *big.Int, rpt *big.Int) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "ClaimCampaign", num_of_campaign, rpt)
}

// ClaimCampaign is a paid mutator transaction binding the contract method 0xee1cfa08.
//
// Solidity: function ClaimCampaign(num_of_campaign uint256, rpt uint256) returns()
func (_Campaign *CampaignSession) ClaimCampaign(num_of_campaign *big.Int, rpt *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.ClaimCampaign(&_Campaign.TransactOpts, num_of_campaign, rpt)
}

// ClaimCampaign is a paid mutator transaction binding the contract method 0xee1cfa08.
//
// Solidity: function ClaimCampaign(num_of_campaign uint256, rpt uint256) returns()
func (_Campaign *CampaignTransactorSession) ClaimCampaign(num_of_campaign *big.Int, rpt *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.ClaimCampaign(&_Campaign.TransactOpts, num_of_campaign, rpt)
}

// QuitCampaign is a paid mutator transaction binding the contract method 0xfdb29715.
//
// Solidity: function QuitCampaign() returns()
func (_Campaign *CampaignTransactor) QuitCampaign(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "QuitCampaign")
}

// QuitCampaign is a paid mutator transaction binding the contract method 0xfdb29715.
//
// Solidity: function QuitCampaign() returns()
func (_Campaign *CampaignSession) QuitCampaign() (*types.Transaction, error) {
	return _Campaign.Contract.QuitCampaign(&_Campaign.TransactOpts)
}

// QuitCampaign is a paid mutator transaction binding the contract method 0xfdb29715.
//
// Solidity: function QuitCampaign() returns()
func (_Campaign *CampaignTransactorSession) QuitCampaign() (*types.Transaction, error) {
	return _Campaign.Contract.QuitCampaign(&_Campaign.TransactOpts)
}

// ViewChange is a paid mutator transaction binding the contract method 0xbeff1476.
//
// Solidity: function ViewChange() returns()
func (_Campaign *CampaignTransactor) ViewChange(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "ViewChange")
}

// ViewChange is a paid mutator transaction binding the contract method 0xbeff1476.
//
// Solidity: function ViewChange() returns()
func (_Campaign *CampaignSession) ViewChange() (*types.Transaction, error) {
	return _Campaign.Contract.ViewChange(&_Campaign.TransactOpts)
}

// ViewChange is a paid mutator transaction binding the contract method 0xbeff1476.
//
// Solidity: function ViewChange() returns()
func (_Campaign *CampaignTransactorSession) ViewChange() (*types.Transaction, error) {
	return _Campaign.Contract.ViewChange(&_Campaign.TransactOpts)
}

// SetABI is the input ABI used to generate the binding from.
const SetABI = "[]"

// SetBin is the compiled bytecode used for deploying new contracts.
const SetBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a723058205db266845b0779922d3f804a359f3c50562e771c4a4b5c72331a31133c38a3d50029`

// DeploySet deploys a new Ethereum contract, binding an instance of Set to it.
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

// Set is an auto generated Go binding around an Ethereum contract.
type Set struct {
	SetCaller     // Read-only binding to the contract
	SetTransactor // Write-only binding to the contract
	SetFilterer   // Log filterer for contract events
}

// SetCaller is an auto generated read-only Go binding around an Ethereum contract.
type SetCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SetTransactor is an auto generated write-only Go binding around an Ethereum contract.
type SetTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SetFilterer is an auto generated log filtering Go binding around an Ethereum contract events.
type SetFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// SetSession is an auto generated Go binding around an Ethereum contract,
// with pre-set call and transact options.
type SetSession struct {
	Contract     *Set              // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// SetCallerSession is an auto generated read-only Go binding around an Ethereum contract,
// with pre-set call options.
type SetCallerSession struct {
	Contract *SetCaller    // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts // Call options to use throughout this session
}

// SetTransactorSession is an auto generated write-only Go binding around an Ethereum contract,
// with pre-set transact options.
type SetTransactorSession struct {
	Contract     *SetTransactor    // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// SetRaw is an auto generated low-level Go binding around an Ethereum contract.
type SetRaw struct {
	Contract *Set // Generic contract binding to access the raw methods on
}

// SetCallerRaw is an auto generated low-level read-only Go binding around an Ethereum contract.
type SetCallerRaw struct {
	Contract *SetCaller // Generic read-only contract binding to access the raw methods on
}

// SetTransactorRaw is an auto generated low-level write-only Go binding around an Ethereum contract.
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
