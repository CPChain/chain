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

// CampaignABI is the input ABI used to generate the binding from.
const CampaignABI = "[{\"constant\":true,\"inputs\":[],\"name\":\"minimumNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"view_idx\",\"type\":\"uint256\"}],\"name\":\"CandidatesOf\",\"outputs\":[{\"name\":\"\",\"type\":\"address[]\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"candidate\",\"type\":\"address\"}],\"name\":\"CandidateInfoOf\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"baseDeposit\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"}],\"name\":\"campaignSnapshots\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"}],\"name\":\"candidates\",\"outputs\":[{\"name\":\"numOfCampaign\",\"type\":\"uint256\"},{\"name\":\"deposit\",\"type\":\"uint256\"},{\"name\":\"timestamp\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"maximumNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"viewIdx\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"ViewChange\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"minimumRpt\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"num_of_campaign\",\"type\":\"uint256\"},{\"name\":\"rpt\",\"type\":\"uint256\"}],\"name\":\"ClaimCampaign\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"QuitCampaign\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]"

// CampaignBin is the compiled bytecode used for deploying new contracts.
const CampaignBin = `0x60806040526000600155603260025560326003556001600455600a60055534801561002957600080fd5b5060008054600160a060020a031916331790556108438061004b6000396000f3006080604052600436106100b95763ffffffff7c0100000000000000000000000000000000000000000000000000000000600035041663241ead3581146100be5780632d621bda146100e5578063684d9e101461015f57806369474625146101b05780637186a1f5146101c55780638ab66a9014610211578063ae3f11bf14610244578063b07eaaf014610259578063beff14761461026e578063e41cf00314610285578063ee1cfa081461029a578063fdb29715146102bd575b600080fd5b3480156100ca57600080fd5b506100d36102c5565b60408051918252519081900360200190f35b3480156100f157600080fd5b5061010f6004803603602081101561010857600080fd5b50356102cb565b60408051602080825283518183015283519192839290830191858101910280838360005b8381101561014b578181015183820152602001610133565b505050509050019250505060405180910390f35b34801561016b57600080fd5b506101926004803603602081101561018257600080fd5b5035600160a060020a0316610337565b60408051938452602084019290925282820152519081900360600190f35b3480156101bc57600080fd5b506100d361035f565b3480156101d157600080fd5b506101f5600480360360408110156101e857600080fd5b5080359060200135610365565b60408051600160a060020a039092168252519081900360200190f35b34801561021d57600080fd5b506101926004803603602081101561023457600080fd5b5035600160a060020a031661039c565b34801561025057600080fd5b506100d36103bd565b34801561026557600080fd5b506100d36103c3565b34801561027a57600080fd5b506102836103c9565b005b34801561029157600080fd5b506100d36104d0565b610283600480360360408110156102b057600080fd5b50803590602001356104d6565b6102836106e9565b60045481565b60008181526007602090815260409182902080548351818402810184019094528084526060939283018282801561032b57602002820191906000526020600020905b8154600160a060020a0316815260019091019060200180831161030d575b50505050509050919050565b600160a060020a03166000908152600660205260409020805460018201546002909201549092565b60025481565b60076020528160005260406000208181548110151561038057fe5b600091825260209091200154600160a060020a03169150829050565b60066020526000908152604090208054600182015460029092015490919083565b60055481565b60015481565b60005b6001546000908152600760205260409020548110156104c557600154600090815260076020526040812080548390811061040257fe5b6000918252602080832090910154600254600160a060020a039091168084526006909252604090922060010154909250106104bc57600254600160a060020a0382166000908152600660209081526040808320600190810180549590950390945592548252600790522080548390811061047857fe5b6000918252602082200154600254604051600160a060020a039092169281156108fc029290818181858888f193505050501580156104ba573d6000803e3d6000fd5b505b506001016103cc565b506001805481019055565b60035481565b600354811015610530576040805160e560020a62461bcd02815260206004820152600c60248201527f746f6f206c6f77207270742e0000000000000000000000000000000000000000604482015290519081900360640190fd5b600454821015801561054457506005548211155b151561059a576040805160e560020a62461bcd02815260206004820152601d60248201527f6e756d206f662063616d706169676e206f7574206f662072616e67652e000000604482015290519081900360640190fd5b600254820234146105f5576040805160e560020a62461bcd02815260206004820152601460248201527f77726f6e67206465706f7369742076616c75652e000000000000000000000000604482015290519081900360640190fd5b336000818152600660205260409020541515610656576040805160608101825284815234602080830191825242838501908152600160a060020a03861660009081526006909252939020915182555160018201559051600290910155610686565b600160a060020a038116600090815260066020526040902080548401815560018101805434019055426002909101555b6001545b83600154018110156106e357600081815260076020908152604082208054600180820183559184529190922001805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a0385161790550161068a565b50505050565b336000818152600660205260408120541161074e576040805160e560020a62461bcd02815260206004820152601660248201527f616c726561647920717569742063616d706169676e2e00000000000000000000604482015290519081900360640190fd5b604080516060810182526000808252602080830182815242848601908152600160a060020a0387168085526006909352858420945185559051600185018190559051600290940193909355925182156108fc029291818181858888f193505050501580156107c0573d6000803e3d6000fd5b5060005b6001546000908152600760205260409020548110156108135760015460009081526007602052604090208054600160a060020a03841691908390811061080657fe5b50600052506001016107c4565b50505600a165627a7a7230582019f58c52950e1d18de15392aed5ab3c929fe1fb2f0aa2766789dc1c5c13c32b60029`

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

// CampaignSnapshots is a free data retrieval call binding the contract method 0x7186a1f5.
//
// Solidity: function campaignSnapshots( uint256,  uint256) constant returns(address)
func (_Campaign *CampaignCaller) CampaignSnapshots(opts *bind.CallOpts, arg0 *big.Int, arg1 *big.Int) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "campaignSnapshots", arg0, arg1)
	return *ret0, err
}

// CampaignSnapshots is a free data retrieval call binding the contract method 0x7186a1f5.
//
// Solidity: function campaignSnapshots( uint256,  uint256) constant returns(address)
func (_Campaign *CampaignSession) CampaignSnapshots(arg0 *big.Int, arg1 *big.Int) (common.Address, error) {
	return _Campaign.Contract.CampaignSnapshots(&_Campaign.CallOpts, arg0, arg1)
}

// CampaignSnapshots is a free data retrieval call binding the contract method 0x7186a1f5.
//
// Solidity: function campaignSnapshots( uint256,  uint256) constant returns(address)
func (_Campaign *CampaignCallerSession) CampaignSnapshots(arg0 *big.Int, arg1 *big.Int) (common.Address, error) {
	return _Campaign.Contract.CampaignSnapshots(&_Campaign.CallOpts, arg0, arg1)
}

// Candidates is a free data retrieval call binding the contract method 0x8ab66a90.
//
// Solidity: function candidates( address) constant returns(numOfCampaign uint256, deposit uint256, timestamp uint256)
func (_Campaign *CampaignCaller) Candidates(opts *bind.CallOpts, arg0 common.Address) (struct {
	NumOfCampaign *big.Int
	Deposit       *big.Int
	Timestamp     *big.Int
}, error) {
	ret := new(struct {
		NumOfCampaign *big.Int
		Deposit       *big.Int
		Timestamp     *big.Int
	})
	out := ret
	err := _Campaign.contract.Call(opts, out, "candidates", arg0)
	return *ret, err
}

// Candidates is a free data retrieval call binding the contract method 0x8ab66a90.
//
// Solidity: function candidates( address) constant returns(numOfCampaign uint256, deposit uint256, timestamp uint256)
func (_Campaign *CampaignSession) Candidates(arg0 common.Address) (struct {
	NumOfCampaign *big.Int
	Deposit       *big.Int
	Timestamp     *big.Int
}, error) {
	return _Campaign.Contract.Candidates(&_Campaign.CallOpts, arg0)
}

// Candidates is a free data retrieval call binding the contract method 0x8ab66a90.
//
// Solidity: function candidates( address) constant returns(numOfCampaign uint256, deposit uint256, timestamp uint256)
func (_Campaign *CampaignCallerSession) Candidates(arg0 common.Address) (struct {
	NumOfCampaign *big.Int
	Deposit       *big.Int
	Timestamp     *big.Int
}, error) {
	return _Campaign.Contract.Candidates(&_Campaign.CallOpts, arg0)
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
