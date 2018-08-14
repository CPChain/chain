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
const CampaignABI = "[{\"constant\":true,\"inputs\":[],\"name\":\"minimumNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"view_idx\",\"type\":\"uint256\"}],\"name\":\"CandidatesOf\",\"outputs\":[{\"name\":\"\",\"type\":\"address[]\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"candidate\",\"type\":\"address\"}],\"name\":\"CandidateInfoOf\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"baseDeposit\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"maximumNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"viewIdx\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"ViewChange\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"minimumRpt\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"num_of_campaign\",\"type\":\"uint256\"},{\"name\":\"rpt\",\"type\":\"uint256\"}],\"name\":\"ClaimCampaign\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"QuitCampaign\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]"

// CampaignBin is the compiled bytecode used for deploying new contracts.
const CampaignBin = `0x60806040526000600155603260025560326003556001600455600a60055534801561002957600080fd5b5060008054600160a060020a03191633179055610a2b8061004b6000396000f3006080604052600436106100a35763ffffffff7c0100000000000000000000000000000000000000000000000000000000600035041663241ead3581146100a85780632d621bda146100cf578063684d9e10146101375780636947462514610176578063ae3f11bf1461018b578063b07eaaf0146101a0578063beff1476146101b5578063e41cf003146101cc578063ee1cfa08146101e1578063fdb29715146101ef575b600080fd5b3480156100b457600080fd5b506100bd6101f7565b60408051918252519081900360200190f35b3480156100db57600080fd5b506100e76004356101fd565b60408051602080825283518183015283519192839290830191858101910280838360005b8381101561012357818101518382015260200161010b565b505050509050019250505060405180910390f35b34801561014357600080fd5b50610158600160a060020a036004351661026c565b60408051938452602084019290925282820152519081900360600190f35b34801561018257600080fd5b506100bd610294565b34801561019757600080fd5b506100bd61029a565b3480156101ac57600080fd5b506100bd6102a0565b3480156101c157600080fd5b506101ca6102a6565b005b3480156101d857600080fd5b506100bd610387565b6101ca60043560243561038d565b6101ca61064f565b60045481565b60008181526007602090815260409182902060010180548351818402810184019094528084526060939283018282801561026057602002820191906000526020600020905b8154600160a060020a03168152600190910190602001808311610242575b50505050509050919050565b600160a060020a03166000908152600660205260409020805460018201546002909201549092565b60025481565b60055481565b60015481565b6000805b600180546000908152600760205260409020015482101561037b57600180546000908152600760205260409020018054839081106102e457fe5b6000918252602080832090910154600254600160a060020a039091168084526006909252604090922060010154909250106103705760028054600160a060020a03831660008181526006602052604080822060010180549490940390935592549151909282156108fc02929190818181858888f1935050505015801561036e573d6000803e3d6000fd5b505b6001909101906102aa565b50506001805481019055565b60035481565b60008060035483101515156103ec576040805160e560020a62461bcd02815260206004820152600c60248201527f746f6f206c6f77207270742e0000000000000000000000000000000000000000604482015290519081900360640190fd5b60025484023414610447576040805160e560020a62461bcd02815260206004820152601460248201527f77726f6e67206465706f7369742076616c75652e000000000000000000000000604482015290519081900360640190fd5b33600081815260066020526040902054909250151561051957600454841015801561047457506005548411155b15156104ca576040805160e560020a62461bcd02815260206004820152601d60248201527f6e756d206f662063616d706169676e206f7574206f662072616e67652e000000604482015290519081900360640190fd5b6040805160608101825285815234602080830191825260018054848601908152600160a060020a03881660009081526006909352949091209251835590519082015590516002909101556105df565b600454600160a060020a0383166000908152600660205260409020548501108015906105615750600554600160a060020a038316600090815260066020526040902054850111155b15156105b7576040805160e560020a62461bcd02815260206004820152601d60248201527f6e756d206f662063616d706169676e206f7574206f662072616e67652e000000604482015290519081900360640190fd5b600160a060020a03821660009081526006602052604090208054850181556001018054340190555b50600160a060020a0381166000908152600660205260409020600201545b600160a060020a0382166000908152600660205260409020600201548401811015610649576000818152600760205260409020610640908363ffffffff61079f16565b506001016105fd565b50505050565b3360008181526006602052604081205481106106b5576040805160e560020a62461bcd02815260206004820152601660248201527f616c726561647920717569742063616d706169676e2e00000000000000000000604482015290519081900360640190fd5b506001545b600160a060020a038216600090815260066020526040902080546002909101540181101561078457600254600160a060020a0383166000908152600660205260409020600101541061075d5760028054600160a060020a03841660008181526006602052604080822060010180549490940390935592549151909282156108fc02929190818181858888f1935050505015801561075b573d6000803e3d6000fd5b505b600081815260076020526040902061077b908363ffffffff61082716565b506001016106ba565b50600160a060020a0316600090815260066020526040812055565b600160a060020a03811660009081526020839052604081205460ff16156107c857506000610821565b50600160a060020a0381166000818152602084815260408220805460ff19166001908117909155858101805480830182559084529190922001805473ffffffffffffffffffffffffffffffffffffffff19169092179091555b92915050565b600160a060020a0381166000908152602083905260408120548190819060ff16151561085657600092506109ad565b600160a060020a0384166000908152602086905260408120805460ff1916905591505b60018501548210156109a85783600160a060020a031685600101838154811015156108a057fe5b600091825260209091200154600160a060020a0316141561099d5750805b6001850154600019018110156109485784600101816001018154811015156108e257fe5b600091825260209091200154600186018054600160a060020a03909216918390811061090a57fe5b6000918252602090912001805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a03929092169190911790556001016108be565b600185018054600019810190811061095c57fe5b6000918252602090912001805473ffffffffffffffffffffffffffffffffffffffff19169055600185018054906109979060001983016109b5565b506109a8565b600190910190610879565b600192505b505092915050565b8154818355818111156109d9576000838152602090206109d99181019083016109de565b505050565b6109fc91905b808211156109f857600081556001016109e4565b5090565b905600a165627a7a723058206bdf486335a6c768152da988dc7400361e30ac9648a1b0dd784e2b04367231fe0029`

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
const SetBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a723058204e4ed00f1c34a78c5d2e02c50c7338d2f7f4c1db977f460b1dcad0ff54aa2df40029`

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
