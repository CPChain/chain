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
const AdmissionInterfaceBin = `0x`

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
const CampaignABI = "[{\"constant\":true,\"inputs\":[],\"name\":\"termLen\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_numOfCampaign\",\"type\":\"uint256\"},{\"name\":\"_cpuNonce\",\"type\":\"uint64\"},{\"name\":\"_cpuBlockNumber\",\"type\":\"uint256\"},{\"name\":\"_memoryNonce\",\"type\":\"uint64\"},{\"name\":\"_memoryBlockNumber\",\"type\":\"uint256\"}],\"name\":\"claimCampaign\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_termIdx\",\"type\":\"uint256\"}],\"name\":\"candidatesOf\",\"outputs\":[{\"name\":\"\",\"type\":\"address[]\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"termIdx\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"minNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"numPerRound\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"setRewardInterface\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"viewLen\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_maxNoc\",\"type\":\"uint256\"}],\"name\":\"updateMaxNoc\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_minNoc\",\"type\":\"uint256\"}],\"name\":\"updateMinNoc\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"setAdmissionAddr\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_termLen\",\"type\":\"uint256\"}],\"name\":\"updateTermLen\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_viewLen\",\"type\":\"uint256\"}],\"name\":\"updateViewLen\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_candidate\",\"type\":\"address\"}],\"name\":\"candidateInfoOf\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"maxNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"updateCandidateStatus\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"inputs\":[{\"name\":\"_admissionAddr\",\"type\":\"address\"},{\"name\":\"_rewardAddr\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"fallback\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"candidate\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"startTermIdx\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"stopTermIdx\",\"type\":\"uint256\"}],\"name\":\"ClaimCampaign\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"candidate\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"payback\",\"type\":\"uint256\"}],\"name\":\"QuitCampaign\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[],\"name\":\"ViewChange\",\"type\":\"event\"}]"

// CampaignBin is the compiled bytecode used for deploying new contracts.
const CampaignBin = `0x6080604052600060015560036002556004600355600254600354026004556001600555600a600655600060075534801561003857600080fd5b50604051604080610b6283398101604052805160209091015160008054600160a060020a03199081163317909155600a8054600160a060020a03948516908316179055600b8054939092169216919091179055610ac88061009a6000396000f3006080604052600436106100e55763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166314b5980e81146100e757806314b90a021461010e5780631984ab0014610133578063358057261461019b5780633a713e37146101b05780634b6b164b146101c55780635c6a541a146101da57806368f237a1146101fb5780638cb5953214610210578063a7e1f08b14610228578063c0e9e35e14610240578063c351d0a514610261578063cd60e21714610279578063db43826914610291578063e2b28158146102d0578063fcf503f8146102e5575b005b3480156100f357600080fd5b506100fc6102ed565b60408051918252519081900360200190f35b6100e560043567ffffffffffffffff60243581169060443590606435166084356102f3565b34801561013f57600080fd5b5061014b60043561067f565b60408051602080825283518183015283519192839290830191858101910280838360005b8381101561018757818101518382015260200161016f565b505050509050019250505060405180910390f35b3480156101a757600080fd5b506100fc6106ee565b3480156101bc57600080fd5b506100fc6106f4565b3480156101d157600080fd5b506100fc6106fa565b3480156101e657600080fd5b506100e5600160a060020a0360043516610700565b34801561020757600080fd5b506100fc610746565b34801561021c57600080fd5b506100e560043561074c565b34801561023457600080fd5b506100e5600435610768565b34801561024c57600080fd5b506100e5600160a060020a0360043516610784565b34801561026d57600080fd5b506100e56004356107ca565b34801561028557600080fd5b506100e56004356107fa565b34801561029d57600080fd5b506102b2600160a060020a0360043516610823565b60408051938452602084019290925282820152519081900360600190f35b3480156102dc57600080fd5b506100fc61084b565b6100e5610851565b60035481565b600a54604080517f3395492e00000000000000000000000000000000000000000000000000000000815267ffffffffffffffff808816600483015260248201879052851660448201526064810184905233608482015290516000928392600160a060020a0390911691633395492e9160a48082019260209290919082900301818787803b15801561038357600080fd5b505af1158015610397573d6000803e3d6000fd5b505050506040513d60208110156103ad57600080fd5b5051151561041c57604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601960248201527f637075206f72206d656d6f7279206e6f74207061737365642e00000000000000604482015290519081900360640190fd5b600554871015801561043057506006548711155b151561049d57604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601d60248201527f6e756d206f662063616d706169676e206f7574206f662072616e67652e000000604482015290519081900360640190fd5b6104a5610851565b336000818152600860205260409020549092501561054a57604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152603760248201527f706c6561736520776169746520756e74696c20796f7572206c61737420726f7560448201527f6e6420656e64656420616e642074727920616761696e2e000000000000000000606482015290519081900360840190fd5b600160a060020a0382166000908152600860205260409020879055600180546105789163ffffffff61097516565b600160a060020a03831660009081526008602052604090206001018190556105a6908863ffffffff61097516565b600160a060020a038316600090815260086020526040902060028101919091556001015490505b600160a060020a03821660009081526008602052604090206002015481101561061757600081815260096020526040902061060e908363ffffffff61098f16565b506001016105cd565b600160a060020a038216600081815260086020908152604091829020600181015460029091015483519485529184015282820152517f8d468194bdd18296bee5d126aa15cc492d26bdf22a0585c4a47ec4490d3a0fcf9181900360600190a150505050505050565b6000818152600960209081526040918290206001018054835181840281018401909452808452606093928301828280156106e257602002820191906000526020600020905b8154600160a060020a031681526001909101906020018083116106c4575b50505050509050919050565b60015481565b60055481565b60045481565b600054600160a060020a0316331461071757600080fd5b600b805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a0392909216919091179055565b60025481565b600054600160a060020a0316331461076357600080fd5b600655565b600054600160a060020a0316331461077f57600080fd5b600555565b600054600160a060020a0316331461079b57600080fd5b600a805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a0392909216919091179055565b600054600160a060020a031633146107e157600080fd5b60038190556002546107f4908290610a17565b60045550565b600054600160a060020a0316331461081157600080fd5b60028190556003546107f49082610a17565b600160a060020a03166000908152600860205260409020805460018201546002909201549092565b60065481565b600080600061085e610a42565b6001546007541061086e57610970565b6001546007541161097057600754600090815260096020526040812060010154935091505b828210156109625760075460009081526009602052604090206001018054839081106108bb57fe5b6000918252602080832090910154600160a060020a0316808352600890915260409091205490915015156108ee57610957565b600160a060020a038116600090815260086020526040902054610912906001610a73565b600160a060020a0382166000908152600860205260409020819055151561095757600160a060020a038116600090815260086020526040812060018101829055600201555b600190910190610893565b60078054600101905561086e565b505050565b60008282018381101561098457fe5b8091505b5092915050565b600160a060020a03811660009081526020839052604081205460ff16156109b857506000610a11565b50600160a060020a0381166000818152602084815260408220805460ff19166001908117909155858101805480830182559084529190922001805473ffffffffffffffffffffffffffffffffffffffff19169092179091555b92915050565b600080831515610a2a5760009150610988565b50828202828482811515610a3a57fe5b041461098457fe5b43801515610a54576000600155610a70565b600454610a6c9060001983019063ffffffff610a8516565b6001555b50565b600082821115610a7f57fe5b50900390565b6000808284811515610a9357fe5b049493505050505600a165627a7a72305820e969c1aef51b8d7dedb1d61b7aac3d6eb13c6e761b85b36ac06c19ff5c0adcb50029`

// DeployCampaign deploys a new cpchain contract, binding an instance of Campaign to it.
func DeployCampaign(auth *bind.TransactOpts, backend bind.ContractBackend, _admissionAddr common.Address, _rewardAddr common.Address) (common.Address, *types.Transaction, *Campaign, error) {
	parsed, err := abi.JSON(strings.NewReader(CampaignABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(CampaignBin), backend, _admissionAddr, _rewardAddr)
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

// ClaimCampaign is a paid mutator transaction binding the contract method 0x14b90a02.
//
// Solidity: function claimCampaign(_numOfCampaign uint256, _cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256) returns()
func (_Campaign *CampaignTransactor) ClaimCampaign(opts *bind.TransactOpts, _numOfCampaign *big.Int, _cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "claimCampaign", _numOfCampaign, _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber)
}

// ClaimCampaign is a paid mutator transaction binding the contract method 0x14b90a02.
//
// Solidity: function claimCampaign(_numOfCampaign uint256, _cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256) returns()
func (_Campaign *CampaignSession) ClaimCampaign(_numOfCampaign *big.Int, _cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.ClaimCampaign(&_Campaign.TransactOpts, _numOfCampaign, _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber)
}

// ClaimCampaign is a paid mutator transaction binding the contract method 0x14b90a02.
//
// Solidity: function claimCampaign(_numOfCampaign uint256, _cpuNonce uint64, _cpuBlockNumber uint256, _memoryNonce uint64, _memoryBlockNumber uint256) returns()
func (_Campaign *CampaignTransactorSession) ClaimCampaign(_numOfCampaign *big.Int, _cpuNonce uint64, _cpuBlockNumber *big.Int, _memoryNonce uint64, _memoryBlockNumber *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.ClaimCampaign(&_Campaign.TransactOpts, _numOfCampaign, _cpuNonce, _cpuBlockNumber, _memoryNonce, _memoryBlockNumber)
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

// SetRewardInterface is a paid mutator transaction binding the contract method 0x5c6a541a.
//
// Solidity: function setRewardInterface(_addr address) returns()
func (_Campaign *CampaignTransactor) SetRewardInterface(opts *bind.TransactOpts, _addr common.Address) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "setRewardInterface", _addr)
}

// SetRewardInterface is a paid mutator transaction binding the contract method 0x5c6a541a.
//
// Solidity: function setRewardInterface(_addr address) returns()
func (_Campaign *CampaignSession) SetRewardInterface(_addr common.Address) (*types.Transaction, error) {
	return _Campaign.Contract.SetRewardInterface(&_Campaign.TransactOpts, _addr)
}

// SetRewardInterface is a paid mutator transaction binding the contract method 0x5c6a541a.
//
// Solidity: function setRewardInterface(_addr address) returns()
func (_Campaign *CampaignTransactorSession) SetRewardInterface(_addr common.Address) (*types.Transaction, error) {
	return _Campaign.Contract.SetRewardInterface(&_Campaign.TransactOpts, _addr)
}

// UpdateCandidateStatus is a paid mutator transaction binding the contract method 0xfcf503f8.
//
// Solidity: function updateCandidateStatus() returns()
func (_Campaign *CampaignTransactor) UpdateCandidateStatus(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "updateCandidateStatus")
}

// UpdateCandidateStatus is a paid mutator transaction binding the contract method 0xfcf503f8.
//
// Solidity: function updateCandidateStatus() returns()
func (_Campaign *CampaignSession) UpdateCandidateStatus() (*types.Transaction, error) {
	return _Campaign.Contract.UpdateCandidateStatus(&_Campaign.TransactOpts)
}

// UpdateCandidateStatus is a paid mutator transaction binding the contract method 0xfcf503f8.
//
// Solidity: function updateCandidateStatus() returns()
func (_Campaign *CampaignTransactorSession) UpdateCandidateStatus() (*types.Transaction, error) {
	return _Campaign.Contract.UpdateCandidateStatus(&_Campaign.TransactOpts)
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

// CampaignQuitCampaignIterator is returned from FilterQuitCampaign and is used to iterate over the raw logs and unpacked data for QuitCampaign events raised by the Campaign contract.
type CampaignQuitCampaignIterator struct {
	Event *CampaignQuitCampaign // Event containing the contract specifics and raw log

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
func (it *CampaignQuitCampaignIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(CampaignQuitCampaign)
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
		it.Event = new(CampaignQuitCampaign)
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
func (it *CampaignQuitCampaignIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *CampaignQuitCampaignIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// CampaignQuitCampaign represents a QuitCampaign event raised by the Campaign contract.
type CampaignQuitCampaign struct {
	Candidate common.Address
	Payback   *big.Int
	Raw       types.Log // Blockchain specific contextual infos
}

// FilterQuitCampaign is a free log retrieval operation binding the contract event 0x2fa4b892c3c1209cb29cf6b97ec72ea6159bbba59ac1f44932e801d1469fbec3.
//
// Solidity: e QuitCampaign(candidate address, payback uint256)
func (_Campaign *CampaignFilterer) FilterQuitCampaign(opts *bind.FilterOpts) (*CampaignQuitCampaignIterator, error) {

	logs, sub, err := _Campaign.contract.FilterLogs(opts, "QuitCampaign")
	if err != nil {
		return nil, err
	}
	return &CampaignQuitCampaignIterator{contract: _Campaign.contract, event: "QuitCampaign", logs: logs, sub: sub}, nil
}

// WatchQuitCampaign is a free log subscription operation binding the contract event 0x2fa4b892c3c1209cb29cf6b97ec72ea6159bbba59ac1f44932e801d1469fbec3.
//
// Solidity: e QuitCampaign(candidate address, payback uint256)
func (_Campaign *CampaignFilterer) WatchQuitCampaign(opts *bind.WatchOpts, sink chan<- *CampaignQuitCampaign) (event.Subscription, error) {

	logs, sub, err := _Campaign.contract.WatchLogs(opts, "QuitCampaign")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(CampaignQuitCampaign)
				if err := _Campaign.contract.UnpackLog(event, "QuitCampaign", log); err != nil {
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

// CampaignViewChangeIterator is returned from FilterViewChange and is used to iterate over the raw logs and unpacked data for ViewChange events raised by the Campaign contract.
type CampaignViewChangeIterator struct {
	Event *CampaignViewChange // Event containing the contract specifics and raw log

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
func (it *CampaignViewChangeIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(CampaignViewChange)
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
		it.Event = new(CampaignViewChange)
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
func (it *CampaignViewChangeIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *CampaignViewChangeIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// CampaignViewChange represents a ViewChange event raised by the Campaign contract.
type CampaignViewChange struct {
	Raw types.Log // Blockchain specific contextual infos
}

// FilterViewChange is a free log retrieval operation binding the contract event 0xbeff1476fe7702a6f0dc32d7145dade82177da4a8728ed523e84f0af5c4585a9.
//
// Solidity: e ViewChange()
func (_Campaign *CampaignFilterer) FilterViewChange(opts *bind.FilterOpts) (*CampaignViewChangeIterator, error) {

	logs, sub, err := _Campaign.contract.FilterLogs(opts, "ViewChange")
	if err != nil {
		return nil, err
	}
	return &CampaignViewChangeIterator{contract: _Campaign.contract, event: "ViewChange", logs: logs, sub: sub}, nil
}

// WatchViewChange is a free log subscription operation binding the contract event 0xbeff1476fe7702a6f0dc32d7145dade82177da4a8728ed523e84f0af5c4585a9.
//
// Solidity: e ViewChange()
func (_Campaign *CampaignFilterer) WatchViewChange(opts *bind.WatchOpts, sink chan<- *CampaignViewChange) (event.Subscription, error) {

	logs, sub, err := _Campaign.contract.WatchLogs(opts, "ViewChange")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(CampaignViewChange)
				if err := _Campaign.contract.UnpackLog(event, "ViewChange", log); err != nil {
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

// RewardInterfaceABI is the input ABI used to generate the binding from.
const RewardInterfaceABI = "[{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"isCandidate\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"}]"

// RewardInterfaceBin is the compiled bytecode used for deploying new contracts.
const RewardInterfaceBin = `0x`

// DeployRewardInterface deploys a new cpchain contract, binding an instance of RewardInterface to it.
func DeployRewardInterface(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *RewardInterface, error) {
	parsed, err := abi.JSON(strings.NewReader(RewardInterfaceABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(RewardInterfaceBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &RewardInterface{RewardInterfaceCaller: RewardInterfaceCaller{contract: contract}, RewardInterfaceTransactor: RewardInterfaceTransactor{contract: contract}, RewardInterfaceFilterer: RewardInterfaceFilterer{contract: contract}}, nil
}

// RewardInterface is an auto generated Go binding around an cpchain contract.
type RewardInterface struct {
	RewardInterfaceCaller     // Read-only binding to the contract
	RewardInterfaceTransactor // Write-only binding to the contract
	RewardInterfaceFilterer   // Log filterer for contract events
}

// RewardInterfaceCaller is an auto generated read-only Go binding around an cpchain contract.
type RewardInterfaceCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RewardInterfaceTransactor is an auto generated write-only Go binding around an cpchain contract.
type RewardInterfaceTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RewardInterfaceFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type RewardInterfaceFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RewardInterfaceSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type RewardInterfaceSession struct {
	Contract     *RewardInterface  // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// RewardInterfaceCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type RewardInterfaceCallerSession struct {
	Contract *RewardInterfaceCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts          // Call options to use throughout this session
}

// RewardInterfaceTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type RewardInterfaceTransactorSession struct {
	Contract     *RewardInterfaceTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts          // Transaction auth options to use throughout this session
}

// RewardInterfaceRaw is an auto generated low-level Go binding around an cpchain contract.
type RewardInterfaceRaw struct {
	Contract *RewardInterface // Generic contract binding to access the raw methods on
}

// RewardInterfaceCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type RewardInterfaceCallerRaw struct {
	Contract *RewardInterfaceCaller // Generic read-only contract binding to access the raw methods on
}

// RewardInterfaceTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type RewardInterfaceTransactorRaw struct {
	Contract *RewardInterfaceTransactor // Generic write-only contract binding to access the raw methods on
}

// NewRewardInterface creates a new instance of RewardInterface, bound to a specific deployed contract.
func NewRewardInterface(address common.Address, backend bind.ContractBackend) (*RewardInterface, error) {
	contract, err := bindRewardInterface(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &RewardInterface{RewardInterfaceCaller: RewardInterfaceCaller{contract: contract}, RewardInterfaceTransactor: RewardInterfaceTransactor{contract: contract}, RewardInterfaceFilterer: RewardInterfaceFilterer{contract: contract}}, nil
}

// NewRewardInterfaceCaller creates a new read-only instance of RewardInterface, bound to a specific deployed contract.
func NewRewardInterfaceCaller(address common.Address, caller bind.ContractCaller) (*RewardInterfaceCaller, error) {
	contract, err := bindRewardInterface(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &RewardInterfaceCaller{contract: contract}, nil
}

// NewRewardInterfaceTransactor creates a new write-only instance of RewardInterface, bound to a specific deployed contract.
func NewRewardInterfaceTransactor(address common.Address, transactor bind.ContractTransactor) (*RewardInterfaceTransactor, error) {
	contract, err := bindRewardInterface(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &RewardInterfaceTransactor{contract: contract}, nil
}

// NewRewardInterfaceFilterer creates a new log filterer instance of RewardInterface, bound to a specific deployed contract.
func NewRewardInterfaceFilterer(address common.Address, filterer bind.ContractFilterer) (*RewardInterfaceFilterer, error) {
	contract, err := bindRewardInterface(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &RewardInterfaceFilterer{contract: contract}, nil
}

// bindRewardInterface binds a generic wrapper to an already deployed contract.
func bindRewardInterface(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(RewardInterfaceABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_RewardInterface *RewardInterfaceRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _RewardInterface.Contract.RewardInterfaceCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_RewardInterface *RewardInterfaceRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _RewardInterface.Contract.RewardInterfaceTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_RewardInterface *RewardInterfaceRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _RewardInterface.Contract.RewardInterfaceTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_RewardInterface *RewardInterfaceCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _RewardInterface.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_RewardInterface *RewardInterfaceTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _RewardInterface.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_RewardInterface *RewardInterfaceTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _RewardInterface.Contract.contract.Transact(opts, method, params...)
}

// IsCandidate is a free data retrieval call binding the contract method 0xd51b9e93.
//
// Solidity: function isCandidate(_addr address) constant returns(bool)
func (_RewardInterface *RewardInterfaceCaller) IsCandidate(opts *bind.CallOpts, _addr common.Address) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _RewardInterface.contract.Call(opts, out, "isCandidate", _addr)
	return *ret0, err
}

// IsCandidate is a free data retrieval call binding the contract method 0xd51b9e93.
//
// Solidity: function isCandidate(_addr address) constant returns(bool)
func (_RewardInterface *RewardInterfaceSession) IsCandidate(_addr common.Address) (bool, error) {
	return _RewardInterface.Contract.IsCandidate(&_RewardInterface.CallOpts, _addr)
}

// IsCandidate is a free data retrieval call binding the contract method 0xd51b9e93.
//
// Solidity: function isCandidate(_addr address) constant returns(bool)
func (_RewardInterface *RewardInterfaceCallerSession) IsCandidate(_addr common.Address) (bool, error) {
	return _RewardInterface.Contract.IsCandidate(&_RewardInterface.CallOpts, _addr)
}

// SafeMathABI is the input ABI used to generate the binding from.
const SafeMathABI = "[]"

// SafeMathBin is the compiled bytecode used for deploying new contracts.
const SafeMathBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a723058201b8caa1be5474007e468c99c8ab9b5a0478462f50dcef260063ab6a40b0f03a50029`

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
const SetBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a723058206fd49004c5df1f8addb31ffa0262c5c9cf2790abf6d403a39f4b16397764a54c0029`

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
