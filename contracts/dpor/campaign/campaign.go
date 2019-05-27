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
const CampaignABI = "[{\"constant\":true,\"inputs\":[],\"name\":\"termLen\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_termIdx\",\"type\":\"uint256\"}],\"name\":\"candidatesOf\",\"outputs\":[{\"name\":\"\",\"type\":\"address[]\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_numOfCampaign\",\"type\":\"uint256\"},{\"name\":\"_cpuNonce\",\"type\":\"uint64\"},{\"name\":\"_cpuBlockNumber\",\"type\":\"uint256\"},{\"name\":\"_memoryNonce\",\"type\":\"uint64\"},{\"name\":\"_memoryBlockNumber\",\"type\":\"uint256\"},{\"name\":\"version\",\"type\":\"uint256\"}],\"name\":\"claimCampaign\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"termIdx\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"minNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"numPerRound\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"maxCandidates\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"viewLen\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"updatedTermIdx\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_supportedVersion\",\"type\":\"uint256\"}],\"name\":\"updateSupportedVersion\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_maxNoc\",\"type\":\"uint256\"}],\"name\":\"updateMaxNoc\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_minNoc\",\"type\":\"uint256\"}],\"name\":\"updateMinNoc\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"acceptableBlocks\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"setAdmissionAddr\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_termLen\",\"type\":\"uint256\"}],\"name\":\"updateTermLen\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_maxCandidates\",\"type\":\"uint256\"}],\"name\":\"updateMaxCandidates\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_viewLen\",\"type\":\"uint256\"}],\"name\":\"updateViewLen\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"supportedVersion\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_acceptableBlocks\",\"type\":\"uint256\"}],\"name\":\"updateAcceptableBlocks\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_candidate\",\"type\":\"address\"}],\"name\":\"candidateInfoOf\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"maxNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"setRnodeInterface\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[{\"name\":\"_admissionAddr\",\"type\":\"address\"},{\"name\":\"_rnodeAddr\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"fallback\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"candidate\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"startTermIdx\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"stopTermIdx\",\"type\":\"uint256\"}],\"name\":\"ClaimCampaign\",\"type\":\"event\"}]"

// CampaignBin is the compiled bytecode used for deploying new contracts.
const CampaignBin = `0x60806040526000600181815560036002819055600c905560246004556005819055600a6006819055600781905560088290556009929092556096909155600b805460ff1916909117905534801561005557600080fd5b50604051604080610ed78339810160405280516020909101516000805433600160a060020a031991821617909155600e80548216600160a060020a0380861691909117909155600f80549092169083161790556004546100da906100c74360016401000000006100e58102610b281704565b90640100000000610b3f6100f782021704565b6009555061010e9050565b6000828211156100f157fe5b50900390565b600080828481151561010557fe5b04949350505050565b610dba8061011d6000396000f3006080604052600436106101275763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166314b5980e811461012c5780631984ab0014610153578063350cc724146101bb57806335805726146101f25780633a713e37146102075780634b6b164b1461021c57806365af2ac81461023157806368f237a11461024657806370e580e51461025b5780637dd604d6146102705780638cb5953214610288578063a7e1f08b146102a0578063a9d1de48146102b8578063c0e9e35e146102cd578063c351d0a5146102ee578063c7882cf214610306578063cd60e2171461031e578063d5601e9f14610336578063dae49ab21461034b578063db43826914610363578063e2b28158146103a2578063f2aaabdd146103b7575b600080fd5b34801561013857600080fd5b506101416103d8565b60408051918252519081900360200190f35b34801561015f57600080fd5b5061016b6004356103de565b60408051602080825283518183015283519192839290830191858101910280838360005b838110156101a757818101518382015260200161018f565b505050509050019250505060405180910390f35b3480156101c757600080fd5b506101f060043567ffffffffffffffff602435811690604435906064351660843560a43561044d565b005b3480156101fe57600080fd5b50610141610959565b34801561021357600080fd5b5061014161095f565b34801561022857600080fd5b50610141610965565b34801561023d57600080fd5b5061014161096b565b34801561025257600080fd5b50610141610971565b34801561026757600080fd5b50610141610977565b34801561027c57600080fd5b506101f060043561097d565b34801561029457600080fd5b506101f0600435610999565b3480156102ac57600080fd5b506101f06004356109b5565b3480156102c457600080fd5b506101416109d1565b3480156102d957600080fd5b506101f0600160a060020a03600435166109d7565b3480156102fa57600080fd5b506101f0600435610a1d565b34801561031257600080fd5b506101f0600435610a4d565b34801561032a57600080fd5b506101f0600435610a69565b34801561034257600080fd5b50610141610a92565b34801561035757600080fd5b506101f0600435610a98565b34801561036f57600080fd5b50610384600160a060020a0360043516610ab4565b60408051938452602084019290925282820152519081900360600190f35b3480156103ae57600080fd5b50610141610adc565b3480156103c357600080fd5b506101f0600160a060020a0360043516610ae2565b60035481565b6000818152600d602090815260409182902060010180548351818402810184019094528084526060939283018282801561044157602002820191906000526020600020905b8154600160a060020a03168152600190910190602001808311610423575b50505050509050919050565b600b546000908190819060ff1615610491576004546104839061047743600163ffffffff610b2816565b9063ffffffff610b3f16565b600955600b805460ff191690555b610499610b5b565b60015460010192505b600154890183116104cf57600a546104b9846103de565b51106104c457600080fd5b6001909201916104a2565b6008548410156104de57600080fd5b600754431115610529576007546104fc90439063ffffffff610b2816565b871015801561051e575060075461051a90439063ffffffff610b2816565b8510155b151561052957600080fd5b600f54604080517fa8f076970000000000000000000000000000000000000000000000000000000081523360048201529051600160a060020a039092169163a8f07697916024808201926020929091908290030181600087803b15801561058f57600080fd5b505af11580156105a3573d6000803e3d6000fd5b505050506040513d60208110156105b957600080fd5b50511515600114610614576040805160e560020a62461bcd02815260206004820152601260248201527f6e6f7420524e6f646520627920726e6f64650000000000000000000000000000604482015290519081900360640190fd5b600e54604080517f3395492e00000000000000000000000000000000000000000000000000000000815267ffffffffffffffff808c166004830152602482018b905289166044820152606481018890523360848201529051600160a060020a0390921691633395492e9160a4808201926020929091908290030181600087803b1580156106a057600080fd5b505af11580156106b4573d6000803e3d6000fd5b505050506040513d60208110156106ca57600080fd5b50511515610722576040805160e560020a62461bcd02815260206004820152601960248201527f637075206f72206d656d6f7279206e6f74207061737365642e00000000000000604482015290519081900360640190fd5b600554891015801561073657506006548911155b151561078c576040805160e560020a62461bcd02815260206004820152601d60248201527f6e756d206f662063616d706169676e206f7574206f662072616e67652e000000604482015290519081900360640190fd5b610794610b8c565b336000818152600c602052604090205490925015610822576040805160e560020a62461bcd02815260206004820152603760248201527f706c6561736520776169746520756e74696c20796f7572206c61737420726f7560448201527f6e6420656e64656420616e642074727920616761696e2e000000000000000000606482015290519081900360840190fd5b600160a060020a0382166000908152600c60205260409020899055600180546108509163ffffffff610ccd16565b600160a060020a0383166000908152600c6020526040902060010181905561087e908a63ffffffff610ccd16565b600160a060020a0383166000908152600c6020526040902060028101919091556001015490505b600160a060020a0382166000908152600c60205260409020600201548110156108ef576000818152600d602052604090206108e6908363ffffffff610ce316565b506001016108a5565b600160a060020a0382166000818152600c6020908152604091829020600181015460029091015483519485529184015282820152517f8d468194bdd18296bee5d126aa15cc492d26bdf22a0585c4a47ec4490d3a0fcf9181900360600190a1505050505050505050565b60015481565b60055481565b60045481565b600a5481565b60025481565b60095481565b600054600160a060020a0316331461099457600080fd5b600855565b600054600160a060020a031633146109b057600080fd5b600655565b600054600160a060020a031633146109cc57600080fd5b600555565b60075481565b600054600160a060020a031633146109ee57600080fd5b600e805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a0392909216919091179055565b600054600160a060020a03163314610a3457600080fd5b6003819055600254610a47908290610d63565b60045550565b600054600160a060020a03163314610a6457600080fd5b600a55565b600054600160a060020a03163314610a8057600080fd5b6002819055600354610a479082610d63565b60085481565b600054600160a060020a03163314610aaf57600080fd5b600755565b600160a060020a03166000908152600c60205260409020805460018201546002909201549092565b60065481565b600054600160a060020a03163314610af957600080fd5b600f805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a0392909216919091179055565b600082821115610b3457fe5b508082035b92915050565b6000808284811515610b4d57fe5b0490508091505b5092915050565b43801515610b6d576000600155610b89565b600454610b859061047783600163ffffffff610b2816565b6001555b50565b6000806000806000600154600954101515610ba657610cc6565b600954600154039450600092505b84831015610cc657600954610bd090600163ffffffff610ccd16565b60098190556000908152600d6020526040812060010154945091505b83821015610cbb576009546000908152600d60205260409020600101805483908110610c1457fe5b6000918252602080832090910154600160a060020a0316808352600c9091526040909120549091501515610c4757610cb0565b600160a060020a0381166000908152600c6020526040902054610c6b906001610b28565b600160a060020a0382166000908152600c602052604090208190551515610cb057600160a060020a0381166000908152600c6020526040812060018101829055600201555b600190910190610bec565b600190920191610bb4565b5050505050565b600082820183811015610cdc57fe5b9392505050565b600160a060020a03811660009081526020839052604081205460ff1615610d0c57506000610b39565b50600160a060020a03166000818152602083815260408220805460ff1916600190811790915593840180548086018255908352912001805473ffffffffffffffffffffffffffffffffffffffff1916909117905590565b600080831515610d765760009150610b54565b50828202828482811515610d8657fe5b0414610cdc57fe00a165627a7a72305820a2ead9683adf42ebb98e73bee85b989cfde3ea80226bf3d09b47bff8733a23850029`

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

// MaxCandidates is a free data retrieval call binding the contract method 0x65af2ac8.
//
// Solidity: function maxCandidates() constant returns(uint256)
func (_Campaign *CampaignCaller) MaxCandidates(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Campaign.contract.Call(opts, out, "maxCandidates")
	return *ret0, err
}

// MaxCandidates is a free data retrieval call binding the contract method 0x65af2ac8.
//
// Solidity: function maxCandidates() constant returns(uint256)
func (_Campaign *CampaignSession) MaxCandidates() (*big.Int, error) {
	return _Campaign.Contract.MaxCandidates(&_Campaign.CallOpts)
}

// MaxCandidates is a free data retrieval call binding the contract method 0x65af2ac8.
//
// Solidity: function maxCandidates() constant returns(uint256)
func (_Campaign *CampaignCallerSession) MaxCandidates() (*big.Int, error) {
	return _Campaign.Contract.MaxCandidates(&_Campaign.CallOpts)
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

// UpdateMaxCandidates is a paid mutator transaction binding the contract method 0xc7882cf2.
//
// Solidity: function updateMaxCandidates(_maxCandidates uint256) returns()
func (_Campaign *CampaignTransactor) UpdateMaxCandidates(opts *bind.TransactOpts, _maxCandidates *big.Int) (*types.Transaction, error) {
	return _Campaign.contract.Transact(opts, "updateMaxCandidates", _maxCandidates)
}

// UpdateMaxCandidates is a paid mutator transaction binding the contract method 0xc7882cf2.
//
// Solidity: function updateMaxCandidates(_maxCandidates uint256) returns()
func (_Campaign *CampaignSession) UpdateMaxCandidates(_maxCandidates *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateMaxCandidates(&_Campaign.TransactOpts, _maxCandidates)
}

// UpdateMaxCandidates is a paid mutator transaction binding the contract method 0xc7882cf2.
//
// Solidity: function updateMaxCandidates(_maxCandidates uint256) returns()
func (_Campaign *CampaignTransactorSession) UpdateMaxCandidates(_maxCandidates *big.Int) (*types.Transaction, error) {
	return _Campaign.Contract.UpdateMaxCandidates(&_Campaign.TransactOpts, _maxCandidates)
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
const SafeMathBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a723058204fbe02d5361705dda8b0abae944f941a43b101856134a018becba4d3ff3edfa70029`

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
const SetBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a7230582032c8e068b56b0e2881115968d669979bae175c0bdf2b46201955333e1bd7d4e50029`

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
