// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package network

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

// NetworkABI is the input ABI used to generate the binding from.
const NetworkABI = "[{\"constant\":true,\"inputs\":[],\"name\":\"count\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_gap\",\"type\":\"uint256\"}],\"name\":\"updateGap\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_open\",\"type\":\"bool\"}],\"name\":\"updateOpen\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_count\",\"type\":\"uint256\"}],\"name\":\"updateCount\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"gap\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"timeout\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_host\",\"type\":\"string\"}],\"name\":\"updateHost\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_timeout\",\"type\":\"uint256\"}],\"name\":\"updateTimeout\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"host\",\"outputs\":[{\"name\":\"\",\"type\":\"string\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"open\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"config\",\"type\":\"string\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"UpdateConfig\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"value\",\"type\":\"string\"}],\"name\":\"UpdateHost\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"value\",\"type\":\"bool\"}],\"name\":\"UpdateOpen\",\"type\":\"event\"}]"

// NetworkBin is the compiled bytecode used for deploying new contracts.
const NetworkBin = `0x60c0604052601560808190527f7777772e6d6963726f736f66742e636f6d3a343433000000000000000000000060a090815261003e9160009190610087565b506003600181815561012c60025560649091556004805460ff1916909117905534801561006a57600080fd5b506004805461010060a860020a0319163361010002179055610122565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f106100c857805160ff19168380011785556100f5565b828001600101855582156100f5579182015b828111156100f55782518255916020019190600101906100da565b50610101929150610105565b5090565b61011f91905b80821115610101576000815560010161010b565b90565b610759806101316000396000f3006080604052600436106100a35763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166306661abd81146100a8578063150899cd146100cf578063316d155b146100e957806345516ee0146101035780636c32c0a61461011b57806370dea79a1461013057806380bed41814610145578063a330214e1461019e578063f437bc59146101b6578063fcfff16f14610240575b600080fd5b3480156100b457600080fd5b506100bd610269565b60408051918252519081900360200190f35b3480156100db57600080fd5b506100e760043561026f565b005b3480156100f557600080fd5b506100e76004351515610324565b34801561010f57600080fd5b506100e7600435610399565b34801561012757600080fd5b506100bd61044d565b34801561013c57600080fd5b506100bd610453565b34801561015157600080fd5b506040805160206004803580820135601f81018490048402850184019095528484526100e79436949293602493928401919081908401838280828437509497506104599650505050505050565b3480156101aa57600080fd5b506100e7600435610546565b3480156101c257600080fd5b506101cb6105fb565b6040805160208082528351818301528351919283929083019185019080838360005b838110156102055781810151838201526020016101ed565b50505050905090810190601f1680156102325780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b34801561024c57600080fd5b50610255610689565b604080519115158252519081900360200190f35b60015481565b600454610100900473ffffffffffffffffffffffffffffffffffffffff16331461029857600080fd5b600a81101580156102ab5750610bb88111155b15156102b657600080fd5b60038181556040805160208101849052818152808201929092527f67617000000000000000000000000000000000000000000000000000000000006060830152517f6818c9181f3a8cb0f4d8178667c423a4c4ed24fc2410822be08e76ef50b2de1e9181900360800190a150565b600454610100900473ffffffffffffffffffffffffffffffffffffffff16331461034d57600080fd5b6004805460ff191682151517908190556040805160ff90921615158252517f3acb93048c9b0c52dcccea319343be25e3be345a3a087b9f3304ef4b7be66449916020908290030190a150565b600454610100900473ffffffffffffffffffffffffffffffffffffffff1633146103c257600080fd5b600181101580156103d4575060148111155b15156103df57600080fd5b600181905560408051602081018390528181526005818301527f636f756e74000000000000000000000000000000000000000000000000000000606082015290517f6818c9181f3a8cb0f4d8178667c423a4c4ed24fc2410822be08e76ef50b2de1e9181900360800190a150565b60035481565b60025481565b600454610100900473ffffffffffffffffffffffffffffffffffffffff16331461048257600080fd5b8051610495906000906020840190610692565b5060408051602080825260008054600260001961010060018416150201909116049183018290527f958adb313e9ddd949012b779ce40fe9b2e593e682b7b256c58f100f1c3235c33939092918291820190849080156105355780601f1061050a57610100808354040283529160200191610535565b820191906000526020600020905b81548152906001019060200180831161051857829003601f168201915b50509250505060405180910390a150565b600454610100900473ffffffffffffffffffffffffffffffffffffffff16331461056f57600080fd5b6032811015801561058257506127108111155b151561058d57600080fd5b600281905560408051602081018390528181526007818301527f74696d656f757400000000000000000000000000000000000000000000000000606082015290517f6818c9181f3a8cb0f4d8178667c423a4c4ed24fc2410822be08e76ef50b2de1e9181900360800190a150565b6000805460408051602060026001851615610100026000190190941693909304601f810184900484028201840190925281815292918301828280156106815780601f1061065657610100808354040283529160200191610681565b820191906000526020600020905b81548152906001019060200180831161066457829003601f168201915b505050505081565b60045460ff1681565b828054600181600116156101000203166002900490600052602060002090601f016020900481019282601f106106d357805160ff1916838001178555610700565b82800160010185558215610700579182015b828111156107005782518255916020019190600101906106e5565b5061070c929150610710565b5090565b61072a91905b8082111561070c5760008155600101610716565b905600a165627a7a723058203692e0ce5fc061e9e6d0feab80e5a3f20eb38249dead1a9c5a697576c4cfe15b0029`

// DeployNetwork deploys a new cpchain contract, binding an instance of Network to it.
func DeployNetwork(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *Network, error) {
	parsed, err := abi.JSON(strings.NewReader(NetworkABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(NetworkBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &Network{NetworkCaller: NetworkCaller{contract: contract}, NetworkTransactor: NetworkTransactor{contract: contract}, NetworkFilterer: NetworkFilterer{contract: contract}}, nil
}

// Network is an auto generated Go binding around an cpchain contract.
type Network struct {
	NetworkCaller     // Read-only binding to the contract
	NetworkTransactor // Write-only binding to the contract
	NetworkFilterer   // Log filterer for contract events
}

// NetworkCaller is an auto generated read-only Go binding around an cpchain contract.
type NetworkCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// NetworkTransactor is an auto generated write-only Go binding around an cpchain contract.
type NetworkTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// NetworkFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type NetworkFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// NetworkSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type NetworkSession struct {
	Contract     *Network          // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// NetworkCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type NetworkCallerSession struct {
	Contract *NetworkCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts  // Call options to use throughout this session
}

// NetworkTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type NetworkTransactorSession struct {
	Contract     *NetworkTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts  // Transaction auth options to use throughout this session
}

// NetworkRaw is an auto generated low-level Go binding around an cpchain contract.
type NetworkRaw struct {
	Contract *Network // Generic contract binding to access the raw methods on
}

// NetworkCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type NetworkCallerRaw struct {
	Contract *NetworkCaller // Generic read-only contract binding to access the raw methods on
}

// NetworkTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type NetworkTransactorRaw struct {
	Contract *NetworkTransactor // Generic write-only contract binding to access the raw methods on
}

// NewNetwork creates a new instance of Network, bound to a specific deployed contract.
func NewNetwork(address common.Address, backend bind.ContractBackend) (*Network, error) {
	contract, err := bindNetwork(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &Network{NetworkCaller: NetworkCaller{contract: contract}, NetworkTransactor: NetworkTransactor{contract: contract}, NetworkFilterer: NetworkFilterer{contract: contract}}, nil
}

// NewNetworkCaller creates a new read-only instance of Network, bound to a specific deployed contract.
func NewNetworkCaller(address common.Address, caller bind.ContractCaller) (*NetworkCaller, error) {
	contract, err := bindNetwork(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &NetworkCaller{contract: contract}, nil
}

// NewNetworkTransactor creates a new write-only instance of Network, bound to a specific deployed contract.
func NewNetworkTransactor(address common.Address, transactor bind.ContractTransactor) (*NetworkTransactor, error) {
	contract, err := bindNetwork(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &NetworkTransactor{contract: contract}, nil
}

// NewNetworkFilterer creates a new log filterer instance of Network, bound to a specific deployed contract.
func NewNetworkFilterer(address common.Address, filterer bind.ContractFilterer) (*NetworkFilterer, error) {
	contract, err := bindNetwork(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &NetworkFilterer{contract: contract}, nil
}

// bindNetwork binds a generic wrapper to an already deployed contract.
func bindNetwork(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(NetworkABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Network *NetworkRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Network.Contract.NetworkCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Network *NetworkRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Network.Contract.NetworkTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Network *NetworkRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Network.Contract.NetworkTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Network *NetworkCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Network.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Network *NetworkTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Network.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Network *NetworkTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Network.Contract.contract.Transact(opts, method, params...)
}

// Count is a free data retrieval call binding the contract method 0x06661abd.
//
// Solidity: function count() constant returns(uint256)
func (_Network *NetworkCaller) Count(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Network.contract.Call(opts, out, "count")
	return *ret0, err
}

// Count is a free data retrieval call binding the contract method 0x06661abd.
//
// Solidity: function count() constant returns(uint256)
func (_Network *NetworkSession) Count() (*big.Int, error) {
	return _Network.Contract.Count(&_Network.CallOpts)
}

// Count is a free data retrieval call binding the contract method 0x06661abd.
//
// Solidity: function count() constant returns(uint256)
func (_Network *NetworkCallerSession) Count() (*big.Int, error) {
	return _Network.Contract.Count(&_Network.CallOpts)
}

// Gap is a free data retrieval call binding the contract method 0x6c32c0a6.
//
// Solidity: function gap() constant returns(uint256)
func (_Network *NetworkCaller) Gap(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Network.contract.Call(opts, out, "gap")
	return *ret0, err
}

// Gap is a free data retrieval call binding the contract method 0x6c32c0a6.
//
// Solidity: function gap() constant returns(uint256)
func (_Network *NetworkSession) Gap() (*big.Int, error) {
	return _Network.Contract.Gap(&_Network.CallOpts)
}

// Gap is a free data retrieval call binding the contract method 0x6c32c0a6.
//
// Solidity: function gap() constant returns(uint256)
func (_Network *NetworkCallerSession) Gap() (*big.Int, error) {
	return _Network.Contract.Gap(&_Network.CallOpts)
}

// Host is a free data retrieval call binding the contract method 0xf437bc59.
//
// Solidity: function host() constant returns(string)
func (_Network *NetworkCaller) Host(opts *bind.CallOpts) (string, error) {
	var (
		ret0 = new(string)
	)
	out := ret0
	err := _Network.contract.Call(opts, out, "host")
	return *ret0, err
}

// Host is a free data retrieval call binding the contract method 0xf437bc59.
//
// Solidity: function host() constant returns(string)
func (_Network *NetworkSession) Host() (string, error) {
	return _Network.Contract.Host(&_Network.CallOpts)
}

// Host is a free data retrieval call binding the contract method 0xf437bc59.
//
// Solidity: function host() constant returns(string)
func (_Network *NetworkCallerSession) Host() (string, error) {
	return _Network.Contract.Host(&_Network.CallOpts)
}

// Open is a free data retrieval call binding the contract method 0xfcfff16f.
//
// Solidity: function open() constant returns(bool)
func (_Network *NetworkCaller) Open(opts *bind.CallOpts) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Network.contract.Call(opts, out, "open")
	return *ret0, err
}

// Open is a free data retrieval call binding the contract method 0xfcfff16f.
//
// Solidity: function open() constant returns(bool)
func (_Network *NetworkSession) Open() (bool, error) {
	return _Network.Contract.Open(&_Network.CallOpts)
}

// Open is a free data retrieval call binding the contract method 0xfcfff16f.
//
// Solidity: function open() constant returns(bool)
func (_Network *NetworkCallerSession) Open() (bool, error) {
	return _Network.Contract.Open(&_Network.CallOpts)
}

// Timeout is a free data retrieval call binding the contract method 0x70dea79a.
//
// Solidity: function timeout() constant returns(uint256)
func (_Network *NetworkCaller) Timeout(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Network.contract.Call(opts, out, "timeout")
	return *ret0, err
}

// Timeout is a free data retrieval call binding the contract method 0x70dea79a.
//
// Solidity: function timeout() constant returns(uint256)
func (_Network *NetworkSession) Timeout() (*big.Int, error) {
	return _Network.Contract.Timeout(&_Network.CallOpts)
}

// Timeout is a free data retrieval call binding the contract method 0x70dea79a.
//
// Solidity: function timeout() constant returns(uint256)
func (_Network *NetworkCallerSession) Timeout() (*big.Int, error) {
	return _Network.Contract.Timeout(&_Network.CallOpts)
}

// UpdateCount is a paid mutator transaction binding the contract method 0x45516ee0.
//
// Solidity: function updateCount(_count uint256) returns()
func (_Network *NetworkTransactor) UpdateCount(opts *bind.TransactOpts, _count *big.Int) (*types.Transaction, error) {
	return _Network.contract.Transact(opts, "updateCount", _count)
}

// UpdateCount is a paid mutator transaction binding the contract method 0x45516ee0.
//
// Solidity: function updateCount(_count uint256) returns()
func (_Network *NetworkSession) UpdateCount(_count *big.Int) (*types.Transaction, error) {
	return _Network.Contract.UpdateCount(&_Network.TransactOpts, _count)
}

// UpdateCount is a paid mutator transaction binding the contract method 0x45516ee0.
//
// Solidity: function updateCount(_count uint256) returns()
func (_Network *NetworkTransactorSession) UpdateCount(_count *big.Int) (*types.Transaction, error) {
	return _Network.Contract.UpdateCount(&_Network.TransactOpts, _count)
}

// UpdateGap is a paid mutator transaction binding the contract method 0x150899cd.
//
// Solidity: function updateGap(_gap uint256) returns()
func (_Network *NetworkTransactor) UpdateGap(opts *bind.TransactOpts, _gap *big.Int) (*types.Transaction, error) {
	return _Network.contract.Transact(opts, "updateGap", _gap)
}

// UpdateGap is a paid mutator transaction binding the contract method 0x150899cd.
//
// Solidity: function updateGap(_gap uint256) returns()
func (_Network *NetworkSession) UpdateGap(_gap *big.Int) (*types.Transaction, error) {
	return _Network.Contract.UpdateGap(&_Network.TransactOpts, _gap)
}

// UpdateGap is a paid mutator transaction binding the contract method 0x150899cd.
//
// Solidity: function updateGap(_gap uint256) returns()
func (_Network *NetworkTransactorSession) UpdateGap(_gap *big.Int) (*types.Transaction, error) {
	return _Network.Contract.UpdateGap(&_Network.TransactOpts, _gap)
}

// UpdateHost is a paid mutator transaction binding the contract method 0x80bed418.
//
// Solidity: function updateHost(_host string) returns()
func (_Network *NetworkTransactor) UpdateHost(opts *bind.TransactOpts, _host string) (*types.Transaction, error) {
	return _Network.contract.Transact(opts, "updateHost", _host)
}

// UpdateHost is a paid mutator transaction binding the contract method 0x80bed418.
//
// Solidity: function updateHost(_host string) returns()
func (_Network *NetworkSession) UpdateHost(_host string) (*types.Transaction, error) {
	return _Network.Contract.UpdateHost(&_Network.TransactOpts, _host)
}

// UpdateHost is a paid mutator transaction binding the contract method 0x80bed418.
//
// Solidity: function updateHost(_host string) returns()
func (_Network *NetworkTransactorSession) UpdateHost(_host string) (*types.Transaction, error) {
	return _Network.Contract.UpdateHost(&_Network.TransactOpts, _host)
}

// UpdateOpen is a paid mutator transaction binding the contract method 0x316d155b.
//
// Solidity: function updateOpen(_open bool) returns()
func (_Network *NetworkTransactor) UpdateOpen(opts *bind.TransactOpts, _open bool) (*types.Transaction, error) {
	return _Network.contract.Transact(opts, "updateOpen", _open)
}

// UpdateOpen is a paid mutator transaction binding the contract method 0x316d155b.
//
// Solidity: function updateOpen(_open bool) returns()
func (_Network *NetworkSession) UpdateOpen(_open bool) (*types.Transaction, error) {
	return _Network.Contract.UpdateOpen(&_Network.TransactOpts, _open)
}

// UpdateOpen is a paid mutator transaction binding the contract method 0x316d155b.
//
// Solidity: function updateOpen(_open bool) returns()
func (_Network *NetworkTransactorSession) UpdateOpen(_open bool) (*types.Transaction, error) {
	return _Network.Contract.UpdateOpen(&_Network.TransactOpts, _open)
}

// UpdateTimeout is a paid mutator transaction binding the contract method 0xa330214e.
//
// Solidity: function updateTimeout(_timeout uint256) returns()
func (_Network *NetworkTransactor) UpdateTimeout(opts *bind.TransactOpts, _timeout *big.Int) (*types.Transaction, error) {
	return _Network.contract.Transact(opts, "updateTimeout", _timeout)
}

// UpdateTimeout is a paid mutator transaction binding the contract method 0xa330214e.
//
// Solidity: function updateTimeout(_timeout uint256) returns()
func (_Network *NetworkSession) UpdateTimeout(_timeout *big.Int) (*types.Transaction, error) {
	return _Network.Contract.UpdateTimeout(&_Network.TransactOpts, _timeout)
}

// UpdateTimeout is a paid mutator transaction binding the contract method 0xa330214e.
//
// Solidity: function updateTimeout(_timeout uint256) returns()
func (_Network *NetworkTransactorSession) UpdateTimeout(_timeout *big.Int) (*types.Transaction, error) {
	return _Network.Contract.UpdateTimeout(&_Network.TransactOpts, _timeout)
}

// NetworkUpdateConfigIterator is returned from FilterUpdateConfig and is used to iterate over the raw logs and unpacked data for UpdateConfig events raised by the Network contract.
type NetworkUpdateConfigIterator struct {
	Event *NetworkUpdateConfig // Event containing the contract specifics and raw log

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
func (it *NetworkUpdateConfigIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(NetworkUpdateConfig)
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
		it.Event = new(NetworkUpdateConfig)
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
func (it *NetworkUpdateConfigIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *NetworkUpdateConfigIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// NetworkUpdateConfig represents a UpdateConfig event raised by the Network contract.
type NetworkUpdateConfig struct {
	Config string
	Value  *big.Int
	Raw    types.Log // Blockchain specific contextual infos
}

// FilterUpdateConfig is a free log retrieval operation binding the contract event 0x6818c9181f3a8cb0f4d8178667c423a4c4ed24fc2410822be08e76ef50b2de1e.
//
// Solidity: e UpdateConfig(config string, value uint256)
func (_Network *NetworkFilterer) FilterUpdateConfig(opts *bind.FilterOpts) (*NetworkUpdateConfigIterator, error) {

	logs, sub, err := _Network.contract.FilterLogs(opts, "UpdateConfig")
	if err != nil {
		return nil, err
	}
	return &NetworkUpdateConfigIterator{contract: _Network.contract, event: "UpdateConfig", logs: logs, sub: sub}, nil
}

// WatchUpdateConfig is a free log subscription operation binding the contract event 0x6818c9181f3a8cb0f4d8178667c423a4c4ed24fc2410822be08e76ef50b2de1e.
//
// Solidity: e UpdateConfig(config string, value uint256)
func (_Network *NetworkFilterer) WatchUpdateConfig(opts *bind.WatchOpts, sink chan<- *NetworkUpdateConfig) (event.Subscription, error) {

	logs, sub, err := _Network.contract.WatchLogs(opts, "UpdateConfig")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(NetworkUpdateConfig)
				if err := _Network.contract.UnpackLog(event, "UpdateConfig", log); err != nil {
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

// NetworkUpdateHostIterator is returned from FilterUpdateHost and is used to iterate over the raw logs and unpacked data for UpdateHost events raised by the Network contract.
type NetworkUpdateHostIterator struct {
	Event *NetworkUpdateHost // Event containing the contract specifics and raw log

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
func (it *NetworkUpdateHostIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(NetworkUpdateHost)
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
		it.Event = new(NetworkUpdateHost)
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
func (it *NetworkUpdateHostIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *NetworkUpdateHostIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// NetworkUpdateHost represents a UpdateHost event raised by the Network contract.
type NetworkUpdateHost struct {
	Value string
	Raw   types.Log // Blockchain specific contextual infos
}

// FilterUpdateHost is a free log retrieval operation binding the contract event 0x958adb313e9ddd949012b779ce40fe9b2e593e682b7b256c58f100f1c3235c33.
//
// Solidity: e UpdateHost(value string)
func (_Network *NetworkFilterer) FilterUpdateHost(opts *bind.FilterOpts) (*NetworkUpdateHostIterator, error) {

	logs, sub, err := _Network.contract.FilterLogs(opts, "UpdateHost")
	if err != nil {
		return nil, err
	}
	return &NetworkUpdateHostIterator{contract: _Network.contract, event: "UpdateHost", logs: logs, sub: sub}, nil
}

// WatchUpdateHost is a free log subscription operation binding the contract event 0x958adb313e9ddd949012b779ce40fe9b2e593e682b7b256c58f100f1c3235c33.
//
// Solidity: e UpdateHost(value string)
func (_Network *NetworkFilterer) WatchUpdateHost(opts *bind.WatchOpts, sink chan<- *NetworkUpdateHost) (event.Subscription, error) {

	logs, sub, err := _Network.contract.WatchLogs(opts, "UpdateHost")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(NetworkUpdateHost)
				if err := _Network.contract.UnpackLog(event, "UpdateHost", log); err != nil {
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

// NetworkUpdateOpenIterator is returned from FilterUpdateOpen and is used to iterate over the raw logs and unpacked data for UpdateOpen events raised by the Network contract.
type NetworkUpdateOpenIterator struct {
	Event *NetworkUpdateOpen // Event containing the contract specifics and raw log

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
func (it *NetworkUpdateOpenIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(NetworkUpdateOpen)
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
		it.Event = new(NetworkUpdateOpen)
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
func (it *NetworkUpdateOpenIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *NetworkUpdateOpenIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// NetworkUpdateOpen represents a UpdateOpen event raised by the Network contract.
type NetworkUpdateOpen struct {
	Value bool
	Raw   types.Log // Blockchain specific contextual infos
}

// FilterUpdateOpen is a free log retrieval operation binding the contract event 0x3acb93048c9b0c52dcccea319343be25e3be345a3a087b9f3304ef4b7be66449.
//
// Solidity: e UpdateOpen(value bool)
func (_Network *NetworkFilterer) FilterUpdateOpen(opts *bind.FilterOpts) (*NetworkUpdateOpenIterator, error) {

	logs, sub, err := _Network.contract.FilterLogs(opts, "UpdateOpen")
	if err != nil {
		return nil, err
	}
	return &NetworkUpdateOpenIterator{contract: _Network.contract, event: "UpdateOpen", logs: logs, sub: sub}, nil
}

// WatchUpdateOpen is a free log subscription operation binding the contract event 0x3acb93048c9b0c52dcccea319343be25e3be345a3a087b9f3304ef4b7be66449.
//
// Solidity: e UpdateOpen(value bool)
func (_Network *NetworkFilterer) WatchUpdateOpen(opts *bind.WatchOpts, sink chan<- *NetworkUpdateOpen) (event.Subscription, error) {

	logs, sub, err := _Network.contract.WatchLogs(opts, "UpdateOpen")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(NetworkUpdateOpen)
				if err := _Network.contract.UnpackLog(event, "UpdateOpen", log); err != nil {
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
