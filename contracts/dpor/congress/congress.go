// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package congress

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

// CongressABI is the input ABI used to generate the binding from.
const CongressABI = "[{\"constant\":false,\"inputs\":[{\"name\":\"_period\",\"type\":\"uint256\"}],\"name\":\"setPeriod\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"isContract\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"threshold\",\"type\":\"uint256\"}],\"name\":\"setCongressThreshold\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"enabled\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"isInCongress\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"enableContract\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"refundAll\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"congressThreshold\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"version\",\"type\":\"uint256\"}],\"name\":\"joinCongress\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"}],\"name\":\"Participants\",\"outputs\":[{\"name\":\"lockedDeposit\",\"type\":\"uint256\"},{\"name\":\"lockedTime\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"version\",\"type\":\"uint256\"}],\"name\":\"setSupportedVersion\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"getCongressNum\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"getCongress\",\"outputs\":[{\"name\":\"\",\"type\":\"address[]\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"quitCongress\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"disableContract\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"supportedVersion\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"period\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"investor\",\"type\":\"address\"}],\"name\":\"refund\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"lockedDeposit\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"lockedTime\",\"type\":\"uint256\"}],\"name\":\"Join\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"}],\"name\":\"Quit\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"amount\",\"type\":\"uint256\"}],\"name\":\"ownerRefund\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"numOfInvestor\",\"type\":\"uint256\"}],\"name\":\"ownerRefundAll\",\"type\":\"event\"}]"

// CongressBin is the compiled bytecode used for deploying new contracts.
const CongressBin = `0x60806040526276a7006001908155692a5a058fc295ed00000060025560038190556007805460ff1916909117905534801561003957600080fd5b5060008054600160a060020a03191633179055610be88061005b6000396000f3006080604052600436106100fb5763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416630f3a9f658114610100578063162790551461011a57806322ab6c3d1461014f578063238dafe01461016757806327bd4ba71461017c578063367edd321461019d57806338e771ab146101b257806339fad16e146101c757806351f5f87a146101ee578063595aa13d146101f95780635f86d4ca146102335780636656b3751461024b5780636a96b9a51461026057806373a5c457146102c5578063894ba833146102da578063d5601e9f146102ef578063ef78d4fd14610304578063fa89401a14610319575b600080fd5b34801561010c57600080fd5b5061011860043561033a565b005b34801561012657600080fd5b5061013b600160a060020a0360043516610366565b604080519115158252519081900360200190f35b34801561015b57600080fd5b5061011860043561036e565b34801561017357600080fd5b5061013b6103a1565b34801561018857600080fd5b5061013b600160a060020a03600435166103aa565b3480156101a957600080fd5b506101186103c3565b3480156101be57600080fd5b506101186103e9565b3480156101d357600080fd5b506101dc61053a565b60408051918252519081900360200190f35b610118600435610540565b34801561020557600080fd5b5061021a600160a060020a03600435166106ca565b6040805192835260208301919091528051918290030190f35b34801561023f57600080fd5b506101186004356106e3565b34801561025757600080fd5b506101dc6106ff565b34801561026c57600080fd5b50610275610706565b60408051602080825283518183015283519192839290830191858101910280838360005b838110156102b1578181015183820152602001610299565b505050509050019250505060405180910390f35b3480156102d157600080fd5b50610118610717565b3480156102e657600080fd5b506101186107e8565b3480156102fb57600080fd5b506101dc61080b565b34801561031057600080fd5b506101dc610811565b34801561032557600080fd5b50610118600160a060020a0360043516610817565b600054600160a060020a0316331461035157600080fd5b6201518081111561036157600080fd5b600155565b6000903b1190565b600054600160a060020a0316331461038557600080fd5b692a5a058fc295ed00000081101561039c57600080fd5b600255565b60075460ff1681565b60006103bd60048363ffffffff61090516565b92915050565b600054600160a060020a031633146103da57600080fd5b6007805460ff19166001179055565b60008054819081908190600160a060020a0316331461040757600080fd5b6006549350600092505b838310156104f75760068054600090811061042857fe5b6000918252602080832090910154600160a060020a0316808352600890915260408083205490519194509250839183156108fc02918491818181858888f1935050505015801561047c573d6000803e3d6000fd5b50600160a060020a0382166000908152600860205260408120556104a760048363ffffffff61092416565b5060408051600160a060020a03841681526020810183905281517f3914ba80eb00486e7a58b91fb4795283df0c5b507eea9cf7c77cce26cc70d25c929181900390910190a1600190920191610411565b6006541561050157fe5b6040805185815290517fb65ebb6b17695b3a5612c7a0f6f60e649c02ba24b36b546b8d037e98215fdb8d9181900360200190a150505050565b60025481565b60075460ff16151561055157600080fd5b60035481101561056057600080fd5b61056933610366565b156105fb57604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602a60248201527f706c65617365206e6f742075736520636f6e74726163742063616c6c2074686960448201527f732066756e6374696f6e00000000000000000000000000000000000000000000606482015290519081900360840190fd5b61060c60043363ffffffff61090516565b1561061657600080fd5b60025434101561062557600080fd5b33600090815260086020526040902054610645903463ffffffff610a6a16565b336000818152600860205260409020918255426001909201919091556106739060049063ffffffff610a8016565b5033600081815260086020908152604091829020805460019091015483519485529184015282820152517fbca387acb0ba7d06e329c4372885bb664f19a98153ccf3e74e56c136bf0e88c49181900360600190a150565b6008602052600090815260409020805460019091015482565b600054600160a060020a031633146106fa57600080fd5b600355565b6006545b90565b60606107126004610b0f565b905090565b61072860043363ffffffff61090516565b151561073357600080fd5b6001805433600090815260086020526040902090910154429101111561075857600080fd5b3360008181526008602052604080822054905181156108fc0292818181858888f1935050505015801561078f573d6000803e3d6000fd5b50336000818152600860205260408120556107b29060049063ffffffff61092416565b506040805133815290517f03c628a4c93ed860bebcdb8d45ac895f4e4b31b42deea215750fdac0403d66dd9181900360200190a1565b600054600160a060020a031633146107ff57600080fd5b6007805460ff19169055565b60035481565b60015481565b60008054600160a060020a0316331461082f57600080fd5b61084060048363ffffffff61090516565b151561084b57600080fd5b50600160a060020a03811660008181526008602052604080822054905190929183156108fc02918491818181858888f19350505050158015610891573d6000803e3d6000fd5b50600160a060020a0382166000908152600860205260408120556108bc60048363ffffffff61092416565b5060408051600160a060020a03841681526020810183905281517f3914ba80eb00486e7a58b91fb4795283df0c5b507eea9cf7c77cce26cc70d25c929181900390910190a15050565b600160a060020a03166000908152602091909152604090205460ff1690565b600160a060020a03811660009081526020839052604081205481908190819060ff1615156109555760009350610a61565b600160a060020a038516600090815260208781526040808320805460ff1916905560028901805460018b019093529220549094509250600019840184811061099957fe5b600091825260209091200154600287018054600160a060020a0390921692508291849081106109c457fe5b6000918252602080832091909101805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a03948516179055918316815260018801909152604090208290556002860180546000198501908110610a2057fe5b6000918252602090912001805473ffffffffffffffffffffffffffffffffffffffff1916905560028601805490610a5b906000198301610b75565b50600193505b50505092915050565b600082820183811015610a7957fe5b9392505050565b600160a060020a03811660009081526020839052604081205460ff1615610aa9575060006103bd565b50600160a060020a0316600081815260208381526040808320805460ff19166001908117909155600286018054968201845291842086905585810182559083529120909201805473ffffffffffffffffffffffffffffffffffffffff1916909117905590565b606081600201805480602002602001604051908101604052809291908181526020018280548015610b6957602002820191906000526020600020905b8154600160a060020a03168152600190910190602001808311610b4b575b50505050509050919050565b815481835581811115610b9957600083815260209020610b99918101908301610b9e565b505050565b61070391905b80821115610bb85760008155600101610ba4565b50905600a165627a7a72305820a9f9d3ac219ec6ce3b24845fac5517ccd5313ee5d15b0581dfd38d69ef8a50990029`

// DeployCongress deploys a new cpchain contract, binding an instance of Congress to it.
func DeployCongress(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *Congress, error) {
	parsed, err := abi.JSON(strings.NewReader(CongressABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(CongressBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &Congress{CongressCaller: CongressCaller{contract: contract}, CongressTransactor: CongressTransactor{contract: contract}, CongressFilterer: CongressFilterer{contract: contract}}, nil
}

// Congress is an auto generated Go binding around an cpchain contract.
type Congress struct {
	CongressCaller     // Read-only binding to the contract
	CongressTransactor // Write-only binding to the contract
	CongressFilterer   // Log filterer for contract events
}

// CongressCaller is an auto generated read-only Go binding around an cpchain contract.
type CongressCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// CongressTransactor is an auto generated write-only Go binding around an cpchain contract.
type CongressTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// CongressFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type CongressFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// CongressSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type CongressSession struct {
	Contract     *Congress         // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// CongressCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type CongressCallerSession struct {
	Contract *CongressCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts   // Call options to use throughout this session
}

// CongressTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type CongressTransactorSession struct {
	Contract     *CongressTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts   // Transaction auth options to use throughout this session
}

// CongressRaw is an auto generated low-level Go binding around an cpchain contract.
type CongressRaw struct {
	Contract *Congress // Generic contract binding to access the raw methods on
}

// CongressCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type CongressCallerRaw struct {
	Contract *CongressCaller // Generic read-only contract binding to access the raw methods on
}

// CongressTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type CongressTransactorRaw struct {
	Contract *CongressTransactor // Generic write-only contract binding to access the raw methods on
}

// NewCongress creates a new instance of Congress, bound to a specific deployed contract.
func NewCongress(address common.Address, backend bind.ContractBackend) (*Congress, error) {
	contract, err := bindCongress(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &Congress{CongressCaller: CongressCaller{contract: contract}, CongressTransactor: CongressTransactor{contract: contract}, CongressFilterer: CongressFilterer{contract: contract}}, nil
}

// NewCongressCaller creates a new read-only instance of Congress, bound to a specific deployed contract.
func NewCongressCaller(address common.Address, caller bind.ContractCaller) (*CongressCaller, error) {
	contract, err := bindCongress(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &CongressCaller{contract: contract}, nil
}

// NewCongressTransactor creates a new write-only instance of Congress, bound to a specific deployed contract.
func NewCongressTransactor(address common.Address, transactor bind.ContractTransactor) (*CongressTransactor, error) {
	contract, err := bindCongress(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &CongressTransactor{contract: contract}, nil
}

// NewCongressFilterer creates a new log filterer instance of Congress, bound to a specific deployed contract.
func NewCongressFilterer(address common.Address, filterer bind.ContractFilterer) (*CongressFilterer, error) {
	contract, err := bindCongress(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &CongressFilterer{contract: contract}, nil
}

// bindCongress binds a generic wrapper to an already deployed contract.
func bindCongress(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(CongressABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Congress *CongressRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Congress.Contract.CongressCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Congress *CongressRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Congress.Contract.CongressTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Congress *CongressRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Congress.Contract.CongressTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Congress *CongressCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Congress.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Congress *CongressTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Congress.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Congress *CongressTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Congress.Contract.contract.Transact(opts, method, params...)
}

// Participants is a free data retrieval call binding the contract method 0x595aa13d.
//
// Solidity: function Participants( address) constant returns(lockedDeposit uint256, lockedTime uint256)
func (_Congress *CongressCaller) Participants(opts *bind.CallOpts, arg0 common.Address) (struct {
	LockedDeposit *big.Int
	LockedTime    *big.Int
}, error) {
	ret := new(struct {
		LockedDeposit *big.Int
		LockedTime    *big.Int
	})
	out := ret
	err := _Congress.contract.Call(opts, out, "Participants", arg0)
	return *ret, err
}

// Participants is a free data retrieval call binding the contract method 0x595aa13d.
//
// Solidity: function Participants( address) constant returns(lockedDeposit uint256, lockedTime uint256)
func (_Congress *CongressSession) Participants(arg0 common.Address) (struct {
	LockedDeposit *big.Int
	LockedTime    *big.Int
}, error) {
	return _Congress.Contract.Participants(&_Congress.CallOpts, arg0)
}

// Participants is a free data retrieval call binding the contract method 0x595aa13d.
//
// Solidity: function Participants( address) constant returns(lockedDeposit uint256, lockedTime uint256)
func (_Congress *CongressCallerSession) Participants(arg0 common.Address) (struct {
	LockedDeposit *big.Int
	LockedTime    *big.Int
}, error) {
	return _Congress.Contract.Participants(&_Congress.CallOpts, arg0)
}

// CongressThreshold is a free data retrieval call binding the contract method 0x39fad16e.
//
// Solidity: function congressThreshold() constant returns(uint256)
func (_Congress *CongressCaller) CongressThreshold(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Congress.contract.Call(opts, out, "congressThreshold")
	return *ret0, err
}

// CongressThreshold is a free data retrieval call binding the contract method 0x39fad16e.
//
// Solidity: function congressThreshold() constant returns(uint256)
func (_Congress *CongressSession) CongressThreshold() (*big.Int, error) {
	return _Congress.Contract.CongressThreshold(&_Congress.CallOpts)
}

// CongressThreshold is a free data retrieval call binding the contract method 0x39fad16e.
//
// Solidity: function congressThreshold() constant returns(uint256)
func (_Congress *CongressCallerSession) CongressThreshold() (*big.Int, error) {
	return _Congress.Contract.CongressThreshold(&_Congress.CallOpts)
}

// Enabled is a free data retrieval call binding the contract method 0x238dafe0.
//
// Solidity: function enabled() constant returns(bool)
func (_Congress *CongressCaller) Enabled(opts *bind.CallOpts) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Congress.contract.Call(opts, out, "enabled")
	return *ret0, err
}

// Enabled is a free data retrieval call binding the contract method 0x238dafe0.
//
// Solidity: function enabled() constant returns(bool)
func (_Congress *CongressSession) Enabled() (bool, error) {
	return _Congress.Contract.Enabled(&_Congress.CallOpts)
}

// Enabled is a free data retrieval call binding the contract method 0x238dafe0.
//
// Solidity: function enabled() constant returns(bool)
func (_Congress *CongressCallerSession) Enabled() (bool, error) {
	return _Congress.Contract.Enabled(&_Congress.CallOpts)
}

// GetCongress is a free data retrieval call binding the contract method 0x6a96b9a5.
//
// Solidity: function getCongress() constant returns(address[])
func (_Congress *CongressCaller) GetCongress(opts *bind.CallOpts) ([]common.Address, error) {
	var (
		ret0 = new([]common.Address)
	)
	out := ret0
	err := _Congress.contract.Call(opts, out, "getCongress")
	return *ret0, err
}

// GetCongress is a free data retrieval call binding the contract method 0x6a96b9a5.
//
// Solidity: function getCongress() constant returns(address[])
func (_Congress *CongressSession) GetCongress() ([]common.Address, error) {
	return _Congress.Contract.GetCongress(&_Congress.CallOpts)
}

// GetCongress is a free data retrieval call binding the contract method 0x6a96b9a5.
//
// Solidity: function getCongress() constant returns(address[])
func (_Congress *CongressCallerSession) GetCongress() ([]common.Address, error) {
	return _Congress.Contract.GetCongress(&_Congress.CallOpts)
}

// GetCongressNum is a free data retrieval call binding the contract method 0x6656b375.
//
// Solidity: function getCongressNum() constant returns(uint256)
func (_Congress *CongressCaller) GetCongressNum(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Congress.contract.Call(opts, out, "getCongressNum")
	return *ret0, err
}

// GetCongressNum is a free data retrieval call binding the contract method 0x6656b375.
//
// Solidity: function getCongressNum() constant returns(uint256)
func (_Congress *CongressSession) GetCongressNum() (*big.Int, error) {
	return _Congress.Contract.GetCongressNum(&_Congress.CallOpts)
}

// GetCongressNum is a free data retrieval call binding the contract method 0x6656b375.
//
// Solidity: function getCongressNum() constant returns(uint256)
func (_Congress *CongressCallerSession) GetCongressNum() (*big.Int, error) {
	return _Congress.Contract.GetCongressNum(&_Congress.CallOpts)
}

// IsContract is a free data retrieval call binding the contract method 0x16279055.
//
// Solidity: function isContract(addr address) constant returns(bool)
func (_Congress *CongressCaller) IsContract(opts *bind.CallOpts, addr common.Address) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Congress.contract.Call(opts, out, "isContract", addr)
	return *ret0, err
}

// IsContract is a free data retrieval call binding the contract method 0x16279055.
//
// Solidity: function isContract(addr address) constant returns(bool)
func (_Congress *CongressSession) IsContract(addr common.Address) (bool, error) {
	return _Congress.Contract.IsContract(&_Congress.CallOpts, addr)
}

// IsContract is a free data retrieval call binding the contract method 0x16279055.
//
// Solidity: function isContract(addr address) constant returns(bool)
func (_Congress *CongressCallerSession) IsContract(addr common.Address) (bool, error) {
	return _Congress.Contract.IsContract(&_Congress.CallOpts, addr)
}

// IsInCongress is a free data retrieval call binding the contract method 0x27bd4ba7.
//
// Solidity: function isInCongress(addr address) constant returns(bool)
func (_Congress *CongressCaller) IsInCongress(opts *bind.CallOpts, addr common.Address) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Congress.contract.Call(opts, out, "isInCongress", addr)
	return *ret0, err
}

// IsInCongress is a free data retrieval call binding the contract method 0x27bd4ba7.
//
// Solidity: function isInCongress(addr address) constant returns(bool)
func (_Congress *CongressSession) IsInCongress(addr common.Address) (bool, error) {
	return _Congress.Contract.IsInCongress(&_Congress.CallOpts, addr)
}

// IsInCongress is a free data retrieval call binding the contract method 0x27bd4ba7.
//
// Solidity: function isInCongress(addr address) constant returns(bool)
func (_Congress *CongressCallerSession) IsInCongress(addr common.Address) (bool, error) {
	return _Congress.Contract.IsInCongress(&_Congress.CallOpts, addr)
}

// Period is a free data retrieval call binding the contract method 0xef78d4fd.
//
// Solidity: function period() constant returns(uint256)
func (_Congress *CongressCaller) Period(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Congress.contract.Call(opts, out, "period")
	return *ret0, err
}

// Period is a free data retrieval call binding the contract method 0xef78d4fd.
//
// Solidity: function period() constant returns(uint256)
func (_Congress *CongressSession) Period() (*big.Int, error) {
	return _Congress.Contract.Period(&_Congress.CallOpts)
}

// Period is a free data retrieval call binding the contract method 0xef78d4fd.
//
// Solidity: function period() constant returns(uint256)
func (_Congress *CongressCallerSession) Period() (*big.Int, error) {
	return _Congress.Contract.Period(&_Congress.CallOpts)
}

// SupportedVersion is a free data retrieval call binding the contract method 0xd5601e9f.
//
// Solidity: function supportedVersion() constant returns(uint256)
func (_Congress *CongressCaller) SupportedVersion(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Congress.contract.Call(opts, out, "supportedVersion")
	return *ret0, err
}

// SupportedVersion is a free data retrieval call binding the contract method 0xd5601e9f.
//
// Solidity: function supportedVersion() constant returns(uint256)
func (_Congress *CongressSession) SupportedVersion() (*big.Int, error) {
	return _Congress.Contract.SupportedVersion(&_Congress.CallOpts)
}

// SupportedVersion is a free data retrieval call binding the contract method 0xd5601e9f.
//
// Solidity: function supportedVersion() constant returns(uint256)
func (_Congress *CongressCallerSession) SupportedVersion() (*big.Int, error) {
	return _Congress.Contract.SupportedVersion(&_Congress.CallOpts)
}

// DisableContract is a paid mutator transaction binding the contract method 0x894ba833.
//
// Solidity: function disableContract() returns()
func (_Congress *CongressTransactor) DisableContract(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Congress.contract.Transact(opts, "disableContract")
}

// DisableContract is a paid mutator transaction binding the contract method 0x894ba833.
//
// Solidity: function disableContract() returns()
func (_Congress *CongressSession) DisableContract() (*types.Transaction, error) {
	return _Congress.Contract.DisableContract(&_Congress.TransactOpts)
}

// DisableContract is a paid mutator transaction binding the contract method 0x894ba833.
//
// Solidity: function disableContract() returns()
func (_Congress *CongressTransactorSession) DisableContract() (*types.Transaction, error) {
	return _Congress.Contract.DisableContract(&_Congress.TransactOpts)
}

// EnableContract is a paid mutator transaction binding the contract method 0x367edd32.
//
// Solidity: function enableContract() returns()
func (_Congress *CongressTransactor) EnableContract(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Congress.contract.Transact(opts, "enableContract")
}

// EnableContract is a paid mutator transaction binding the contract method 0x367edd32.
//
// Solidity: function enableContract() returns()
func (_Congress *CongressSession) EnableContract() (*types.Transaction, error) {
	return _Congress.Contract.EnableContract(&_Congress.TransactOpts)
}

// EnableContract is a paid mutator transaction binding the contract method 0x367edd32.
//
// Solidity: function enableContract() returns()
func (_Congress *CongressTransactorSession) EnableContract() (*types.Transaction, error) {
	return _Congress.Contract.EnableContract(&_Congress.TransactOpts)
}

// JoinCongress is a paid mutator transaction binding the contract method 0x51f5f87a.
//
// Solidity: function joinCongress(version uint256) returns()
func (_Congress *CongressTransactor) JoinCongress(opts *bind.TransactOpts, version *big.Int) (*types.Transaction, error) {
	return _Congress.contract.Transact(opts, "joinCongress", version)
}

// JoinCongress is a paid mutator transaction binding the contract method 0x51f5f87a.
//
// Solidity: function joinCongress(version uint256) returns()
func (_Congress *CongressSession) JoinCongress(version *big.Int) (*types.Transaction, error) {
	return _Congress.Contract.JoinCongress(&_Congress.TransactOpts, version)
}

// JoinCongress is a paid mutator transaction binding the contract method 0x51f5f87a.
//
// Solidity: function joinCongress(version uint256) returns()
func (_Congress *CongressTransactorSession) JoinCongress(version *big.Int) (*types.Transaction, error) {
	return _Congress.Contract.JoinCongress(&_Congress.TransactOpts, version)
}

// QuitCongress is a paid mutator transaction binding the contract method 0x73a5c457.
//
// Solidity: function quitCongress() returns()
func (_Congress *CongressTransactor) QuitCongress(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Congress.contract.Transact(opts, "quitCongress")
}

// QuitCongress is a paid mutator transaction binding the contract method 0x73a5c457.
//
// Solidity: function quitCongress() returns()
func (_Congress *CongressSession) QuitCongress() (*types.Transaction, error) {
	return _Congress.Contract.QuitCongress(&_Congress.TransactOpts)
}

// QuitCongress is a paid mutator transaction binding the contract method 0x73a5c457.
//
// Solidity: function quitCongress() returns()
func (_Congress *CongressTransactorSession) QuitCongress() (*types.Transaction, error) {
	return _Congress.Contract.QuitCongress(&_Congress.TransactOpts)
}

// Refund is a paid mutator transaction binding the contract method 0xfa89401a.
//
// Solidity: function refund(investor address) returns()
func (_Congress *CongressTransactor) Refund(opts *bind.TransactOpts, investor common.Address) (*types.Transaction, error) {
	return _Congress.contract.Transact(opts, "refund", investor)
}

// Refund is a paid mutator transaction binding the contract method 0xfa89401a.
//
// Solidity: function refund(investor address) returns()
func (_Congress *CongressSession) Refund(investor common.Address) (*types.Transaction, error) {
	return _Congress.Contract.Refund(&_Congress.TransactOpts, investor)
}

// Refund is a paid mutator transaction binding the contract method 0xfa89401a.
//
// Solidity: function refund(investor address) returns()
func (_Congress *CongressTransactorSession) Refund(investor common.Address) (*types.Transaction, error) {
	return _Congress.Contract.Refund(&_Congress.TransactOpts, investor)
}

// RefundAll is a paid mutator transaction binding the contract method 0x38e771ab.
//
// Solidity: function refundAll() returns()
func (_Congress *CongressTransactor) RefundAll(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Congress.contract.Transact(opts, "refundAll")
}

// RefundAll is a paid mutator transaction binding the contract method 0x38e771ab.
//
// Solidity: function refundAll() returns()
func (_Congress *CongressSession) RefundAll() (*types.Transaction, error) {
	return _Congress.Contract.RefundAll(&_Congress.TransactOpts)
}

// RefundAll is a paid mutator transaction binding the contract method 0x38e771ab.
//
// Solidity: function refundAll() returns()
func (_Congress *CongressTransactorSession) RefundAll() (*types.Transaction, error) {
	return _Congress.Contract.RefundAll(&_Congress.TransactOpts)
}

// SetCongressThreshold is a paid mutator transaction binding the contract method 0x22ab6c3d.
//
// Solidity: function setCongressThreshold(threshold uint256) returns()
func (_Congress *CongressTransactor) SetCongressThreshold(opts *bind.TransactOpts, threshold *big.Int) (*types.Transaction, error) {
	return _Congress.contract.Transact(opts, "setCongressThreshold", threshold)
}

// SetCongressThreshold is a paid mutator transaction binding the contract method 0x22ab6c3d.
//
// Solidity: function setCongressThreshold(threshold uint256) returns()
func (_Congress *CongressSession) SetCongressThreshold(threshold *big.Int) (*types.Transaction, error) {
	return _Congress.Contract.SetCongressThreshold(&_Congress.TransactOpts, threshold)
}

// SetCongressThreshold is a paid mutator transaction binding the contract method 0x22ab6c3d.
//
// Solidity: function setCongressThreshold(threshold uint256) returns()
func (_Congress *CongressTransactorSession) SetCongressThreshold(threshold *big.Int) (*types.Transaction, error) {
	return _Congress.Contract.SetCongressThreshold(&_Congress.TransactOpts, threshold)
}

// SetPeriod is a paid mutator transaction binding the contract method 0x0f3a9f65.
//
// Solidity: function setPeriod(_period uint256) returns()
func (_Congress *CongressTransactor) SetPeriod(opts *bind.TransactOpts, _period *big.Int) (*types.Transaction, error) {
	return _Congress.contract.Transact(opts, "setPeriod", _period)
}

// SetPeriod is a paid mutator transaction binding the contract method 0x0f3a9f65.
//
// Solidity: function setPeriod(_period uint256) returns()
func (_Congress *CongressSession) SetPeriod(_period *big.Int) (*types.Transaction, error) {
	return _Congress.Contract.SetPeriod(&_Congress.TransactOpts, _period)
}

// SetPeriod is a paid mutator transaction binding the contract method 0x0f3a9f65.
//
// Solidity: function setPeriod(_period uint256) returns()
func (_Congress *CongressTransactorSession) SetPeriod(_period *big.Int) (*types.Transaction, error) {
	return _Congress.Contract.SetPeriod(&_Congress.TransactOpts, _period)
}

// SetSupportedVersion is a paid mutator transaction binding the contract method 0x5f86d4ca.
//
// Solidity: function setSupportedVersion(version uint256) returns()
func (_Congress *CongressTransactor) SetSupportedVersion(opts *bind.TransactOpts, version *big.Int) (*types.Transaction, error) {
	return _Congress.contract.Transact(opts, "setSupportedVersion", version)
}

// SetSupportedVersion is a paid mutator transaction binding the contract method 0x5f86d4ca.
//
// Solidity: function setSupportedVersion(version uint256) returns()
func (_Congress *CongressSession) SetSupportedVersion(version *big.Int) (*types.Transaction, error) {
	return _Congress.Contract.SetSupportedVersion(&_Congress.TransactOpts, version)
}

// SetSupportedVersion is a paid mutator transaction binding the contract method 0x5f86d4ca.
//
// Solidity: function setSupportedVersion(version uint256) returns()
func (_Congress *CongressTransactorSession) SetSupportedVersion(version *big.Int) (*types.Transaction, error) {
	return _Congress.Contract.SetSupportedVersion(&_Congress.TransactOpts, version)
}

// CongressJoinIterator is returned from FilterJoin and is used to iterate over the raw logs and unpacked data for Join events raised by the Congress contract.
type CongressJoinIterator struct {
	Event *CongressJoin // Event containing the contract specifics and raw log

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
func (it *CongressJoinIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(CongressJoin)
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
		it.Event = new(CongressJoin)
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
func (it *CongressJoinIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *CongressJoinIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// CongressJoin represents a Join event raised by the Congress contract.
type CongressJoin struct {
	Who           common.Address
	LockedDeposit *big.Int
	LockedTime    *big.Int
	Raw           types.Log // Blockchain specific contextual infos
}

// FilterJoin is a free log retrieval operation binding the contract event 0xbca387acb0ba7d06e329c4372885bb664f19a98153ccf3e74e56c136bf0e88c4.
//
// Solidity: e Join(who address, lockedDeposit uint256, lockedTime uint256)
func (_Congress *CongressFilterer) FilterJoin(opts *bind.FilterOpts) (*CongressJoinIterator, error) {

	logs, sub, err := _Congress.contract.FilterLogs(opts, "Join")
	if err != nil {
		return nil, err
	}
	return &CongressJoinIterator{contract: _Congress.contract, event: "Join", logs: logs, sub: sub}, nil
}

// WatchJoin is a free log subscription operation binding the contract event 0xbca387acb0ba7d06e329c4372885bb664f19a98153ccf3e74e56c136bf0e88c4.
//
// Solidity: e Join(who address, lockedDeposit uint256, lockedTime uint256)
func (_Congress *CongressFilterer) WatchJoin(opts *bind.WatchOpts, sink chan<- *CongressJoin) (event.Subscription, error) {

	logs, sub, err := _Congress.contract.WatchLogs(opts, "Join")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(CongressJoin)
				if err := _Congress.contract.UnpackLog(event, "Join", log); err != nil {
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

// CongressQuitIterator is returned from FilterQuit and is used to iterate over the raw logs and unpacked data for Quit events raised by the Congress contract.
type CongressQuitIterator struct {
	Event *CongressQuit // Event containing the contract specifics and raw log

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
func (it *CongressQuitIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(CongressQuit)
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
		it.Event = new(CongressQuit)
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
func (it *CongressQuitIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *CongressQuitIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// CongressQuit represents a Quit event raised by the Congress contract.
type CongressQuit struct {
	Who common.Address
	Raw types.Log // Blockchain specific contextual infos
}

// FilterQuit is a free log retrieval operation binding the contract event 0x03c628a4c93ed860bebcdb8d45ac895f4e4b31b42deea215750fdac0403d66dd.
//
// Solidity: e Quit(who address)
func (_Congress *CongressFilterer) FilterQuit(opts *bind.FilterOpts) (*CongressQuitIterator, error) {

	logs, sub, err := _Congress.contract.FilterLogs(opts, "Quit")
	if err != nil {
		return nil, err
	}
	return &CongressQuitIterator{contract: _Congress.contract, event: "Quit", logs: logs, sub: sub}, nil
}

// WatchQuit is a free log subscription operation binding the contract event 0x03c628a4c93ed860bebcdb8d45ac895f4e4b31b42deea215750fdac0403d66dd.
//
// Solidity: e Quit(who address)
func (_Congress *CongressFilterer) WatchQuit(opts *bind.WatchOpts, sink chan<- *CongressQuit) (event.Subscription, error) {

	logs, sub, err := _Congress.contract.WatchLogs(opts, "Quit")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(CongressQuit)
				if err := _Congress.contract.UnpackLog(event, "Quit", log); err != nil {
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

// CongressOwnerRefundIterator is returned from FilterOwnerRefund and is used to iterate over the raw logs and unpacked data for OwnerRefund events raised by the Congress contract.
type CongressOwnerRefundIterator struct {
	Event *CongressOwnerRefund // Event containing the contract specifics and raw log

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
func (it *CongressOwnerRefundIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(CongressOwnerRefund)
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
		it.Event = new(CongressOwnerRefund)
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
func (it *CongressOwnerRefundIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *CongressOwnerRefundIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// CongressOwnerRefund represents a OwnerRefund event raised by the Congress contract.
type CongressOwnerRefund struct {
	Who    common.Address
	Amount *big.Int
	Raw    types.Log // Blockchain specific contextual infos
}

// FilterOwnerRefund is a free log retrieval operation binding the contract event 0x3914ba80eb00486e7a58b91fb4795283df0c5b507eea9cf7c77cce26cc70d25c.
//
// Solidity: e ownerRefund(who address, amount uint256)
func (_Congress *CongressFilterer) FilterOwnerRefund(opts *bind.FilterOpts) (*CongressOwnerRefundIterator, error) {

	logs, sub, err := _Congress.contract.FilterLogs(opts, "ownerRefund")
	if err != nil {
		return nil, err
	}
	return &CongressOwnerRefundIterator{contract: _Congress.contract, event: "ownerRefund", logs: logs, sub: sub}, nil
}

// WatchOwnerRefund is a free log subscription operation binding the contract event 0x3914ba80eb00486e7a58b91fb4795283df0c5b507eea9cf7c77cce26cc70d25c.
//
// Solidity: e ownerRefund(who address, amount uint256)
func (_Congress *CongressFilterer) WatchOwnerRefund(opts *bind.WatchOpts, sink chan<- *CongressOwnerRefund) (event.Subscription, error) {

	logs, sub, err := _Congress.contract.WatchLogs(opts, "ownerRefund")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(CongressOwnerRefund)
				if err := _Congress.contract.UnpackLog(event, "ownerRefund", log); err != nil {
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

// CongressOwnerRefundAllIterator is returned from FilterOwnerRefundAll and is used to iterate over the raw logs and unpacked data for OwnerRefundAll events raised by the Congress contract.
type CongressOwnerRefundAllIterator struct {
	Event *CongressOwnerRefundAll // Event containing the contract specifics and raw log

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
func (it *CongressOwnerRefundAllIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(CongressOwnerRefundAll)
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
		it.Event = new(CongressOwnerRefundAll)
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
func (it *CongressOwnerRefundAllIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *CongressOwnerRefundAllIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// CongressOwnerRefundAll represents a OwnerRefundAll event raised by the Congress contract.
type CongressOwnerRefundAll struct {
	NumOfInvestor *big.Int
	Raw           types.Log // Blockchain specific contextual infos
}

// FilterOwnerRefundAll is a free log retrieval operation binding the contract event 0xb65ebb6b17695b3a5612c7a0f6f60e649c02ba24b36b546b8d037e98215fdb8d.
//
// Solidity: e ownerRefundAll(numOfInvestor uint256)
func (_Congress *CongressFilterer) FilterOwnerRefundAll(opts *bind.FilterOpts) (*CongressOwnerRefundAllIterator, error) {

	logs, sub, err := _Congress.contract.FilterLogs(opts, "ownerRefundAll")
	if err != nil {
		return nil, err
	}
	return &CongressOwnerRefundAllIterator{contract: _Congress.contract, event: "ownerRefundAll", logs: logs, sub: sub}, nil
}

// WatchOwnerRefundAll is a free log subscription operation binding the contract event 0xb65ebb6b17695b3a5612c7a0f6f60e649c02ba24b36b546b8d037e98215fdb8d.
//
// Solidity: e ownerRefundAll(numOfInvestor uint256)
func (_Congress *CongressFilterer) WatchOwnerRefundAll(opts *bind.WatchOpts, sink chan<- *CongressOwnerRefundAll) (event.Subscription, error) {

	logs, sub, err := _Congress.contract.WatchLogs(opts, "ownerRefundAll")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(CongressOwnerRefundAll)
				if err := _Congress.contract.UnpackLog(event, "ownerRefundAll", log); err != nil {
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

// SafeMathABI is the input ABI used to generate the binding from.
const SafeMathABI = "[]"

// SafeMathBin is the compiled bytecode used for deploying new contracts.
const SafeMathBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a72305820796e4a167614a99e404ec89ca342beb00635fcd4c74d1244e449272f3ba688dc0029`

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
const SetBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a72305820be640a71d4bccffb1161bb1ff89d2b379fdf5a1d004bbe8f4a024ac2f404af8a0029`

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
