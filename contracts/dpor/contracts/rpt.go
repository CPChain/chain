// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package dpor

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

// PrimitiveContractsInterfaceABI is the input ABI used to generate the binding from.
const PrimitiveContractsInterfaceABI = "[]"

// PrimitiveContractsInterfaceBin is the compiled bytecode used for deploying new contracts.
const PrimitiveContractsInterfaceBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a72305820c10985a8ec8cbb1362c9a1db0859203a02b216e46d6d4775c1f26baa4c969c090029`

// DeployPrimitiveContractsInterface deploys a new cpchain contract, binding an instance of PrimitiveContractsInterface to it.
func DeployPrimitiveContractsInterface(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *PrimitiveContractsInterface, error) {
	parsed, err := abi.JSON(strings.NewReader(PrimitiveContractsInterfaceABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(PrimitiveContractsInterfaceBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &PrimitiveContractsInterface{PrimitiveContractsInterfaceCaller: PrimitiveContractsInterfaceCaller{contract: contract}, PrimitiveContractsInterfaceTransactor: PrimitiveContractsInterfaceTransactor{contract: contract}, PrimitiveContractsInterfaceFilterer: PrimitiveContractsInterfaceFilterer{contract: contract}}, nil
}

// PrimitiveContractsInterface is an auto generated Go binding around an cpchain contract.
type PrimitiveContractsInterface struct {
	PrimitiveContractsInterfaceCaller     // Read-only binding to the contract
	PrimitiveContractsInterfaceTransactor // Write-only binding to the contract
	PrimitiveContractsInterfaceFilterer   // Log filterer for contract events
}

// PrimitiveContractsInterfaceCaller is an auto generated read-only Go binding around an cpchain contract.
type PrimitiveContractsInterfaceCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// PrimitiveContractsInterfaceTransactor is an auto generated write-only Go binding around an cpchain contract.
type PrimitiveContractsInterfaceTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// PrimitiveContractsInterfaceFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type PrimitiveContractsInterfaceFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// PrimitiveContractsInterfaceSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type PrimitiveContractsInterfaceSession struct {
	Contract     *PrimitiveContractsInterface // Generic contract binding to set the session for
	CallOpts     bind.CallOpts                // Call options to use throughout this session
	TransactOpts bind.TransactOpts            // Transaction auth options to use throughout this session
}

// PrimitiveContractsInterfaceCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type PrimitiveContractsInterfaceCallerSession struct {
	Contract *PrimitiveContractsInterfaceCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts                      // Call options to use throughout this session
}

// PrimitiveContractsInterfaceTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type PrimitiveContractsInterfaceTransactorSession struct {
	Contract     *PrimitiveContractsInterfaceTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts                      // Transaction auth options to use throughout this session
}

// PrimitiveContractsInterfaceRaw is an auto generated low-level Go binding around an cpchain contract.
type PrimitiveContractsInterfaceRaw struct {
	Contract *PrimitiveContractsInterface // Generic contract binding to access the raw methods on
}

// PrimitiveContractsInterfaceCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type PrimitiveContractsInterfaceCallerRaw struct {
	Contract *PrimitiveContractsInterfaceCaller // Generic read-only contract binding to access the raw methods on
}

// PrimitiveContractsInterfaceTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type PrimitiveContractsInterfaceTransactorRaw struct {
	Contract *PrimitiveContractsInterfaceTransactor // Generic write-only contract binding to access the raw methods on
}

// NewPrimitiveContractsInterface creates a new instance of PrimitiveContractsInterface, bound to a specific deployed contract.
func NewPrimitiveContractsInterface(address common.Address, backend bind.ContractBackend) (*PrimitiveContractsInterface, error) {
	contract, err := bindPrimitiveContractsInterface(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &PrimitiveContractsInterface{PrimitiveContractsInterfaceCaller: PrimitiveContractsInterfaceCaller{contract: contract}, PrimitiveContractsInterfaceTransactor: PrimitiveContractsInterfaceTransactor{contract: contract}, PrimitiveContractsInterfaceFilterer: PrimitiveContractsInterfaceFilterer{contract: contract}}, nil
}

// NewPrimitiveContractsInterfaceCaller creates a new read-only instance of PrimitiveContractsInterface, bound to a specific deployed contract.
func NewPrimitiveContractsInterfaceCaller(address common.Address, caller bind.ContractCaller) (*PrimitiveContractsInterfaceCaller, error) {
	contract, err := bindPrimitiveContractsInterface(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &PrimitiveContractsInterfaceCaller{contract: contract}, nil
}

// NewPrimitiveContractsInterfaceTransactor creates a new write-only instance of PrimitiveContractsInterface, bound to a specific deployed contract.
func NewPrimitiveContractsInterfaceTransactor(address common.Address, transactor bind.ContractTransactor) (*PrimitiveContractsInterfaceTransactor, error) {
	contract, err := bindPrimitiveContractsInterface(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &PrimitiveContractsInterfaceTransactor{contract: contract}, nil
}

// NewPrimitiveContractsInterfaceFilterer creates a new log filterer instance of PrimitiveContractsInterface, bound to a specific deployed contract.
func NewPrimitiveContractsInterfaceFilterer(address common.Address, filterer bind.ContractFilterer) (*PrimitiveContractsInterfaceFilterer, error) {
	contract, err := bindPrimitiveContractsInterface(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &PrimitiveContractsInterfaceFilterer{contract: contract}, nil
}

// bindPrimitiveContractsInterface binds a generic wrapper to an already deployed contract.
func bindPrimitiveContractsInterface(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(PrimitiveContractsInterfaceABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_PrimitiveContractsInterface *PrimitiveContractsInterfaceRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _PrimitiveContractsInterface.Contract.PrimitiveContractsInterfaceCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_PrimitiveContractsInterface *PrimitiveContractsInterfaceRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _PrimitiveContractsInterface.Contract.PrimitiveContractsInterfaceTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_PrimitiveContractsInterface *PrimitiveContractsInterfaceRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _PrimitiveContractsInterface.Contract.PrimitiveContractsInterfaceTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_PrimitiveContractsInterface *PrimitiveContractsInterfaceCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _PrimitiveContractsInterface.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_PrimitiveContractsInterface *PrimitiveContractsInterfaceTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _PrimitiveContractsInterface.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_PrimitiveContractsInterface *PrimitiveContractsInterfaceTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _PrimitiveContractsInterface.Contract.contract.Transact(opts, method, params...)
}

// RptABI is the input ABI used to generate the binding from.
const RptABI = "[{\"constant\":false,\"inputs\":[{\"name\":\"_alpha\",\"type\":\"uint256\"}],\"name\":\"updateAlpha\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"omega\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"f\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"},{\"name\":\"_blockNumber\",\"type\":\"uint256\"}],\"name\":\"getProxyRep\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"window\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_gamma\",\"type\":\"uint256\"}],\"name\":\"updateGamma\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"},{\"name\":\"_blockNumber\",\"type\":\"uint256\"}],\"name\":\"getRpt\",\"outputs\":[{\"name\":\"rpt\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"},{\"name\":\"_blockNumber\",\"type\":\"uint256\"}],\"name\":\"getTx\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"},{\"name\":\"_blockNumber\",\"type\":\"uint256\"}],\"name\":\"getDataContribution\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"psi\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"owner\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"beta\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_omega\",\"type\":\"uint256\"}],\"name\":\"updateOmega\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_beta\",\"type\":\"uint256\"}],\"name\":\"updateBeta\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"gamma\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_psi\",\"type\":\"uint256\"}],\"name\":\"updatePsi\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_window\",\"type\":\"uint256\"}],\"name\":\"updateWindow\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_alpha\",\"type\":\"uint256\"},{\"name\":\"_beta\",\"type\":\"uint256\"},{\"name\":\"_gamma\",\"type\":\"uint256\"},{\"name\":\"_psi\",\"type\":\"uint256\"},{\"name\":\"_omega\",\"type\":\"uint256\"},{\"name\":\"_f\",\"type\":\"uint256\"},{\"name\":\"_window\",\"type\":\"uint256\"}],\"name\":\"updateConfigs\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"alpha\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"},{\"name\":\"_blockNumber\",\"type\":\"uint256\"}],\"name\":\"getCoinage\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"},{\"name\":\"_blockNumber\",\"type\":\"uint256\"}],\"name\":\"getBlockchainMaintenance\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"blockNumber\",\"type\":\"uint256\"}],\"name\":\"UpdateConfigs\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"blockNumber\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"configName\",\"type\":\"string\"},{\"indexed\":false,\"name\":\"configValue\",\"type\":\"uint256\"}],\"name\":\"UpdateOneConfig\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"blockNumber\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"exprNmae\",\"type\":\"string\"},{\"indexed\":false,\"name\":\"expr\",\"type\":\"string\"}],\"name\":\"SetExp\",\"type\":\"event\"}]"

// RptBin is the compiled bytecode used for deploying new contracts.
const RptBin = `0x60806040526032600055600f600155600a600255600f600355600a6004556004600555601560065534801561003357600080fd5b5060078054600160a060020a03191633179055610ba0806100556000396000f30060806040526004361061011c5763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166306d2d3dc81146101215780632262a1b31461013b57806326121ff01461016257806344cc5c5214610177578063461645bf1461019b5780636d8004c5146101b05780636f126a8f146101c8578063741a35c4146101ec5780637c9f4b661461021057806386f87fdd146102345780638da5cb5b146102495780639faa3c911461027a578063a23f52b81461028f578063ac7dabbc146102a7578063b1373929146102bf578063b2f801c4146102d4578063b98f0056146102ec578063bd5c5f8614610304578063db1d0fd51461032e578063db40a12e14610343578063e81092a514610367575b600080fd5b34801561012d57600080fd5b5061013960043561038b565b005b34801561014757600080fd5b50610150610406565b60408051918252519081900360200190f35b34801561016e57600080fd5b5061015061040c565b34801561018357600080fd5b50610150600160a060020a0360043516602435610412565b3480156101a757600080fd5b506101506104a0565b3480156101bc57600080fd5b506101396004356104a6565b3480156101d457600080fd5b50610150600160a060020a0360043516602435610521565b3480156101f857600080fd5b50610150600160a060020a036004351660243561063a565b34801561021c57600080fd5b50610150600160a060020a0360043516602435610688565b34801561024057600080fd5b506101506106d8565b34801561025557600080fd5b5061025e6106de565b60408051600160a060020a039092168252519081900360200190f35b34801561028657600080fd5b506101506106ed565b34801561029b57600080fd5b506101396004356106f3565b3480156102b357600080fd5b5061013960043561076e565b3480156102cb57600080fd5b506101506107e9565b3480156102e057600080fd5b506101396004356107ef565b3480156102f857600080fd5b50610139600435610869565b34801561031057600080fd5b5061013960043560243560443560643560843560a43560c4356108e4565b34801561033a57600080fd5b5061015061095a565b34801561034f57600080fd5b50610150600160a060020a0360043516602435610960565b34801561037357600080fd5b50610150600160a060020a03600435166024356109ea565b600754600160a060020a031633146103a257600080fd5b6000819055604080514381528082018390526060602082018190526005908201527f616c70686100000000000000000000000000000000000000000000000000000060808201529051600080516020610b558339815191529181900360a00190a150565b60045481565b60065481565b6000808080610430600160a060020a0387168663ffffffff610a3416565b92508215156104425760009350610497565b61045b600160a060020a0387168663ffffffff610a6116565b915061047f600a61047384600563ffffffff610a8616565b9063ffffffff610ab116565b905060648111156104935760649350610497565b8093505b50505092915050565b60055481565b600754600160a060020a031633146104bd57600080fd5b6002819055604080514381528082018390526060602082018190526005908201527f67616d6d6100000000000000000000000000000000000000000000000000000060808201529051600080516020610b558339815191529181900360a00190a150565b60004382111561059257604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601960248201527f626c6f636b4e756d62657220697320746f6f206c617267652e00000000000000604482015290519081900360640190fd5b5060006105b36105a28484610960565b60005483910263ffffffff610ab116565b90506105d36105c2848461063a565b60015483910263ffffffff610ab116565b90506105f36105e28484610412565b60025483910263ffffffff610ab116565b90506106136106028484610688565b60035483910263ffffffff610ab116565b905061063361062284846109ea565b60045483910263ffffffff610ab116565b9392505050565b600080610656600160a060020a0385168463ffffffff610ac016565b905061066981600563ffffffff610a8616565b9050606481111561067d5760649150610681565b8091505b5092915050565b600080806106a5600160a060020a0386168563ffffffff610ae516565b91506106b882600363ffffffff610a8616565b905060648111156106cc57606492506106d0565b8092505b505092915050565b60035481565b600754600160a060020a031681565b60015481565b600754600160a060020a0316331461070a57600080fd5b6004819055604080514381528082018390526060602082018190526005908201527f6f6d65676100000000000000000000000000000000000000000000000000000060808201529051600080516020610b558339815191529181900360a00190a150565b600754600160a060020a0316331461078557600080fd5b6001819055604080514381528082018390526060602082018190526004908201527f626574610000000000000000000000000000000000000000000000000000000060808201529051600080516020610b558339815191529181900360a00190a150565b60025481565b600754600160a060020a0316331461080657600080fd5b6003818155604080514381528082018490526060602082018190528101929092527f7073690000000000000000000000000000000000000000000000000000000000608083015251600080516020610b558339815191529181900360a00190a150565b600754600160a060020a0316331461088057600080fd5b6005819055604080514381528082018390526060602082018190526006908201527f77696e646f77000000000000000000000000000000000000000000000000000060808201529051600080516020610b558339815191529181900360a00190a150565b600754600160a060020a031633146108fb57600080fd5b60008790556001869055600285905560038490556004839055600581905560068290556040805143815290517f78a3671679b68721aaad9eb74535be0be119bd34c0efa671eb6ab3210d1fe2579181900360200190a150505050505050565b60005481565b60008061097c600160a060020a0385168463ffffffff610b0a16565b905060028110156109905760649150610681565b60058110156109a257605a9150610681565b600f8110156109b45760509150610681565b60238110156109c65760469150610681565b603c8110156109d857603c9150610681565b605081101561067d5760289150610681565b600080610a06600160a060020a0385168463ffffffff610b2f16565b9050801515610a185760649150610681565b8060011415610a2a5760509150610681565b50603c9392505050565b60006040518381528260208201526020816040836069600019fa1515610a5957600080fd5b519392505050565b60006040518381528260208201526020816040836066600019fa1515610a5957600080fd5b600080831515610a995760009150610681565b50828202828482811515610aa957fe5b041461067d57fe5b60008282018381101561067d57fe5b60006040518381528260208201526020816040836068600019fa1515610a5957600080fd5b60006040518381528260208201526020816040836067600019fa1515610a5957600080fd5b60006040518381528260208201526020816040836064600019fa1515610a5957600080fd5b60006040518381528260208201526020816040836065600019fa1515610a5957600080fd007c2d85cf45868065466ed7df2e23f26349626794d112e41a734a4e34727fcb21a165627a7a7230582057a49777fc594f5478a1fcac7d11c3c919fd3baaedca172187b9a1d514ba6f2f0029`

// DeployRpt deploys a new cpchain contract, binding an instance of Rpt to it.
func DeployRpt(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *Rpt, error) {
	parsed, err := abi.JSON(strings.NewReader(RptABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(RptBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &Rpt{RptCaller: RptCaller{contract: contract}, RptTransactor: RptTransactor{contract: contract}, RptFilterer: RptFilterer{contract: contract}}, nil
}

// Rpt is an auto generated Go binding around an cpchain contract.
type Rpt struct {
	RptCaller     // Read-only binding to the contract
	RptTransactor // Write-only binding to the contract
	RptFilterer   // Log filterer for contract events
}

// RptCaller is an auto generated read-only Go binding around an cpchain contract.
type RptCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RptTransactor is an auto generated write-only Go binding around an cpchain contract.
type RptTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RptFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type RptFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RptSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type RptSession struct {
	Contract     *Rpt              // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// RptCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type RptCallerSession struct {
	Contract *RptCaller    // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts // Call options to use throughout this session
}

// RptTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type RptTransactorSession struct {
	Contract     *RptTransactor    // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// RptRaw is an auto generated low-level Go binding around an cpchain contract.
type RptRaw struct {
	Contract *Rpt // Generic contract binding to access the raw methods on
}

// RptCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type RptCallerRaw struct {
	Contract *RptCaller // Generic read-only contract binding to access the raw methods on
}

// RptTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type RptTransactorRaw struct {
	Contract *RptTransactor // Generic write-only contract binding to access the raw methods on
}

// NewRpt creates a new instance of Rpt, bound to a specific deployed contract.
func NewRpt(address common.Address, backend bind.ContractBackend) (*Rpt, error) {
	contract, err := bindRpt(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &Rpt{RptCaller: RptCaller{contract: contract}, RptTransactor: RptTransactor{contract: contract}, RptFilterer: RptFilterer{contract: contract}}, nil
}

// NewRptCaller creates a new read-only instance of Rpt, bound to a specific deployed contract.
func NewRptCaller(address common.Address, caller bind.ContractCaller) (*RptCaller, error) {
	contract, err := bindRpt(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &RptCaller{contract: contract}, nil
}

// NewRptTransactor creates a new write-only instance of Rpt, bound to a specific deployed contract.
func NewRptTransactor(address common.Address, transactor bind.ContractTransactor) (*RptTransactor, error) {
	contract, err := bindRpt(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &RptTransactor{contract: contract}, nil
}

// NewRptFilterer creates a new log filterer instance of Rpt, bound to a specific deployed contract.
func NewRptFilterer(address common.Address, filterer bind.ContractFilterer) (*RptFilterer, error) {
	contract, err := bindRpt(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &RptFilterer{contract: contract}, nil
}

// bindRpt binds a generic wrapper to an already deployed contract.
func bindRpt(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(RptABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Rpt *RptRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Rpt.Contract.RptCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Rpt *RptRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Rpt.Contract.RptTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Rpt *RptRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Rpt.Contract.RptTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Rpt *RptCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Rpt.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Rpt *RptTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Rpt.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Rpt *RptTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Rpt.Contract.contract.Transact(opts, method, params...)
}

// Alpha is a free data retrieval call binding the contract method 0xdb1d0fd5.
//
// Solidity: function alpha() constant returns(uint256)
func (_Rpt *RptCaller) Alpha(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "alpha")
	return *ret0, err
}

// Alpha is a free data retrieval call binding the contract method 0xdb1d0fd5.
//
// Solidity: function alpha() constant returns(uint256)
func (_Rpt *RptSession) Alpha() (*big.Int, error) {
	return _Rpt.Contract.Alpha(&_Rpt.CallOpts)
}

// Alpha is a free data retrieval call binding the contract method 0xdb1d0fd5.
//
// Solidity: function alpha() constant returns(uint256)
func (_Rpt *RptCallerSession) Alpha() (*big.Int, error) {
	return _Rpt.Contract.Alpha(&_Rpt.CallOpts)
}

// Beta is a free data retrieval call binding the contract method 0x9faa3c91.
//
// Solidity: function beta() constant returns(uint256)
func (_Rpt *RptCaller) Beta(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "beta")
	return *ret0, err
}

// Beta is a free data retrieval call binding the contract method 0x9faa3c91.
//
// Solidity: function beta() constant returns(uint256)
func (_Rpt *RptSession) Beta() (*big.Int, error) {
	return _Rpt.Contract.Beta(&_Rpt.CallOpts)
}

// Beta is a free data retrieval call binding the contract method 0x9faa3c91.
//
// Solidity: function beta() constant returns(uint256)
func (_Rpt *RptCallerSession) Beta() (*big.Int, error) {
	return _Rpt.Contract.Beta(&_Rpt.CallOpts)
}

// F is a free data retrieval call binding the contract method 0x26121ff0.
//
// Solidity: function f() constant returns(uint256)
func (_Rpt *RptCaller) F(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "f")
	return *ret0, err
}

// F is a free data retrieval call binding the contract method 0x26121ff0.
//
// Solidity: function f() constant returns(uint256)
func (_Rpt *RptSession) F() (*big.Int, error) {
	return _Rpt.Contract.F(&_Rpt.CallOpts)
}

// F is a free data retrieval call binding the contract method 0x26121ff0.
//
// Solidity: function f() constant returns(uint256)
func (_Rpt *RptCallerSession) F() (*big.Int, error) {
	return _Rpt.Contract.F(&_Rpt.CallOpts)
}

// Gamma is a free data retrieval call binding the contract method 0xb1373929.
//
// Solidity: function gamma() constant returns(uint256)
func (_Rpt *RptCaller) Gamma(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "gamma")
	return *ret0, err
}

// Gamma is a free data retrieval call binding the contract method 0xb1373929.
//
// Solidity: function gamma() constant returns(uint256)
func (_Rpt *RptSession) Gamma() (*big.Int, error) {
	return _Rpt.Contract.Gamma(&_Rpt.CallOpts)
}

// Gamma is a free data retrieval call binding the contract method 0xb1373929.
//
// Solidity: function gamma() constant returns(uint256)
func (_Rpt *RptCallerSession) Gamma() (*big.Int, error) {
	return _Rpt.Contract.Gamma(&_Rpt.CallOpts)
}

// GetBlockchainMaintenance is a free data retrieval call binding the contract method 0xe81092a5.
//
// Solidity: function getBlockchainMaintenance(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptCaller) GetBlockchainMaintenance(opts *bind.CallOpts, _addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "getBlockchainMaintenance", _addr, _blockNumber)
	return *ret0, err
}

// GetBlockchainMaintenance is a free data retrieval call binding the contract method 0xe81092a5.
//
// Solidity: function getBlockchainMaintenance(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptSession) GetBlockchainMaintenance(_addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	return _Rpt.Contract.GetBlockchainMaintenance(&_Rpt.CallOpts, _addr, _blockNumber)
}

// GetBlockchainMaintenance is a free data retrieval call binding the contract method 0xe81092a5.
//
// Solidity: function getBlockchainMaintenance(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptCallerSession) GetBlockchainMaintenance(_addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	return _Rpt.Contract.GetBlockchainMaintenance(&_Rpt.CallOpts, _addr, _blockNumber)
}

// GetCoinage is a free data retrieval call binding the contract method 0xdb40a12e.
//
// Solidity: function getCoinage(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptCaller) GetCoinage(opts *bind.CallOpts, _addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "getCoinage", _addr, _blockNumber)
	return *ret0, err
}

// GetCoinage is a free data retrieval call binding the contract method 0xdb40a12e.
//
// Solidity: function getCoinage(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptSession) GetCoinage(_addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	return _Rpt.Contract.GetCoinage(&_Rpt.CallOpts, _addr, _blockNumber)
}

// GetCoinage is a free data retrieval call binding the contract method 0xdb40a12e.
//
// Solidity: function getCoinage(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptCallerSession) GetCoinage(_addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	return _Rpt.Contract.GetCoinage(&_Rpt.CallOpts, _addr, _blockNumber)
}

// GetDataContribution is a free data retrieval call binding the contract method 0x7c9f4b66.
//
// Solidity: function getDataContribution(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptCaller) GetDataContribution(opts *bind.CallOpts, _addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "getDataContribution", _addr, _blockNumber)
	return *ret0, err
}

// GetDataContribution is a free data retrieval call binding the contract method 0x7c9f4b66.
//
// Solidity: function getDataContribution(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptSession) GetDataContribution(_addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	return _Rpt.Contract.GetDataContribution(&_Rpt.CallOpts, _addr, _blockNumber)
}

// GetDataContribution is a free data retrieval call binding the contract method 0x7c9f4b66.
//
// Solidity: function getDataContribution(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptCallerSession) GetDataContribution(_addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	return _Rpt.Contract.GetDataContribution(&_Rpt.CallOpts, _addr, _blockNumber)
}

// GetProxyRep is a free data retrieval call binding the contract method 0x44cc5c52.
//
// Solidity: function getProxyRep(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptCaller) GetProxyRep(opts *bind.CallOpts, _addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "getProxyRep", _addr, _blockNumber)
	return *ret0, err
}

// GetProxyRep is a free data retrieval call binding the contract method 0x44cc5c52.
//
// Solidity: function getProxyRep(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptSession) GetProxyRep(_addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	return _Rpt.Contract.GetProxyRep(&_Rpt.CallOpts, _addr, _blockNumber)
}

// GetProxyRep is a free data retrieval call binding the contract method 0x44cc5c52.
//
// Solidity: function getProxyRep(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptCallerSession) GetProxyRep(_addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	return _Rpt.Contract.GetProxyRep(&_Rpt.CallOpts, _addr, _blockNumber)
}

// GetRpt is a free data retrieval call binding the contract method 0x6f126a8f.
//
// Solidity: function getRpt(_addr address, _blockNumber uint256) constant returns(rpt uint256)
func (_Rpt *RptCaller) GetRpt(opts *bind.CallOpts, _addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "getRpt", _addr, _blockNumber)
	return *ret0, err
}

// GetRpt is a free data retrieval call binding the contract method 0x6f126a8f.
//
// Solidity: function getRpt(_addr address, _blockNumber uint256) constant returns(rpt uint256)
func (_Rpt *RptSession) GetRpt(_addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	return _Rpt.Contract.GetRpt(&_Rpt.CallOpts, _addr, _blockNumber)
}

// GetRpt is a free data retrieval call binding the contract method 0x6f126a8f.
//
// Solidity: function getRpt(_addr address, _blockNumber uint256) constant returns(rpt uint256)
func (_Rpt *RptCallerSession) GetRpt(_addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	return _Rpt.Contract.GetRpt(&_Rpt.CallOpts, _addr, _blockNumber)
}

// GetTx is a free data retrieval call binding the contract method 0x741a35c4.
//
// Solidity: function getTx(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptCaller) GetTx(opts *bind.CallOpts, _addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "getTx", _addr, _blockNumber)
	return *ret0, err
}

// GetTx is a free data retrieval call binding the contract method 0x741a35c4.
//
// Solidity: function getTx(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptSession) GetTx(_addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	return _Rpt.Contract.GetTx(&_Rpt.CallOpts, _addr, _blockNumber)
}

// GetTx is a free data retrieval call binding the contract method 0x741a35c4.
//
// Solidity: function getTx(_addr address, _blockNumber uint256) constant returns(uint256)
func (_Rpt *RptCallerSession) GetTx(_addr common.Address, _blockNumber *big.Int) (*big.Int, error) {
	return _Rpt.Contract.GetTx(&_Rpt.CallOpts, _addr, _blockNumber)
}

// Omega is a free data retrieval call binding the contract method 0x2262a1b3.
//
// Solidity: function omega() constant returns(uint256)
func (_Rpt *RptCaller) Omega(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "omega")
	return *ret0, err
}

// Omega is a free data retrieval call binding the contract method 0x2262a1b3.
//
// Solidity: function omega() constant returns(uint256)
func (_Rpt *RptSession) Omega() (*big.Int, error) {
	return _Rpt.Contract.Omega(&_Rpt.CallOpts)
}

// Omega is a free data retrieval call binding the contract method 0x2262a1b3.
//
// Solidity: function omega() constant returns(uint256)
func (_Rpt *RptCallerSession) Omega() (*big.Int, error) {
	return _Rpt.Contract.Omega(&_Rpt.CallOpts)
}

// Owner is a free data retrieval call binding the contract method 0x8da5cb5b.
//
// Solidity: function owner() constant returns(address)
func (_Rpt *RptCaller) Owner(opts *bind.CallOpts) (common.Address, error) {
	var (
		ret0 = new(common.Address)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "owner")
	return *ret0, err
}

// Owner is a free data retrieval call binding the contract method 0x8da5cb5b.
//
// Solidity: function owner() constant returns(address)
func (_Rpt *RptSession) Owner() (common.Address, error) {
	return _Rpt.Contract.Owner(&_Rpt.CallOpts)
}

// Owner is a free data retrieval call binding the contract method 0x8da5cb5b.
//
// Solidity: function owner() constant returns(address)
func (_Rpt *RptCallerSession) Owner() (common.Address, error) {
	return _Rpt.Contract.Owner(&_Rpt.CallOpts)
}

// Psi is a free data retrieval call binding the contract method 0x86f87fdd.
//
// Solidity: function psi() constant returns(uint256)
func (_Rpt *RptCaller) Psi(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "psi")
	return *ret0, err
}

// Psi is a free data retrieval call binding the contract method 0x86f87fdd.
//
// Solidity: function psi() constant returns(uint256)
func (_Rpt *RptSession) Psi() (*big.Int, error) {
	return _Rpt.Contract.Psi(&_Rpt.CallOpts)
}

// Psi is a free data retrieval call binding the contract method 0x86f87fdd.
//
// Solidity: function psi() constant returns(uint256)
func (_Rpt *RptCallerSession) Psi() (*big.Int, error) {
	return _Rpt.Contract.Psi(&_Rpt.CallOpts)
}

// Window is a free data retrieval call binding the contract method 0x461645bf.
//
// Solidity: function window() constant returns(uint256)
func (_Rpt *RptCaller) Window(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Rpt.contract.Call(opts, out, "window")
	return *ret0, err
}

// Window is a free data retrieval call binding the contract method 0x461645bf.
//
// Solidity: function window() constant returns(uint256)
func (_Rpt *RptSession) Window() (*big.Int, error) {
	return _Rpt.Contract.Window(&_Rpt.CallOpts)
}

// Window is a free data retrieval call binding the contract method 0x461645bf.
//
// Solidity: function window() constant returns(uint256)
func (_Rpt *RptCallerSession) Window() (*big.Int, error) {
	return _Rpt.Contract.Window(&_Rpt.CallOpts)
}

// UpdateAlpha is a paid mutator transaction binding the contract method 0x06d2d3dc.
//
// Solidity: function updateAlpha(_alpha uint256) returns()
func (_Rpt *RptTransactor) UpdateAlpha(opts *bind.TransactOpts, _alpha *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateAlpha", _alpha)
}

// UpdateAlpha is a paid mutator transaction binding the contract method 0x06d2d3dc.
//
// Solidity: function updateAlpha(_alpha uint256) returns()
func (_Rpt *RptSession) UpdateAlpha(_alpha *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateAlpha(&_Rpt.TransactOpts, _alpha)
}

// UpdateAlpha is a paid mutator transaction binding the contract method 0x06d2d3dc.
//
// Solidity: function updateAlpha(_alpha uint256) returns()
func (_Rpt *RptTransactorSession) UpdateAlpha(_alpha *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateAlpha(&_Rpt.TransactOpts, _alpha)
}

// UpdateBeta is a paid mutator transaction binding the contract method 0xac7dabbc.
//
// Solidity: function updateBeta(_beta uint256) returns()
func (_Rpt *RptTransactor) UpdateBeta(opts *bind.TransactOpts, _beta *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateBeta", _beta)
}

// UpdateBeta is a paid mutator transaction binding the contract method 0xac7dabbc.
//
// Solidity: function updateBeta(_beta uint256) returns()
func (_Rpt *RptSession) UpdateBeta(_beta *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateBeta(&_Rpt.TransactOpts, _beta)
}

// UpdateBeta is a paid mutator transaction binding the contract method 0xac7dabbc.
//
// Solidity: function updateBeta(_beta uint256) returns()
func (_Rpt *RptTransactorSession) UpdateBeta(_beta *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateBeta(&_Rpt.TransactOpts, _beta)
}

// UpdateConfigs is a paid mutator transaction binding the contract method 0xbd5c5f86.
//
// Solidity: function updateConfigs(_alpha uint256, _beta uint256, _gamma uint256, _psi uint256, _omega uint256, _f uint256, _window uint256) returns()
func (_Rpt *RptTransactor) UpdateConfigs(opts *bind.TransactOpts, _alpha *big.Int, _beta *big.Int, _gamma *big.Int, _psi *big.Int, _omega *big.Int, _f *big.Int, _window *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateConfigs", _alpha, _beta, _gamma, _psi, _omega, _f, _window)
}

// UpdateConfigs is a paid mutator transaction binding the contract method 0xbd5c5f86.
//
// Solidity: function updateConfigs(_alpha uint256, _beta uint256, _gamma uint256, _psi uint256, _omega uint256, _f uint256, _window uint256) returns()
func (_Rpt *RptSession) UpdateConfigs(_alpha *big.Int, _beta *big.Int, _gamma *big.Int, _psi *big.Int, _omega *big.Int, _f *big.Int, _window *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateConfigs(&_Rpt.TransactOpts, _alpha, _beta, _gamma, _psi, _omega, _f, _window)
}

// UpdateConfigs is a paid mutator transaction binding the contract method 0xbd5c5f86.
//
// Solidity: function updateConfigs(_alpha uint256, _beta uint256, _gamma uint256, _psi uint256, _omega uint256, _f uint256, _window uint256) returns()
func (_Rpt *RptTransactorSession) UpdateConfigs(_alpha *big.Int, _beta *big.Int, _gamma *big.Int, _psi *big.Int, _omega *big.Int, _f *big.Int, _window *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateConfigs(&_Rpt.TransactOpts, _alpha, _beta, _gamma, _psi, _omega, _f, _window)
}

// UpdateGamma is a paid mutator transaction binding the contract method 0x6d8004c5.
//
// Solidity: function updateGamma(_gamma uint256) returns()
func (_Rpt *RptTransactor) UpdateGamma(opts *bind.TransactOpts, _gamma *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateGamma", _gamma)
}

// UpdateGamma is a paid mutator transaction binding the contract method 0x6d8004c5.
//
// Solidity: function updateGamma(_gamma uint256) returns()
func (_Rpt *RptSession) UpdateGamma(_gamma *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateGamma(&_Rpt.TransactOpts, _gamma)
}

// UpdateGamma is a paid mutator transaction binding the contract method 0x6d8004c5.
//
// Solidity: function updateGamma(_gamma uint256) returns()
func (_Rpt *RptTransactorSession) UpdateGamma(_gamma *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateGamma(&_Rpt.TransactOpts, _gamma)
}

// UpdateOmega is a paid mutator transaction binding the contract method 0xa23f52b8.
//
// Solidity: function updateOmega(_omega uint256) returns()
func (_Rpt *RptTransactor) UpdateOmega(opts *bind.TransactOpts, _omega *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateOmega", _omega)
}

// UpdateOmega is a paid mutator transaction binding the contract method 0xa23f52b8.
//
// Solidity: function updateOmega(_omega uint256) returns()
func (_Rpt *RptSession) UpdateOmega(_omega *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateOmega(&_Rpt.TransactOpts, _omega)
}

// UpdateOmega is a paid mutator transaction binding the contract method 0xa23f52b8.
//
// Solidity: function updateOmega(_omega uint256) returns()
func (_Rpt *RptTransactorSession) UpdateOmega(_omega *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateOmega(&_Rpt.TransactOpts, _omega)
}

// UpdatePsi is a paid mutator transaction binding the contract method 0xb2f801c4.
//
// Solidity: function updatePsi(_psi uint256) returns()
func (_Rpt *RptTransactor) UpdatePsi(opts *bind.TransactOpts, _psi *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updatePsi", _psi)
}

// UpdatePsi is a paid mutator transaction binding the contract method 0xb2f801c4.
//
// Solidity: function updatePsi(_psi uint256) returns()
func (_Rpt *RptSession) UpdatePsi(_psi *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdatePsi(&_Rpt.TransactOpts, _psi)
}

// UpdatePsi is a paid mutator transaction binding the contract method 0xb2f801c4.
//
// Solidity: function updatePsi(_psi uint256) returns()
func (_Rpt *RptTransactorSession) UpdatePsi(_psi *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdatePsi(&_Rpt.TransactOpts, _psi)
}

// UpdateWindow is a paid mutator transaction binding the contract method 0xb98f0056.
//
// Solidity: function updateWindow(_window uint256) returns()
func (_Rpt *RptTransactor) UpdateWindow(opts *bind.TransactOpts, _window *big.Int) (*types.Transaction, error) {
	return _Rpt.contract.Transact(opts, "updateWindow", _window)
}

// UpdateWindow is a paid mutator transaction binding the contract method 0xb98f0056.
//
// Solidity: function updateWindow(_window uint256) returns()
func (_Rpt *RptSession) UpdateWindow(_window *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateWindow(&_Rpt.TransactOpts, _window)
}

// UpdateWindow is a paid mutator transaction binding the contract method 0xb98f0056.
//
// Solidity: function updateWindow(_window uint256) returns()
func (_Rpt *RptTransactorSession) UpdateWindow(_window *big.Int) (*types.Transaction, error) {
	return _Rpt.Contract.UpdateWindow(&_Rpt.TransactOpts, _window)
}

// RptSetExpIterator is returned from FilterSetExp and is used to iterate over the raw logs and unpacked data for SetExp events raised by the Rpt contract.
type RptSetExpIterator struct {
	Event *RptSetExp // Event containing the contract specifics and raw log

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
func (it *RptSetExpIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RptSetExp)
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
		it.Event = new(RptSetExp)
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
func (it *RptSetExpIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RptSetExpIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RptSetExp represents a SetExp event raised by the Rpt contract.
type RptSetExp struct {
	BlockNumber *big.Int
	ExprNmae    string
	Expr        string
	Raw         types.Log // Blockchain specific contextual infos
}

// FilterSetExp is a free log retrieval operation binding the contract event 0xb14fcf0092d0dcc5be78d778e4f514b5d12a1671f6260cf9d84ac5847b08e894.
//
// Solidity: e SetExp(blockNumber uint256, exprNmae string, expr string)
func (_Rpt *RptFilterer) FilterSetExp(opts *bind.FilterOpts) (*RptSetExpIterator, error) {

	logs, sub, err := _Rpt.contract.FilterLogs(opts, "SetExp")
	if err != nil {
		return nil, err
	}
	return &RptSetExpIterator{contract: _Rpt.contract, event: "SetExp", logs: logs, sub: sub}, nil
}

// WatchSetExp is a free log subscription operation binding the contract event 0xb14fcf0092d0dcc5be78d778e4f514b5d12a1671f6260cf9d84ac5847b08e894.
//
// Solidity: e SetExp(blockNumber uint256, exprNmae string, expr string)
func (_Rpt *RptFilterer) WatchSetExp(opts *bind.WatchOpts, sink chan<- *RptSetExp) (event.Subscription, error) {

	logs, sub, err := _Rpt.contract.WatchLogs(opts, "SetExp")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RptSetExp)
				if err := _Rpt.contract.UnpackLog(event, "SetExp", log); err != nil {
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

// RptUpdateConfigsIterator is returned from FilterUpdateConfigs and is used to iterate over the raw logs and unpacked data for UpdateConfigs events raised by the Rpt contract.
type RptUpdateConfigsIterator struct {
	Event *RptUpdateConfigs // Event containing the contract specifics and raw log

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
func (it *RptUpdateConfigsIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RptUpdateConfigs)
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
		it.Event = new(RptUpdateConfigs)
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
func (it *RptUpdateConfigsIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RptUpdateConfigsIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RptUpdateConfigs represents a UpdateConfigs event raised by the Rpt contract.
type RptUpdateConfigs struct {
	BlockNumber *big.Int
	Raw         types.Log // Blockchain specific contextual infos
}

// FilterUpdateConfigs is a free log retrieval operation binding the contract event 0x78a3671679b68721aaad9eb74535be0be119bd34c0efa671eb6ab3210d1fe257.
//
// Solidity: e UpdateConfigs(blockNumber uint256)
func (_Rpt *RptFilterer) FilterUpdateConfigs(opts *bind.FilterOpts) (*RptUpdateConfigsIterator, error) {

	logs, sub, err := _Rpt.contract.FilterLogs(opts, "UpdateConfigs")
	if err != nil {
		return nil, err
	}
	return &RptUpdateConfigsIterator{contract: _Rpt.contract, event: "UpdateConfigs", logs: logs, sub: sub}, nil
}

// WatchUpdateConfigs is a free log subscription operation binding the contract event 0x78a3671679b68721aaad9eb74535be0be119bd34c0efa671eb6ab3210d1fe257.
//
// Solidity: e UpdateConfigs(blockNumber uint256)
func (_Rpt *RptFilterer) WatchUpdateConfigs(opts *bind.WatchOpts, sink chan<- *RptUpdateConfigs) (event.Subscription, error) {

	logs, sub, err := _Rpt.contract.WatchLogs(opts, "UpdateConfigs")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RptUpdateConfigs)
				if err := _Rpt.contract.UnpackLog(event, "UpdateConfigs", log); err != nil {
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

// RptUpdateOneConfigIterator is returned from FilterUpdateOneConfig and is used to iterate over the raw logs and unpacked data for UpdateOneConfig events raised by the Rpt contract.
type RptUpdateOneConfigIterator struct {
	Event *RptUpdateOneConfig // Event containing the contract specifics and raw log

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
func (it *RptUpdateOneConfigIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RptUpdateOneConfig)
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
		it.Event = new(RptUpdateOneConfig)
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
func (it *RptUpdateOneConfigIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RptUpdateOneConfigIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RptUpdateOneConfig represents a UpdateOneConfig event raised by the Rpt contract.
type RptUpdateOneConfig struct {
	BlockNumber *big.Int
	ConfigName  string
	ConfigValue *big.Int
	Raw         types.Log // Blockchain specific contextual infos
}

// FilterUpdateOneConfig is a free log retrieval operation binding the contract event 0x7c2d85cf45868065466ed7df2e23f26349626794d112e41a734a4e34727fcb21.
//
// Solidity: e UpdateOneConfig(blockNumber uint256, configName string, configValue uint256)
func (_Rpt *RptFilterer) FilterUpdateOneConfig(opts *bind.FilterOpts) (*RptUpdateOneConfigIterator, error) {

	logs, sub, err := _Rpt.contract.FilterLogs(opts, "UpdateOneConfig")
	if err != nil {
		return nil, err
	}
	return &RptUpdateOneConfigIterator{contract: _Rpt.contract, event: "UpdateOneConfig", logs: logs, sub: sub}, nil
}

// WatchUpdateOneConfig is a free log subscription operation binding the contract event 0x7c2d85cf45868065466ed7df2e23f26349626794d112e41a734a4e34727fcb21.
//
// Solidity: e UpdateOneConfig(blockNumber uint256, configName string, configValue uint256)
func (_Rpt *RptFilterer) WatchUpdateOneConfig(opts *bind.WatchOpts, sink chan<- *RptUpdateOneConfig) (event.Subscription, error) {

	logs, sub, err := _Rpt.contract.WatchLogs(opts, "UpdateOneConfig")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RptUpdateOneConfig)
				if err := _Rpt.contract.UnpackLog(event, "UpdateOneConfig", log); err != nil {
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
const SafeMathBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a723058203c583f566367488ec923b14604a730c6212ec94bca82a871c067b0cbf882af130029`

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
