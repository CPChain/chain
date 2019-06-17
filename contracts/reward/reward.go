// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package reward

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

// RewardABI is the input ABI used to generate the binding from.
const RewardABI = "[{\"constant\":true,\"inputs\":[],\"name\":\"settlementPeriod\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"totalInvestment\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"round\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"inLock\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"inSettlement\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"bonusPool\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"inRaise\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"nextSettlementTime\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"amount\",\"type\":\"uint256\"}],\"name\":\"withdraw\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"disable\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"nextLockTime\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"claimInterest\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"newLock\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"lockPeriod\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"investor\",\"type\":\"address\"},{\"name\":\"amount\",\"type\":\"uint256\"}],\"name\":\"refund\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"raisePeriod\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_raisePeriod\",\"type\":\"uint256\"}],\"name\":\"setRaisePeriod\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_nextLockTime\",\"type\":\"uint256\"}],\"name\":\"setNextLockTime\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"nextRaiseTime\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_lockPeriod\",\"type\":\"uint256\"}],\"name\":\"setLockPeriod\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_settlementPeriod\",\"type\":\"uint256\"}],\"name\":\"setSettlementPeriod\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"newSettlement\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"newRaise\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"\",\"type\":\"address\"}],\"name\":\"investments\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_nextSettlementTime\",\"type\":\"uint256\"}],\"name\":\"setNextSettlementTime\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_nextRaiseTime\",\"type\":\"uint256\"}],\"name\":\"setNextRaiseTime\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"totalInterest\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"deposit\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"getEnodes\",\"outputs\":[{\"name\":\"\",\"type\":\"address[]\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"enodeThreshold\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_enodeThreshold\",\"type\":\"uint256\"}],\"name\":\"setEnodeThreshold\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"fallback\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"amount\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"total\",\"type\":\"uint256\"}],\"name\":\"FundBonusPool\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"what\",\"type\":\"string\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"SetConfig\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"what\",\"type\":\"string\"},{\"indexed\":false,\"name\":\"when\",\"type\":\"uint256\"}],\"name\":\"SetTime\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"when\",\"type\":\"uint256\"}],\"name\":\"NewRaise\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"investment\",\"type\":\"uint256\"}],\"name\":\"NewEnode\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"balance\",\"type\":\"uint256\"}],\"name\":\"EnodeQuit\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"amount\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"total\",\"type\":\"uint256\"}],\"name\":\"AddInvestment\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"amount\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"total\",\"type\":\"uint256\"}],\"name\":\"SubInvestment\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"when\",\"type\":\"uint256\"}],\"name\":\"NewLock\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"when\",\"type\":\"uint256\"}],\"name\":\"NewSettlement\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"income\",\"type\":\"uint256\"}],\"name\":\"ApplyForSettlement\",\"type\":\"event\"}]"

// RewardBin is the compiled bytecode used for deploying new contracts.
const RewardBin = `0x60806040526008805462ffffff191690556203f480600a819055626ebe00600b55600c5569043c33c1937564800000600d556000600e819055600f819055601081905560115534801561005157600080fd5b5060008054600160a060020a03191633179055611472806100736000396000f30060806040526004361061018a5763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416630f1071be81146101f757806310ea13df1461021e578063146ca53114610233578063197331b81461024857806324eceaf6146102715780632693ee8014610286578063273bac0b1461029b5780632b024aaf146102b05780632e1a7d4d146102c55780632f2770db146102df5780633086f3a4146102f457806335981fd814610309578063363245e11461031e5780633fd8b02f14610333578063410085df146103485780634618d9d21461036c578063491fcdea1461038157806364f44c0b146103995780636e216366146103b1578063779972da146103c65780638072a022146103de5780638baaf031146103f65780638f83bc7f1461040b57806396b98862146104205780639d63e6e614610441578063a19046e314610459578063bc7a36d614610471578063d0e30db014610486578063de4ff4bf1461048e578063ea86298c146104f3578063ec9f105f14610508575b60085460ff16151560011461019e57600080fd5b6009546101b1903463ffffffff61052016565b60098190556040805133815234602082015280820192909252517fa1610f5f05db2d5caefef4f1bb2d913438a2fdb236ebc0ceedfacb398af1955b9181900360600190a1005b34801561020357600080fd5b5061020c61053a565b60408051918252519081900360200190f35b34801561022a57600080fd5b5061020c610540565b34801561023f57600080fd5b5061020c610546565b34801561025457600080fd5b5061025d61054c565b604080519115158252519081900360200190f35b34801561027d57600080fd5b5061025d61055a565b34801561029257600080fd5b5061020c610569565b3480156102a757600080fd5b5061025d61056f565b3480156102bc57600080fd5b5061020c610578565b3480156102d157600080fd5b506102dd60043561057e565b005b3480156102eb57600080fd5b506102dd6106dc565b34801561030057600080fd5b5061020c610701565b34801561031557600080fd5b506102dd610707565b34801561032a57600080fd5b506102dd61084a565b34801561033f57600080fd5b5061020c61093c565b34801561035457600080fd5b506102dd600160a060020a0360043516602435610942565b34801561037857600080fd5b5061020c610a6b565b34801561038d57600080fd5b506102dd600435610a71565b3480156103a557600080fd5b506102dd600435610ae4565b3480156103bd57600080fd5b5061020c610b57565b3480156103d257600080fd5b506102dd600435610b5d565b3480156103ea57600080fd5b506102dd600435610bd0565b34801561040257600080fd5b506102dd610c43565b34801561041757600080fd5b506102dd610d30565b34801561042c57600080fd5b5061020c600160a060020a0360043516610e72565b34801561044d57600080fd5b506102dd600435610e84565b34801561046557600080fd5b506102dd600435610ef7565b34801561047d57600080fd5b5061020c610f6a565b6102dd610f70565b34801561049a57600080fd5b506104a3611081565b60408051602080825283518183015283519192839290830191858101910280838360005b838110156104df5781810151838201526020016104c7565b505050509050019250505060405180910390f35b3480156104ff57600080fd5b5061020c611093565b34801561051457600080fd5b506102dd600435611099565b60008282018381101561052f57fe5b8091505b5092915050565b600c5481565b60065481565b600e5481565b600854610100900460ff1681565b60085462010000900460ff1681565b60095481565b60085460ff1681565b60115481565b60085460ff16151560011461059257600080fd5b336000908152600460205260409020548111156105ae57600080fd5b604051339082156108fc029083906000818181858888f193505050501580156105db573d6000803e3d6000fd5b50336000908152600460205260409020546105fc908263ffffffff61110c16565b3360009081526004602052604090205560065461061f908263ffffffff61110c16565b6006819055604080513381526020810184905280820192909252517fdcd7220e3580673dbcb5899da3a05c073c2df48aa178b65b33fec6b43e13a09d9181900360600190a1600d543360009081526004602052604090205410156106d95761068e60013363ffffffff61112316565b50336000818152600460209081526040918290205482519384529083015280517f79586139b58324379448df2efc55fe4634876e66799646ecabe665279eac8e3e9281900390910190a15b50565b600054600160a060020a031633146106f357600080fd5b6008805462ffffff19169055565b60105481565b60085460009062010000900460ff16151560011461072457600080fd5b600e54600090815260056020908152604080832033845290915290205460ff161561074e57600080fd5b61075f60013363ffffffff61126916565b151561076a57600080fd5b600654336000908152600460205260409020546009546107a19291610795919063ffffffff61128816565b9063ffffffff6112b316565b6007549091506107b7908263ffffffff61052016565b600755336000908152600460205260409020546107da908263ffffffff61052016565b33600081815260046020908152604080832094909455600e54825260058152838220838352815290839020805460ff191660011790558251918252810183905281517f1e6476e13208eaabfb4df240debd08374faf3c82dbf157ad79e99f812429bf21929181900390910190a150565b600054600160a060020a0316331461086157600080fd5b601054610877906201518063ffffffff61110c16565b42101561088357600080fd5b6008805462ff00001961ffff1990911661010017169055600b546108ae90429063ffffffff61052016565b60118190556040805160208101929092528082526014828201527f6e65787420736574746c656d656e742074696d650000000000000000000000006060830152516000805160206114078339815191529181900360800190a16040805142815290517fb31d85c8dd6420b94a0301198a31f222bf0121111239360678a05581918363d29181900360200190a1565b600b5481565b600054600160a060020a0316331461095957600080fd5b600160a060020a03821660009081526004602052604090205481111561097e57600080fd5b604051600160a060020a0383169082156108fc029083906000818181858888f193505050501580156109b4573d6000803e3d6000fd5b50600160a060020a0382166000908152600460205260409020546109de908263ffffffff61110c16565b600160a060020a0383166000908152600460205260409020819055600d541115610a6757610a1360018363ffffffff61112316565b50600160a060020a0382166000818152600460209081526040918290205482519384529083015280517f79586139b58324379448df2efc55fe4634876e66799646ecabe665279eac8e3e9281900390910190a15b5050565b600a5481565b600054600160a060020a03163314610a8857600080fd5b600a8190556040805160208101839052818152600c818301527f726169736520706572696f640000000000000000000000000000000000000000606082015290516000805160206114278339815191529181900360800190a150565b600054600160a060020a03163314610afb57600080fd5b60108190556040805160208101839052818152600e818301527f6e657874206c6f636b2074696d65000000000000000000000000000000000000606082015290516000805160206114078339815191529181900360800190a150565b600f5481565b600054600160a060020a03163314610b7457600080fd5b600b8181556040805160208101849052818152808201929092527f6c6f636b20706572696f640000000000000000000000000000000000000000006060830152516000805160206114278339815191529181900360800190a150565b600054600160a060020a03163314610be757600080fd5b600c81905560408051602081018390528181526011818301527f736574746c656d656e7420706572696f64000000000000000000000000000000606082015290516000805160206114278339815191529181900360800190a150565b600054600160a060020a03163314610c5a57600080fd5b601154610c70906201518063ffffffff61110c16565b421015610c7c57600080fd5b6008805462ffffff191662010000179055600c54610ca190429063ffffffff61052016565b600f818155604080516020810193909352808352828101919091527f6e6578742072616973652074696d6500000000000000000000000000000000006060830152516000805160206114078339815191529181900360800190a16040805142815290517f5281dfe0dbeb8cfb053968120a0ecb9da2b12bc2dcc60f9734171a83ec6103339181900360200190a1565b600054600160a060020a03163314610d4757600080fd5b6000600e541115610d7457600f54610d68906201518063ffffffff61110c16565b421015610d7457600080fd5b60088054600160ff19909116811762ffff001916909155600e54610d9791610520565b600e55600a54610dae90429063ffffffff61052016565b601055600754600954610dc69163ffffffff61110c16565b600955600754600654610dde9163ffffffff61052016565b6006556000600755601054604080516020810192909252808252600e828201527f6e657874206c6f636b2074696d650000000000000000000000000000000000006060830152516000805160206114078339815191529181900360800190a16040805142815290517f2c6acffc376bae0dce9f74a673af6142300bd796866c1acec95c70f80d2332829181900360200190a1565b60046020526000908152604090205481565b600054600160a060020a03163314610e9b57600080fd5b601181905560408051602081018390528181526014818301527f6e65787420736574746c656d656e742074696d65000000000000000000000000606082015290516000805160206114078339815191529181900360800190a150565b600054600160a060020a03163314610f0e57600080fd5b600f8181556040805160208101849052818152808201929092527f6e6578742072616973652074696d6500000000000000000000000000000000006060830152516000805160206114078339815191529181900360800190a150565b60075481565b60085460ff161515600114610f8457600080fd5b33600090815260046020526040902054610fa4903463ffffffff61052016565b33600090815260046020526040902055600654610fc7903463ffffffff61052016565b60068190556040805133815234602082015280820192909252517f843f02bcc52ab5b45e8e33b61e593cb6e8f8b5d725107e495cfb41169c020b1a9181900360600190a1600d54336000908152600460205260409020541061107f5761103460013363ffffffff6112ca16565b50336000818152600460209081526040918290205482519384529083015280517f210672d0bc3ee003d955e13c2d9d0a8f32e584d6afd71d9c442d62c93fa388fd9281900390910190a15b565b606061108d6001611359565b90505b90565b600d5481565b600054600160a060020a031633146110b057600080fd5b600d8190556040805160208101839052818152600f818301527f656e6f6465207468726573686f6c640000000000000000000000000000000000606082015290516000805160206114278339815191529181900360800190a150565b60008282111561111857fe5b508082035b92915050565b600160a060020a03811660009081526020839052604081205481908190819060ff1615156111545760009350611260565b600160a060020a038516600090815260208781526040808320805460ff1916905560028901805460018b019093529220549094509250600019840184811061119857fe5b600091825260209091200154600287018054600160a060020a0390921692508291849081106111c357fe5b6000918252602080832091909101805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a0394851617905591831681526001880190915260409020829055600286018054600019850190811061121f57fe5b6000918252602090912001805473ffffffffffffffffffffffffffffffffffffffff191690556002860180549061125a9060001983016113bf565b50600193505b50505092915050565b600160a060020a03166000908152602091909152604090205460ff1690565b60008083151561129b5760009150610533565b508282028284828115156112ab57fe5b041461052f57fe5b60008082848115156112c157fe5b04949350505050565b600160a060020a03811660009081526020839052604081205460ff16156112f35750600061111d565b50600160a060020a0316600081815260208381526040808320805460ff19166001908117909155600286018054968201845291842086905585810182559083529120909201805473ffffffffffffffffffffffffffffffffffffffff1916909117905590565b6060816002018054806020026020016040519081016040528092919081815260200182805480156113b357602002820191906000526020600020905b8154600160a060020a03168152600190910190602001808311611395575b50505050509050919050565b8154818355818111156113e3576000838152602090206113e39181019083016113e8565b505050565b61109091905b8082111561140257600081556001016113ee565b5090560046e55608d5463575e90f64d3ae173372234546746315e0f3574a3bdf35567f9f361737d1051ccafab7e68fcbafe4466aaec6ee5ac4b3eb51447ac84a15cce16da165627a7a723058201052116f45812f47ccec1b13d7b5e55195ed467be0f45af92e51ba85e4f115eb0029`

// DeployReward deploys a new cpchain contract, binding an instance of Reward to it.
func DeployReward(auth *bind.TransactOpts, backend bind.ContractBackend) (common.Address, *types.Transaction, *Reward, error) {
	parsed, err := abi.JSON(strings.NewReader(RewardABI))
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	address, tx, contract, err := bind.DeployContract(auth, parsed, common.FromHex(RewardBin), backend)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &Reward{RewardCaller: RewardCaller{contract: contract}, RewardTransactor: RewardTransactor{contract: contract}, RewardFilterer: RewardFilterer{contract: contract}}, nil
}

// Reward is an auto generated Go binding around an cpchain contract.
type Reward struct {
	RewardCaller     // Read-only binding to the contract
	RewardTransactor // Write-only binding to the contract
	RewardFilterer   // Log filterer for contract events
}

// RewardCaller is an auto generated read-only Go binding around an cpchain contract.
type RewardCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RewardTransactor is an auto generated write-only Go binding around an cpchain contract.
type RewardTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RewardFilterer is an auto generated log filtering Go binding around an cpchain contract events.
type RewardFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// RewardSession is an auto generated Go binding around an cpchain contract,
// with pre-set call and transact options.
type RewardSession struct {
	Contract     *Reward           // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// RewardCallerSession is an auto generated read-only Go binding around an cpchain contract,
// with pre-set call options.
type RewardCallerSession struct {
	Contract *RewardCaller // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts // Call options to use throughout this session
}

// RewardTransactorSession is an auto generated write-only Go binding around an cpchain contract,
// with pre-set transact options.
type RewardTransactorSession struct {
	Contract     *RewardTransactor // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// RewardRaw is an auto generated low-level Go binding around an cpchain contract.
type RewardRaw struct {
	Contract *Reward // Generic contract binding to access the raw methods on
}

// RewardCallerRaw is an auto generated low-level read-only Go binding around an cpchain contract.
type RewardCallerRaw struct {
	Contract *RewardCaller // Generic read-only contract binding to access the raw methods on
}

// RewardTransactorRaw is an auto generated low-level write-only Go binding around an cpchain contract.
type RewardTransactorRaw struct {
	Contract *RewardTransactor // Generic write-only contract binding to access the raw methods on
}

// NewReward creates a new instance of Reward, bound to a specific deployed contract.
func NewReward(address common.Address, backend bind.ContractBackend) (*Reward, error) {
	contract, err := bindReward(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &Reward{RewardCaller: RewardCaller{contract: contract}, RewardTransactor: RewardTransactor{contract: contract}, RewardFilterer: RewardFilterer{contract: contract}}, nil
}

// NewRewardCaller creates a new read-only instance of Reward, bound to a specific deployed contract.
func NewRewardCaller(address common.Address, caller bind.ContractCaller) (*RewardCaller, error) {
	contract, err := bindReward(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &RewardCaller{contract: contract}, nil
}

// NewRewardTransactor creates a new write-only instance of Reward, bound to a specific deployed contract.
func NewRewardTransactor(address common.Address, transactor bind.ContractTransactor) (*RewardTransactor, error) {
	contract, err := bindReward(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &RewardTransactor{contract: contract}, nil
}

// NewRewardFilterer creates a new log filterer instance of Reward, bound to a specific deployed contract.
func NewRewardFilterer(address common.Address, filterer bind.ContractFilterer) (*RewardFilterer, error) {
	contract, err := bindReward(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &RewardFilterer{contract: contract}, nil
}

// bindReward binds a generic wrapper to an already deployed contract.
func bindReward(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := abi.JSON(strings.NewReader(RewardABI))
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Reward *RewardRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Reward.Contract.RewardCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Reward *RewardRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Reward.Contract.RewardTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Reward *RewardRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Reward.Contract.RewardTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_Reward *RewardCallerRaw) Call(opts *bind.CallOpts, result interface{}, method string, params ...interface{}) error {
	return _Reward.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_Reward *RewardTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Reward.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_Reward *RewardTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _Reward.Contract.contract.Transact(opts, method, params...)
}

// BonusPool is a free data retrieval call binding the contract method 0x2693ee80.
//
// Solidity: function bonusPool() constant returns(uint256)
func (_Reward *RewardCaller) BonusPool(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "bonusPool")
	return *ret0, err
}

// BonusPool is a free data retrieval call binding the contract method 0x2693ee80.
//
// Solidity: function bonusPool() constant returns(uint256)
func (_Reward *RewardSession) BonusPool() (*big.Int, error) {
	return _Reward.Contract.BonusPool(&_Reward.CallOpts)
}

// BonusPool is a free data retrieval call binding the contract method 0x2693ee80.
//
// Solidity: function bonusPool() constant returns(uint256)
func (_Reward *RewardCallerSession) BonusPool() (*big.Int, error) {
	return _Reward.Contract.BonusPool(&_Reward.CallOpts)
}

// EnodeThreshold is a free data retrieval call binding the contract method 0xea86298c.
//
// Solidity: function enodeThreshold() constant returns(uint256)
func (_Reward *RewardCaller) EnodeThreshold(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "enodeThreshold")
	return *ret0, err
}

// EnodeThreshold is a free data retrieval call binding the contract method 0xea86298c.
//
// Solidity: function enodeThreshold() constant returns(uint256)
func (_Reward *RewardSession) EnodeThreshold() (*big.Int, error) {
	return _Reward.Contract.EnodeThreshold(&_Reward.CallOpts)
}

// EnodeThreshold is a free data retrieval call binding the contract method 0xea86298c.
//
// Solidity: function enodeThreshold() constant returns(uint256)
func (_Reward *RewardCallerSession) EnodeThreshold() (*big.Int, error) {
	return _Reward.Contract.EnodeThreshold(&_Reward.CallOpts)
}

// GetEnodes is a free data retrieval call binding the contract method 0xde4ff4bf.
//
// Solidity: function getEnodes() constant returns(address[])
func (_Reward *RewardCaller) GetEnodes(opts *bind.CallOpts) ([]common.Address, error) {
	var (
		ret0 = new([]common.Address)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "getEnodes")
	return *ret0, err
}

// GetEnodes is a free data retrieval call binding the contract method 0xde4ff4bf.
//
// Solidity: function getEnodes() constant returns(address[])
func (_Reward *RewardSession) GetEnodes() ([]common.Address, error) {
	return _Reward.Contract.GetEnodes(&_Reward.CallOpts)
}

// GetEnodes is a free data retrieval call binding the contract method 0xde4ff4bf.
//
// Solidity: function getEnodes() constant returns(address[])
func (_Reward *RewardCallerSession) GetEnodes() ([]common.Address, error) {
	return _Reward.Contract.GetEnodes(&_Reward.CallOpts)
}

// InLock is a free data retrieval call binding the contract method 0x197331b8.
//
// Solidity: function inLock() constant returns(bool)
func (_Reward *RewardCaller) InLock(opts *bind.CallOpts) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "inLock")
	return *ret0, err
}

// InLock is a free data retrieval call binding the contract method 0x197331b8.
//
// Solidity: function inLock() constant returns(bool)
func (_Reward *RewardSession) InLock() (bool, error) {
	return _Reward.Contract.InLock(&_Reward.CallOpts)
}

// InLock is a free data retrieval call binding the contract method 0x197331b8.
//
// Solidity: function inLock() constant returns(bool)
func (_Reward *RewardCallerSession) InLock() (bool, error) {
	return _Reward.Contract.InLock(&_Reward.CallOpts)
}

// InRaise is a free data retrieval call binding the contract method 0x273bac0b.
//
// Solidity: function inRaise() constant returns(bool)
func (_Reward *RewardCaller) InRaise(opts *bind.CallOpts) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "inRaise")
	return *ret0, err
}

// InRaise is a free data retrieval call binding the contract method 0x273bac0b.
//
// Solidity: function inRaise() constant returns(bool)
func (_Reward *RewardSession) InRaise() (bool, error) {
	return _Reward.Contract.InRaise(&_Reward.CallOpts)
}

// InRaise is a free data retrieval call binding the contract method 0x273bac0b.
//
// Solidity: function inRaise() constant returns(bool)
func (_Reward *RewardCallerSession) InRaise() (bool, error) {
	return _Reward.Contract.InRaise(&_Reward.CallOpts)
}

// InSettlement is a free data retrieval call binding the contract method 0x24eceaf6.
//
// Solidity: function inSettlement() constant returns(bool)
func (_Reward *RewardCaller) InSettlement(opts *bind.CallOpts) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "inSettlement")
	return *ret0, err
}

// InSettlement is a free data retrieval call binding the contract method 0x24eceaf6.
//
// Solidity: function inSettlement() constant returns(bool)
func (_Reward *RewardSession) InSettlement() (bool, error) {
	return _Reward.Contract.InSettlement(&_Reward.CallOpts)
}

// InSettlement is a free data retrieval call binding the contract method 0x24eceaf6.
//
// Solidity: function inSettlement() constant returns(bool)
func (_Reward *RewardCallerSession) InSettlement() (bool, error) {
	return _Reward.Contract.InSettlement(&_Reward.CallOpts)
}

// Investments is a free data retrieval call binding the contract method 0x96b98862.
//
// Solidity: function investments( address) constant returns(uint256)
func (_Reward *RewardCaller) Investments(opts *bind.CallOpts, arg0 common.Address) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "investments", arg0)
	return *ret0, err
}

// Investments is a free data retrieval call binding the contract method 0x96b98862.
//
// Solidity: function investments( address) constant returns(uint256)
func (_Reward *RewardSession) Investments(arg0 common.Address) (*big.Int, error) {
	return _Reward.Contract.Investments(&_Reward.CallOpts, arg0)
}

// Investments is a free data retrieval call binding the contract method 0x96b98862.
//
// Solidity: function investments( address) constant returns(uint256)
func (_Reward *RewardCallerSession) Investments(arg0 common.Address) (*big.Int, error) {
	return _Reward.Contract.Investments(&_Reward.CallOpts, arg0)
}

// LockPeriod is a free data retrieval call binding the contract method 0x3fd8b02f.
//
// Solidity: function lockPeriod() constant returns(uint256)
func (_Reward *RewardCaller) LockPeriod(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "lockPeriod")
	return *ret0, err
}

// LockPeriod is a free data retrieval call binding the contract method 0x3fd8b02f.
//
// Solidity: function lockPeriod() constant returns(uint256)
func (_Reward *RewardSession) LockPeriod() (*big.Int, error) {
	return _Reward.Contract.LockPeriod(&_Reward.CallOpts)
}

// LockPeriod is a free data retrieval call binding the contract method 0x3fd8b02f.
//
// Solidity: function lockPeriod() constant returns(uint256)
func (_Reward *RewardCallerSession) LockPeriod() (*big.Int, error) {
	return _Reward.Contract.LockPeriod(&_Reward.CallOpts)
}

// NextLockTime is a free data retrieval call binding the contract method 0x3086f3a4.
//
// Solidity: function nextLockTime() constant returns(uint256)
func (_Reward *RewardCaller) NextLockTime(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "nextLockTime")
	return *ret0, err
}

// NextLockTime is a free data retrieval call binding the contract method 0x3086f3a4.
//
// Solidity: function nextLockTime() constant returns(uint256)
func (_Reward *RewardSession) NextLockTime() (*big.Int, error) {
	return _Reward.Contract.NextLockTime(&_Reward.CallOpts)
}

// NextLockTime is a free data retrieval call binding the contract method 0x3086f3a4.
//
// Solidity: function nextLockTime() constant returns(uint256)
func (_Reward *RewardCallerSession) NextLockTime() (*big.Int, error) {
	return _Reward.Contract.NextLockTime(&_Reward.CallOpts)
}

// NextRaiseTime is a free data retrieval call binding the contract method 0x6e216366.
//
// Solidity: function nextRaiseTime() constant returns(uint256)
func (_Reward *RewardCaller) NextRaiseTime(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "nextRaiseTime")
	return *ret0, err
}

// NextRaiseTime is a free data retrieval call binding the contract method 0x6e216366.
//
// Solidity: function nextRaiseTime() constant returns(uint256)
func (_Reward *RewardSession) NextRaiseTime() (*big.Int, error) {
	return _Reward.Contract.NextRaiseTime(&_Reward.CallOpts)
}

// NextRaiseTime is a free data retrieval call binding the contract method 0x6e216366.
//
// Solidity: function nextRaiseTime() constant returns(uint256)
func (_Reward *RewardCallerSession) NextRaiseTime() (*big.Int, error) {
	return _Reward.Contract.NextRaiseTime(&_Reward.CallOpts)
}

// NextSettlementTime is a free data retrieval call binding the contract method 0x2b024aaf.
//
// Solidity: function nextSettlementTime() constant returns(uint256)
func (_Reward *RewardCaller) NextSettlementTime(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "nextSettlementTime")
	return *ret0, err
}

// NextSettlementTime is a free data retrieval call binding the contract method 0x2b024aaf.
//
// Solidity: function nextSettlementTime() constant returns(uint256)
func (_Reward *RewardSession) NextSettlementTime() (*big.Int, error) {
	return _Reward.Contract.NextSettlementTime(&_Reward.CallOpts)
}

// NextSettlementTime is a free data retrieval call binding the contract method 0x2b024aaf.
//
// Solidity: function nextSettlementTime() constant returns(uint256)
func (_Reward *RewardCallerSession) NextSettlementTime() (*big.Int, error) {
	return _Reward.Contract.NextSettlementTime(&_Reward.CallOpts)
}

// RaisePeriod is a free data retrieval call binding the contract method 0x4618d9d2.
//
// Solidity: function raisePeriod() constant returns(uint256)
func (_Reward *RewardCaller) RaisePeriod(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "raisePeriod")
	return *ret0, err
}

// RaisePeriod is a free data retrieval call binding the contract method 0x4618d9d2.
//
// Solidity: function raisePeriod() constant returns(uint256)
func (_Reward *RewardSession) RaisePeriod() (*big.Int, error) {
	return _Reward.Contract.RaisePeriod(&_Reward.CallOpts)
}

// RaisePeriod is a free data retrieval call binding the contract method 0x4618d9d2.
//
// Solidity: function raisePeriod() constant returns(uint256)
func (_Reward *RewardCallerSession) RaisePeriod() (*big.Int, error) {
	return _Reward.Contract.RaisePeriod(&_Reward.CallOpts)
}

// Round is a free data retrieval call binding the contract method 0x146ca531.
//
// Solidity: function round() constant returns(uint256)
func (_Reward *RewardCaller) Round(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "round")
	return *ret0, err
}

// Round is a free data retrieval call binding the contract method 0x146ca531.
//
// Solidity: function round() constant returns(uint256)
func (_Reward *RewardSession) Round() (*big.Int, error) {
	return _Reward.Contract.Round(&_Reward.CallOpts)
}

// Round is a free data retrieval call binding the contract method 0x146ca531.
//
// Solidity: function round() constant returns(uint256)
func (_Reward *RewardCallerSession) Round() (*big.Int, error) {
	return _Reward.Contract.Round(&_Reward.CallOpts)
}

// SettlementPeriod is a free data retrieval call binding the contract method 0x0f1071be.
//
// Solidity: function settlementPeriod() constant returns(uint256)
func (_Reward *RewardCaller) SettlementPeriod(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "settlementPeriod")
	return *ret0, err
}

// SettlementPeriod is a free data retrieval call binding the contract method 0x0f1071be.
//
// Solidity: function settlementPeriod() constant returns(uint256)
func (_Reward *RewardSession) SettlementPeriod() (*big.Int, error) {
	return _Reward.Contract.SettlementPeriod(&_Reward.CallOpts)
}

// SettlementPeriod is a free data retrieval call binding the contract method 0x0f1071be.
//
// Solidity: function settlementPeriod() constant returns(uint256)
func (_Reward *RewardCallerSession) SettlementPeriod() (*big.Int, error) {
	return _Reward.Contract.SettlementPeriod(&_Reward.CallOpts)
}

// TotalInterest is a free data retrieval call binding the contract method 0xbc7a36d6.
//
// Solidity: function totalInterest() constant returns(uint256)
func (_Reward *RewardCaller) TotalInterest(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "totalInterest")
	return *ret0, err
}

// TotalInterest is a free data retrieval call binding the contract method 0xbc7a36d6.
//
// Solidity: function totalInterest() constant returns(uint256)
func (_Reward *RewardSession) TotalInterest() (*big.Int, error) {
	return _Reward.Contract.TotalInterest(&_Reward.CallOpts)
}

// TotalInterest is a free data retrieval call binding the contract method 0xbc7a36d6.
//
// Solidity: function totalInterest() constant returns(uint256)
func (_Reward *RewardCallerSession) TotalInterest() (*big.Int, error) {
	return _Reward.Contract.TotalInterest(&_Reward.CallOpts)
}

// TotalInvestment is a free data retrieval call binding the contract method 0x10ea13df.
//
// Solidity: function totalInvestment() constant returns(uint256)
func (_Reward *RewardCaller) TotalInvestment(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "totalInvestment")
	return *ret0, err
}

// TotalInvestment is a free data retrieval call binding the contract method 0x10ea13df.
//
// Solidity: function totalInvestment() constant returns(uint256)
func (_Reward *RewardSession) TotalInvestment() (*big.Int, error) {
	return _Reward.Contract.TotalInvestment(&_Reward.CallOpts)
}

// TotalInvestment is a free data retrieval call binding the contract method 0x10ea13df.
//
// Solidity: function totalInvestment() constant returns(uint256)
func (_Reward *RewardCallerSession) TotalInvestment() (*big.Int, error) {
	return _Reward.Contract.TotalInvestment(&_Reward.CallOpts)
}

// ClaimInterest is a paid mutator transaction binding the contract method 0x35981fd8.
//
// Solidity: function claimInterest() returns()
func (_Reward *RewardTransactor) ClaimInterest(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "claimInterest")
}

// ClaimInterest is a paid mutator transaction binding the contract method 0x35981fd8.
//
// Solidity: function claimInterest() returns()
func (_Reward *RewardSession) ClaimInterest() (*types.Transaction, error) {
	return _Reward.Contract.ClaimInterest(&_Reward.TransactOpts)
}

// ClaimInterest is a paid mutator transaction binding the contract method 0x35981fd8.
//
// Solidity: function claimInterest() returns()
func (_Reward *RewardTransactorSession) ClaimInterest() (*types.Transaction, error) {
	return _Reward.Contract.ClaimInterest(&_Reward.TransactOpts)
}

// Deposit is a paid mutator transaction binding the contract method 0xd0e30db0.
//
// Solidity: function deposit() returns()
func (_Reward *RewardTransactor) Deposit(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "deposit")
}

// Deposit is a paid mutator transaction binding the contract method 0xd0e30db0.
//
// Solidity: function deposit() returns()
func (_Reward *RewardSession) Deposit() (*types.Transaction, error) {
	return _Reward.Contract.Deposit(&_Reward.TransactOpts)
}

// Deposit is a paid mutator transaction binding the contract method 0xd0e30db0.
//
// Solidity: function deposit() returns()
func (_Reward *RewardTransactorSession) Deposit() (*types.Transaction, error) {
	return _Reward.Contract.Deposit(&_Reward.TransactOpts)
}

// Disable is a paid mutator transaction binding the contract method 0x2f2770db.
//
// Solidity: function disable() returns()
func (_Reward *RewardTransactor) Disable(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "disable")
}

// Disable is a paid mutator transaction binding the contract method 0x2f2770db.
//
// Solidity: function disable() returns()
func (_Reward *RewardSession) Disable() (*types.Transaction, error) {
	return _Reward.Contract.Disable(&_Reward.TransactOpts)
}

// Disable is a paid mutator transaction binding the contract method 0x2f2770db.
//
// Solidity: function disable() returns()
func (_Reward *RewardTransactorSession) Disable() (*types.Transaction, error) {
	return _Reward.Contract.Disable(&_Reward.TransactOpts)
}

// NewLock is a paid mutator transaction binding the contract method 0x363245e1.
//
// Solidity: function newLock() returns()
func (_Reward *RewardTransactor) NewLock(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "newLock")
}

// NewLock is a paid mutator transaction binding the contract method 0x363245e1.
//
// Solidity: function newLock() returns()
func (_Reward *RewardSession) NewLock() (*types.Transaction, error) {
	return _Reward.Contract.NewLock(&_Reward.TransactOpts)
}

// NewLock is a paid mutator transaction binding the contract method 0x363245e1.
//
// Solidity: function newLock() returns()
func (_Reward *RewardTransactorSession) NewLock() (*types.Transaction, error) {
	return _Reward.Contract.NewLock(&_Reward.TransactOpts)
}

// NewRaise is a paid mutator transaction binding the contract method 0x8f83bc7f.
//
// Solidity: function newRaise() returns()
func (_Reward *RewardTransactor) NewRaise(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "newRaise")
}

// NewRaise is a paid mutator transaction binding the contract method 0x8f83bc7f.
//
// Solidity: function newRaise() returns()
func (_Reward *RewardSession) NewRaise() (*types.Transaction, error) {
	return _Reward.Contract.NewRaise(&_Reward.TransactOpts)
}

// NewRaise is a paid mutator transaction binding the contract method 0x8f83bc7f.
//
// Solidity: function newRaise() returns()
func (_Reward *RewardTransactorSession) NewRaise() (*types.Transaction, error) {
	return _Reward.Contract.NewRaise(&_Reward.TransactOpts)
}

// NewSettlement is a paid mutator transaction binding the contract method 0x8baaf031.
//
// Solidity: function newSettlement() returns()
func (_Reward *RewardTransactor) NewSettlement(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "newSettlement")
}

// NewSettlement is a paid mutator transaction binding the contract method 0x8baaf031.
//
// Solidity: function newSettlement() returns()
func (_Reward *RewardSession) NewSettlement() (*types.Transaction, error) {
	return _Reward.Contract.NewSettlement(&_Reward.TransactOpts)
}

// NewSettlement is a paid mutator transaction binding the contract method 0x8baaf031.
//
// Solidity: function newSettlement() returns()
func (_Reward *RewardTransactorSession) NewSettlement() (*types.Transaction, error) {
	return _Reward.Contract.NewSettlement(&_Reward.TransactOpts)
}

// Refund is a paid mutator transaction binding the contract method 0x410085df.
//
// Solidity: function refund(investor address, amount uint256) returns()
func (_Reward *RewardTransactor) Refund(opts *bind.TransactOpts, investor common.Address, amount *big.Int) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "refund", investor, amount)
}

// Refund is a paid mutator transaction binding the contract method 0x410085df.
//
// Solidity: function refund(investor address, amount uint256) returns()
func (_Reward *RewardSession) Refund(investor common.Address, amount *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.Refund(&_Reward.TransactOpts, investor, amount)
}

// Refund is a paid mutator transaction binding the contract method 0x410085df.
//
// Solidity: function refund(investor address, amount uint256) returns()
func (_Reward *RewardTransactorSession) Refund(investor common.Address, amount *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.Refund(&_Reward.TransactOpts, investor, amount)
}

// SetEnodeThreshold is a paid mutator transaction binding the contract method 0xec9f105f.
//
// Solidity: function setEnodeThreshold(_enodeThreshold uint256) returns()
func (_Reward *RewardTransactor) SetEnodeThreshold(opts *bind.TransactOpts, _enodeThreshold *big.Int) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "setEnodeThreshold", _enodeThreshold)
}

// SetEnodeThreshold is a paid mutator transaction binding the contract method 0xec9f105f.
//
// Solidity: function setEnodeThreshold(_enodeThreshold uint256) returns()
func (_Reward *RewardSession) SetEnodeThreshold(_enodeThreshold *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetEnodeThreshold(&_Reward.TransactOpts, _enodeThreshold)
}

// SetEnodeThreshold is a paid mutator transaction binding the contract method 0xec9f105f.
//
// Solidity: function setEnodeThreshold(_enodeThreshold uint256) returns()
func (_Reward *RewardTransactorSession) SetEnodeThreshold(_enodeThreshold *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetEnodeThreshold(&_Reward.TransactOpts, _enodeThreshold)
}

// SetLockPeriod is a paid mutator transaction binding the contract method 0x779972da.
//
// Solidity: function setLockPeriod(_lockPeriod uint256) returns()
func (_Reward *RewardTransactor) SetLockPeriod(opts *bind.TransactOpts, _lockPeriod *big.Int) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "setLockPeriod", _lockPeriod)
}

// SetLockPeriod is a paid mutator transaction binding the contract method 0x779972da.
//
// Solidity: function setLockPeriod(_lockPeriod uint256) returns()
func (_Reward *RewardSession) SetLockPeriod(_lockPeriod *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetLockPeriod(&_Reward.TransactOpts, _lockPeriod)
}

// SetLockPeriod is a paid mutator transaction binding the contract method 0x779972da.
//
// Solidity: function setLockPeriod(_lockPeriod uint256) returns()
func (_Reward *RewardTransactorSession) SetLockPeriod(_lockPeriod *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetLockPeriod(&_Reward.TransactOpts, _lockPeriod)
}

// SetNextLockTime is a paid mutator transaction binding the contract method 0x64f44c0b.
//
// Solidity: function setNextLockTime(_nextLockTime uint256) returns()
func (_Reward *RewardTransactor) SetNextLockTime(opts *bind.TransactOpts, _nextLockTime *big.Int) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "setNextLockTime", _nextLockTime)
}

// SetNextLockTime is a paid mutator transaction binding the contract method 0x64f44c0b.
//
// Solidity: function setNextLockTime(_nextLockTime uint256) returns()
func (_Reward *RewardSession) SetNextLockTime(_nextLockTime *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetNextLockTime(&_Reward.TransactOpts, _nextLockTime)
}

// SetNextLockTime is a paid mutator transaction binding the contract method 0x64f44c0b.
//
// Solidity: function setNextLockTime(_nextLockTime uint256) returns()
func (_Reward *RewardTransactorSession) SetNextLockTime(_nextLockTime *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetNextLockTime(&_Reward.TransactOpts, _nextLockTime)
}

// SetNextRaiseTime is a paid mutator transaction binding the contract method 0xa19046e3.
//
// Solidity: function setNextRaiseTime(_nextRaiseTime uint256) returns()
func (_Reward *RewardTransactor) SetNextRaiseTime(opts *bind.TransactOpts, _nextRaiseTime *big.Int) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "setNextRaiseTime", _nextRaiseTime)
}

// SetNextRaiseTime is a paid mutator transaction binding the contract method 0xa19046e3.
//
// Solidity: function setNextRaiseTime(_nextRaiseTime uint256) returns()
func (_Reward *RewardSession) SetNextRaiseTime(_nextRaiseTime *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetNextRaiseTime(&_Reward.TransactOpts, _nextRaiseTime)
}

// SetNextRaiseTime is a paid mutator transaction binding the contract method 0xa19046e3.
//
// Solidity: function setNextRaiseTime(_nextRaiseTime uint256) returns()
func (_Reward *RewardTransactorSession) SetNextRaiseTime(_nextRaiseTime *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetNextRaiseTime(&_Reward.TransactOpts, _nextRaiseTime)
}

// SetNextSettlementTime is a paid mutator transaction binding the contract method 0x9d63e6e6.
//
// Solidity: function setNextSettlementTime(_nextSettlementTime uint256) returns()
func (_Reward *RewardTransactor) SetNextSettlementTime(opts *bind.TransactOpts, _nextSettlementTime *big.Int) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "setNextSettlementTime", _nextSettlementTime)
}

// SetNextSettlementTime is a paid mutator transaction binding the contract method 0x9d63e6e6.
//
// Solidity: function setNextSettlementTime(_nextSettlementTime uint256) returns()
func (_Reward *RewardSession) SetNextSettlementTime(_nextSettlementTime *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetNextSettlementTime(&_Reward.TransactOpts, _nextSettlementTime)
}

// SetNextSettlementTime is a paid mutator transaction binding the contract method 0x9d63e6e6.
//
// Solidity: function setNextSettlementTime(_nextSettlementTime uint256) returns()
func (_Reward *RewardTransactorSession) SetNextSettlementTime(_nextSettlementTime *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetNextSettlementTime(&_Reward.TransactOpts, _nextSettlementTime)
}

// SetRaisePeriod is a paid mutator transaction binding the contract method 0x491fcdea.
//
// Solidity: function setRaisePeriod(_raisePeriod uint256) returns()
func (_Reward *RewardTransactor) SetRaisePeriod(opts *bind.TransactOpts, _raisePeriod *big.Int) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "setRaisePeriod", _raisePeriod)
}

// SetRaisePeriod is a paid mutator transaction binding the contract method 0x491fcdea.
//
// Solidity: function setRaisePeriod(_raisePeriod uint256) returns()
func (_Reward *RewardSession) SetRaisePeriod(_raisePeriod *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetRaisePeriod(&_Reward.TransactOpts, _raisePeriod)
}

// SetRaisePeriod is a paid mutator transaction binding the contract method 0x491fcdea.
//
// Solidity: function setRaisePeriod(_raisePeriod uint256) returns()
func (_Reward *RewardTransactorSession) SetRaisePeriod(_raisePeriod *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetRaisePeriod(&_Reward.TransactOpts, _raisePeriod)
}

// SetSettlementPeriod is a paid mutator transaction binding the contract method 0x8072a022.
//
// Solidity: function setSettlementPeriod(_settlementPeriod uint256) returns()
func (_Reward *RewardTransactor) SetSettlementPeriod(opts *bind.TransactOpts, _settlementPeriod *big.Int) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "setSettlementPeriod", _settlementPeriod)
}

// SetSettlementPeriod is a paid mutator transaction binding the contract method 0x8072a022.
//
// Solidity: function setSettlementPeriod(_settlementPeriod uint256) returns()
func (_Reward *RewardSession) SetSettlementPeriod(_settlementPeriod *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetSettlementPeriod(&_Reward.TransactOpts, _settlementPeriod)
}

// SetSettlementPeriod is a paid mutator transaction binding the contract method 0x8072a022.
//
// Solidity: function setSettlementPeriod(_settlementPeriod uint256) returns()
func (_Reward *RewardTransactorSession) SetSettlementPeriod(_settlementPeriod *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetSettlementPeriod(&_Reward.TransactOpts, _settlementPeriod)
}

// Withdraw is a paid mutator transaction binding the contract method 0x2e1a7d4d.
//
// Solidity: function withdraw(amount uint256) returns()
func (_Reward *RewardTransactor) Withdraw(opts *bind.TransactOpts, amount *big.Int) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "withdraw", amount)
}

// Withdraw is a paid mutator transaction binding the contract method 0x2e1a7d4d.
//
// Solidity: function withdraw(amount uint256) returns()
func (_Reward *RewardSession) Withdraw(amount *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.Withdraw(&_Reward.TransactOpts, amount)
}

// Withdraw is a paid mutator transaction binding the contract method 0x2e1a7d4d.
//
// Solidity: function withdraw(amount uint256) returns()
func (_Reward *RewardTransactorSession) Withdraw(amount *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.Withdraw(&_Reward.TransactOpts, amount)
}

// RewardAddInvestmentIterator is returned from FilterAddInvestment and is used to iterate over the raw logs and unpacked data for AddInvestment events raised by the Reward contract.
type RewardAddInvestmentIterator struct {
	Event *RewardAddInvestment // Event containing the contract specifics and raw log

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
func (it *RewardAddInvestmentIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardAddInvestment)
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
		it.Event = new(RewardAddInvestment)
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
func (it *RewardAddInvestmentIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardAddInvestmentIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardAddInvestment represents a AddInvestment event raised by the Reward contract.
type RewardAddInvestment struct {
	Who    common.Address
	Amount *big.Int
	Total  *big.Int
	Raw    types.Log // Blockchain specific contextual infos
}

// FilterAddInvestment is a free log retrieval operation binding the contract event 0x843f02bcc52ab5b45e8e33b61e593cb6e8f8b5d725107e495cfb41169c020b1a.
//
// Solidity: e AddInvestment(who address, amount uint256, total uint256)
func (_Reward *RewardFilterer) FilterAddInvestment(opts *bind.FilterOpts) (*RewardAddInvestmentIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "AddInvestment")
	if err != nil {
		return nil, err
	}
	return &RewardAddInvestmentIterator{contract: _Reward.contract, event: "AddInvestment", logs: logs, sub: sub}, nil
}

// WatchAddInvestment is a free log subscription operation binding the contract event 0x843f02bcc52ab5b45e8e33b61e593cb6e8f8b5d725107e495cfb41169c020b1a.
//
// Solidity: e AddInvestment(who address, amount uint256, total uint256)
func (_Reward *RewardFilterer) WatchAddInvestment(opts *bind.WatchOpts, sink chan<- *RewardAddInvestment) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "AddInvestment")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardAddInvestment)
				if err := _Reward.contract.UnpackLog(event, "AddInvestment", log); err != nil {
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

// RewardApplyForSettlementIterator is returned from FilterApplyForSettlement and is used to iterate over the raw logs and unpacked data for ApplyForSettlement events raised by the Reward contract.
type RewardApplyForSettlementIterator struct {
	Event *RewardApplyForSettlement // Event containing the contract specifics and raw log

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
func (it *RewardApplyForSettlementIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardApplyForSettlement)
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
		it.Event = new(RewardApplyForSettlement)
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
func (it *RewardApplyForSettlementIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardApplyForSettlementIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardApplyForSettlement represents a ApplyForSettlement event raised by the Reward contract.
type RewardApplyForSettlement struct {
	Who    common.Address
	Income *big.Int
	Raw    types.Log // Blockchain specific contextual infos
}

// FilterApplyForSettlement is a free log retrieval operation binding the contract event 0x1e6476e13208eaabfb4df240debd08374faf3c82dbf157ad79e99f812429bf21.
//
// Solidity: e ApplyForSettlement(who address, income uint256)
func (_Reward *RewardFilterer) FilterApplyForSettlement(opts *bind.FilterOpts) (*RewardApplyForSettlementIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "ApplyForSettlement")
	if err != nil {
		return nil, err
	}
	return &RewardApplyForSettlementIterator{contract: _Reward.contract, event: "ApplyForSettlement", logs: logs, sub: sub}, nil
}

// WatchApplyForSettlement is a free log subscription operation binding the contract event 0x1e6476e13208eaabfb4df240debd08374faf3c82dbf157ad79e99f812429bf21.
//
// Solidity: e ApplyForSettlement(who address, income uint256)
func (_Reward *RewardFilterer) WatchApplyForSettlement(opts *bind.WatchOpts, sink chan<- *RewardApplyForSettlement) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "ApplyForSettlement")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardApplyForSettlement)
				if err := _Reward.contract.UnpackLog(event, "ApplyForSettlement", log); err != nil {
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

// RewardEnodeQuitIterator is returned from FilterEnodeQuit and is used to iterate over the raw logs and unpacked data for EnodeQuit events raised by the Reward contract.
type RewardEnodeQuitIterator struct {
	Event *RewardEnodeQuit // Event containing the contract specifics and raw log

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
func (it *RewardEnodeQuitIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardEnodeQuit)
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
		it.Event = new(RewardEnodeQuit)
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
func (it *RewardEnodeQuitIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardEnodeQuitIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardEnodeQuit represents a EnodeQuit event raised by the Reward contract.
type RewardEnodeQuit struct {
	Who     common.Address
	Balance *big.Int
	Raw     types.Log // Blockchain specific contextual infos
}

// FilterEnodeQuit is a free log retrieval operation binding the contract event 0x79586139b58324379448df2efc55fe4634876e66799646ecabe665279eac8e3e.
//
// Solidity: e EnodeQuit(who address, balance uint256)
func (_Reward *RewardFilterer) FilterEnodeQuit(opts *bind.FilterOpts) (*RewardEnodeQuitIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "EnodeQuit")
	if err != nil {
		return nil, err
	}
	return &RewardEnodeQuitIterator{contract: _Reward.contract, event: "EnodeQuit", logs: logs, sub: sub}, nil
}

// WatchEnodeQuit is a free log subscription operation binding the contract event 0x79586139b58324379448df2efc55fe4634876e66799646ecabe665279eac8e3e.
//
// Solidity: e EnodeQuit(who address, balance uint256)
func (_Reward *RewardFilterer) WatchEnodeQuit(opts *bind.WatchOpts, sink chan<- *RewardEnodeQuit) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "EnodeQuit")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardEnodeQuit)
				if err := _Reward.contract.UnpackLog(event, "EnodeQuit", log); err != nil {
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

// RewardFundBonusPoolIterator is returned from FilterFundBonusPool and is used to iterate over the raw logs and unpacked data for FundBonusPool events raised by the Reward contract.
type RewardFundBonusPoolIterator struct {
	Event *RewardFundBonusPool // Event containing the contract specifics and raw log

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
func (it *RewardFundBonusPoolIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardFundBonusPool)
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
		it.Event = new(RewardFundBonusPool)
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
func (it *RewardFundBonusPoolIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardFundBonusPoolIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardFundBonusPool represents a FundBonusPool event raised by the Reward contract.
type RewardFundBonusPool struct {
	Who    common.Address
	Amount *big.Int
	Total  *big.Int
	Raw    types.Log // Blockchain specific contextual infos
}

// FilterFundBonusPool is a free log retrieval operation binding the contract event 0xa1610f5f05db2d5caefef4f1bb2d913438a2fdb236ebc0ceedfacb398af1955b.
//
// Solidity: e FundBonusPool(who address, amount uint256, total uint256)
func (_Reward *RewardFilterer) FilterFundBonusPool(opts *bind.FilterOpts) (*RewardFundBonusPoolIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "FundBonusPool")
	if err != nil {
		return nil, err
	}
	return &RewardFundBonusPoolIterator{contract: _Reward.contract, event: "FundBonusPool", logs: logs, sub: sub}, nil
}

// WatchFundBonusPool is a free log subscription operation binding the contract event 0xa1610f5f05db2d5caefef4f1bb2d913438a2fdb236ebc0ceedfacb398af1955b.
//
// Solidity: e FundBonusPool(who address, amount uint256, total uint256)
func (_Reward *RewardFilterer) WatchFundBonusPool(opts *bind.WatchOpts, sink chan<- *RewardFundBonusPool) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "FundBonusPool")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardFundBonusPool)
				if err := _Reward.contract.UnpackLog(event, "FundBonusPool", log); err != nil {
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

// RewardNewEnodeIterator is returned from FilterNewEnode and is used to iterate over the raw logs and unpacked data for NewEnode events raised by the Reward contract.
type RewardNewEnodeIterator struct {
	Event *RewardNewEnode // Event containing the contract specifics and raw log

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
func (it *RewardNewEnodeIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardNewEnode)
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
		it.Event = new(RewardNewEnode)
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
func (it *RewardNewEnodeIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardNewEnodeIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardNewEnode represents a NewEnode event raised by the Reward contract.
type RewardNewEnode struct {
	Who        common.Address
	Investment *big.Int
	Raw        types.Log // Blockchain specific contextual infos
}

// FilterNewEnode is a free log retrieval operation binding the contract event 0x210672d0bc3ee003d955e13c2d9d0a8f32e584d6afd71d9c442d62c93fa388fd.
//
// Solidity: e NewEnode(who address, investment uint256)
func (_Reward *RewardFilterer) FilterNewEnode(opts *bind.FilterOpts) (*RewardNewEnodeIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "NewEnode")
	if err != nil {
		return nil, err
	}
	return &RewardNewEnodeIterator{contract: _Reward.contract, event: "NewEnode", logs: logs, sub: sub}, nil
}

// WatchNewEnode is a free log subscription operation binding the contract event 0x210672d0bc3ee003d955e13c2d9d0a8f32e584d6afd71d9c442d62c93fa388fd.
//
// Solidity: e NewEnode(who address, investment uint256)
func (_Reward *RewardFilterer) WatchNewEnode(opts *bind.WatchOpts, sink chan<- *RewardNewEnode) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "NewEnode")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardNewEnode)
				if err := _Reward.contract.UnpackLog(event, "NewEnode", log); err != nil {
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

// RewardNewLockIterator is returned from FilterNewLock and is used to iterate over the raw logs and unpacked data for NewLock events raised by the Reward contract.
type RewardNewLockIterator struct {
	Event *RewardNewLock // Event containing the contract specifics and raw log

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
func (it *RewardNewLockIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardNewLock)
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
		it.Event = new(RewardNewLock)
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
func (it *RewardNewLockIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardNewLockIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardNewLock represents a NewLock event raised by the Reward contract.
type RewardNewLock struct {
	When *big.Int
	Raw  types.Log // Blockchain specific contextual infos
}

// FilterNewLock is a free log retrieval operation binding the contract event 0xb31d85c8dd6420b94a0301198a31f222bf0121111239360678a05581918363d2.
//
// Solidity: e NewLock(when uint256)
func (_Reward *RewardFilterer) FilterNewLock(opts *bind.FilterOpts) (*RewardNewLockIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "NewLock")
	if err != nil {
		return nil, err
	}
	return &RewardNewLockIterator{contract: _Reward.contract, event: "NewLock", logs: logs, sub: sub}, nil
}

// WatchNewLock is a free log subscription operation binding the contract event 0xb31d85c8dd6420b94a0301198a31f222bf0121111239360678a05581918363d2.
//
// Solidity: e NewLock(when uint256)
func (_Reward *RewardFilterer) WatchNewLock(opts *bind.WatchOpts, sink chan<- *RewardNewLock) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "NewLock")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardNewLock)
				if err := _Reward.contract.UnpackLog(event, "NewLock", log); err != nil {
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

// RewardNewRaiseIterator is returned from FilterNewRaise and is used to iterate over the raw logs and unpacked data for NewRaise events raised by the Reward contract.
type RewardNewRaiseIterator struct {
	Event *RewardNewRaise // Event containing the contract specifics and raw log

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
func (it *RewardNewRaiseIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardNewRaise)
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
		it.Event = new(RewardNewRaise)
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
func (it *RewardNewRaiseIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardNewRaiseIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardNewRaise represents a NewRaise event raised by the Reward contract.
type RewardNewRaise struct {
	When *big.Int
	Raw  types.Log // Blockchain specific contextual infos
}

// FilterNewRaise is a free log retrieval operation binding the contract event 0x2c6acffc376bae0dce9f74a673af6142300bd796866c1acec95c70f80d233282.
//
// Solidity: e NewRaise(when uint256)
func (_Reward *RewardFilterer) FilterNewRaise(opts *bind.FilterOpts) (*RewardNewRaiseIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "NewRaise")
	if err != nil {
		return nil, err
	}
	return &RewardNewRaiseIterator{contract: _Reward.contract, event: "NewRaise", logs: logs, sub: sub}, nil
}

// WatchNewRaise is a free log subscription operation binding the contract event 0x2c6acffc376bae0dce9f74a673af6142300bd796866c1acec95c70f80d233282.
//
// Solidity: e NewRaise(when uint256)
func (_Reward *RewardFilterer) WatchNewRaise(opts *bind.WatchOpts, sink chan<- *RewardNewRaise) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "NewRaise")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardNewRaise)
				if err := _Reward.contract.UnpackLog(event, "NewRaise", log); err != nil {
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

// RewardNewSettlementIterator is returned from FilterNewSettlement and is used to iterate over the raw logs and unpacked data for NewSettlement events raised by the Reward contract.
type RewardNewSettlementIterator struct {
	Event *RewardNewSettlement // Event containing the contract specifics and raw log

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
func (it *RewardNewSettlementIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardNewSettlement)
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
		it.Event = new(RewardNewSettlement)
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
func (it *RewardNewSettlementIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardNewSettlementIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardNewSettlement represents a NewSettlement event raised by the Reward contract.
type RewardNewSettlement struct {
	When *big.Int
	Raw  types.Log // Blockchain specific contextual infos
}

// FilterNewSettlement is a free log retrieval operation binding the contract event 0x5281dfe0dbeb8cfb053968120a0ecb9da2b12bc2dcc60f9734171a83ec610333.
//
// Solidity: e NewSettlement(when uint256)
func (_Reward *RewardFilterer) FilterNewSettlement(opts *bind.FilterOpts) (*RewardNewSettlementIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "NewSettlement")
	if err != nil {
		return nil, err
	}
	return &RewardNewSettlementIterator{contract: _Reward.contract, event: "NewSettlement", logs: logs, sub: sub}, nil
}

// WatchNewSettlement is a free log subscription operation binding the contract event 0x5281dfe0dbeb8cfb053968120a0ecb9da2b12bc2dcc60f9734171a83ec610333.
//
// Solidity: e NewSettlement(when uint256)
func (_Reward *RewardFilterer) WatchNewSettlement(opts *bind.WatchOpts, sink chan<- *RewardNewSettlement) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "NewSettlement")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardNewSettlement)
				if err := _Reward.contract.UnpackLog(event, "NewSettlement", log); err != nil {
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

// RewardSetConfigIterator is returned from FilterSetConfig and is used to iterate over the raw logs and unpacked data for SetConfig events raised by the Reward contract.
type RewardSetConfigIterator struct {
	Event *RewardSetConfig // Event containing the contract specifics and raw log

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
func (it *RewardSetConfigIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardSetConfig)
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
		it.Event = new(RewardSetConfig)
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
func (it *RewardSetConfigIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardSetConfigIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardSetConfig represents a SetConfig event raised by the Reward contract.
type RewardSetConfig struct {
	What  string
	Value *big.Int
	Raw   types.Log // Blockchain specific contextual infos
}

// FilterSetConfig is a free log retrieval operation binding the contract event 0x361737d1051ccafab7e68fcbafe4466aaec6ee5ac4b3eb51447ac84a15cce16d.
//
// Solidity: e SetConfig(what string, value uint256)
func (_Reward *RewardFilterer) FilterSetConfig(opts *bind.FilterOpts) (*RewardSetConfigIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "SetConfig")
	if err != nil {
		return nil, err
	}
	return &RewardSetConfigIterator{contract: _Reward.contract, event: "SetConfig", logs: logs, sub: sub}, nil
}

// WatchSetConfig is a free log subscription operation binding the contract event 0x361737d1051ccafab7e68fcbafe4466aaec6ee5ac4b3eb51447ac84a15cce16d.
//
// Solidity: e SetConfig(what string, value uint256)
func (_Reward *RewardFilterer) WatchSetConfig(opts *bind.WatchOpts, sink chan<- *RewardSetConfig) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "SetConfig")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardSetConfig)
				if err := _Reward.contract.UnpackLog(event, "SetConfig", log); err != nil {
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

// RewardSetTimeIterator is returned from FilterSetTime and is used to iterate over the raw logs and unpacked data for SetTime events raised by the Reward contract.
type RewardSetTimeIterator struct {
	Event *RewardSetTime // Event containing the contract specifics and raw log

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
func (it *RewardSetTimeIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardSetTime)
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
		it.Event = new(RewardSetTime)
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
func (it *RewardSetTimeIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardSetTimeIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardSetTime represents a SetTime event raised by the Reward contract.
type RewardSetTime struct {
	What string
	When *big.Int
	Raw  types.Log // Blockchain specific contextual infos
}

// FilterSetTime is a free log retrieval operation binding the contract event 0x46e55608d5463575e90f64d3ae173372234546746315e0f3574a3bdf35567f9f.
//
// Solidity: e SetTime(what string, when uint256)
func (_Reward *RewardFilterer) FilterSetTime(opts *bind.FilterOpts) (*RewardSetTimeIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "SetTime")
	if err != nil {
		return nil, err
	}
	return &RewardSetTimeIterator{contract: _Reward.contract, event: "SetTime", logs: logs, sub: sub}, nil
}

// WatchSetTime is a free log subscription operation binding the contract event 0x46e55608d5463575e90f64d3ae173372234546746315e0f3574a3bdf35567f9f.
//
// Solidity: e SetTime(what string, when uint256)
func (_Reward *RewardFilterer) WatchSetTime(opts *bind.WatchOpts, sink chan<- *RewardSetTime) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "SetTime")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardSetTime)
				if err := _Reward.contract.UnpackLog(event, "SetTime", log); err != nil {
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

// RewardSubInvestmentIterator is returned from FilterSubInvestment and is used to iterate over the raw logs and unpacked data for SubInvestment events raised by the Reward contract.
type RewardSubInvestmentIterator struct {
	Event *RewardSubInvestment // Event containing the contract specifics and raw log

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
func (it *RewardSubInvestmentIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardSubInvestment)
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
		it.Event = new(RewardSubInvestment)
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
func (it *RewardSubInvestmentIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardSubInvestmentIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardSubInvestment represents a SubInvestment event raised by the Reward contract.
type RewardSubInvestment struct {
	Who    common.Address
	Amount *big.Int
	Total  *big.Int
	Raw    types.Log // Blockchain specific contextual infos
}

// FilterSubInvestment is a free log retrieval operation binding the contract event 0xdcd7220e3580673dbcb5899da3a05c073c2df48aa178b65b33fec6b43e13a09d.
//
// Solidity: e SubInvestment(who address, amount uint256, total uint256)
func (_Reward *RewardFilterer) FilterSubInvestment(opts *bind.FilterOpts) (*RewardSubInvestmentIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "SubInvestment")
	if err != nil {
		return nil, err
	}
	return &RewardSubInvestmentIterator{contract: _Reward.contract, event: "SubInvestment", logs: logs, sub: sub}, nil
}

// WatchSubInvestment is a free log subscription operation binding the contract event 0xdcd7220e3580673dbcb5899da3a05c073c2df48aa178b65b33fec6b43e13a09d.
//
// Solidity: e SubInvestment(who address, amount uint256, total uint256)
func (_Reward *RewardFilterer) WatchSubInvestment(opts *bind.WatchOpts, sink chan<- *RewardSubInvestment) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "SubInvestment")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardSubInvestment)
				if err := _Reward.contract.UnpackLog(event, "SubInvestment", log); err != nil {
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
const SafeMathBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a7230582045c9149d657c1500044f71c78b102d8f1ec69984a0af0f9988d3b1efa9d6acba0029`

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
const SetBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a72305820939bcffd9fd90722dacc43034a73ce4dce71a88a9f293c7bb1836d1a133eda500029`

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
