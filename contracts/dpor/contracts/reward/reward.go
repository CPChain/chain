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
const RewardABI = "[{\"constant\":false,\"inputs\":[{\"name\":\"_period\",\"type\":\"uint256\"}],\"name\":\"setPeriod\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"isContract\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"bonusPool\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"isRNode\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_value\",\"type\":\"uint256\"}],\"name\":\"withdraw\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"totalInvestAmountNow\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"nextRound\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"nextRoundStartTime\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"},{\"name\":\"_value\",\"type\":\"uint256\"}],\"name\":\"transferDeposit\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"totalInvestAmount\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"getFreeBalance\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"wantRenew\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"newRaise\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"quitRenew\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"isLocked\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"getInvestors\",\"outputs\":[{\"name\":\"\",\"type\":\"address[]\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"isENode\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"startNewRound\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"basicCriteria\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"getLockedBalance\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"getTotalBalance\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"electionCriteria\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_bonus\",\"type\":\"uint256\"}],\"name\":\"setBonusPool\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"submitDeposit\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"isToRenew\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"fallback\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"SubmitDeposit\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"WithdrawDeposit\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"JoinENodes\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"JoinRNodes\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"TransferDeposit\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"round\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"lock\",\"type\":\"bool\"},{\"indexed\":false,\"name\":\"_bonusPool\",\"type\":\"uint256\"}],\"name\":\"NewRaise\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"DepositInsufficient\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"_addr\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"_iscontinue\",\"type\":\"bool\"}],\"name\":\"ContinuedInvest\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"FundBonusPool\",\"type\":\"event\"}]"

// RewardBin is the compiled bytecode used for deploying new contracts.
const RewardBin = `0x60806040526000805460a060020a60ff0219167401000000000000000000000000000000000000000017815569043c33c1937564800000600155692a5a058fc295ed0000006002556a0108b2a2c280290940000060035560048190556009556276a700600a5534801561007157600080fd5b5060008054600160a060020a0319163317905561132f806100936000396000f3006080604052600436106101485763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416630f3a9f65811461017d57806316279055146101975780632693ee80146101cc5780632baaabc1146101f35780632e1a7d4d146102145780633ad9b7b91461021f57806347e40553146102345780634aeb31eb1461024957806350f3dbec1461025e578063665db73d146102825780638870985b146102975780638ca2ca7f146102b85780638f83bc7f146102cd5780638ffb6376146102e2578063a4e2d634146102f7578063b2f5a54c1461030c578063b95ec20314610371578063bd85948c14610392578063c0209d1f146103a7578063c4086893146103bc578063d3d38193146103dd578063d9f7700a146103fe578063db99cb3e14610413578063e9843a3e1461042b578063f509dd4a14610433575b6040805134815290517f71030773066b852afef8d0f98dbfdaec8e9a62f2f5533916ec7dfa15a0edc1f29181900360200190a1005b34801561018957600080fd5b50610195600435610454565b005b3480156101a357600080fd5b506101b8600160a060020a0360043516610470565b604080519115158252519081900360200190f35b3480156101d857600080fd5b506101e1610478565b60408051918252519081900360200190f35b3480156101ff57600080fd5b506101b8600160a060020a036004351661047e565b610195600435610497565b34801561022b57600080fd5b506101e1610550565b34801561024057600080fd5b506101e16105ac565b34801561025557600080fd5b506101e16105b2565b34801561026a57600080fd5b50610195600160a060020a03600435166024356105b8565b34801561028e57600080fd5b506101e16106ad565b3480156102a357600080fd5b506101e1600160a060020a0360043516610714565b3480156102c457600080fd5b5061019561072f565b3480156102d957600080fd5b50610195610765565b3480156102ee57600080fd5b506101956107ed565b34801561030357600080fd5b506101b8610820565b34801561031857600080fd5b50610321610833565b60408051602080825283518183015283519192839290830191858101910280838360005b8381101561035d578181015183820152602001610345565b505050509050019250505060405180910390f35b34801561037d57600080fd5b506101b8600160a060020a036004351661085d565b34801561039e57600080fd5b50610195610870565b3480156103b357600080fd5b506101e1610b48565b3480156103c857600080fd5b506101e1600160a060020a0360043516610b4e565b3480156103e957600080fd5b506101e1600160a060020a0360043516610b6c565b34801561040a57600080fd5b506101e1610ba4565b34801561041f57600080fd5b50610195600435610baa565b610195610bc6565b34801561043f57600080fd5b506101b8600160a060020a0360043516610d0d565b600054600160a060020a0316331461046b57600080fd5b600a55565b6000903b1190565b60035481565b600061049160058363ffffffff610d2e16565b92915050565b336000908152600b60205260409020548111156104b357600080fd5b336000908152600b60205260409020546104d3908263ffffffff610d4d16565b336000818152600b6020526040808220939093559151909183156108fc02918491818181858888f19350505050158015610511573d6000803e3d6000fd5b50604080513381526020810183905281517f195ddc41d185a27fe901831dcad44dd85716c95be78b1d71aa42393697966d40929181900390910190a150565b600080805b6008548110156105a6576008805461059c9161058f918490811061057557fe5b600091825260209091200154600160a060020a0316610b6c565b839063ffffffff610d5f16565b9150600101610555565b50919050565b60045481565b60095481565b600054600160a060020a031633146105cf57600080fd5b600160a060020a0382166000908152600b60205260409020548111156105f457600080fd5b600160a060020a0382166000908152600b602052604090205461061d908263ffffffff610d4d16565b600160a060020a0383166000818152600b6020526040808220939093559151909183156108fc02918491818181858888f19350505050158015610664573d6000803e3d6000fd5b5060408051600160a060020a03841681526020810183905281517f65134cf3b0cc43a1e4a814449241d36665e5774b4c36f7747755a62cf02493d5929181900390910190a15050565b600080805b6008548110156105a65761070a600b60006007600101848154811015156106d557fe5b6000918252602080832090910154600160a060020a03168352820192909252604001902060010154839063ffffffff610d5f16565b91506001016106b2565b600160a060020a03166000908152600b602052604090205490565b60005460a060020a900460ff161561074657600080fd5b336000908152600b60205260409020600301805460ff19166001179055565b600054600160a060020a0316331461077c57600080fd5b6000805474ff00000000000000000000000000000000000000001916908190556004546003546040805192835260a060020a90930460ff16151560208301528183015290517fc8ea7d3c44e48dda18a813373040ce0eda7c908ad2cd30b53310d9b4b30012149181900360600190a1565b60005460a060020a900460ff161561080457600080fd5b336000908152600b60205260409020600301805460ff19169055565b60005460a060020a900460ff16805b5090565b600054606090600160a060020a0316331461084d57600080fd5b6108576007610d79565b90505b90565b600061049160078363ffffffff610d2e16565b60008054819081908190600160a060020a0316331461088e57600080fd5b6009544210156108ff57604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601860248201527f746865206e65787420726f756e64206e6f742073746172740000000000000000604482015290519081900360640190fd5b6000600454111561091257610912610ddf565b60045461092690600163ffffffff610d5f16565b600455600a5442016201517f1901600955600093505b600854841015610b1e57600880548590811061095457fe5b6000918252602080832090910154600160a060020a0316808352600b9091526040909120909350915061098683610b6c565b9050600154811015610a1157600282015482546109a89163ffffffff610d5f16565b82556001820154156109b657fe5b6109c760058463ffffffff61108c16565b5060408051600160a060020a03851681526020810183905281517f9873c485f5a9e0be9a918f4d6ad5b64912fcb8352006b316a63427b1f408e824929181900390910190a1610b0c565b81546001830154610a279163ffffffff610d5f16565b600180840191909155600280840154845560038401805460ff191690921790915554811015610ab057610a6160058463ffffffff61108c16565b50600182015460408051600160a060020a0386168152602081019290925280517fc77e37a0f773afcb213afe8a3075752e50740f11368b2098fcffb6b99dd439789281900390910190a1610b0c565b610ac160058463ffffffff6111fe16565b50600182015460408051600160a060020a0386168152602081019290925280517fd8bcb238cc6e3b6f0e56058422877e35c9b0c97497d911cd98ec09ea45b4e6239281900390910190a15b6000600283015560019093019261093c565b50506000805474ff0000000000000000000000000000000000000000191660a060020a1790555050565b60015481565b600160a060020a03166000908152600b602052604090206001015490565b600160a060020a0381166000908152600b602052604081208054600190910154610b9c828263ffffffff610d5f16565b949350505050565b60025481565b600054600160a060020a03163314610bc157600080fd5b600355565b60005460a060020a900460ff1615610bdd57600080fd5b610be633610470565b15610c7857604080517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602a60248201527f706c65617365206e6f742075736520636f6e74726163742063616c6c2074686960448201527f732066756e6374696f6e00000000000000000000000000000000000000000000606482015290519081900360840190fd5b610c813361085d565b1515610c9a57610c9860073363ffffffff6111fe16565b505b336000908152600b6020526040902054610cba903463ffffffff610d5f16565b336000818152600b6020908152604091829020939093558051918252349282019290925281517f78d81951b78dad84771f88d35b4c93a632e1ed2da8706bbc7d8e465110686830929181900390910190a1565b600160a060020a03166000908152600b602052604090206003015460ff1690565b600160a060020a03166000908152602091909152604090205460ff1690565b600082821115610d5957fe5b50900390565b600082820183811015610d6e57fe5b8091505b5092915050565b606081600101805480602002602001604051908101604052809291908181526020018280548015610dd357602002820191906000526020600020905b8154600160a060020a03168152600190910190602001808311610db5575b50505050509050919050565b600080600080610ded6106ad565b9350831515610dfb57611086565b5060005b6008548110156110865760088054600b9160009184908110610e1d57fe5b6000918252602080832090910154600160a060020a03168352820192909252604001902060010154600354909350610e6d908590610e61908663ffffffff61127e16565b9063ffffffff6112a916565b9150610ebd82600b6000600760010185815481101515610e8957fe5b6000918252602080832090910154600160a060020a031683528201929092526040019020600201549063ffffffff610d5f16565b60088054600b9160009185908110610ed157fe5b6000918252602080832090910154600160a060020a0316835282019290925260400181206002019190915560088054600b92919084908110610f0f57fe5b6000918252602080832090910154600160a060020a0316835282019290925260400190206003015460ff161515610fd557610f5a83600b6000600760010185815481101515610e8957fe5b60088054600b9160009185908110610f6e57fe5b6000918252602080832090910154600160a060020a0316835282019290925260400181206002019190915560088054600b91839185908110610fac57fe5b6000918252602080832090910154600160a060020a031683528201929092526040019020600101555b600880547f2772659b237083773d3a2874ab3591def1a8625215ae057bde8fc4ef3dee729091908390811061100657fe5b600091825260208220015460088054600160a060020a0390921692600b929091908690811061103157fe5b6000918252602080832090910154600160a060020a03908116845283820194909452604092830190912060030154825194909316845260ff9092161515918301919091528051918290030190a1600101610dff565b50505050565b600160a060020a0381166000908152602083905260408120548190819060ff1615156110bb57600092506111f6565b5050600160a060020a0382166000908152602084905260408120805460ff191690556001840154905b818110156111f15783600160a060020a0316856001018281548110151561110757fe5b600091825260209091200154600160a060020a031614156111e957600185018054600019840190811061113657fe5b600091825260209091200154600186018054600160a060020a03909216918390811061115e57fe5b6000918252602090912001805473ffffffffffffffffffffffffffffffffffffffff1916600160a060020a039290921691909117905560018501805460001984019081106111a857fe5b6000918252602090912001805473ffffffffffffffffffffffffffffffffffffffff19169055600185018054906111e39060001983016112c0565b506111f1565b6001016110e4565b600192505b505092915050565b600160a060020a03811660009081526020839052604081205460ff161561122757506000610491565b50600160a060020a03166000818152602083815260408220805460ff1916600190811790915593840180548086018255908352912001805473ffffffffffffffffffffffffffffffffffffffff1916909117905590565b6000808315156112915760009150610d72565b508282028284828115156112a157fe5b0414610d6e57fe5b60008082848115156112b757fe5b04949350505050565b8154818355818111156112e4576000838152602090206112e49181019083016112e9565b505050565b61085a91905b8082111561082f57600081556001016112ef5600a165627a7a72305820e46e604637bac4100eadb33da2b665a8d21376e93f032a2393ba59b1303d9ac20029`

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

// BasicCriteria is a free data retrieval call binding the contract method 0xc0209d1f.
//
// Solidity: function basicCriteria() constant returns(uint256)
func (_Reward *RewardCaller) BasicCriteria(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "basicCriteria")
	return *ret0, err
}

// BasicCriteria is a free data retrieval call binding the contract method 0xc0209d1f.
//
// Solidity: function basicCriteria() constant returns(uint256)
func (_Reward *RewardSession) BasicCriteria() (*big.Int, error) {
	return _Reward.Contract.BasicCriteria(&_Reward.CallOpts)
}

// BasicCriteria is a free data retrieval call binding the contract method 0xc0209d1f.
//
// Solidity: function basicCriteria() constant returns(uint256)
func (_Reward *RewardCallerSession) BasicCriteria() (*big.Int, error) {
	return _Reward.Contract.BasicCriteria(&_Reward.CallOpts)
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

// ElectionCriteria is a free data retrieval call binding the contract method 0xd9f7700a.
//
// Solidity: function electionCriteria() constant returns(uint256)
func (_Reward *RewardCaller) ElectionCriteria(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "electionCriteria")
	return *ret0, err
}

// ElectionCriteria is a free data retrieval call binding the contract method 0xd9f7700a.
//
// Solidity: function electionCriteria() constant returns(uint256)
func (_Reward *RewardSession) ElectionCriteria() (*big.Int, error) {
	return _Reward.Contract.ElectionCriteria(&_Reward.CallOpts)
}

// ElectionCriteria is a free data retrieval call binding the contract method 0xd9f7700a.
//
// Solidity: function electionCriteria() constant returns(uint256)
func (_Reward *RewardCallerSession) ElectionCriteria() (*big.Int, error) {
	return _Reward.Contract.ElectionCriteria(&_Reward.CallOpts)
}

// GetFreeBalance is a free data retrieval call binding the contract method 0x8870985b.
//
// Solidity: function getFreeBalance(_addr address) constant returns(uint256)
func (_Reward *RewardCaller) GetFreeBalance(opts *bind.CallOpts, _addr common.Address) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "getFreeBalance", _addr)
	return *ret0, err
}

// GetFreeBalance is a free data retrieval call binding the contract method 0x8870985b.
//
// Solidity: function getFreeBalance(_addr address) constant returns(uint256)
func (_Reward *RewardSession) GetFreeBalance(_addr common.Address) (*big.Int, error) {
	return _Reward.Contract.GetFreeBalance(&_Reward.CallOpts, _addr)
}

// GetFreeBalance is a free data retrieval call binding the contract method 0x8870985b.
//
// Solidity: function getFreeBalance(_addr address) constant returns(uint256)
func (_Reward *RewardCallerSession) GetFreeBalance(_addr common.Address) (*big.Int, error) {
	return _Reward.Contract.GetFreeBalance(&_Reward.CallOpts, _addr)
}

// GetInvestors is a free data retrieval call binding the contract method 0xb2f5a54c.
//
// Solidity: function getInvestors() constant returns(address[])
func (_Reward *RewardCaller) GetInvestors(opts *bind.CallOpts) ([]common.Address, error) {
	var (
		ret0 = new([]common.Address)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "getInvestors")
	return *ret0, err
}

// GetInvestors is a free data retrieval call binding the contract method 0xb2f5a54c.
//
// Solidity: function getInvestors() constant returns(address[])
func (_Reward *RewardSession) GetInvestors() ([]common.Address, error) {
	return _Reward.Contract.GetInvestors(&_Reward.CallOpts)
}

// GetInvestors is a free data retrieval call binding the contract method 0xb2f5a54c.
//
// Solidity: function getInvestors() constant returns(address[])
func (_Reward *RewardCallerSession) GetInvestors() ([]common.Address, error) {
	return _Reward.Contract.GetInvestors(&_Reward.CallOpts)
}

// GetLockedBalance is a free data retrieval call binding the contract method 0xc4086893.
//
// Solidity: function getLockedBalance(_addr address) constant returns(uint256)
func (_Reward *RewardCaller) GetLockedBalance(opts *bind.CallOpts, _addr common.Address) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "getLockedBalance", _addr)
	return *ret0, err
}

// GetLockedBalance is a free data retrieval call binding the contract method 0xc4086893.
//
// Solidity: function getLockedBalance(_addr address) constant returns(uint256)
func (_Reward *RewardSession) GetLockedBalance(_addr common.Address) (*big.Int, error) {
	return _Reward.Contract.GetLockedBalance(&_Reward.CallOpts, _addr)
}

// GetLockedBalance is a free data retrieval call binding the contract method 0xc4086893.
//
// Solidity: function getLockedBalance(_addr address) constant returns(uint256)
func (_Reward *RewardCallerSession) GetLockedBalance(_addr common.Address) (*big.Int, error) {
	return _Reward.Contract.GetLockedBalance(&_Reward.CallOpts, _addr)
}

// GetTotalBalance is a free data retrieval call binding the contract method 0xd3d38193.
//
// Solidity: function getTotalBalance(_addr address) constant returns(uint256)
func (_Reward *RewardCaller) GetTotalBalance(opts *bind.CallOpts, _addr common.Address) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "getTotalBalance", _addr)
	return *ret0, err
}

// GetTotalBalance is a free data retrieval call binding the contract method 0xd3d38193.
//
// Solidity: function getTotalBalance(_addr address) constant returns(uint256)
func (_Reward *RewardSession) GetTotalBalance(_addr common.Address) (*big.Int, error) {
	return _Reward.Contract.GetTotalBalance(&_Reward.CallOpts, _addr)
}

// GetTotalBalance is a free data retrieval call binding the contract method 0xd3d38193.
//
// Solidity: function getTotalBalance(_addr address) constant returns(uint256)
func (_Reward *RewardCallerSession) GetTotalBalance(_addr common.Address) (*big.Int, error) {
	return _Reward.Contract.GetTotalBalance(&_Reward.CallOpts, _addr)
}

// IsContract is a free data retrieval call binding the contract method 0x16279055.
//
// Solidity: function isContract(addr address) constant returns(bool)
func (_Reward *RewardCaller) IsContract(opts *bind.CallOpts, addr common.Address) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "isContract", addr)
	return *ret0, err
}

// IsContract is a free data retrieval call binding the contract method 0x16279055.
//
// Solidity: function isContract(addr address) constant returns(bool)
func (_Reward *RewardSession) IsContract(addr common.Address) (bool, error) {
	return _Reward.Contract.IsContract(&_Reward.CallOpts, addr)
}

// IsContract is a free data retrieval call binding the contract method 0x16279055.
//
// Solidity: function isContract(addr address) constant returns(bool)
func (_Reward *RewardCallerSession) IsContract(addr common.Address) (bool, error) {
	return _Reward.Contract.IsContract(&_Reward.CallOpts, addr)
}

// IsENode is a free data retrieval call binding the contract method 0xb95ec203.
//
// Solidity: function isENode(_addr address) constant returns(bool)
func (_Reward *RewardCaller) IsENode(opts *bind.CallOpts, _addr common.Address) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "isENode", _addr)
	return *ret0, err
}

// IsENode is a free data retrieval call binding the contract method 0xb95ec203.
//
// Solidity: function isENode(_addr address) constant returns(bool)
func (_Reward *RewardSession) IsENode(_addr common.Address) (bool, error) {
	return _Reward.Contract.IsENode(&_Reward.CallOpts, _addr)
}

// IsENode is a free data retrieval call binding the contract method 0xb95ec203.
//
// Solidity: function isENode(_addr address) constant returns(bool)
func (_Reward *RewardCallerSession) IsENode(_addr common.Address) (bool, error) {
	return _Reward.Contract.IsENode(&_Reward.CallOpts, _addr)
}

// IsLocked is a free data retrieval call binding the contract method 0xa4e2d634.
//
// Solidity: function isLocked() constant returns(bool)
func (_Reward *RewardCaller) IsLocked(opts *bind.CallOpts) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "isLocked")
	return *ret0, err
}

// IsLocked is a free data retrieval call binding the contract method 0xa4e2d634.
//
// Solidity: function isLocked() constant returns(bool)
func (_Reward *RewardSession) IsLocked() (bool, error) {
	return _Reward.Contract.IsLocked(&_Reward.CallOpts)
}

// IsLocked is a free data retrieval call binding the contract method 0xa4e2d634.
//
// Solidity: function isLocked() constant returns(bool)
func (_Reward *RewardCallerSession) IsLocked() (bool, error) {
	return _Reward.Contract.IsLocked(&_Reward.CallOpts)
}

// IsRNode is a free data retrieval call binding the contract method 0x2baaabc1.
//
// Solidity: function isRNode(_addr address) constant returns(bool)
func (_Reward *RewardCaller) IsRNode(opts *bind.CallOpts, _addr common.Address) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "isRNode", _addr)
	return *ret0, err
}

// IsRNode is a free data retrieval call binding the contract method 0x2baaabc1.
//
// Solidity: function isRNode(_addr address) constant returns(bool)
func (_Reward *RewardSession) IsRNode(_addr common.Address) (bool, error) {
	return _Reward.Contract.IsRNode(&_Reward.CallOpts, _addr)
}

// IsRNode is a free data retrieval call binding the contract method 0x2baaabc1.
//
// Solidity: function isRNode(_addr address) constant returns(bool)
func (_Reward *RewardCallerSession) IsRNode(_addr common.Address) (bool, error) {
	return _Reward.Contract.IsRNode(&_Reward.CallOpts, _addr)
}

// IsToRenew is a free data retrieval call binding the contract method 0xf509dd4a.
//
// Solidity: function isToRenew(_addr address) constant returns(bool)
func (_Reward *RewardCaller) IsToRenew(opts *bind.CallOpts, _addr common.Address) (bool, error) {
	var (
		ret0 = new(bool)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "isToRenew", _addr)
	return *ret0, err
}

// IsToRenew is a free data retrieval call binding the contract method 0xf509dd4a.
//
// Solidity: function isToRenew(_addr address) constant returns(bool)
func (_Reward *RewardSession) IsToRenew(_addr common.Address) (bool, error) {
	return _Reward.Contract.IsToRenew(&_Reward.CallOpts, _addr)
}

// IsToRenew is a free data retrieval call binding the contract method 0xf509dd4a.
//
// Solidity: function isToRenew(_addr address) constant returns(bool)
func (_Reward *RewardCallerSession) IsToRenew(_addr common.Address) (bool, error) {
	return _Reward.Contract.IsToRenew(&_Reward.CallOpts, _addr)
}

// NextRound is a free data retrieval call binding the contract method 0x47e40553.
//
// Solidity: function nextRound() constant returns(uint256)
func (_Reward *RewardCaller) NextRound(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "nextRound")
	return *ret0, err
}

// NextRound is a free data retrieval call binding the contract method 0x47e40553.
//
// Solidity: function nextRound() constant returns(uint256)
func (_Reward *RewardSession) NextRound() (*big.Int, error) {
	return _Reward.Contract.NextRound(&_Reward.CallOpts)
}

// NextRound is a free data retrieval call binding the contract method 0x47e40553.
//
// Solidity: function nextRound() constant returns(uint256)
func (_Reward *RewardCallerSession) NextRound() (*big.Int, error) {
	return _Reward.Contract.NextRound(&_Reward.CallOpts)
}

// NextRoundStartTime is a free data retrieval call binding the contract method 0x4aeb31eb.
//
// Solidity: function nextRoundStartTime() constant returns(uint256)
func (_Reward *RewardCaller) NextRoundStartTime(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "nextRoundStartTime")
	return *ret0, err
}

// NextRoundStartTime is a free data retrieval call binding the contract method 0x4aeb31eb.
//
// Solidity: function nextRoundStartTime() constant returns(uint256)
func (_Reward *RewardSession) NextRoundStartTime() (*big.Int, error) {
	return _Reward.Contract.NextRoundStartTime(&_Reward.CallOpts)
}

// NextRoundStartTime is a free data retrieval call binding the contract method 0x4aeb31eb.
//
// Solidity: function nextRoundStartTime() constant returns(uint256)
func (_Reward *RewardCallerSession) NextRoundStartTime() (*big.Int, error) {
	return _Reward.Contract.NextRoundStartTime(&_Reward.CallOpts)
}

// TotalInvestAmount is a free data retrieval call binding the contract method 0x665db73d.
//
// Solidity: function totalInvestAmount() constant returns(uint256)
func (_Reward *RewardCaller) TotalInvestAmount(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "totalInvestAmount")
	return *ret0, err
}

// TotalInvestAmount is a free data retrieval call binding the contract method 0x665db73d.
//
// Solidity: function totalInvestAmount() constant returns(uint256)
func (_Reward *RewardSession) TotalInvestAmount() (*big.Int, error) {
	return _Reward.Contract.TotalInvestAmount(&_Reward.CallOpts)
}

// TotalInvestAmount is a free data retrieval call binding the contract method 0x665db73d.
//
// Solidity: function totalInvestAmount() constant returns(uint256)
func (_Reward *RewardCallerSession) TotalInvestAmount() (*big.Int, error) {
	return _Reward.Contract.TotalInvestAmount(&_Reward.CallOpts)
}

// TotalInvestAmountNow is a free data retrieval call binding the contract method 0x3ad9b7b9.
//
// Solidity: function totalInvestAmountNow() constant returns(uint256)
func (_Reward *RewardCaller) TotalInvestAmountNow(opts *bind.CallOpts) (*big.Int, error) {
	var (
		ret0 = new(*big.Int)
	)
	out := ret0
	err := _Reward.contract.Call(opts, out, "totalInvestAmountNow")
	return *ret0, err
}

// TotalInvestAmountNow is a free data retrieval call binding the contract method 0x3ad9b7b9.
//
// Solidity: function totalInvestAmountNow() constant returns(uint256)
func (_Reward *RewardSession) TotalInvestAmountNow() (*big.Int, error) {
	return _Reward.Contract.TotalInvestAmountNow(&_Reward.CallOpts)
}

// TotalInvestAmountNow is a free data retrieval call binding the contract method 0x3ad9b7b9.
//
// Solidity: function totalInvestAmountNow() constant returns(uint256)
func (_Reward *RewardCallerSession) TotalInvestAmountNow() (*big.Int, error) {
	return _Reward.Contract.TotalInvestAmountNow(&_Reward.CallOpts)
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

// QuitRenew is a paid mutator transaction binding the contract method 0x8ffb6376.
//
// Solidity: function quitRenew() returns()
func (_Reward *RewardTransactor) QuitRenew(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "quitRenew")
}

// QuitRenew is a paid mutator transaction binding the contract method 0x8ffb6376.
//
// Solidity: function quitRenew() returns()
func (_Reward *RewardSession) QuitRenew() (*types.Transaction, error) {
	return _Reward.Contract.QuitRenew(&_Reward.TransactOpts)
}

// QuitRenew is a paid mutator transaction binding the contract method 0x8ffb6376.
//
// Solidity: function quitRenew() returns()
func (_Reward *RewardTransactorSession) QuitRenew() (*types.Transaction, error) {
	return _Reward.Contract.QuitRenew(&_Reward.TransactOpts)
}

// SetBonusPool is a paid mutator transaction binding the contract method 0xdb99cb3e.
//
// Solidity: function setBonusPool(_bonus uint256) returns()
func (_Reward *RewardTransactor) SetBonusPool(opts *bind.TransactOpts, _bonus *big.Int) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "setBonusPool", _bonus)
}

// SetBonusPool is a paid mutator transaction binding the contract method 0xdb99cb3e.
//
// Solidity: function setBonusPool(_bonus uint256) returns()
func (_Reward *RewardSession) SetBonusPool(_bonus *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetBonusPool(&_Reward.TransactOpts, _bonus)
}

// SetBonusPool is a paid mutator transaction binding the contract method 0xdb99cb3e.
//
// Solidity: function setBonusPool(_bonus uint256) returns()
func (_Reward *RewardTransactorSession) SetBonusPool(_bonus *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetBonusPool(&_Reward.TransactOpts, _bonus)
}

// SetPeriod is a paid mutator transaction binding the contract method 0x0f3a9f65.
//
// Solidity: function setPeriod(_period uint256) returns()
func (_Reward *RewardTransactor) SetPeriod(opts *bind.TransactOpts, _period *big.Int) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "setPeriod", _period)
}

// SetPeriod is a paid mutator transaction binding the contract method 0x0f3a9f65.
//
// Solidity: function setPeriod(_period uint256) returns()
func (_Reward *RewardSession) SetPeriod(_period *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetPeriod(&_Reward.TransactOpts, _period)
}

// SetPeriod is a paid mutator transaction binding the contract method 0x0f3a9f65.
//
// Solidity: function setPeriod(_period uint256) returns()
func (_Reward *RewardTransactorSession) SetPeriod(_period *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.SetPeriod(&_Reward.TransactOpts, _period)
}

// StartNewRound is a paid mutator transaction binding the contract method 0xbd85948c.
//
// Solidity: function startNewRound() returns()
func (_Reward *RewardTransactor) StartNewRound(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "startNewRound")
}

// StartNewRound is a paid mutator transaction binding the contract method 0xbd85948c.
//
// Solidity: function startNewRound() returns()
func (_Reward *RewardSession) StartNewRound() (*types.Transaction, error) {
	return _Reward.Contract.StartNewRound(&_Reward.TransactOpts)
}

// StartNewRound is a paid mutator transaction binding the contract method 0xbd85948c.
//
// Solidity: function startNewRound() returns()
func (_Reward *RewardTransactorSession) StartNewRound() (*types.Transaction, error) {
	return _Reward.Contract.StartNewRound(&_Reward.TransactOpts)
}

// SubmitDeposit is a paid mutator transaction binding the contract method 0xe9843a3e.
//
// Solidity: function submitDeposit() returns()
func (_Reward *RewardTransactor) SubmitDeposit(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "submitDeposit")
}

// SubmitDeposit is a paid mutator transaction binding the contract method 0xe9843a3e.
//
// Solidity: function submitDeposit() returns()
func (_Reward *RewardSession) SubmitDeposit() (*types.Transaction, error) {
	return _Reward.Contract.SubmitDeposit(&_Reward.TransactOpts)
}

// SubmitDeposit is a paid mutator transaction binding the contract method 0xe9843a3e.
//
// Solidity: function submitDeposit() returns()
func (_Reward *RewardTransactorSession) SubmitDeposit() (*types.Transaction, error) {
	return _Reward.Contract.SubmitDeposit(&_Reward.TransactOpts)
}

// TransferDeposit is a paid mutator transaction binding the contract method 0x50f3dbec.
//
// Solidity: function transferDeposit(_addr address, _value uint256) returns()
func (_Reward *RewardTransactor) TransferDeposit(opts *bind.TransactOpts, _addr common.Address, _value *big.Int) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "transferDeposit", _addr, _value)
}

// TransferDeposit is a paid mutator transaction binding the contract method 0x50f3dbec.
//
// Solidity: function transferDeposit(_addr address, _value uint256) returns()
func (_Reward *RewardSession) TransferDeposit(_addr common.Address, _value *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.TransferDeposit(&_Reward.TransactOpts, _addr, _value)
}

// TransferDeposit is a paid mutator transaction binding the contract method 0x50f3dbec.
//
// Solidity: function transferDeposit(_addr address, _value uint256) returns()
func (_Reward *RewardTransactorSession) TransferDeposit(_addr common.Address, _value *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.TransferDeposit(&_Reward.TransactOpts, _addr, _value)
}

// WantRenew is a paid mutator transaction binding the contract method 0x8ca2ca7f.
//
// Solidity: function wantRenew() returns()
func (_Reward *RewardTransactor) WantRenew(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "wantRenew")
}

// WantRenew is a paid mutator transaction binding the contract method 0x8ca2ca7f.
//
// Solidity: function wantRenew() returns()
func (_Reward *RewardSession) WantRenew() (*types.Transaction, error) {
	return _Reward.Contract.WantRenew(&_Reward.TransactOpts)
}

// WantRenew is a paid mutator transaction binding the contract method 0x8ca2ca7f.
//
// Solidity: function wantRenew() returns()
func (_Reward *RewardTransactorSession) WantRenew() (*types.Transaction, error) {
	return _Reward.Contract.WantRenew(&_Reward.TransactOpts)
}

// Withdraw is a paid mutator transaction binding the contract method 0x2e1a7d4d.
//
// Solidity: function withdraw(_value uint256) returns()
func (_Reward *RewardTransactor) Withdraw(opts *bind.TransactOpts, _value *big.Int) (*types.Transaction, error) {
	return _Reward.contract.Transact(opts, "withdraw", _value)
}

// Withdraw is a paid mutator transaction binding the contract method 0x2e1a7d4d.
//
// Solidity: function withdraw(_value uint256) returns()
func (_Reward *RewardSession) Withdraw(_value *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.Withdraw(&_Reward.TransactOpts, _value)
}

// Withdraw is a paid mutator transaction binding the contract method 0x2e1a7d4d.
//
// Solidity: function withdraw(_value uint256) returns()
func (_Reward *RewardTransactorSession) Withdraw(_value *big.Int) (*types.Transaction, error) {
	return _Reward.Contract.Withdraw(&_Reward.TransactOpts, _value)
}

// RewardContinuedInvestIterator is returned from FilterContinuedInvest and is used to iterate over the raw logs and unpacked data for ContinuedInvest events raised by the Reward contract.
type RewardContinuedInvestIterator struct {
	Event *RewardContinuedInvest // Event containing the contract specifics and raw log

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
func (it *RewardContinuedInvestIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardContinuedInvest)
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
		it.Event = new(RewardContinuedInvest)
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
func (it *RewardContinuedInvestIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardContinuedInvestIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardContinuedInvest represents a ContinuedInvest event raised by the Reward contract.
type RewardContinuedInvest struct {
	Addr       common.Address
	Iscontinue bool
	Raw        types.Log // Blockchain specific contextual infos
}

// FilterContinuedInvest is a free log retrieval operation binding the contract event 0x2772659b237083773d3a2874ab3591def1a8625215ae057bde8fc4ef3dee7290.
//
// Solidity: e ContinuedInvest(_addr address, _iscontinue bool)
func (_Reward *RewardFilterer) FilterContinuedInvest(opts *bind.FilterOpts) (*RewardContinuedInvestIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "ContinuedInvest")
	if err != nil {
		return nil, err
	}
	return &RewardContinuedInvestIterator{contract: _Reward.contract, event: "ContinuedInvest", logs: logs, sub: sub}, nil
}

// WatchContinuedInvest is a free log subscription operation binding the contract event 0x2772659b237083773d3a2874ab3591def1a8625215ae057bde8fc4ef3dee7290.
//
// Solidity: e ContinuedInvest(_addr address, _iscontinue bool)
func (_Reward *RewardFilterer) WatchContinuedInvest(opts *bind.WatchOpts, sink chan<- *RewardContinuedInvest) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "ContinuedInvest")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardContinuedInvest)
				if err := _Reward.contract.UnpackLog(event, "ContinuedInvest", log); err != nil {
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

// RewardDepositInsufficientIterator is returned from FilterDepositInsufficient and is used to iterate over the raw logs and unpacked data for DepositInsufficient events raised by the Reward contract.
type RewardDepositInsufficientIterator struct {
	Event *RewardDepositInsufficient // Event containing the contract specifics and raw log

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
func (it *RewardDepositInsufficientIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardDepositInsufficient)
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
		it.Event = new(RewardDepositInsufficient)
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
func (it *RewardDepositInsufficientIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardDepositInsufficientIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardDepositInsufficient represents a DepositInsufficient event raised by the Reward contract.
type RewardDepositInsufficient struct {
	Who   common.Address
	Value *big.Int
	Raw   types.Log // Blockchain specific contextual infos
}

// FilterDepositInsufficient is a free log retrieval operation binding the contract event 0x9873c485f5a9e0be9a918f4d6ad5b64912fcb8352006b316a63427b1f408e824.
//
// Solidity: e DepositInsufficient(who address, value uint256)
func (_Reward *RewardFilterer) FilterDepositInsufficient(opts *bind.FilterOpts) (*RewardDepositInsufficientIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "DepositInsufficient")
	if err != nil {
		return nil, err
	}
	return &RewardDepositInsufficientIterator{contract: _Reward.contract, event: "DepositInsufficient", logs: logs, sub: sub}, nil
}

// WatchDepositInsufficient is a free log subscription operation binding the contract event 0x9873c485f5a9e0be9a918f4d6ad5b64912fcb8352006b316a63427b1f408e824.
//
// Solidity: e DepositInsufficient(who address, value uint256)
func (_Reward *RewardFilterer) WatchDepositInsufficient(opts *bind.WatchOpts, sink chan<- *RewardDepositInsufficient) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "DepositInsufficient")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardDepositInsufficient)
				if err := _Reward.contract.UnpackLog(event, "DepositInsufficient", log); err != nil {
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
	Value *big.Int
	Raw   types.Log // Blockchain specific contextual infos
}

// FilterFundBonusPool is a free log retrieval operation binding the contract event 0x71030773066b852afef8d0f98dbfdaec8e9a62f2f5533916ec7dfa15a0edc1f2.
//
// Solidity: e FundBonusPool(value uint256)
func (_Reward *RewardFilterer) FilterFundBonusPool(opts *bind.FilterOpts) (*RewardFundBonusPoolIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "FundBonusPool")
	if err != nil {
		return nil, err
	}
	return &RewardFundBonusPoolIterator{contract: _Reward.contract, event: "FundBonusPool", logs: logs, sub: sub}, nil
}

// WatchFundBonusPool is a free log subscription operation binding the contract event 0x71030773066b852afef8d0f98dbfdaec8e9a62f2f5533916ec7dfa15a0edc1f2.
//
// Solidity: e FundBonusPool(value uint256)
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

// RewardJoinENodesIterator is returned from FilterJoinENodes and is used to iterate over the raw logs and unpacked data for JoinENodes events raised by the Reward contract.
type RewardJoinENodesIterator struct {
	Event *RewardJoinENodes // Event containing the contract specifics and raw log

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
func (it *RewardJoinENodesIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardJoinENodes)
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
		it.Event = new(RewardJoinENodes)
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
func (it *RewardJoinENodesIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardJoinENodesIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardJoinENodes represents a JoinENodes event raised by the Reward contract.
type RewardJoinENodes struct {
	Who   common.Address
	Value *big.Int
	Raw   types.Log // Blockchain specific contextual infos
}

// FilterJoinENodes is a free log retrieval operation binding the contract event 0xc77e37a0f773afcb213afe8a3075752e50740f11368b2098fcffb6b99dd43978.
//
// Solidity: e JoinENodes(who address, value uint256)
func (_Reward *RewardFilterer) FilterJoinENodes(opts *bind.FilterOpts) (*RewardJoinENodesIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "JoinENodes")
	if err != nil {
		return nil, err
	}
	return &RewardJoinENodesIterator{contract: _Reward.contract, event: "JoinENodes", logs: logs, sub: sub}, nil
}

// WatchJoinENodes is a free log subscription operation binding the contract event 0xc77e37a0f773afcb213afe8a3075752e50740f11368b2098fcffb6b99dd43978.
//
// Solidity: e JoinENodes(who address, value uint256)
func (_Reward *RewardFilterer) WatchJoinENodes(opts *bind.WatchOpts, sink chan<- *RewardJoinENodes) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "JoinENodes")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardJoinENodes)
				if err := _Reward.contract.UnpackLog(event, "JoinENodes", log); err != nil {
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

// RewardJoinRNodesIterator is returned from FilterJoinRNodes and is used to iterate over the raw logs and unpacked data for JoinRNodes events raised by the Reward contract.
type RewardJoinRNodesIterator struct {
	Event *RewardJoinRNodes // Event containing the contract specifics and raw log

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
func (it *RewardJoinRNodesIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardJoinRNodes)
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
		it.Event = new(RewardJoinRNodes)
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
func (it *RewardJoinRNodesIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardJoinRNodesIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardJoinRNodes represents a JoinRNodes event raised by the Reward contract.
type RewardJoinRNodes struct {
	Who   common.Address
	Value *big.Int
	Raw   types.Log // Blockchain specific contextual infos
}

// FilterJoinRNodes is a free log retrieval operation binding the contract event 0xd8bcb238cc6e3b6f0e56058422877e35c9b0c97497d911cd98ec09ea45b4e623.
//
// Solidity: e JoinRNodes(who address, value uint256)
func (_Reward *RewardFilterer) FilterJoinRNodes(opts *bind.FilterOpts) (*RewardJoinRNodesIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "JoinRNodes")
	if err != nil {
		return nil, err
	}
	return &RewardJoinRNodesIterator{contract: _Reward.contract, event: "JoinRNodes", logs: logs, sub: sub}, nil
}

// WatchJoinRNodes is a free log subscription operation binding the contract event 0xd8bcb238cc6e3b6f0e56058422877e35c9b0c97497d911cd98ec09ea45b4e623.
//
// Solidity: e JoinRNodes(who address, value uint256)
func (_Reward *RewardFilterer) WatchJoinRNodes(opts *bind.WatchOpts, sink chan<- *RewardJoinRNodes) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "JoinRNodes")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardJoinRNodes)
				if err := _Reward.contract.UnpackLog(event, "JoinRNodes", log); err != nil {
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
	Round     *big.Int
	Lock      bool
	BonusPool *big.Int
	Raw       types.Log // Blockchain specific contextual infos
}

// FilterNewRaise is a free log retrieval operation binding the contract event 0xc8ea7d3c44e48dda18a813373040ce0eda7c908ad2cd30b53310d9b4b3001214.
//
// Solidity: e NewRaise(round uint256, lock bool, _bonusPool uint256)
func (_Reward *RewardFilterer) FilterNewRaise(opts *bind.FilterOpts) (*RewardNewRaiseIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "NewRaise")
	if err != nil {
		return nil, err
	}
	return &RewardNewRaiseIterator{contract: _Reward.contract, event: "NewRaise", logs: logs, sub: sub}, nil
}

// WatchNewRaise is a free log subscription operation binding the contract event 0xc8ea7d3c44e48dda18a813373040ce0eda7c908ad2cd30b53310d9b4b3001214.
//
// Solidity: e NewRaise(round uint256, lock bool, _bonusPool uint256)
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

// RewardSubmitDepositIterator is returned from FilterSubmitDeposit and is used to iterate over the raw logs and unpacked data for SubmitDeposit events raised by the Reward contract.
type RewardSubmitDepositIterator struct {
	Event *RewardSubmitDeposit // Event containing the contract specifics and raw log

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
func (it *RewardSubmitDepositIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardSubmitDeposit)
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
		it.Event = new(RewardSubmitDeposit)
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
func (it *RewardSubmitDepositIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardSubmitDepositIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardSubmitDeposit represents a SubmitDeposit event raised by the Reward contract.
type RewardSubmitDeposit struct {
	Who   common.Address
	Value *big.Int
	Raw   types.Log // Blockchain specific contextual infos
}

// FilterSubmitDeposit is a free log retrieval operation binding the contract event 0x78d81951b78dad84771f88d35b4c93a632e1ed2da8706bbc7d8e465110686830.
//
// Solidity: e SubmitDeposit(who address, value uint256)
func (_Reward *RewardFilterer) FilterSubmitDeposit(opts *bind.FilterOpts) (*RewardSubmitDepositIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "SubmitDeposit")
	if err != nil {
		return nil, err
	}
	return &RewardSubmitDepositIterator{contract: _Reward.contract, event: "SubmitDeposit", logs: logs, sub: sub}, nil
}

// WatchSubmitDeposit is a free log subscription operation binding the contract event 0x78d81951b78dad84771f88d35b4c93a632e1ed2da8706bbc7d8e465110686830.
//
// Solidity: e SubmitDeposit(who address, value uint256)
func (_Reward *RewardFilterer) WatchSubmitDeposit(opts *bind.WatchOpts, sink chan<- *RewardSubmitDeposit) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "SubmitDeposit")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardSubmitDeposit)
				if err := _Reward.contract.UnpackLog(event, "SubmitDeposit", log); err != nil {
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

// RewardTransferDepositIterator is returned from FilterTransferDeposit and is used to iterate over the raw logs and unpacked data for TransferDeposit events raised by the Reward contract.
type RewardTransferDepositIterator struct {
	Event *RewardTransferDeposit // Event containing the contract specifics and raw log

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
func (it *RewardTransferDepositIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardTransferDeposit)
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
		it.Event = new(RewardTransferDeposit)
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
func (it *RewardTransferDepositIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardTransferDepositIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardTransferDeposit represents a TransferDeposit event raised by the Reward contract.
type RewardTransferDeposit struct {
	Who   common.Address
	Value *big.Int
	Raw   types.Log // Blockchain specific contextual infos
}

// FilterTransferDeposit is a free log retrieval operation binding the contract event 0x65134cf3b0cc43a1e4a814449241d36665e5774b4c36f7747755a62cf02493d5.
//
// Solidity: e TransferDeposit(who address, value uint256)
func (_Reward *RewardFilterer) FilterTransferDeposit(opts *bind.FilterOpts) (*RewardTransferDepositIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "TransferDeposit")
	if err != nil {
		return nil, err
	}
	return &RewardTransferDepositIterator{contract: _Reward.contract, event: "TransferDeposit", logs: logs, sub: sub}, nil
}

// WatchTransferDeposit is a free log subscription operation binding the contract event 0x65134cf3b0cc43a1e4a814449241d36665e5774b4c36f7747755a62cf02493d5.
//
// Solidity: e TransferDeposit(who address, value uint256)
func (_Reward *RewardFilterer) WatchTransferDeposit(opts *bind.WatchOpts, sink chan<- *RewardTransferDeposit) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "TransferDeposit")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardTransferDeposit)
				if err := _Reward.contract.UnpackLog(event, "TransferDeposit", log); err != nil {
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

// RewardWithdrawDepositIterator is returned from FilterWithdrawDeposit and is used to iterate over the raw logs and unpacked data for WithdrawDeposit events raised by the Reward contract.
type RewardWithdrawDepositIterator struct {
	Event *RewardWithdrawDeposit // Event containing the contract specifics and raw log

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
func (it *RewardWithdrawDepositIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(RewardWithdrawDeposit)
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
		it.Event = new(RewardWithdrawDeposit)
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
func (it *RewardWithdrawDepositIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *RewardWithdrawDepositIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// RewardWithdrawDeposit represents a WithdrawDeposit event raised by the Reward contract.
type RewardWithdrawDeposit struct {
	Who   common.Address
	Value *big.Int
	Raw   types.Log // Blockchain specific contextual infos
}

// FilterWithdrawDeposit is a free log retrieval operation binding the contract event 0x195ddc41d185a27fe901831dcad44dd85716c95be78b1d71aa42393697966d40.
//
// Solidity: e WithdrawDeposit(who address, value uint256)
func (_Reward *RewardFilterer) FilterWithdrawDeposit(opts *bind.FilterOpts) (*RewardWithdrawDepositIterator, error) {

	logs, sub, err := _Reward.contract.FilterLogs(opts, "WithdrawDeposit")
	if err != nil {
		return nil, err
	}
	return &RewardWithdrawDepositIterator{contract: _Reward.contract, event: "WithdrawDeposit", logs: logs, sub: sub}, nil
}

// WatchWithdrawDeposit is a free log subscription operation binding the contract event 0x195ddc41d185a27fe901831dcad44dd85716c95be78b1d71aa42393697966d40.
//
// Solidity: e WithdrawDeposit(who address, value uint256)
func (_Reward *RewardFilterer) WatchWithdrawDeposit(opts *bind.WatchOpts, sink chan<- *RewardWithdrawDeposit) (event.Subscription, error) {

	logs, sub, err := _Reward.contract.WatchLogs(opts, "WithdrawDeposit")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(RewardWithdrawDeposit)
				if err := _Reward.contract.UnpackLog(event, "WithdrawDeposit", log); err != nil {
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
const SafeMathBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a7230582037b0201b35fcbe7d787e53a42d71fb75dd5e4675e6969da6ffbf93409a2872110029`

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
const SetBin = `0x604c602c600b82828239805160001a60731460008114601c57601e565bfe5b5030600052607381538281f30073000000000000000000000000000000000000000030146080604052600080fd00a165627a7a72305820cf10abf4e7fb5e46d82b906dc0ba42bbf134940b8a4d419436bba57cd28c1fdc0029`

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
