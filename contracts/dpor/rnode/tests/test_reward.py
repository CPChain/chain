import math
import time
import os.path as osp

from solc import compile_files

from cpc_fusion import Web3

pwd = osp.dirname(osp.abspath(__file__))


def init():

    # install_solc('v0.4.25')
    global cpc
    cpc = int(math.pow(10, 18))

    global password
    password = "123"

    global owner
    owner = "0xb3801b8743DEA10c30b0c21CAe8b1923d9625F84"

    global rnode_succeed
    rnode_succeed = "0x4A030EC3ea9A813FBb0aFb79cB175c09ce56B3bE"

    global rnode_failed
    rnode_failed = "0x8FB5ECa33af7757a8d6cE679C3Ad16cCe007fE7f"

    global cf
    cf = Web3(Web3.HTTPProvider('http://127.0.0.1:8521'))

    cf.personal.unlockAccount("0x4A030EC3ea9A813FBb0aFb79cB175c09ce56B3bE", password)
    cf.personal.unlockAccount("0x8FB5ECa33af7757a8d6cE679C3Ad16cCe007fE7f", password)

    global abi
    abi = {'constant': True, 'inputs': [], 'name': 'getRnodeNum', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_period', 'type': 'uint256'}], 'name': 'setPeriod', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [], 'name': 'quitRnode', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': True, 'inputs': [{'name': 'addr', 'type': 'address'}], 'name': 'isContract', 'outputs': [{'name': '', 'type': 'bool'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [{'name': '', 'type': 'address'}], 'name': 'Participants', 'outputs': [{'name': 'lockedDeposit', 'type': 'uint256'}, {'name': 'lockedTime', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': 'threshold', 'type': 'uint256'}], 'name': 'setRnodeThreshold', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': True, 'inputs': [{'name': 'addr', 'type': 'address'}], 'name': 'isRnode', 'outputs': [{'name': '', 'type': 'bool'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'rnodeThreshold', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [], 'name': 'joinRnode', 'outputs': [], 'payable': True, 'stateMutability': 'payable', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'getRnodes', 'outputs': [{'name': '', 'type': 'address[]'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'period', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'inputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'constructor'}, {'anonymous': False, 'inputs': [{'indexed': False, 'name': 'who', 'type': 'address'}, {'indexed': False, 'name': 'lockedDeposit', 'type': 'uint256'}, {'indexed': False, 'name': 'lockedTime', 'type': 'uint256'}], 'name': 'NewRnode', 'type': 'event'}, {'anonymous': False, 'inputs': [{'indexed': False, 'name': 'who', 'type': 'address'}], 'name': 'RnodeQuit', 'type': 'event'}
    global bin
    bin = "6080604052603c600155692a5a058fc295ed00000060025534801561002357600080fd5b50336000806101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff160217905550610e04806100736000396000f3006080604052600436106100af576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680630b443f42146100b45780630f3a9f65146100df578063113c84981461010c5780631627905514610123578063595aa13d1461017e578063975dd4b2146101dc578063a8f0769714610209578063b7b3e9da14610264578063b892c6da1461028f578063e508bb8514610299578063ef78d4fd14610305575b600080fd5b3480156100c057600080fd5b506100c9610330565b6040518082815260200191505060405180910390f35b3480156100eb57600080fd5b5061010a60048036038101908080359060200190929190505050610340565b005b34801561011857600080fd5b506101216103a5565b005b34801561012f57600080fd5b50610164600480360381019080803573ffffffffffffffffffffffffffffffffffffffff169060200190929190505050610564565b604051808215151515815260200191505060405180910390f35b34801561018a57600080fd5b506101bf600480360381019080803573ffffffffffffffffffffffffffffffffffffffff169060200190929190505050610577565b604051808381526020018281526020019250505060405180910390f35b3480156101e857600080fd5b506102076004803603810190808035906020019092919050505061059b565b005b34801561021557600080fd5b5061024a600480360381019080803573ffffffffffffffffffffffffffffffffffffffff169060200190929190505050610600565b604051808215151515815260200191505060405180910390f35b34801561027057600080fd5b5061027961061d565b6040518082815260200191505060405180910390f35b610297610623565b005b3480156102a557600080fd5b506102ae6108e8565b6040518080602001828103825283818151815260200191508051906020019060200280838360005b838110156102f15780820151818401526020810190506102d6565b505050509050019250505060405180910390f35b34801561031157600080fd5b5061031a6108f9565b6040518082815260200191505060405180910390f35b6000600360010180549050905090565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff1614151561039b57600080fd5b8060018190555050565b6103b93360036108ff90919063ffffffff16565b15156103c457600080fd5b42600154600560003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060010154011115151561041957600080fd5b3373ffffffffffffffffffffffffffffffffffffffff166108fc600560003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600001549081150290604051600060405180830381858888f193505050501580156104a1573d6000803e3d6000fd5b506000600560003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600001819055506104fe33600361095890919063ffffffff16565b507f602a2a9c94f70293aa2be9077f0b2dc89d388bc293fdbcd968274f43494c380d33604051808273ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200191505060405180910390a1565b600080823b905060008111915050919050565b60056020528060005260406000206000915090508060000154908060010154905082565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff161415156105f657600080fd5b8060028190555050565b60006106168260036108ff90919063ffffffff16565b9050919050565b60025481565b61062c33610564565b1515156106c7576040517f08c379a000000000000000000000000000000000000000000000000000000000815260040180806020018281038252602a8152602001807f706c65617365206e6f742075736520636f6e74726163742063616c6c2074686981526020017f732066756e6374696f6e0000000000000000000000000000000000000000000081525060400191505060405180910390fd5b6106db3360036108ff90919063ffffffff16565b1515156106e757600080fd5b60025434101515156106f857600080fd5b61074d34600560003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060000154610bab90919063ffffffff16565b600560003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000018190555042600560003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600101819055506107ee336003610bc990919063ffffffff16565b507f586bfaa7a657ad9313326c9269639546950d589bd479b3d6928be469d6dc290333600560003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060000154600560003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060010154604051808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001838152602001828152602001935050505060405180910390a1565b60606108f46003610cf5565b905090565b60015481565b60008260000160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060009054906101000a900460ff16905092915050565b60008060008460000160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060009054906101000a900460ff1615156109bb5760009250610ba3565b60008560000160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060006101000a81548160ff02191690831515021790555084600101805490509150600090505b81811015610b9e578373ffffffffffffffffffffffffffffffffffffffff168560010182815481101515610a5457fe5b9060005260206000200160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff161415610b91578460010160018303815481101515610aaf57fe5b9060005260206000200160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff168560010182815481101515610aeb57fe5b9060005260206000200160006101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff1602179055508460010160018303815481101515610b4757fe5b9060005260206000200160006101000a81549073ffffffffffffffffffffffffffffffffffffffff021916905584600101805480919060019003610b8b9190610d87565b50610b9e565b8080600101915050610a24565b600192505b505092915050565b6000808284019050838110151515610bbf57fe5b8091505092915050565b60008260000160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060009054906101000a900460ff1615610c285760009050610cef565b60018360000160008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060006101000a81548160ff021916908315150217905550826001018290806001815401808255809150509060018203906000526020600020016000909192909190916101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff16021790555050600190505b92915050565b606081600101805480602002602001604051908101604052809291908181526020018280548015610d7b57602002820191906000526020600020905b8160009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019060010190808311610d31575b50505050509050919050565b815481835581811115610dae57818360005260206000209182019101610dad9190610db3565b5b505050565b610dd591905b80821115610dd1576000816000905550600101610db9565b5090565b905600a165627a7a72305820a61199baf3a5c3a2b980fae962df409a696d87b726b0836a07c747a7173bc5370029"
    global contract_address
    contract_address = "0x37880d44eE800AD4819117c5B498Fb4D4192c5B2"


def compile_file():
    output = compile_files(["../rnode.sol"])
    abi = output['../rnode.sol:Rnode']["abi"]
    bin = output['../rnode.sol:Rnode']["bin"]
    print(abi)
    print(bin)
    config = {}
    config["abi"] = abi
    config["bin"] = bin
    print("config: ")
    print(config)

    return config


# def compile_contract():
#     sol_map = {
#         "language": "Solidity",
#         "sources": {},
#         "settings": {
#             "optimizer": {
#                 "enabled": True
#             },
#             "outputSelection": {
#                 "*": {
#                     "*": ["abi", "evm.bytecode"]
#                 }
#             }
#         }
#     }
#     d = sol_map["sources"]["Rnode.sol"] = {}
#     d["urls"] = ["../rnode.sol"]
#     output = compile_standard(sol_map, allow_paths="../")
#     return output['contracts']['contract']['Rnode']


def deploy_contract(interface):
    init()
    cf.cpc.defaultAccount = owner
    contract = cf.cpc.contract(abi=interface['abi'], bytecode=interface['bin'])

    estimated_gas = contract.constructor().estimateGas()
    tx_hash = contract.constructor().transact(dict(gas=estimated_gas))

    # get tx receipt to get contract address
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    address = tx_receipt['contractAddress']

    # contract = cf.cpc.contract(address=address, abi=interface['abi'])

    return address

def get_contract():
    print("address: ", contract_address)
    print("abi: ", abi)
    return cf.cpc.contract(address=contract_address, abi=abi)


def test_claim_rnode(addr, contract_instance):
    contract = contract_instance
    cf.cpc.defaultAccount = addr
    tx_hash = contract.functions.joinRnode().transact({"gas": 200000, "from": addr, "value": 210000 * cpc})
    print("tx hash: ", tx_hash)
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("tx receipt: ", tx_receipt)


def test_claim_rnode_failure(addr, contract_instance):
    contract = contract_instance
    cf.cpc.defaultAccount = addr
    tx_hash = contract.functions.joinRnode().transact({"gas": 200000, "from": addr, "value": 10})
    print("tx hash: ", tx_hash)
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("tx receipt: ", tx_receipt)


def test_quit_rnode(addr, contract_instance):
    contract = contract_instance
    cf.cpc.defaultAccount = addr
    tx_hash = contract.functions.quitRnode().transact({"from": addr, "gas": 200000})
    print("tx hash: ", tx_hash)
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("tx receipt: ", tx_receipt)


def is_rnode(addr, contract_instance):
    contract = contract_instance
    cf.cpc.defaultAccount = addr
    result = contract.functions.isRnode(addr).call({"from": addr})
    print("is rnode: ", result)
    # print("tx hash: ", tx_hash)
    # tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    # print("tx receipt: ", tx_receipt)


def test_set_period(addr, contract_instance, period):
    contract = contract_instance
    cf.cpc.defaultAccount = addr
    tx_hash = contract.functions.setPeriod(period).transact({"from": addr, "gas": 200000})
    print("tx hash: ", tx_hash)
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("tx receipt: ", tx_receipt)


def test_case_1():
    print("test join rnode failed because money not enough")
    init()
    contract_ins = get_contract()
    print("balance before claim: ", cf.fromWei(cf.cpc.getBalance(rnode_failed), 'ether'))
    print("is rnode before: ", is_rnode(rnode_failed, contract_ins))
    print("claim rnode...")
    test_claim_rnode_failure(rnode_failed, contract_ins)
    time.sleep(20)
    print("balance after claim: ", cf.fromWei(cf.cpc.getBalance(rnode_failed), 'ether'))
    print("is rnode after: ", is_rnode(rnode_failed, contract_ins))


def test_case_2():
    print("test join rnode succeed")
    init()
    contract_ins = get_contract()
    print("balance before claim: ", cf.fromWei(cf.cpc.getBalance(rnode_succeed), 'ether'))
    print("is rnode before: ", is_rnode(rnode_succeed, contract_ins))
    print("claim rnode...")
    test_claim_rnode(rnode_succeed, contract_ins)
    time.sleep(20)
    print("balance after claim: ", cf.fromWei(cf.cpc.getBalance(rnode_succeed), 'ether'))
    print("is rnode after: ", is_rnode(rnode_succeed, contract_ins))


def test_case_3():
    print("test join rnode again")
    init()
    contract_ins = get_contract()
    print("balance before claim: ", cf.fromWei(cf.cpc.getBalance(rnode_succeed), 'ether'))
    print("is rnode before: ", is_rnode(rnode_succeed, contract_ins))
    print("claim rnode...")
    test_claim_rnode(rnode_succeed, contract_ins)
    time.sleep(20)
    print("balance after claim: ", cf.fromWei(cf.cpc.getBalance(rnode_succeed), 'ether'))
    print("is rnode after: ", is_rnode(rnode_succeed, contract_ins))


def test_case_4():
    print("test quit rnode")
    init()
    contract_ins = get_contract()
    print("balance before quit: ", cf.fromWei(cf.cpc.getBalance(rnode_succeed), 'ether'))
    print("is rnode before: ", is_rnode(rnode_succeed, contract_ins))
    print("quit rnode...")
    test_quit_rnode(rnode_succeed, contract_ins)
    time.sleep(20)
    print("balance after quit: ", cf.fromWei(cf.cpc.getBalance(rnode_succeed), 'ether'))
    print("is rnode after: ", is_rnode(rnode_succeed, contract_ins))


def test_case_5():
    print("test quit rnode while not a rnode")
    init()
    contract_ins = get_contract()
    print("balance before quit: ", cf.fromWei(cf.cpc.getBalance(rnode_failed), 'ether'))
    print("is rnode before: ", is_rnode(rnode_failed, contract_ins))
    print("quit rnode...")
    test_quit_rnode(rnode_failed, contract_ins)
    time.sleep(20)
    print("balance after quit: ", cf.fromWei(cf.cpc.getBalance(rnode_failed), 'ether'))
    print("is rnode after: ", is_rnode(rnode_failed, contract_ins))


def test_case_6():
    # test owner sets period
    init()
    contract_ins = get_contract()
    print("before set")
    print("period: ", contract_ins.functions.period().call())
    print("setting...")
    test_set_period(owner, contract_ins, 99)
    time.sleep(20)
    print("after set")
    print("period: ", contract_ins.functions.period().call())


def main():
    config = compile_file()
    print(config['abi'])
    print(config['bin'])
    # address = deploy_contract(config)
    # print(address)
    # test_case_1()
    # test_case_2()
    # test_case_3()
    # test_case_4()
    # test_case_5()
    # test_case_6()


if __name__ == '__main__':
    main()
