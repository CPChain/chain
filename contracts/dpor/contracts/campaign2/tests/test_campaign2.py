import math

from solc import compile_files

from cpc_fusion import Web3


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

    global rnode_contract_abi
    rnode_contract_abi = {'constant': True, 'inputs': [], 'name': 'getRnodeNum', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_period', 'type': 'uint256'}], 'name': 'setPeriod', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [], 'name': 'quitRnode', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': True, 'inputs': [{'name': 'addr', 'type': 'address'}], 'name': 'isContract', 'outputs': [{'name': '', 'type': 'bool'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [{'name': '', 'type': 'address'}], 'name': 'Participants', 'outputs': [{'name': 'lockedDeposit', 'type': 'uint256'}, {'name': 'lockedTime', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': 'threshold', 'type': 'uint256'}], 'name': 'setRnodeThreshold', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': True, 'inputs': [{'name': 'addr', 'type': 'address'}], 'name': 'isRnode', 'outputs': [{'name': '', 'type': 'bool'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'rnodeThreshold', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [], 'name': 'joinRnode', 'outputs': [], 'payable': True, 'stateMutability': 'payable', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'getRnodes', 'outputs': [{'name': '', 'type': 'address[]'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'period', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'inputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'constructor'}, {'anonymous': False, 'inputs': [{'indexed': False, 'name': 'who', 'type': 'address'}, {'indexed': False, 'name': 'lockedDeposit', 'type': 'uint256'}, {'indexed': False, 'name': 'lockedTime', 'type': 'uint256'}], 'name': 'NewRnode', 'type': 'event'}, {'anonymous': False, 'inputs': [{'indexed': False, 'name': 'who', 'type': 'address'}], 'name': 'RnodeQuit', 'type': 'event'}
    global rnode_contract_address
    rnode_contract_address = "0x37880d44eE800AD4819117c5B498Fb4D4192c5B2"

    global campaign2_contract_abi
    campaign2_contract_abi = {'constant': True, 'inputs': [], 'name': 'termLen', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_numOfCampaign', 'type': 'uint256'}, {'name': '_cpuNonce', 'type': 'uint64'}, {'name': '_cpuBlockNumber', 'type': 'uint256'}, {'name': '_memoryNonce', 'type': 'uint64'}, {'name': '_memoryBlockNumber', 'type': 'uint256'}], 'name': 'claimCampaign', 'outputs': [], 'payable': True, 'stateMutability': 'payable', 'type': 'function'}, {'constant': True, 'inputs': [{'name': '_termIdx', 'type': 'uint256'}], 'name': 'candidatesOf', 'outputs': [{'name': '', 'type': 'address[]'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'termIdx', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'minNoc', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'numPerRound', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'viewLen', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_maxNoc', 'type': 'uint256'}], 'name': 'updateMaxNoc', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_minNoc', 'type': 'uint256'}], 'name': 'updateMinNoc', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_addr', 'type': 'address'}], 'name': 'setAdmissionAddr', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_termLen', 'type': 'uint256'}], 'name': 'updateTermLen', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_viewLen', 'type': 'uint256'}], 'name': 'updateViewLen', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': True, 'inputs': [{'name': '_candidate', 'type': 'address'}], 'name': 'candidateInfoOf', 'outputs': [{'name': '', 'type': 'uint256'}, {'name': '', 'type': 'uint256'}, {'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'maxNoc', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_addr', 'type': 'address'}], 'name': 'setRnodeInterface', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [], 'name': 'updateCandidateStatus', 'outputs': [], 'payable': True, 'stateMutability': 'payable', 'type': 'function'}, {'inputs': [{'name': '_admissionAddr', 'type': 'address'}, {'name': '_rnodeAddr', 'type': 'address'}], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'constructor'}, {'payable': True, 'stateMutability': 'payable', 'type': 'fallback'}, {'anonymous': False, 'inputs': [{'indexed': False, 'name': 'candidate', 'type': 'address'}, {'indexed': False, 'name': 'startTermIdx', 'type': 'uint256'}, {'indexed': False, 'name': 'stopTermIdx', 'type': 'uint256'}], 'name': 'ClaimCampaign', 'type': 'event'}, {'anonymous': False, 'inputs': [{'indexed': False, 'name': 'candidate', 'type': 'address'}, {'indexed': False, 'name': 'payback', 'type': 'uint256'}], 'name': 'QuitCampaign', 'type': 'event'}, {'anonymous': False, 'inputs': [], 'name': 'ViewChange', 'type': 'event'}
    global campaign2_contract_address
    campaign2_contract_address = "0x4cEC126e475D4F4FF3d8eFa549a985f11B19621A"


def compile_file():
    output = compile_files(["../campaign2.sol"])
    abi = output['../campaign2.sol:Campaign']["abi"]
    bin = output['../campaign2.sol:Campaign']["bin"]
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

    estimated_gas = contract.constructor("0x8f01875F462CBBc956CB9C0392dE6053A31C9C99", rnode_contract_address).estimateGas()
    tx_hash = contract.constructor("0x8f01875F462CBBc956CB9C0392dE6053A31C9C99", rnode_contract_address).transact(dict(gas=estimated_gas))

    # get tx receipt to get contract address
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    address = tx_receipt['contractAddress']

    # contract = cf.cpc.contract(address=address, abi=interface['abi'])

    return address


def main():
    init()
    config = compile_file()
    address = deploy_contract(config)
    print(address)


if __name__ == '__main__':
    main()
