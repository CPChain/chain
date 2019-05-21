from solc import compile_files

from cpc_fusion import Web3

import time


def compile_file():
    output = compile_files(["../campaign.sol"])
    abi = output['../campaign.sol:Campaign']["abi"]
    bin = output['../campaign.sol:Campaign']["bin"]
    print(abi)
    print(bin)
    config = {}
    config["abi"] = abi
    config["bin"] = bin
    print("config: ")
    print(config)

    return config

def test_case_1():
    cf = Web3(Web3.HTTPProvider("http://127.0.0.1:8521"))
    print("========config account=========")
    candidate = "0x4dc8319379E36534b60f5E93C4715d39042723d5"
    owner = "0xb3801b8743DEA10c30b0c21CAe8b1923d9625F84"
    password = "password"
    cf.personal.unlockAccount(candidate, password)
    cf.personal.unlockAccount(owner, password)
    print("balance of candidate: ", cf.fromWei(cf.cpc.getBalance(candidate), "ether"))
    print("balance of owner: ", cf.fromWei(cf.cpc.getBalance(owner), "ether"))

    print("===========deploy contract==============")
    config = compile_file()
    contract = cf.cpc.contract(abi=config["abi"], bytecode=config["bin"])
    cf.cpc.defaultAccount = owner
    estimated_gas = contract.constructor("0xA5e0EA2a14d91031986c2f25F6e724BEeeB66781", "0xD4826927aa2dba7930117782ED183576CCeBEd93").estimateGas()
    tx_hash = contract.constructor("0xA5e0EA2a14d91031986c2f25F6e724BEeeB66781", "0xD4826927aa2dba7930117782ED183576CCeBEd93").transact(dict(gas=estimated_gas))
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    address = tx_receipt['contractAddress']
    print("contract address: ", address)

    print("============read configs==============")
    campaign = cf.cpc.contract(abi=config["abi"], address=address)
    term_id = campaign.functions.termIdx().call()
    view_len = campaign.functions.viewLen().call()
    term_len = campaign.functions.termLen().call()
    print("current term: ", term_id)
    print("view length: ", view_len)
    print("term length: ", term_len)

    print("===========candidate tries to set configs=============")
    cf.cpc.defaultAccount = candidate
    tx_hash = campaign.functions.updateTermLen(1).transact({"gas": 89121, "from": candidate, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    print("after candidate update")
    term_len = campaign.functions.termLen().call()
    print("term length: ", term_len)

    print("============owner update configs=====================")
    cf.cpc.defaultAccount = owner
    print("owner set termLen")
    tx_hash = campaign.functions.updateTermLen(1).transact({"gas": 89121, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    print("owner set viewLen")
    tx_hash = campaign.functions.updateViewLen(1).transact({"gas": 89121, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    print("after owner set")
    term_id = campaign.functions.termIdx().call()
    view_len = campaign.functions.viewLen().call()
    term_len = campaign.functions.termLen().call()
    print("current term: ", term_id)
    print("view length: ", view_len)
    print("term length: ", term_len)

    print("============candidate claim campaign===============")
    cf.cpc.defaultAccount = candidate
    while True:
        term_id = campaign.functions.termIdx().call()
        updated_term = campaign.functions.updatedTermIdx().call()
        block_number = cf.cpc.blockNumber
        blocks_per_term = campaign.functions.numPerRound().call()
        print("block number: ", block_number)
        print("blocks per term: ", blocks_per_term)
        print("current term: ", term_id)
        print("updated term: ", updated_term)
        print("candidate try once")
        tx_hash = campaign.functions.claimCampaign(3, 0, 0, 0, 0, 2).transact({"gas": 989121, "from": candidate, "value": 0})
        tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
        print("claim result: ", tx_receipt["status"])
        candidates = campaign.functions.candidatesOf(term_id+1).call()
        print("candidates: ", candidates)
        # time.sleep(4)




    #     uint _numOfCampaign,  // number of terms that the node want to claim campaign
    #
    # // admission parameters
    # uint64 _cpuNonce,
    # uint _cpuBlockNumber,
    # uint64 _memoryNonce,
    # uint _memoryBlockNumber,
    # uint version

def check_campaign():
    cf = Web3(Web3.HTTPProvider("http://127.0.0.1:8521"))
    abi = [{'constant': True, 'inputs': [], 'name': 'termLen', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [{'name': '_termIdx', 'type': 'uint256'}], 'name': 'candidatesOf', 'outputs': [{'name': '', 'type': 'address[]'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_numOfCampaign', 'type': 'uint256'}, {'name': '_cpuNonce', 'type': 'uint64'}, {'name': '_cpuBlockNumber', 'type': 'uint256'}, {'name': '_memoryNonce', 'type': 'uint64'}, {'name': '_memoryBlockNumber', 'type': 'uint256'}, {'name': 'version', 'type': 'uint256'}], 'name': 'claimCampaign', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'termIdx', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'minNoc', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'numPerRound', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'viewLen', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'updatedTermIdx', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_supportedVersion', 'type': 'uint256'}], 'name': 'updateSupportedVersion', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_maxNoc', 'type': 'uint256'}], 'name': 'updateMaxNoc', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_minNoc', 'type': 'uint256'}], 'name': 'updateMinNoc', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'acceptableBlocks', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_addr', 'type': 'address'}], 'name': 'setAdmissionAddr', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_termLen', 'type': 'uint256'}], 'name': 'updateTermLen', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_viewLen', 'type': 'uint256'}], 'name': 'updateViewLen', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'supportedVersion', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_acceptableBlocks', 'type': 'uint256'}], 'name': 'updateAcceptableBlocks', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': True, 'inputs': [{'name': '_candidate', 'type': 'address'}], 'name': 'candidateInfoOf', 'outputs': [{'name': '', 'type': 'uint256'}, {'name': '', 'type': 'uint256'}, {'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'maxNoc', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_addr', 'type': 'address'}], 'name': 'setRnodeInterface', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'inputs': [{'name': '_admissionAddr', 'type': 'address'}, {'name': '_rnodeAddr', 'type': 'address'}], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'constructor'}, {'payable': True, 'stateMutability': 'payable', 'type': 'fallback'}, {'anonymous': False, 'inputs': [{'indexed': False, 'name': 'candidate', 'type': 'address'}, {'indexed': False, 'name': 'startTermIdx', 'type': 'uint256'}, {'indexed': False, 'name': 'stopTermIdx', 'type': 'uint256'}], 'name': 'ClaimCampaign', 'type': 'event'}]
    address = "0xa3D1C5b449007f3A3002917D496E7Ed328D3c710"
    campaign = cf.cpc.contract(abi=abi, address=address)
    term_id = campaign.functions.termIdx().call()
    print("current term: ", term_id)
    print("block number: ", cf.cpc.blockNumber)
    for i in range(term_id-20, term_id):
        candidates = campaign.functions.candidatesOf(i).call()
        print("candidates: ", candidates)



def prepare():
    cf = Web3(Web3.HTTPProvider("http://127.0.0.1:8521"))
    print("current account: ", cf.cpc.accounts)
    print("balance of owner: ", cf.fromWei(cf.cpc.getBalance(cf.cpc.accounts[0]), "ether"))
    # cf.personal.newAccount("password")
    print("current account: ", cf.cpc.accounts)
    cf.cpc.sendTransaction({"from": "0xb3801b8743DEA10c30b0c21CAe8b1923d9625F84", "to": "0x4dc8319379E36534b60f5E93C4715d39042723d5", "value": cf.toWei(100000, "ether")})
    print("balance of owner: ", cf.fromWei(cf.cpc.getBalance("0x4dc8319379E36534b60f5E93C4715d39042723d5"), "ether"))


def main():
    # check_campaign()
    # test_case_1()
    compile_file()
    # prepare()


if __name__ == '__main__':
    main()
