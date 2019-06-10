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


def check_campaign(config):
    cf = Web3(Web3.HTTPProvider("http://127.0.0.1:8521"))
    abi = config["abi"]
    address = cf.toChecksumAddress("0xf26b6864749cde85a29afea57ffeae115b24b505")
    campaign = cf.cpc.contract(abi=abi, address=address)
    term_id = campaign.functions.termIdx().call()
    print("current term: ", term_id)
    print("block number: ", cf.cpc.blockNumber)
    for i in range(term_id-10, term_id):
        candidates = campaign.functions.candidatesOf(i).call()
        print("candidates: ", candidates)


def set_max_candidate(config):
    cf = Web3(Web3.HTTPProvider("http://127.0.0.1:8521"))
    abi = config["abi"]
    address = cf.toChecksumAddress("0xf26b6864749cde85a29afea57ffeae115b24b505")
    campaign = cf.cpc.contract(abi=abi, address=address)
    tx_hash = campaign.functions.updateMaxCandidates(5).transact({"from": cf.cpc.accounts[0], "gas": 88888888, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])


def prepare():
    cf = Web3(Web3.HTTPProvider("http://127.0.0.1:8521"))
    print("current account: ", cf.cpc.accounts)
    print("balance of owner: ", cf.fromWei(cf.cpc.getBalance(cf.cpc.accounts[0]), "ether"))
    # cf.personal.newAccount("password")
    print("current account: ", cf.cpc.accounts)
    cf.cpc.sendTransaction({"from": "0xb3801b8743DEA10c30b0c21CAe8b1923d9625F84", "to": "0x3Bd95ae403FD7D98972D54e0d44F332bEf9Bc175", "value": cf.toWei(100000, "ether")})
    # print("balance of owner: ", cf.fromWei(cf.cpc.getBalance("0xcA2a8be03aB0889b0a7edBD95550e5C61D557670"), "ether"))


def test_case_2():
    cf = Web3(Web3.HTTPProvider("http://127.0.0.1:8521"))
    print("========config account=========")
    candidate = "0x3Bd95ae403FD7D98972D54e0d44F332bEf9Bc175"
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

    print("============owner update configs=====================")
    cf.cpc.defaultAccount = owner
    print("owner set max candidates")
    tx_hash = campaign.functions.updateMaxCandidates(1).transact({"gas": 89121, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    print("after owner set")
    max_candidate = campaign.functions.maxCandidates().call()
    print("max candidates: ", max_candidate)

    print("==================claim campaign===============")
    cf.cpc.defaultAccount = candidate
    tx_hash = campaign.functions.claimCampaign(3, 0, 0, 0, 0, 2).transact({"gas": 989121, "from": candidate, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("claim result: ", tx_receipt["status"])
    print(tx_receipt)

    cf.cpc.defaultAccount = owner
    tx_hash = campaign.functions.claimCampaign(3, 0, 0, 0, 0, 2).transact({"gas": 989121, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("claim result: ", tx_receipt["status"])
    print(tx_receipt)

    term_id = campaign.functions.termIdx().call()
    print("current term: ", term_id)
    candidates = campaign.functions.candidatesOf(term_id+1).call()
    print("term: ", term_id+1)
    print(candidates)

    candidates = campaign.functions.candidatesOf(term_id+2).call()
    print("term: ", term_id+2)
    print(candidates)

    candidates = campaign.functions.candidatesOf(term_id+3).call()
    print("term: ", term_id+3)
    print(candidates)

    # cf.cpc.defaultAccount = candidate
    # while True:
    #     term_id = campaign.functions.termIdx().call()
    #     updated_term = campaign.functions.updatedTermIdx().call()
    #     block_number = cf.cpc.blockNumber
    #     blocks_per_term = campaign.functions.numPerRound().call()
    #     print("block number: ", block_number)
    #     print("blocks per term: ", blocks_per_term)
    #     print("current term: ", term_id)
    #     print("updated term: ", updated_term)
    #     print("candidate try once")
    #     tx_hash = campaign.functions.claimCampaign(3, 0, 0, 0, 0, 2).transact({"gas": 989121, "from": candidate, "value": 0})
    #     tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    #     print("claim result: ", tx_receipt["status"])
    #     candidates = campaign.functions.candidatesOf(term_id+1).call()
    #     print("candidates: ", candidates)




def main():
    # test_case_1()
    # compile_file()
    # prepare()
    test_case_2()


if __name__ == '__main__':
    main()
