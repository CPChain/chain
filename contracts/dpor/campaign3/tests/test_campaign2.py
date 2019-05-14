from solc import compile_files

from cpc_fusion import Web3


def compile_file():
    output = compile_files(["../campaign3.sol"])
    abi = output['../campaign3.sol:Campaign']["abi"]
    bin = output['../campaign3.sol:Campaign']["bin"]
    print(abi)
    print(bin)
    config = {}
    config["abi"] = abi
    config["bin"] = bin
    print("config: ")
    print(config)

    return config


def deploy_contract(interface):
    rnode_contract_address = "0x7B4769C7d332105F8Ace1506c322597AEd7DeF59"
    cf = Web3(Web3.HTTPProvider("http://13.250.201.89:8501"))
    contract = cf.cpc.contract(abi=interface['abi'], bytecode=interface['bin'])

    estimated_gas = contract.constructor("0x8f01875F462CBBc956CB9C0392dE6053A31C9C99", rnode_contract_address).estimateGas()
    tx_hash = contract.constructor("0x8f01875F462CBBc956CB9C0392dE6053A31C9C99", rnode_contract_address).transact(dict(gas=estimated_gas))

    # get tx receipt to get contract address
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    address = tx_receipt['contractAddress']

    # contract = cf.cpc.contract(address=address, abi=interface['abi'])

    return address


def test_campaign(contract_abi, contract_address):
    abi = contract_abi
    address = contract_address
    cf = Web3(Web3.HTTPProvider('http://13.250.201.89:8501'))

    # cf.cpc.defaultAccount = cf.cpc.accounts[0]

    campaign = cf.cpc.contract(abi=abi, address=address)

    withdraw_term = campaign.functions.withdrawTermIdx().call()
    print("withdraw term: ", withdraw_term)
    terms = campaign.functions.termIdx().call()
    print("term: ", terms)
    # start = terms - 10
    # end = terms
    # print("total terms: ", terms)
    # for term in range(start, end):
    #     result = campaign.functions.candidatesOf(term).call()
    #     num = len(result)
    #     print("term: ", term)
    #     print("number of candidate: ", num)
    #     print(result)


def main():
    # init()
    config = compile_file()
    print(config['abi'])
    print(config['bin'])
    # address = deploy_contract(config)
    # print(address)
    # test_campaign(config['abi'], address)


if __name__ == '__main__':
    main()
