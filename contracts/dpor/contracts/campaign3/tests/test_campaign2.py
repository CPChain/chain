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


def test_campaign():
    abi = {'constant': True, 'inputs': [], 'name': 'termLen', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_numOfCampaign', 'type': 'uint256'}, {'name': '_cpuNonce', 'type': 'uint64'}, {'name': '_cpuBlockNumber', 'type': 'uint256'}, {'name': '_memoryNonce', 'type': 'uint64'}, {'name': '_memoryBlockNumber', 'type': 'uint256'}], 'name': 'claimCampaign', 'outputs': [], 'payable': True, 'stateMutability': 'payable', 'type': 'function'}, {'constant': True, 'inputs': [{'name': '_termIdx', 'type': 'uint256'}], 'name': 'candidatesOf', 'outputs': [{'name': '', 'type': 'address[]'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'termIdx', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'minNoc', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'numPerRound', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'viewLen', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_maxNoc', 'type': 'uint256'}], 'name': 'updateMaxNoc', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_minNoc', 'type': 'uint256'}], 'name': 'updateMinNoc', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_addr', 'type': 'address'}], 'name': 'setAdmissionAddr', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_termLen', 'type': 'uint256'}], 'name': 'updateTermLen', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_viewLen', 'type': 'uint256'}], 'name': 'updateViewLen', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': True, 'inputs': [{'name': '_candidate', 'type': 'address'}], 'name': 'candidateInfoOf', 'outputs': [{'name': '', 'type': 'uint256'}, {'name': '', 'type': 'uint256'}, {'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': True, 'inputs': [], 'name': 'maxNoc', 'outputs': [{'name': '', 'type': 'uint256'}], 'payable': False, 'stateMutability': 'view', 'type': 'function'}, {'constant': False, 'inputs': [{'name': '_addr', 'type': 'address'}], 'name': 'setRnodeInterface', 'outputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'function'}, {'constant': False, 'inputs': [], 'name': 'updateCandidateStatus', 'outputs': [], 'payable': True, 'stateMutability': 'payable', 'type': 'function'}, {'inputs': [{'name': '_admissionAddr', 'type': 'address'}, {'name': '_rnodeAddr', 'type': 'address'}], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'constructor'}, {'payable': True, 'stateMutability': 'payable', 'type': 'fallback'}, {'anonymous': False, 'inputs': [{'indexed': False, 'name': 'candidate', 'type': 'address'}, {'indexed': False, 'name': 'startTermIdx', 'type': 'uint256'}, {'indexed': False, 'name': 'stopTermIdx', 'type': 'uint256'}], 'name': 'ClaimCampaign', 'type': 'event'}, {'anonymous': False, 'inputs': [{'indexed': False, 'name': 'candidate', 'type': 'address'}, {'indexed': False, 'name': 'payback', 'type': 'uint256'}], 'name': 'QuitCampaign', 'type': 'event'}, {'anonymous': False, 'inputs': [], 'name': 'ViewChange', 'type': 'event'}
    address = "0x238cFc9AD2C5685946CDd5EE67F116f6aCccF3b7"
    cf = Web3(Web3.HTTPProvider('http://192.168.123.124:8501'))

    # cf.cpc.defaultAccount = cf.cpc.accounts[0]

    campaign = cf.cpc.contract(abi=abi, address=address)

    terms = campaign.functions.termIdx().call()
    start = terms - 10
    end = terms
    print("total terms: ", terms)
    for term in range(start, end):
        result = campaign.functions.candidatesOf(term).call()
        num = len(result)
        print("term: ", term)
        print("number of candidate: ", num)
        print(result)


def main():
    # init()
    config = compile_file()
    print(config['abi'])
    print(config['bin'])
    address = deploy_contract(config)
    print(address)
    # test_campaign()


if __name__ == '__main__':
    main()
