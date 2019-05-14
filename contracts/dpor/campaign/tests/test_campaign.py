from cpc_fusion import Web3

from solc import compile_files


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


def test_campaign():
    config = compile_file()
    abi = config['abi']
    contract_address = "0x1404Bf355428523F8e51E68Df00A0521e413F98E"

    cf = Web3(Web3.HTTPProvider('http://192.168.123.124:8501'))

    # cf.cpc.defaultAccount = cf.cpc.accounts[0]

    campaign = cf.cpc.contract(abi=abi, address=contract_address)

    terms = campaign.functions.termIdx().call()
    start = terms - 10
    end = terms
    print("total terms: ", terms)
    num_per_term = campaign.functions.numPerRound().call()
    print(num_per_term)
    for term in range(200, 230):
        result = campaign.functions.candidatesOf(term).call()
        print("term: ", term)
        print("number of candidate: ", len(result))
        print(result)


def main():
    test_campaign()


if __name__ == '__main__':
    main()
