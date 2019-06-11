from solc import compile_files

from cpc_fusion import Web3


def compile_file():
    output = compile_files(["../reward.sol"])
    abi = output['../reward.sol:Reward']["abi"]
    bin = output['../reward.sol:Reward']["bin"]
    print(abi)
    print(bin)
    config = {}
    config["abi"] = abi
    config["bin"] = bin
    print("config: ")
    print(config)

    return config


def test_case_1():
    pass


def main():
    compile_file()


if __name__ == '__main__':
    main()
