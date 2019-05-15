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


def main():
    config = compile_file()
    print(config["abi"])


if __name__ == '__main__':
    main()
