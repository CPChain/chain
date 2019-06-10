from solc import compile_files
import json

def compile_file(contract_path, contract_name):
    output = compile_files([contract_path])
    abi = output[contract_path+":"+contract_name]["abi"]
    bin = output[contract_path+":"+contract_name]["bin"]
    config = {}
    config["abi"] = abi
    config["bin"] = bin
    print("config: ")
    print(config)

    return config



def main():
    admission_config = compile_file("./dpor/admission/admission.sol", "Admission")
    with open("./assets/config/admission.json", "w+") as f:
        f.write(json.dumps(admission_config))

    campaign_config = compile_file("./dpor/campaign/campaign.sol", "Campaign")
    with open("./assets/config/campaign.json", "w+") as f:
        f.write(json.dumps(campaign_config))

    rpt_config = compile_file("./dpor/rpt/rpt.sol", "Rpt")
    with open("./assets/config/rpt.json", "w+") as f:
        f.write(json.dumps(rpt_config))

    rnode_config = compile_file("./dpor/rnode/rnode.sol", "Rnode")
    with open("./assets/config/rnode.json", "w+") as f:
        f.write(json.dumps(rnode_config))

    network_config = compile_file("./dpor/network/network.sol", "Network")
    with open("./assets/config/network.json", "w+") as f:
        f.write(json.dumps(network_config))

    reward_config = compile_file("./reward/reward.sol", "Reward")
    with open("./assets/config/reward.json", "w+") as f:
        f.write(json.dumps(reward_config))


if __name__ == '__main__':
    main()
