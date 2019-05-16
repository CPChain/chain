from solc import compile_files

from cpc_fusion import Web3

def compile_file():
    output = compile_files(["../rpt.sol"])
    abi = output['../rpt.sol:Rpt']["abi"]
    bin = output['../rpt.sol:Rpt']["bin"]
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
    civilian = "0x970c18A634B23c95a61746d172C48356DB58D8EC"
    owner = "0xb3801b8743DEA10c30b0c21CAe8b1923d9625F84"
    password = "password"
    cf.personal.unlockAccount(civilian, password)
    cf.personal.unlockAccount(owner, password)
    print("balance of civilian: ", cf.fromWei(cf.cpc.getBalance(civilian), "ether"))
    print("balance of owner: ", cf.fromWei(cf.cpc.getBalance(owner), "ether"))

    print("===========deploy contract==============")
    config = compile_file()
    contract = cf.cpc.contract(abi=config["abi"], bytecode=config["bin"])
    cf.cpc.defaultAccount = owner
    estimated_gas = contract.constructor().estimateGas()
    tx_hash = contract.constructor().transact(dict(gas=estimated_gas))
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    address = tx_receipt['contractAddress']
    print("contract address: ", address)

    print("============read configs================")
    rpt_ins = cf.cpc.contract(abi=config["abi"], address=address)
    window = rpt_ins.functions.window().call()
    alpha = rpt_ins.functions.alpha().call()
    beta = rpt_ins.functions.beta().call()
    gamma = rpt_ins.functions.gamma().call()
    psi = rpt_ins.functions.psi().call()
    omega = rpt_ins.functions.omega().call()
    random_level = rpt_ins.functions.randomLevel().call()
    print("window: ", window)
    print("alpha: ", alpha)
    print("beta: ", beta)
    print("gamma: ", gamma)
    print("psi: ", psi)
    print("omega: ", omega)
    print("random level: ", random_level)

    print("================test only owner=================")
    print("civilian tries to update configs")
    cf.cpc.defaultAccount = civilian
    tx_hash = rpt_ins.functions.updateConfigs(1,1,1,1,1,1,1).transact({"gas": 892113, "from": civilian, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    print("after update")
    window = rpt_ins.functions.window().call()
    alpha = rpt_ins.functions.alpha().call()
    beta = rpt_ins.functions.beta().call()
    gamma = rpt_ins.functions.gamma().call()
    psi = rpt_ins.functions.psi().call()
    omega = rpt_ins.functions.omega().call()
    random_level = rpt_ins.functions.randomLevel().call()
    print("window: ", window)
    print("alpha: ", alpha)
    print("beta: ", beta)
    print("gamma: ", gamma)
    print("psi: ", psi)
    print("omega: ", omega)
    print("random level: ", random_level)
    print("owner tries to set")
    cf.cpc.defaultAccount = owner
    tx_hash = rpt_ins.functions.updateConfigs(1,1,1,1,1,1,1).transact({"gas": 892113, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    print("after update")
    window = rpt_ins.functions.window().call()
    alpha = rpt_ins.functions.alpha().call()
    beta = rpt_ins.functions.beta().call()
    gamma = rpt_ins.functions.gamma().call()
    psi = rpt_ins.functions.psi().call()
    omega = rpt_ins.functions.omega().call()
    random_level = rpt_ins.functions.randomLevel().call()
    print("window: ", window)
    print("alpha: ", alpha)
    print("beta: ", beta)
    print("gamma: ", gamma)
    print("psi: ", psi)
    print("omega: ", omega)
    print("random level: ", random_level)


def main():
    test_case_1()


if __name__ == '__main__':
    main()
