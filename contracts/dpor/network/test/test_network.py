from solc import compile_files

from cpc_fusion import Web3

def compile_file():
    output = compile_files(["../network.sol"])
    abi = output['../network.sol:Network']["abi"]
    bin = output['../network.sol:Network']["bin"]
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
    cf.cpc.defaultAccount = cf.cpc.accounts[0]
    cf.personal.unlockAccount(cf.cpc.accounts[0], "password")
    config = compile_file()
    contract = cf.cpc.contract(abi=config["abi"], bytecode=config["bin"])
    print("===========deploy contract================")
    estimated_gas = contract.constructor().estimateGas()
    tx_hash = contract.constructor().transact(dict(gas=estimated_gas))
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    address = tx_receipt['contractAddress']
    print("contract address: ", address)
    network_ins = cf.cpc.contract(abi=config["abi"], address=address)
    print("============read config===================")
    host = network_ins.functions.host().call()
    count = network_ins.functions.count().call()
    timeout = network_ins.functions.timeout().call()
    gap = network_ins.functions.gap().call()
    open = network_ins.functions.open().call()
    print("host: ", host)
    print("count: ", count)
    print("timeout: ", timeout)
    print("gap: ", gap)
    print("open: ", open)
    print("============owner set configs=============")
    tx_hash = network_ins.functions.updateHost("google.com").transact({"gas": 8888888})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("set host result: ", tx_receipt["status"])
    tx_hash = network_ins.functions.updateCount(10).transact({"gas": 8888888})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("set count result: ", tx_receipt["status"])
    tx_hash = network_ins.functions.updateTimeout(300).transact({"gas": 8888888})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("set timeout result: ", tx_receipt["status"])
    tx_hash = network_ins.functions.updateGap(10).transact({"gas": 8888888})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("set gap result: ", tx_receipt["status"])
    tx_hash = network_ins.functions.updateOpen(False).transact({"gas": 8888888})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("set open result: ", tx_receipt["status"])
    print("============read config again===============")
    host = network_ins.functions.host().call()
    count = network_ins.functions.count().call()
    timeout = network_ins.functions.timeout().call()
    gap = network_ins.functions.gap().call()
    open = network_ins.functions.open().call()
    print("host: ", host)
    print("count: ", count)
    print("timeout: ", timeout)
    print("gap: ", gap)
    print("open: ", open)


def main():
    test_case_1()


if __name__ == '__main__':
    main()
