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
    cf = Web3(Web3.HTTPProvider("http://127.0.0.1:8521"))
    print("========config account=========")
    enode = "0xDd6Fa584319199eBCBd5f9e8eDaE8FE9016680aE"
    civilian = "0xBaf0c559C77dDe9340C82df8043eD9a21f2577AF"
    owner = "0xb3801b8743DEA10c30b0c21CAe8b1923d9625F84"
    password = "password"
    cf.personal.unlockAccount(enode, password)
    cf.personal.unlockAccount(civilian, password)
    cf.personal.unlockAccount(owner, password)
    print("balance of enode: ", cf.fromWei(cf.cpc.getBalance(enode), "ether"))
    print("balance of civilian: ", cf.fromWei(cf.cpc.getBalance(civilian), "ether"))
    print("balance of owner: ", cf.fromWei(cf.cpc.getBalance(owner), "ether"))

    print("===========owner deploy contract=============")
    config = compile_file()
    contract = cf.cpc.contract(abi=config["abi"], bytecode=config["bin"])
    cf.cpc.defaultAccount = owner
    estimated_gas = contract.constructor().estimateGas()
    tx_hash = contract.constructor().transact(dict(gas=estimated_gas))
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    address = tx_receipt['contractAddress']
    print("contract address: ", address)

    print("===============test onlyOwner===============")
    reward_ins = cf.cpc.contract(abi=config["abi"], address=address)
    period = reward_ins.functions.period().call()
    print("before set, period: ", period)
    print("civilian tries to set period")
    cf.cpc.defaultAccount = civilian
    tx_hash = reward_ins.functions.setPeriod(100).transact({"gas": 829776, "from": civilian, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    period = reward_ins.functions.period().call()
    print("after civilian set, period: ", period)
    print("owner tries to set period")
    cf.cpc.defaultAccount = owner
    tx_hash = reward_ins.functions.setPeriod(100).transact({"gas": 829776, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    period = reward_ins.functions.period().call()
    print("after owner set, period: ", period)

    print("=============test deposit=================")
    locked = reward_ins.functions.locked().call()
    print("is the contract locked: ", locked)
    print("enode tries to deposit")
    is_enode = reward_ins.functions.isEnode(enode).call()
    print("before submit, is enode: ", is_enode)
    cf.cpc.defaultAccount = enode
    tx_hash = reward_ins.functions.submitDeposit().transact({"gas": 829776, "from": enode, "value": cf.toWei(30000, "ether")})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    is_enode = reward_ins.functions.isEnode(enode).call()
    print("after submit attempt, is enode: ", is_enode)
    print("owner start a new raise")
    cf.cpc.defaultAccount = owner
    tx_hash = reward_ins.functions.newRaise().transact({"gas": 829776, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    locked = reward_ins.functions.locked().call()
    print("is the contract locked: ", locked)
    print("enode tries again")
    is_enode = reward_ins.functions.isEnode(enode).call()
    print("before submit, is enode: ", is_enode)
    cf.cpc.defaultAccount = enode
    tx_hash = reward_ins.functions.submitDeposit().transact({"gas": 829776, "from": enode, "value": cf.toWei(30000, "ether")})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    is_enode = reward_ins.functions.isEnode(enode).call()
    print("after submit attempt, is enode: ", is_enode)

    print("==============test owner set bonus pool=================")
    bonus_pool = reward_ins.functions.bonusPool().call()
    print("before set, bonus pool: ", bonus_pool)
    cf.cpc.defaultAccount = owner
    tx_hash = reward_ins.functions.setBonusPool().transact({"gas": 829776, "from": owner, "value": cf.toWei(100000, "ether")})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    bonus_pool = reward_ins.functions.bonusPool().call()
    print("after set, bonus pool: ", cf.fromWei(bonus_pool, "ether"))

    print("==============test owner start new round=================")
    next_round = reward_ins.functions.nextRoundStartTime().call()
    print("before start, next round: ", next_round)
    cf.cpc.defaultAccount = owner
    tx_hash = reward_ins.functions.startNewRound().transact({"gas": 829776, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    next_round = reward_ins.functions.nextRoundStartTime().call()
    print("after start, next round: ", next_round)

    print("=============check investors=======================")
    investors = reward_ins.functions.getInvestors().call()
    print("number of investors: ", len(investors))
    print(investors)

    print("=============test interest calculation===================")
    free_balance = reward_ins.functions.getFreeBalanceOf(enode).call()
    print("before end, free balance: ", free_balance)
    print("owner close this round")
    cf.cpc.defaultAccount = owner
    tx_hash = reward_ins.functions.startNewRound().transact({"gas": 829776, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    free_balance = reward_ins.functions.getFreeBalanceOf(enode).call()
    total_balance = reward_ins.functions.getTotalBalanceOf(enode).call()
    print("after end, free balance: ", cf.fromWei(free_balance, "ether"))
    print("after end, total balance: ", cf.fromWei(total_balance, "ether"))

    print("============enode withdraw=================")
    bonus_pool = reward_ins.functions.bonusPool().call()
    print("bonus pool: ", cf.fromWei(bonus_pool, "ether"))
    print("owner start a new raise")
    cf.cpc.defaultAccount = owner
    tx_hash = reward_ins.functions.newRaise().transact({"gas": 829776, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    print("before withdraw")
    print("enode free balance: ", cf.fromWei(free_balance, "ether"))
    print("enode total balance: ", cf.fromWei(total_balance, "ether"))
    print("enode withdraw")
    tx_hash = reward_ins.functions.withdraw(free_balance).transact({"gas": 829776, "from": enode, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    total_balance = reward_ins.functions.getTotalBalanceOf(enode).call()
    free_balance = reward_ins.functions.getFreeBalanceOf(enode).call()
    print("after withdraw")
    print("enode free balance: ", cf.fromWei(free_balance, "ether"))
    print("enode total balance: ", cf.fromWei(total_balance, "ether"))
    print("enode quit renew")
    is_renew = reward_ins.functions.isToRenew(enode).call()
    print("before quit: ", is_renew)
    cf.cpc.defaultAccount = enode
    tx_hash = reward_ins.functions.quitRenew().transact({"gas": 829776, "from": enode, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    is_renew = reward_ins.functions.isToRenew(enode).call()
    print("after quit: ", is_renew)
    print("owner close previous round")
    tx_hash = reward_ins.functions.startNewRound().transact({"gas": 829776, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    cf.cpc.defaultAccount = enode
    total_balance = reward_ins.functions.getTotalBalanceOf(enode).call()
    free_balance = reward_ins.functions.getFreeBalanceOf(enode).call()
    print("before withdraw")
    print("enode free balance: ", cf.fromWei(free_balance, "ether"))
    print("enode total balance: ", cf.fromWei(total_balance, "ether"))
    print("enode withdraw")
    tx_hash = reward_ins.functions.withdraw(free_balance).transact({"gas": 829776, "from": enode, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    total_balance = reward_ins.functions.getTotalBalanceOf(enode).call()
    free_balance = reward_ins.functions.getFreeBalanceOf(enode).call()
    print("after withdraw")
    print("enode free balance: ", cf.fromWei(free_balance, "ether"))
    print("enode total balance: ", cf.fromWei(total_balance, "ether"))

    print("=============check investors again=====================")
    print("owner start a new raise")
    cf.cpc.defaultAccount = owner
    tx_hash = reward_ins.functions.newRaise().transact({"gas": 829776, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    print("owner close previous round")
    tx_hash = reward_ins.functions.startNewRound().transact({"gas": 829776, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    investors = reward_ins.functions.getInvestors().call()
    print("number of investors: ", len(investors))
    print(investors)

    print("=============test disable===============================")
    print("before kill the contract, balance: ", cf.fromWei(cf.cpc.getBalance(enode), "ether"))
    print("owner kill the contract")
    cf.cpc.defaultAccount = owner
    tx_hash = reward_ins.functions.disableContract().transact({"gas": 829776, "from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    print("after kill the contract, balance: ", cf.fromWei(cf.cpc.getBalance(enode), "ether"))


def prepare():
    cf = Web3(Web3.HTTPProvider("http://127.0.0.1:8521"))
    print("current account: ", cf.cpc.accounts)
    print("balance of owner: ", cf.fromWei(cf.cpc.getBalance(cf.cpc.accounts[0]), "ether"))
    # cf.personal.newAccount("password")
    print("current account: ", cf.cpc.accounts)
    # cf.cpc.sendTransaction({"from": "0xb3801b8743DEA10c30b0c21CAe8b1923d9625F84", "to": "0xBaf0c559C77dDe9340C82df8043eD9a21f2577AF", "value": cf.toWei(100000, "ether")})
    print("balance of owner: ", cf.fromWei(cf.cpc.getBalance("0xBaf0c559C77dDe9340C82df8043eD9a21f2577AF"), "ether"))


def main():
    test_case_1()
    # compile_file()
    # prepare()


if __name__ == '__main__':
    main()
