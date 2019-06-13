from solc import compile_files
import time

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


def monitor(reward, cf):
    total_investment = reward.functions.totalInvestment().call()
    total_interest = reward.functions.totalInterest().call()
    in_raise = reward.functions.inRaise().call()
    in_lock = reward.functions.inLock().call()
    in_settlement = reward.functions.inSettlement().call()
    bonus_pool = reward.functions.bonusPool().call()
    raise_period = reward.functions.raisePeriod().call()
    lock_period = reward.functions.lockPeriod().call()
    settlement_period = reward.functions.settlementPeriod().call()
    enode_threshold = reward.functions.enodeThreshold().call()
    round = reward.functions.round().call()
    next_raise_time = reward.functions.nextRaiseTime().call()
    next_lock_time = reward.functions.nextLockTime().call()
    next_settlement_time = reward.functions.nextSettlementTime().call()
    enodes = reward.functions.getEnodes().call()

    print("*************all configs*******************")
    print("total investment: ", cf.fromWei(total_investment, "ether"))
    print("total interest: ", cf.fromWei(total_interest, "ether"))
    print("is in raise: ", in_raise)
    print("is in lock: ", in_lock)
    print("is in settlement: ", in_settlement)
    print("bonus pool: ", cf.fromWei(bonus_pool, "ether"))
    print("raise period: ", raise_period)
    print("lock period: ", lock_period)
    print("settlement period: ", settlement_period)
    print("enode threshold: ", cf.fromWei(enode_threshold, "ether"))
    print("round: ", round)
    print("next raise time: ", next_raise_time)
    print("next lock time: ", next_lock_time)
    print("next settlement time: ", next_settlement_time)
    print("number of enodes: ", len(enodes))
    print(enodes)
    print("*********************************************")


def test_case_1():
    cf = Web3(Web3.HTTPProvider("http://127.0.0.1:8521"))
    owner = cf.toChecksumAddress("b3801b8743dea10c30b0c21cae8b1923d9625f84")
    cf.personal.unlockAccount(owner, "password")
    enodes = []

    print("================generate 10 enodes======================")
    for i in range(10):
        enode = cf.toChecksumAddress(cf.personal.newAccount("password"))
        enodes.append(enode)
        cf.cpc.sendTransaction({"from": owner, "to": enode, "value": cf.toWei(30000, "ether")})
    print("wait for tx confirmation...")
    time.sleep(15)
    for enode in enodes:
        balance = cf.fromWei(cf.cpc.getBalance(enode), "ether")
        print("address: ", enode)
        print("balance: ", balance)
    print("=================deploy contract====================")
    config = compile_file()
    contract = cf.cpc.contract(abi=config["abi"], bytecode=config["bin"])
    cf.cpc.defaultAccount = owner
    cf.personal.unlockAccount(owner, "password")
    estimated_gas = contract.constructor().estimateGas()
    tx_hash = contract.constructor().transact(dict(gas=estimated_gas))
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    address = tx_receipt['contractAddress']
    reward = cf.cpc.contract(abi=config["abi"], address=address)
    print("===============first round normal case==================")
    monitor(reward, cf)
    cf.cpc.defaultAccount = owner
    print("owner sets periods for convenience of tests")
    tx_hash = reward.functions.setRaisePeriod(1).transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("set raise period, result: ", tx_receipt["status"])
    tx_hash = reward.functions.setLockPeriod(1).transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("set lock period, result: ", tx_receipt["status"])
    tx_hash = reward.functions.setSettlementPeriod(1).transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("set settlement period, result: ", tx_receipt["status"])
    print("after setting")
    monitor(reward, cf)
    print("==============start new raise==================")
    print("owner starts a new raise")
    cf.cpc.defaultAccount = owner
    cf.personal.unlockAccount(owner, "password")
    tx_hash = reward.functions.newRaise().transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("owner starts new raise, result: ", tx_receipt["status"])
    print("owner fund bonus pool")
    cf.cpc.sendTransaction({"from": owner, "to": address, "value": cf.toWei(100000, "ether")})
    print("wait for tx confirmation")
    time.sleep(10)
    print("enodes deposit")
    for enode in enodes:
        cf.personal.unlockAccount(enode, "password")
        cf.cpc.defaultAccount = enode
        tx_hash = reward.functions.deposit().transact({"from": enode, "value": cf.toWei(20000, "ether")})
        tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
        print("enode: ", enode)
        print("deposit result: ", tx_receipt["status"])
    monitor(reward, cf)
    print("==============start new lock===================")
    print("owner starts a new lock")
    cf.cpc.defaultAccount = owner
    cf.personal.unlockAccount(owner, "password")
    tx_hash = reward.functions.newLock().transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("owner starts new lock, result: ", tx_receipt["status"])
    monitor(reward, cf)
    print("=============start new settlement=============")
    print("owner starts a new settlement")
    cf.cpc.defaultAccount = owner
    cf.personal.unlockAccount(owner, "password")
    tx_hash = reward.functions.newSettlement().transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("owner starts new settlement, result: ", tx_receipt["status"])
    print("enodes claim interest")
    for enode in enodes:
        cf.personal.unlockAccount(enode, "password")
        cf.cpc.defaultAccount = enode
        tx_hash = reward.functions.claimInterest().transact({"from": enode, "value": 0})
        tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
        print("enode: ", enode)
        print("claim result: ", tx_receipt["status"])
    monitor(reward, cf)
    print("enodes claim interest again, should fail")
    for enode in enodes:
        cf.personal.unlockAccount(enode, "password")
        cf.cpc.defaultAccount = enode
        tx_hash = reward.functions.claimInterest().transact({"from": enode, "value": 0})
        tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
        print("enode: ", enode)
        print("claim result: ", tx_receipt["status"])
    monitor(reward, cf)
    print("=============second round=====================")
    print("owner starts a new raise")
    cf.cpc.defaultAccount = owner
    cf.personal.unlockAccount(owner, "password")
    tx_hash = reward.functions.newRaise().transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("owner starts new raise, result: ", tx_receipt["status"])
    monitor(reward, cf)
    print("enodes withdraw")
    for enode in enodes:
        cf.personal.unlockAccount(enode, "password")
        cf.cpc.defaultAccount = enode
        enode_balance = reward.functions.investments(enode).call()
        print("enode: ", enode)
        print("balance: ", cf.fromWei(enode_balance, "ether"))
        tx_hash = reward.functions.withdraw(enode_balance).transact({"from": enode, "value": 0})
        tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
        print("enode withdraw result: ", tx_receipt["status"])
    monitor(reward, cf)


def main():
    test_case_1()


if __name__ == '__main__':
    main()
