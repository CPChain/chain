from solc import compile_files
import time

from cpc_fusion import Web3


def init():
    cf = Web3(Web3.HTTPProvider("http://127.0.0.1:8521"))
    owner = cf.cpc.accounts[0]

    return cf, owner


def compile_file():
    output = compile_files(["../reward.sol"])
    abi = output['../reward.sol:Reward']["abi"]
    bin = output['../reward.sol:Reward']["bin"]
    print(abi)
    print(bin)
    config = dict(abi=abi, bin=bin)

    return config


def deploy_contract(config, cf, owner):
    contract = cf.cpc.contract(abi=config["abi"], bytecode=config["bin"])
    estimated_gas = contract.constructor().estimateGas()
    cf.personal.unlockAccount(owner, "password")
    tx_hash = contract.constructor().transact({"from": owner, "gas": estimated_gas})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("deploy contract, result: ", tx_receipt["status"])
    contract_address = tx_receipt["contractAddress"]
    reward = cf.cpc.contract(abi=config["abi"], address=contract_address)
    return contract_address, reward


def generate_nodes(num, cf, owner):
    enodes = []
    for i in range(num):
        enode = cf.toChecksumAddress(cf.personal.newAccount("password"))
        enodes.append(enode)
        cf.cpc.sendTransaction({"from": owner, "to": enode, "value": cf.toWei(30000, "ether")})
    print("wait for tx confirmation...")
    time.sleep(15)
    for enode in enodes:
        balance = cf.fromWei(cf.cpc.getBalance(enode), "ether")
        print("address: ", enode)
        print("balance: ", balance)
    return enodes


def new_raise(cf, reward, owner):
    tx_hash = reward.functions.newRaise().transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("owner starts a new raise, result: ", tx_receipt["status"])


def fund_bonus_pool(cf, owner, contract_address):
    tx_hash = cf.cpc.sendTransaction({"from": owner, "to": contract_address, "value": cf.toWei(1250000, "ether")})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("fund for bonus pool, result: ", tx_receipt["status"])


def deposit(enode, value, reward):
    tx_hash = reward.functions.deposit().transact({"from": enode, "value": value})
    return tx_hash


def withdraw(enode, value, reward):
    tx_hash = reward.functions.withdraw(value).transact({"from": enode})
    return tx_hash


def new_lock(cf, reward, owner):
    tx_hash = reward.functions.newLock().transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("owner starts a new lock and locks all free balance of enodes, result: ", tx_receipt["status"])


def only_lock(cf, reward, owner):
    tx_hash = reward.functions.onlyNewLock().transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("onwer only starts a new lock, result: ", tx_receipt["status"])


def lock_deposit(enode, reward, owner):
    tx_hash = reward.functions.lockDeposit(enode).transact({"from": owner, "value": 0})
    return tx_hash


def new_settlement(cf, reward, owner):
    tx_hash = reward.functions.newSettlement().transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("owner starts a new settlement and distribute interest for all enodes, result: ", tx_receipt["status"])


def only_settle(cf, reward, owner):
    tx_hash = reward.functions.onlyNewSettlement().transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("owner only starts a new settlement")


def settle(reward, owner, enode):
    tx_hash = reward.functions.settle(enode).transact({"from": owner, "value": 0})
    return tx_hash


def monitor(reward, cf):
    total_free_balance = reward.functions.totalFreeBalance().call()
    total_locked_balance = reward.functions.totalLockedBalance().call()
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

    print("*************all configs*********************")
    print("total free balance: ", cf.fromWei(total_free_balance, "ether"))
    print("total locked balance: ", cf.fromWei(total_locked_balance, "ether"))
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
    pass


def test_case_2():
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
    # print("enodes claim interest again, should fail")
    # for enode in enodes:
    #     cf.personal.unlockAccount(enode, "password")
    #     cf.cpc.defaultAccount = enode
    #     tx_hash = reward.functions.claimInterest().transact({"from": enode, "value": 0})
    #     tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    #     print("enode: ", enode)
    #     print("claim result: ", tx_receipt["status"])
    # monitor(reward, cf)
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
    # test_case_1()
    compile_file()


if __name__ == '__main__':
    main()
