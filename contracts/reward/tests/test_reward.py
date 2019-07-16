from solc import compile_files
import time

from cpc_fusion import Web3


def init():
    cf = Web3(Web3.HTTPProvider("http://127.0.0.1:8521"))
    owner = cf.toChecksumAddress("b3801b8743dea10c30b0c21cae8b1923d9625f84")

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


def generate_nodes(num, cf, owner, value):
    enodes = []
    for i in range(num):
        enode = cf.toChecksumAddress(cf.personal.newAccount("password"))
        enodes.append(enode)
        cf.cpc.sendTransaction({"from": owner, "to": enode, "value": cf.toWei(value, "ether")})
    print("wait for tx confirmation...")
    time.sleep(21)
    for enode in enodes:
        balance = cf.fromWei(cf.cpc.getBalance(enode), "ether")
        print("address: ", enode)
        print("balance: ", balance)
    return enodes


def set_period(reward, cf, owner, raise_p, lock_p, settle_p):
    tx_hash = reward.functions.setRaisePeriod(raise_p).transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("owner sets raise period, result: ", tx_receipt["status"])
    tx_hash = reward.functions.setLockPeriod(lock_p).transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("owner sets lock period, result: ", tx_receipt["status"])
    tx_hash = reward.functions.setSettlementPeriod(settle_p).transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("owner sets settlement period, result: ", tx_receipt["status"])


def new_raise(cf, reward, owner):
    tx_hash = reward.functions.newRaise().transact({"from": owner, "value": 0})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("owner starts a new raise, result: ", tx_receipt["status"])


def fund_bonus_pool(cf, owner, contract_address):
    tx_hash = cf.cpc.sendTransaction({"from": owner, "to": contract_address, "value": cf.toWei(1250000, "ether")})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("fund for bonus pool, result: ", tx_receipt["status"])


def deposit(enode, value, reward):
    tx_hash = reward.functions.deposit().transact({"from": enode, "value": value * 10**18})
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
    print("owner only starts a new settlement, result: ", tx_receipt["status"])


def settle(reward, owner, enode):
    tx_hash = reward.functions.settle(enode).transact({"from": owner, "value": 0})
    return tx_hash


def monitor(reward, cf):
    round = reward.functions.round().call()
    total_free_balance = reward.functions.totalFreeBalance().call()
    total_locked_balance = reward.functions.totalLockedBalance().call()
    bonus = reward.functions.bonus(round).call()
    investment = reward.functions.investments(round).call()
    in_raise = reward.functions.inRaise().call()
    in_lock = reward.functions.inLock().call()
    in_settlement = reward.functions.inSettlement().call()
    bonus_pool = reward.functions.bonusPool().call()
    raise_period = reward.functions.raisePeriod().call()
    lock_period = reward.functions.lockPeriod().call()
    settlement_period = reward.functions.settlementPeriod().call()
    enode_threshold = reward.functions.enodeThreshold().call()
    next_raise_time = reward.functions.nextRaiseTime().call()
    next_lock_time = reward.functions.nextLockTime().call()
    next_settlement_time = reward.functions.nextSettlementTime().call()
    enodes = reward.functions.getEnodes().call()

    print("*************all configs*********************")
    print("total free balance: ", cf.fromWei(total_free_balance, "ether"))
    print("total locked balance: ", cf.fromWei(total_locked_balance, "ether"))
    print("is in raise: ", in_raise)
    print("is in lock: ", in_lock)
    print("is in settlement: ", in_settlement)
    print("bonus pool: ", cf.fromWei(bonus_pool, "ether"))
    print("raise period: ", raise_period)
    print("lock period: ", lock_period)
    print("settlement period: ", settlement_period)
    print("enode threshold: ", cf.fromWei(enode_threshold, "ether"))
    print("round: ", round)
    print("bonus of this round: ", cf.fromWei(bonus, "ether"))
    print("investment of this round: ", cf.fromWei(investment, "ether"))
    print("next raise time: ", next_raise_time)
    print("next lock time: ", next_lock_time)
    print("next settlement time: ", next_settlement_time)
    print("number of enodes: ", len(enodes))
    print(enodes)
    print("*********************************************")


def test_case_1():
    print("#" * 30)
    print("normal case:\n1. 5 enodes, each 30,000\n2. 5 investors, each 10,000\n"
          "3. investors withdraw 10,000 during lock, succeed\n"
          "4. enodes withdraw 10,000 during lock, failed\n"
          "5. next raise, enodes withdraw money, check value")
    print("#" * 30)
    print("[1. compile and deploy contract]")
    cf, owner = init()
    config = compile_file()
    contract_address, reward = deploy_contract(config, cf, owner)
    print("contract address: ", contract_address)
    print("[2. initialize enodes and investors]")
    enodes = generate_nodes(2, cf, owner, 30000)
    investors = generate_nodes(1, cf, owner, 10000)
    print("[3. owner sets period for test]")
    set_period(reward, cf, owner, 1, 1, 1)
    monitor(reward, cf)
    print("[4. owner starts a new raise]")
    new_raise(cf, reward, owner)
    monitor(reward, cf)
    print("owner fund for bonus pool")
    tx_hash = cf.cpc.sendTransaction({"from": owner, "to": contract_address, "value": cf.toWei(20000, "ether")})
    tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
    print("result: ", tx_receipt["status"])
    print("[5. enodes and investors deposit]")
    for enode in enodes:
        cf.personal.unlockAccount(enode, "password")
        tx_hash = deposit(enode, 20000, reward)
        tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
        print("enode address: ", enode)
        print("deposit result: ", tx_receipt["status"])
    for investor in investors:
        cf.personal.unlockAccount(investor, "password")
        tx_hash = deposit(investor, 5000, reward)
        cf.cpc.waitForTransactionReceipt(tx_hash)
        print("investor address: ", investor)
        print("deposit result: ", tx_receipt["status"])
    monitor(reward, cf)
    print("[6. owner starts a new lock]")
    new_lock(cf, reward, owner)
    monitor(reward, cf)
    print("[7. investors withdraw money]")
    for investor in investors:
        cf.personal.unlockAccount(investor, "password")
        free_balance = reward.functions.freeBalanceOf(investor).call()
        locked_balance = reward.functions.lockedBalanceOf(investor).call()
        print("address: ", investor)
        print("free balance: ", cf.fromWei(free_balance, "ether"))
        print("locked balance: ", cf.fromWei(locked_balance, "ether"))
        tx_hash = reward.functions.withdraw(free_balance).transact({"from": investor, "value": 0})
        tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
        print("investor withdraw result: ", tx_receipt["status"])
    monitor(reward, cf)
    print("[8. owner starts a new settlement and distribute interest]")
    new_settlement(cf, reward, owner)
    monitor(reward, cf)
    print("[9. enodes withdraw money, and check value]")
    for enode in enodes:
        cf.personal.unlockAccount(enode, "password")
        free_balance = reward.functions.freeBalanceOf(enode).call()
        locked_balance = reward.functions.lockedBalanceOf(enode).call()
        print("address: ", enode)
        print("free balance: ", cf.fromWei(free_balance, "ether"))
        print("locked balance: ", cf.fromWei(locked_balance, "ether"))
        tx_hash = reward.functions.withdraw(free_balance).transact({"from": enode, "value": 0})
        tx_receipt = cf.cpc.waitForTransactionReceipt(tx_hash)
        print("enode withdraw result: ", tx_receipt["status"])
    monitor(reward, cf)
    print("[10. owner starts a new raise, and check configs]")
    new_raise(cf, reward, owner)
    monitor(reward, cf)


def build_transaction():
    cf, owner = init()
    config = compile_file()
    contract_address, reward = deploy_contract(config, cf, owner)
    nonce = cf.cpc.getTransactionCount(owner)
    deposit_tx = reward.functions.deposit().buildTransaction({"chainId": 41, "gas": 7000, "nonce": nonce, "value": cf.toWei(30000, "ether")})
    print("deposit tx: ", deposit_tx)
    withdraw_tx = reward.functions.withdraw(cf.toWei(20000, "ether")).buildTransaction({"chainId": 41, "gas": 7000, "nonce": nonce, "value": 0})
    print("deposit tx: ", withdraw_tx)


def main():
    # test_case_1()
    # compile_file()
    build_transaction()


if __name__ == '__main__':
    main()
