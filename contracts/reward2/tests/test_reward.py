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


def monitor(reward):
    total_investment = reward.functions.totalInvestment().call()
    total_interest = reward.functions.totalInterest().call()
    in_raise = reward.functions.inRaise().call()
    in_lock = reward.functions.inLock().call()
    in_settlement = reward.functions.inSettlement().call()
    bonus_pool = reward.functions.bonusPool().call()
    raise_period = reward.functions.raisePeriod().call()
    settlement_period = reward.functions.settlementPeriod().call()
    enode_threshold = reward.functions.enodeThreshold().call()
    round = reward.functions.round().call()
    next_raise_time = reward.functions.nextRaiseTime().call()
    next_lock_time = reward.functions.nextLockTime().call()
    next_settlement_time = reward.functions.nextSettlementTime().call()

    print("total investment: ", total_investment)
    print("total interest: ", total_interest)
    print("is in raise: ", in_raise)
    print("is in lock: ", in_lock)
    print("is in settlement: ", in_settlement)
    print("bonus pool: ", bonus_pool)
    print("raise period: ", raise_period)
    print("settlement period: ", settlement_period)
    print("enode threshold: ", enode_threshold)
    print("round: ", round)
    print("next raise time: ", next_raise_time)
    print("next lock time: ", next_lock_time)
    print("next settlement time: ", next_settlement_time)


def test_case_1():
    cf = Web3(Web3.HTTPProvider("http://127.0.0.1:8501"))
    owner = cf.toChecksumAddress("b3801b8743dea10c30b0c21cae8b1923d9625f84")
    cf.personal.unlockAccount(owner, "password")
    enodes = []

    print("================generate 15 rnodes======================")
    for i in range(15):
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
    monitor(reward)


def main():
    test_case_1()


if __name__ == '__main__':
    main()
