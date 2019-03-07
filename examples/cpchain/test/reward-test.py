#!/usr/bin/env python3

from cpc_fusion import Web3
import time
import math

campaignConfig = {
    "abi": "[{\"constant\":true,\"inputs\":[],\"name\":\"termLen\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_numOfCampaign\",\"type\":\"uint256\"},{\"name\":\"_cpuNonce\",\"type\":\"uint64\"},{\"name\":\"_cpuBlockNumber\",\"type\":\"uint256\"},{\"name\":\"_memoryNonce\",\"type\":\"uint64\"},{\"name\":\"_memoryBlockNumber\",\"type\":\"uint256\"}],\"name\":\"claimCampaign\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_termIdx\",\"type\":\"uint256\"}],\"name\":\"candidatesOf\",\"outputs\":[{\"name\":\"\",\"type\":\"address[]\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"termIdx\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"minNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"numPerRound\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"setRewardInterface\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"viewLen\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_maxNoc\",\"type\":\"uint256\"}],\"name\":\"updateMaxNoc\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_minNoc\",\"type\":\"uint256\"}],\"name\":\"updateMinNoc\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"setAdmissionAddr\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_termLen\",\"type\":\"uint256\"}],\"name\":\"updateTermLen\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_viewLen\",\"type\":\"uint256\"}],\"name\":\"updateViewLen\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_candidate\",\"type\":\"address\"}],\"name\":\"candidateInfoOf\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"maxNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"updateCandidateStatus\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"inputs\":[{\"name\":\"_admissionAddr\",\"type\":\"address\"},{\"name\":\"_rewardAddr\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"fallback\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"candidate\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"startTermIdx\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"stopTermIdx\",\"type\":\"uint256\"}],\"name\":\"ClaimCampaign\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"candidate\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"payback\",\"type\":\"uint256\"}],\"name\":\"QuitCampaign\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[],\"name\":\"ViewChange\",\"type\":\"event\"}]",
    "address": "0x82104907AA699b2982Fc46f38Fd8C915d03Cdb8d",
}

rewardConfig ={
    "abi":"[{\"constant\":false,\"inputs\":[{\"name\":\"_period\",\"type\":\"uint256\"}],\"name\":\"setPeriod\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"isContract\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"bonusPool\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"isRNode\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_value\",\"type\":\"uint256\"}],\"name\":\"withdraw\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"nextRound\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"nextRoundStartTime\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"},{\"name\":\"_value\",\"type\":\"uint256\"}],\"name\":\"transferDeposit\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"totalInvestAmount\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"getFreeBalance\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"wantRenew\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"newRaise\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"quitRenew\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"isLocked\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"isENode\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"startNewRound\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"basicCriteria\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"getLockedBalance\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"getTotalBalance\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"electionCriteria\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_bonus\",\"type\":\"uint256\"}],\"name\":\"setBonusPool\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"submitDeposit\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"isToRenew\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"fallback\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"SubmitDeposit\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"WithdrawDeposit\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"JoinENodes\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"JoinRNodes\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"TransferDeposit\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"round\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"lock\",\"type\":\"bool\"},{\"indexed\":false,\"name\":\"_bonusPool\",\"type\":\"uint256\"}],\"name\":\"NewRaise\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"DepositInsufficient\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"_addr\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"_iscontinue\",\"type\":\"bool\"}],\"name\":\"ContinuedInvest\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"FundBonusPool\",\"type\":\"event\"}]",
    "address": "0x94576e35a55D6BbF9bB45120bC835a668557eF42",
}



web3 = Web3(Web3.HTTPProvider('http://127.0.0.1:8521'))


campaign = web3.cpc.contract(address=campaignConfig['address'], abi=campaignConfig['abi'])

reward = web3.cpc.contract(address=rewardConfig['address'], abi=rewardConfig['abi'])

Ether = int(math.pow(10, 18))

def get_instance(node):
    instance =node.cpc.contract(address=rewardConfig['address'], abi=rewardConfig['abi'])
    return instance

def print_info(string,account):

    print(string)
    print('RNode is ', reward.functions.isRNode(account).call())
    print("totalInvestAmount", reward.functions.totalInvestAmount().call())
    print("getTotalBalance ", reward.functions.getTotalBalance(account).call())
    print("balance:", web3.cpc.getBalance(account))
    print('\n')

def testRnode(node, instance, totalInvestAmount, totalBalance, bool):
    getTotalInvestment = instance.functions.totalInvestAmount().call()
    getTotalBalance = instance.functions.getTotalBalance(node.cpc.accounts[0]).call()
    assert totalInvestAmount == getTotalInvestment , \
        f'wrong totalInvestAmount, we want {totalInvestAmount}, but we get {getTotalInvestment}'
    assert getTotalBalance == totalBalance , \
        f'wrong totalInvestAmount, we want {totalBalance}, but we get {getTotalBalance}'
    assert instance.functions.isRNode(node.cpc.accounts[0]).call() == bool

def testEnode(node, instance, totalInvestAmount, totalBalance, bool):
    getTotalInvestment = instance.functions.totalInvestAmount().call()
    getTotalBalance = instance.functions.getTotalBalance(node.cpc.accounts[0]).call()
    assert totalInvestAmount == getTotalInvestment , \
        f'wrong totalInvestAmount, we want {totalInvestAmount}, but we get {getTotalInvestment}'
    assert getTotalBalance == totalBalance ,  \
        f'wrong totalInvestAmount, we want {totalBalance}, but we get {getTotalBalance}'
    assert instance.functions.isENode(node.cpc.accounts[0]).call() == bool

def testBalance(node,instance,totalBalance,lockBalance,Renew):
    getTotalBalance = instance.functions.getTotalBalance(node.cpc.accounts[0]).call()
    getLockBalance = instance.functions.getFreeBalance(node.cpc.accounts[0]).call()
    getFreeBalance = instance.functions.getFreeBalance(node.cpc.accounts[0]).call()
    assert getTotalBalance > totalBalance,\
        f'wrong totalInvestAmount, we want {totalInvestAmount}, but we get {getTotalInvestment}'
    assert getLockBalance == lockBalance,\
        f'wrong LockBalance, totalBalance: {totalBalance},getLockBalance: {getLockBalance}'
    if Renew == True:
        assert getTotalBalance - totalBalance >= getFreeBalance
    elif Renew == False:
        assert getFreeBalance >= totalBalance

def get_web3_inst(num):
    port = 8500 + num
    return Web3(Web3.HTTPProvider(f"http://127.0.0.1:{port}"))

# plaese ensure address:0xe83a71428655b9f52ff6dc556e2b37043f39f194 have max money to test
def main():

    # init node
    rnode1 = get_web3_inst(1) # quitRenew
    rnode1_instance = get_instance(rnode1)
    rnode2 =get_web3_inst(2) # wantRenew
    rnode2_instance =get_instance(rnode2)
    enode1 = get_web3_inst(3) # quitRenew
    enode1_instance = get_instance(enode1)
    enode2 = get_web3_inst(4) # wantRenew
    enode2_instance = get_instance(enode2)

    print("web3 balance",web3.eth.getBalance(web3.cpc.accounts[0]),"\n")
    rnode1_balance = web3.eth.getBalance(rnode1.cpc.accounts[0])
    print("rnode1 balance", rnode1_balance,"\n")

    rnode2_balance = web3.eth.getBalance(rnode2.cpc.accounts[0])
    print("rnode2 balance", rnode2_balance,"\n")

    enode1_balance = web3.eth.getBalance(enode1.cpc.accounts[0])
    print("enode1 balance", enode1_balance,"\n")

    enode2_balance = web3.eth.getBalance(enode1.cpc.accounts[0])
    print("enode2 balance", enode2_balance,"\n")


    # send money to node
    web3.personal.sendTransaction({'to': rnode1.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 200000 * Ether},
                                 'password')
    web3.personal.sendTransaction({'to': rnode2.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 200000 * Ether},
                                  'password')
    web3.personal.sendTransaction({'to': enode1.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 20000 * Ether},
                                  'password')
    web3.personal.sendTransaction({'to': enode2.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 20000 * Ether},
                                  'password')

    rnode1_reward_balance = web3.eth.getBalance(rnode1.cpc.accounts[0])
    print("rnode1 balance", rnode1_reward_balance)

    rnode2_reward_balance = web3.eth.getBalance(rnode2.cpc.accounts[0])
    print("rnode2 balance", rnode2_reward_balance )

    enode1_reward_balance = web3.eth.getBalance(enode1.cpc.accounts[0])
    print("enode1 balance", enode1_reward_balance )

    enode2__reward_balance = web3.eth.getBalance(enode2.cpc.accounts[0])
    print("enode2 balance", enode2__reward_balance )


    # set period = 0
    reward.functions.setPeriod(0).transact({
        'gas': 3000000,
        'from': web3.cpc.accounts[0],
    })

    # start new Raise
    print("locked want true",reward.functions.isLocked().call())
    # assert reward.functions.isLocked().call() == True,\
    #     'the lock is not locked'
    reward.functions.newRaise().transact({
        'gas': 3000000,
        'from': web3.cpc.accounts[0],
    })
    time.sleep(3)
    print('locked want false', reward.functions.isLocked().call())
    assert reward.functions.isLocked().call() == False,\
        'the lock is not open'

    # submitDeposit
    rnode1_instance.functions.submitDeposit().transact({
        'gas': 300000,
        'value': 200000*Ether,
        'from': rnode1.cpc.accounts[0],
    })

    rnode2_instance.functions.submitDeposit().transact({
        'gas': 300000,
        'value': 200000 * Ether,
        'from': rnode2.cpc.accounts[0],
    })

    enode1_instance.functions.submitDeposit().transact({
        'gas': 300000,
        'value': 20000 * Ether,
        'from': enode1.cpc.accounts[0],
    })

    enode2_instance.functions.submitDeposit().transact({
        'gas': 300000,
        'value': 20000 * Ether,
        'from': enode2.cpc.accounts[0],
    })

    # start new campaign
    reward.functions.startNewRound().transact({
        'gas': 3000000,
        'from': web3.cpc.accounts[0],
    })
    time.sleep(3)
    print('locked want true', reward.functions.isLocked().call())
    assert reward.functions.isLocked().call() == True,\
        'the lock is not Locked'

    print_info('rnode1',rnode1.cpc.accounts[0])
    print_info('rnode2', rnode2.cpc.accounts[0])
    print_info('enode1', enode2.cpc.accounts[0])
    print_info('enode2', enode2.cpc.accounts[0])
    testRnode(rnode1, rnode1_instance, 440000 * Ether, 200000 * Ether, True)
    testRnode(rnode2, rnode2_instance, 440000 * Ether, 200000 * Ether, True)
    testEnode(enode1, enode1_instance, 440000 * Ether, 20000 * Ether, True)
    testEnode(enode2, enode2_instance, 440000 * Ether, 20000 * Ether, True)

    # start next new round
    print("####start next new round####")
    reward.functions.newRaise().transact({
        'gas': 3000000,
        'from': web3.cpc.accounts[0],
    })
    time.sleep(3)
    print('locked want false', reward.functions.isLocked().call())
    assert reward.functions.isLocked().call() == False,\
        'the lock is not Locked'

    # set Renew
    rnode1_instance.functions.quitRenew().transact({
        'gas': 3000000,
        'from': rnode1.cpc.accounts[0],
    })

    rnode2_instance.functions.wantRenew().transact({
        'gas': 3000000,
        'from': rnode2.cpc.accounts[0]
    })

    enode1_instance.functions.quitRenew().transact({
        'gas': 3000000,
        'from': enode1.cpc.accounts[0],
    })

    enode2_instance.functions.wantRenew().transact({
        'gas': 3000000,
        'from': enode2.cpc.accounts[0],
    })

    # startNewRound
    reward.functions.startNewRound().transact({
        'gas': 3000000,
        'from': web3.cpc.accounts[0],
    })
    print('locked want true', reward.functions.isLocked().call())
    assert reward.functions.isLocked().call() == True,\
        'the lock is not Locked'

    # test isToRenew
    assert rnode1_instance.functions.isToRenew(
        rnode1.cpc.accounts[0]).call() == False, \
        'we want isToRenew is False but we get True'

    assert rnode2_instance.functions.isToRenew(
        rnode2.cpc.accounts[0]).call() == True, \
        'we want isToRenew is True but we get False'

    assert enode1_instance.functions.isToRenew(
        enode1.cpc.accounts[0]).call() == False, \
        'we want isToRenew is False but we get True'

    assert enode2_instance.functions.isToRenew(
        enode2.cpc.accounts[0]).call() == True, \
        'we want isToRenew is True but we get False'

    # test balance
    testRnode(rnode1, rnode1_instance, 220000 * Ether, 0, False)
    testRnode(rnode2, rnode2_instance, 220000 * Ether, 200000 * Ether, True)
    testEnode(enode1, enode2_instance, 220000 * Ether, 0, False)
    testEnode(enode2, enode2_instance, 220000 * Ether, 20000 * Ether, True)

    #test deposit
    testBalance(rnode1,rnode1_instance,rnode1_reward_balance,0,False)
    testBalance(rnode2,rnode2_instance,rnode2_reward_balance,200000 * Ether,True)
    testBalance(enode1,enode1_instance,enode1_reward_balance,0,False)
    testBalance(enode2,enode2_instance,enode2__reward_balance,20000 * Ether,True)

    reward.functions.setPeriod(90).transact({
        'gas': 3000000,
        'from': web3.cpc.accounts[0],
    })


if __name__ == '__main__':
    main()
