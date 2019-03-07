#!/usr/bin/env python3

from cpc_fusion import Web3
import time
import math
import os
campaignConfig = {
    "abi": "[{\"constant\":true,\"inputs\":[],\"name\":\"termLen\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_numOfCampaign\",\"type\":\"uint256\"},{\"name\":\"_cpuNonce\",\"type\":\"uint64\"},{\"name\":\"_cpuBlockNumber\",\"type\":\"uint256\"},{\"name\":\"_memoryNonce\",\"type\":\"uint64\"},{\"name\":\"_memoryBlockNumber\",\"type\":\"uint256\"}],\"name\":\"claimCampaign\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_termIdx\",\"type\":\"uint256\"}],\"name\":\"candidatesOf\",\"outputs\":[{\"name\":\"\",\"type\":\"address[]\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"termIdx\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"minNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"numPerRound\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"setRewardInterface\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"viewLen\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_maxNoc\",\"type\":\"uint256\"}],\"name\":\"updateMaxNoc\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_minNoc\",\"type\":\"uint256\"}],\"name\":\"updateMinNoc\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"setAdmissionAddr\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_termLen\",\"type\":\"uint256\"}],\"name\":\"updateTermLen\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_viewLen\",\"type\":\"uint256\"}],\"name\":\"updateViewLen\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_candidate\",\"type\":\"address\"}],\"name\":\"candidateInfoOf\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"maxNoc\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"updateCandidateStatus\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"inputs\":[{\"name\":\"_admissionAddr\",\"type\":\"address\"},{\"name\":\"_rewardAddr\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"fallback\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"candidate\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"startTermIdx\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"stopTermIdx\",\"type\":\"uint256\"}],\"name\":\"ClaimCampaign\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"candidate\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"payback\",\"type\":\"uint256\"}],\"name\":\"QuitCampaign\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[],\"name\":\"ViewChange\",\"type\":\"event\"}]",
    "address": "0x82104907AA699b2982Fc46f38Fd8C915d03Cdb8d",
}

rewardConfig ={
    "abi":"[{\"constant\":false,\"inputs\":[{\"name\":\"_period\",\"type\":\"uint256\"}],\"name\":\"setPeriod\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"isContract\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"bonusPool\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"isRNode\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_value\",\"type\":\"uint256\"}],\"name\":\"withdraw\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"nextRound\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"nextRoundStartTime\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"},{\"name\":\"_value\",\"type\":\"uint256\"}],\"name\":\"transferDeposit\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"totalInvestAmount\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"getFreeBalance\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"wantRenew\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"newRaise\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"quitRenew\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"isParticipant\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"isLocked\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"startNewRound\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"basicCriteria\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"getLockedBalance\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"getTotalBalance\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"electionCriteria\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_bonus\",\"type\":\"uint256\"}],\"name\":\"setBonusPool\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[],\"name\":\"submitDeposit\",\"outputs\":[],\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_addr\",\"type\":\"address\"}],\"name\":\"isToRenew\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"payable\":true,\"stateMutability\":\"payable\",\"type\":\"fallback\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"SubmitDeposit\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"WithdrawDeposit\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"JoinPartcipant\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"JoinCandidates\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"TransferDeposit\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"round\",\"type\":\"uint256\"},{\"indexed\":false,\"name\":\"lock\",\"type\":\"bool\"},{\"indexed\":false,\"name\":\"_bonusPool\",\"type\":\"uint256\"}],\"name\":\"NewRaise\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"who\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"DepositInsufficient\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"_addr\",\"type\":\"address\"},{\"indexed\":false,\"name\":\"_iscontinue\",\"type\":\"bool\"}],\"name\":\"ContinuedInvest\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"name\":\"value\",\"type\":\"uint256\"}],\"name\":\"FundBonusPool\",\"type\":\"event\"}]",
    "address": "0x94576e35a55D6BbF9bB45120bC835a668557eF42",
}



web3 = Web3(Web3.HTTPProvider('http://127.0.0.1:8521'))


campaign = web3.cpc.contract(address=campaignConfig['address'], abi=campaignConfig['abi'])

reward = web3.cpc.contract(address=rewardConfig['address'], abi=rewardConfig['abi'])

Ether = int(math.pow(10, 18))

def printInfo(account):

    print('RNode is ', reward.functions.isRNode(account).call())
    print("totalInvestAmount", reward.functions.totalInvestAmount().call())
    print("getTotalBalance ", reward.functions.getTotalBalance(account).call())
    print("balance:", web3.cpc.getBalance(account))

def get_web3_inst(num):
    port = 8500 + num
    return Web3(Web3.HTTPProvider(f"http://127.0.0.1:{port}"))

def get_instance(node):
    instance =node.cpc.contract(address=rewardConfig['address'], abi=rewardConfig['abi'])
    return instance

# plaese ensure address:0xe83a71428655b9f52ff6dc556e2b37043f39f194 have max money to test
def main():

    # init node
    node1 = get_web3_inst(1)
    node2 = get_web3_inst(2)
    node3 = get_web3_inst(3)
    node4 = get_web3_inst(4)
    node5 = get_web3_inst(5)
    node6 = get_web3_inst(6)

    print(web3.cpc.accounts[0])
    print("balance", web3.cpc.getBalance(web3.cpc.accounts[0]))

    # set period==0
    reward.functions.setPeriod(0).transact({
        'gas': 3000000,
        'from': web3.cpc.accounts[0],
    })

    # start new Raise
    print('locked',reward.functions.isLocked().call())
    reward.functions.newRaise().transact({
        'gas': 3000000,
        'from': web3.cpc.accounts[0],
    })
    time.sleep(3)
    print('locked', reward.functions.isLocked().call())

    assert reward.functions.isRNode(node1.cpc.accounts[0]).call() == False,\
        'node1 is rnode but it not have enough money'

    web3.personal.sendTransaction({'to': node1.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 200000 * Ether},
                                  'password')
    print("balance", node1.cpc.getBalance(node1.cpc.accounts[0]))
    web3.personal.sendTransaction({'to': node2.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 200000 * Ether},
                                  'password')
    print("balance", node2.cpc.getBalance(node2.cpc.accounts[0]))
    web3.personal.sendTransaction({'to': node3.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 200000 * Ether},
                                  'password')
    print("balance", node3.cpc.getBalance(node3.cpc.accounts[0]))
    web3.personal.sendTransaction({'to': node4.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 200000 * Ether},
                                  'password')
    print("balance", node4.cpc.getBalance(node4.cpc.accounts[0]))
    web3.personal.sendTransaction({'to': node5.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 200000 * Ether},
                                  'password')
    print("balance", node5.cpc.getBalance(node5.cpc.accounts[0]))
    web3.personal.sendTransaction({'to': node6.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 200000 * Ether},
                                  'password')
    print("balance", node6.cpc.getBalance(node6.cpc.accounts[0]))

    reward.functions.newRaise().transact({
        'gas': 3000000,
        'from': web3.cpc.accounts[0],
    })
    print('locked', reward.functions.isLocked().call())

    assert reward.functions.isRNode(node1.cpc.accounts[0]).call() == True,\
        'node1 is not rnode but he have enough money'
    assert reward.functions.isRNode(node2.cpc.accounts[0]).call() == True,\
        'node2 is not rnode but he have enough money'
    assert reward.functions.isRNode(node3.cpc.accounts[0]).call() == True,\
        'node3 is not rnode but he have enough money'
    assert reward.functions.isRNode(node4.cpc.accounts[0]).call() == True,\
        'node4 is not rnode but he have enough money'
    assert reward.functions.isRNode(node5.cpc.accounts[0]).call() == True,\
        'node5 is not rnode but he have enough money'
    assert reward.functions.isRNode(node6.cpc.accounts[0]).call() == True,\
        'node6 is not rnode but he have enough money'


    reward.functions.startNewRound().transact({
        'gas': 3000000,
        'from': web3.cpc.accounts[0],
    })
    time.sleep(3)
    print('locked', reward.functions.isLocked().call())

    # os.system("ps -efw | grep cpchain | grep -v grep | awk '{print $2}' | xargs kill -9")
    # os.system("./cpchain-all.sh")
    # time.sleep(30)


    # start next new round
    print("####start next new round####")
    reward.functions.newRaise().transact({
        'gas': 3000000,
        'from': web3.cpc.accounts[0],
    })
    time.sleep(3)
    print('locked', reward.functions.isLocked().call())

    node6_insatnce = get_instance(node6)
    node6_insatnce.functions.quitRenew().transact({
        'gas': 3000000,
        'from': node6.cpc.accounts[0],
    })

    reward.functions.startNewRound().transact({
        'gas': 3000000,
        'from': web3.cpc.accounts[0],
    })
    print('locked', reward.functions.isLocked().call())
    node6_balance1 = web3.eth.getBalance(node6.cpc.accounts[0])
    node5_balance1 = web3.eth.getBalance(node5.cpc.accounts[0])
    assert reward.functions.isRNode(node5.cpc.accounts[0]).call() == True
    assert reward.functions.isRNode(node6.cpc.accounts[0]).call() == False

    time.sleep(20)
    node5_balance2 = web3.eth.getBalance(node5.cpc.accounts[0])
    node6_balance2 = web3.eth.getBalance(node6.cpc.accounts[0])

    assert node5_balance2 > node5_balance1,\
        'node 5 is not mining but it is Rnode'

    assert node6_balance1== node6_balance2 ,\
        'node 6 is still mining but it not Rnode'

    reward.functions.setPeriod(90).transact({
        'gas': 3000000,
        'from': web3.cpc.accounts[0],
    })




if __name__ == '__main__':
    main()
