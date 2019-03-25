#!/usr/bin/env python3

from cpc_fusion import Web3
import time
import math

web3 = Web3(Web3.HTTPProvider('http://127.0.0.1:8521'))

Ether = int(math.pow(10, 18))

def get_web3_inst(num):
    port = 8500 + num
    return Web3(Web3.HTTPProvider(f"http://127.0.0.1:{port}"))

# plaese ensure address:0xe83a71428655b9f52ff6dc556e2b37043f39f194 have max money to test
def main():
    # init node
    node1 = get_web3_inst(1)
    node2 =get_web3_inst(2)
    node3 =get_web3_inst(3)
    node4 =get_web3_inst(4)
    node11 =get_web3_inst(11)
    node12 =get_web3_inst(12)

    print("web3 balance",web3.eth.getBalance(web3.cpc.accounts[0]),"\n")

    node1_balance = web3.eth.getBalance(node1.cpc.accounts[0])
    print("node1 balance", node1_balance,"\n")

    node2_balance = web3.eth.getBalance(node2.cpc.accounts[0])
    print("node2 balance", node2_balance,"\n")

    node3_balance = web3.eth.getBalance(node3.cpc.accounts[0])
    print("node3 balance", node3_balance,"\n")

    node4_balance = web3.eth.getBalance(node4.cpc.accounts[0])
    print("node4 balance", node4_balance,"\n")

    node11_balance = web3.eth.getBalance(node11.cpc.accounts[0])
    print("node11 balance", node11_balance,"\n")

    node12_balance = web3.eth.getBalance(node12.cpc.accounts[0])
    print("node12 balance", node12_balance,"\n")


    # send money to node
    web3.personal.sendTransaction({'to': node1.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 1000000 * Ether},
                                 'password')
    web3.personal.sendTransaction({'to': node2.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 1000000 * Ether},
                                  'password')
    web3.personal.sendTransaction({'to': node3.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 1000000 * Ether},
                                  'password')
    web3.personal.sendTransaction({'to': node4.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 1000000 * Ether},
                                  'password')
    web3.personal.sendTransaction({'to': node11.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 1000000 * Ether},
                                  'password')
    web3.personal.sendTransaction({'to': node12.cpc.accounts[0], 'from': web3.eth.coinbase, 'value': 1000000 * Ether},
                                  'password')

    time.sleep(5)

    print("***************** AFTER TRANSFERING MONEY *****************")

    print("web3 balance",web3.eth.getBalance(web3.cpc.accounts[0]),"\n")

    node1_balance = web3.eth.getBalance(node1.cpc.accounts[0])
    print("node1 balance", node1_balance,"\n")

    node2_balance = web3.eth.getBalance(node2.cpc.accounts[0])
    print("node2 balance", node2_balance,"\n")

    node3_balance = web3.eth.getBalance(node3.cpc.accounts[0])
    print("node3 balance", node3_balance,"\n")

    node4_balance = web3.eth.getBalance(node4.cpc.accounts[0])
    print("node4 balance", node4_balance,"\n")

    node11_balance = web3.eth.getBalance(node11.cpc.accounts[0])
    print("node11 balance", node11_balance,"\n")

    node12_balance = web3.eth.getBalance(node12.cpc.accounts[0])
    print("node12 balance", node12_balance,"\n")

if __name__ == '__main__':
    main()
