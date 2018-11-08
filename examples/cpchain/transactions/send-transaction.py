#!/usr/bin/env python3

from web3 import Web3

web3 = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))

def main():

    account1 = web3.toChecksumAddress('0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a')
    account2 = web3.toChecksumAddress('0xc05302acebd0730e3a18a058d7d1cb1204c4a092')
    print('web3.eth.blockNumber:' + str(web3.eth.blockNumber))
    print(web3.eth.getBlock('latest'))

    print ('\nlistAccounts:')
    print(web3.eth.accounts)

    print ('\nunlock:')
    print (web3.personal.unlockAccount(account1, 'password'))

    print ('\nbalance of :' + account1)
    print (web3.eth.getBalance(account1))

    print ('balance of :' + account2)
    print (web3.eth.getBalance(account2))

    print ('\nsend tx1:')
    tx_hash = web3.personal.sendTransaction({'to': account2, 'from': web3.eth.coinbase, 'value': 10},'password')

    print ('\nwaitForTransactionReceipt:')
    tx_receipt = web3.eth.waitForTransactionReceipt(tx_hash)
    print (tx_receipt)

    print ('\nnew balance of:' + account1)
    print (web3.eth.getBalance(account1))

    print ('new balance of:' + account2)
    print (web3.eth.getBalance(account2))

if __name__ == '__main__':
    main()