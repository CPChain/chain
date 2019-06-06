#!/usr/bin/env python3

from cpc_fusion import Web3


def test_local_sendRawTransaction():
    web3 = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))
    # web3.middleware_stack.inject(geth_poa_middleware, layer=0)
    # change the keypath to your keystore file
    with open('//home/shi/chain/workspace/src/bitbucket.org/cpchain/chain/examples/cpchain/data/data21/keystore/key21') as keyfile:
        encrypted_key = keyfile.read()
    # print(web3.cpc.getBalance(web3.cpc.accounts))
    print(web3.cpc.accounts)
    print('balance:', web3.cpc.getBalance(web3.cpc.accounts[0]))
    print("================================encrypted_key======================\n")
    print(encrypted_key)
    private_key_for_senders_account = web3.cpc.account.decrypt(encrypted_key, 'password')
    print("private_key_for_senders_account:")
    print(private_key_for_senders_account)
    print('coinbase:', web3.cpc.coinbase)
    from_addr = web3.toChecksumAddress('0xb3801b8743dea10c30b0c21cae8b1923d9625f84')
    to_addr = web3.toChecksumAddress('0xc05302acebd0730e3a18a058d7d1cb1204c4a092')

    print('gasPrice:', web3.cpc.gasPrice)
    # set chainId to None if you want a transaction that can be replayed across networks
    tx_dict = dict(
        type=0,
        nonce=web3.cpc.getTransactionCount(from_addr),
        gasPrice=web3.cpc.gasPrice,
        gas=90000,
        to=to_addr,
        value=123,
        data=b'',
        chainId=42,
    )
    signed_txn = web3.cpc.account.signTransaction(tx_dict,
                                                  private_key_for_senders_account,
                                                  )
    print("signed_txn:")
    print(signed_txn)

    print("sendRawTransaction:")
    print(web3.toHex(signed_txn.rawTransaction))
    print(web3.cpc.sendRawTransaction(signed_txn.rawTransaction))

if __name__=='__main__':
	test_local_sendRawTransaction()
