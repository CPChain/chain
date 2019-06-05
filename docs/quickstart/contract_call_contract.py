# coding=utf-8
#!/usr/bin/python3

from cpc_fusion import Web3
from solc import compile_source
from cpc_fusion.contract import ConciseContract

# the failure of calling creat_contract may be due to a low gas value
# adding gas may solve the problem

def creat_contract(filepath,url,contact_name,keypath,password,account_addr,gas):
    # Solidity source code
    contract_code_file = open(filepath,"r")
    contract_source_code = contract_code_file.read()
    print(contract_source_code)
    compiled_sol = compile_source(contract_source_code)  # Compiled source code
    contract_interface = compiled_sol[f'<stdin>:{contact_name}']

    # web3.py instance
    w3 = Web3(Web3.HTTPProvider(url))

    # set pre-funded account as sender
    w3.cpc.defaultAccount = w3.cpc.accounts[0]

    # Instantiate and deploy contract
    Greeter = w3.cpc.contract(abi=contract_interface['abi'], bytecode=contract_interface['bin'])

    # Submit the transaction that deploys the contract
    from_addr = w3.toChecksumAddress(account_addr)
    tx_hash = Greeter.constructor().raw_transact({
        # Increase or decrease gas according to contract conditions
        'gas': gas,
        'from': from_addr,
        'value': 0
    }, keypath, password, 42)

    print('*********', w3.cpc.getTransactionReceipt(tx_hash))

    # Wait for the transaction to be mined, and get the transaction receipt
    tx_receipt = w3.cpc.waitForTransactionReceipt(tx_hash)
    # tx_receipt1 = w3.cpc.waitForTransactionReceipt(tx_hash_raw)
    print(tx_receipt)
    # print(tx_receipt1)

    # Create the contract instance with the newly-deployed address
    greeter = w3.cpc.contract(
        address=tx_receipt.contractAddress,
        abi=contract_interface['abi'],
    )
    return greeter,w3,tx_receipt.contractAddress

def call_contract(greeter,account_addr,keypath,password,url):
    w3 = Web3(Web3.HTTPProvider(url))

    from_addr = w3.toChecksumAddress(account_addr)

    # Display the default greeting from the contract
    print('Default contract greeting: {}'.format(
        greeter.functions.greet().call()
    ))

    print('Setting the greeting to Nihao...')
    tx_hash = greeter.functions.setGreeting('Nihao').raw_transact({
        'gas': 300000,
        'from':from_addr,
        'value': 0,
    },keypath,password,42)

    # Wait for transaction to be mined...
    w3.cpc.waitForTransactionReceipt(tx_hash)

    # Display the new greeting value
    print('Updated contract greeting: {}'.format(
        greeter.functions.greet().call()
    ))

    # When issuing a lot of reads, try this more concise reader:
    reader = ConciseContract(greeter)
    assert reader.greet() == "Nihao"

    a = greeter.events.test.createFilter(fromBlock=0,toBlock='latest')
    eventlist = a.get_all_entries()
    print(eventlist)
if __name__ == '__main__':
    url = 'http://127.0.0.1:8501'
    # change the keypath to your keystore file
    keypath = "//home/shi/chain/workspace/src/bitbucket.org/cpchain/chain/examples/cpchain/data/data21/keystore/key21"
    password = "password"
    filepath = "call_contract_test.txt"
    account_addr = '0xb3801b8743dea10c30b0c21cae8b1923d9625f84'
    gas = 819776
    creat_contract(filepath,url,'Greeter',keypath,password,account_addr,gas)
