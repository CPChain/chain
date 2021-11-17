#!/usr/bin/python3

from cpc_fusion import Web3
from solc import compile_source
from cpc_fusion.contract import ConciseContract

def main():
    # Solidity source code
    contract_source_code = '''
    pragma solidity ^0.4.24;

    contract Greeter {
        string public greeting;
        event test(address who,string a);
        function Greeter() public {
            greeting = 'Hello';
        }

        function setGreeting(string _greeting) public {
            emit test(msg.sender,_greeting);
            greeting = _greeting;
        }

        function greet() view public returns (string) {
            return greeting;
        }
    }
    '''
    print(contract_source_code)

    compiled_sol = compile_source(contract_source_code)  # Compiled source code
    contract_interface = compiled_sol['<stdin>:Greeter']

    # web3.py instance
    w3 = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))

    # set pre-funded account as sender
    w3.cpc.defaultAccount = w3.cpc.accounts[0]

    # Instantiate and deploy contract
    Greeter = w3.cpc.contract(abi=contract_interface['abi'], bytecode=contract_interface['bin'])

    # Submit the transaction that deploys the contract
    # your keypath
    # change the keypath to your keystore file
    keypath = "//home/shi/chain/workspace/src/bitbucket.org/cpchain/chain/examples/cpchain/data/data21/keystore/key21"
    # your password
    password = "password"
    # your account address
    from_addr = w3.toChecksumAddress('0xb3801b8743dea10c30b0c21cae8b1923d9625f84')
    tx_hash = Greeter.constructor().raw_transact({
        # Increase or decrease gas according to contract conditions
        'gas': 819776,
        'from': from_addr,
        'value': 0
    }, keypath, password, 42)
    # tx_hash = Greeter.constructor().transact()

    # print('*********',w3.cpc.getTransactionReceipt(tx_hash_raw))
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
if __name__ == '__main__':
    main()
