#!/usr/bin/env python3

# import json
# import os.path as osp

# cf. http://tinyurl.com/yd7mbzp3
from solc import compile_standard
from cpc_fusion import Web3, HTTPProvider
from cpc_fusion.contract import ImplicitContract

# solidity source code
contract_source_code = '''
pragma solidity ^0.4.0;

contract Greeter {
    event SetGreetingEvent(
        address indexed _from,
        uint val
    );

    string public greeting;

    function Greeter() {
        greeting = 'Hello';
    }

    function setGreeting(string _greeting) public {
        emit SetGreetingEvent(msg.sender, 42);
        greeting = _greeting;
    }

    function greet() constant returns (string) {
        return greeting;
    }
}
'''

w3 = None
http_provider = "http://127.0.0.1:8501"


def set_default_w3():
    global w3
    global http_provider
    provider = HTTPProvider(http_provider)
    w3 = Web3(provider)

    # cf. https://web3py.readthedocs.io/en/stable/middleware.html#geth-style-proof-of-authority
    from web3.middleware import geth_poa_middleware
    # inject the poa compatibility middleware to the innermost layer
    w3.middleware_stack.inject(geth_poa_middleware, layer=0)

    w3.eth.defaultAccount = w3.eth.accounts[0]

    
def compile_contract():
    #compiled_sol = compile_source(contract_source_code)
    #return compiled_sol
    
    # cf. http://tinyurl.com/yap75nl8
    sol_map = {
        "language": "Solidity",
        "sources": {},
        "settings": {
            "outputSelection": {
                "*": {
                    "*": ["abi", "evm.bytecode"]
                }
            }
        }
    }
    d = sol_map["sources"]["contract"] = {}
    d["content"] = contract_source_code
    output = compile_standard(sol_map)
    return output['contracts']['contract']['Greeter']


def deploy_contract(interface):
    contract = w3.eth.contract(abi=interface['abi'], bytecode=interface['evm']['bytecode']['object'])

    # create filter
    event_filter = contract.events.SetGreetingEvent.createFilter(fromBlock=0, toBlock="latest")
    
    estimated_gas = contract.constructor().estimateGas()
    tx_hash = contract.constructor().transact(dict(gas=estimated_gas))

    # get tx receipt to get contract address
    tx_receipt = w3.eth.waitForTransactionReceipt(tx_hash)
    address = tx_receipt['contractAddress']

    contract = w3.eth.contract(address=address, abi=interface['abi'], ContractFactoryClass=ImplicitContract)

    print('Contract value: {}'.format(contract.greet()))
    tx_hash = contract.setGreeting('Nihao')
    w3.eth.waitForTransactionReceipt(tx_hash)
    print('Setting value to: Nihao')
    output = contract.greet()
    print('Contract value: {}'.format(contract.greet()))
    assert output == "Nihao" 
    
    entry = event_filter.get_all_entries()[0]
    assert entry.args.val == 42


def main():
    set_default_w3()
    interface = compile_contract()
    deploy_contract(interface)


if __name__ == '__main__':
    main()
