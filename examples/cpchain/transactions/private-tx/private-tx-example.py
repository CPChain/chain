#!/usr/bin/env python3

import math

import cpc_fusion as cpc
from cpc_fusion.contract import ConciseContract
from solc import compile_source


account1 = "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a"
account2 = "0xc05302acebd0730e3a18a058d7d1cb1204c4a092"
account3 = "0xef3dd127de235f15ffb4fc0d71469d1339df6465"
account4 = "0x3a18598184ef84198db90c28fdfdfdf56544f747"

# NOTE: you must update the public keys with the real ones in running environment.
# Party A, seller
pubkey1 = "0x3082010a0282010100a8cc14bf597f1961580c7ca23aa294686680c665e9291edeb1cec666f1eed6b7f923b1028f7069279a2a9a8b72a464c004f75fa0e4a78d6fed746a05920c1d6da42b74744be50444e507c025cba76b47d7df39924de003a8e204c1bab05b527b38bf96fb192733cd153bfd44d661eae09d3a1f99f21868cd44ecc58cffa89d41669d4aae313f6d628897c241115c584f0965d90d4a5731cf90e1b61677ff5bf23be781019c937e4bd0b9f028d111be4f589835d97f88ad3964e58183c7725bc04f34c1acd0dd816373bb3b6b06abb17bd02d5b4e8703f11365eae245fc61982c19126206b0f9c012a6ba604f944fe159bb9300433fee09405ec64636a3513e830203010001"

# Party B, buyer
pubkey2 = "0x3082010a0282010100de2310a2486121bcce10618b1d0ea5a72648ec6439e19cf7fe0be5815ae4284a0d8fe1578a70fc23cc73b00c7e1dbfdc50cb2cd6f3bafc9fe574f05c062b035e8597aaf050d92a399cd9b2cdb977dbb3a025e4339b1205d5a80ceca6fa89153fb7a2f0c0f33d81e9b869e0dd979f3208245c9040e7118e188af495a36fba120f4d9efb0fc58e167eb7721a1553117658c7527b290b87048bb2202db57d17d6be9368e2ba1b5c0b2bb04671b69df2976d33b574075d1fe541763cd445a5760998b3e7c13e9f6559226a5b890ac77aeb1cd33894c8e278bf5d48708be7c0217d207e715df29a1243b9293b116ceedb389daf62e8ba7b6615255ad340ec9ebbf9ff0203010001"

# Agent P, e.g. PDash
pubkey3 = "0x3082010a0282010100be41bee48d9bcf9fccaaa2b985455121a4f652cdf0196f371c24172cbbd55abc90bc26359da2780437f15fdde134c7f741bac10ba1fe0f010fd79898ea3a63fb893ef0e3177300e936c0c85731cb12d9b2125d704b774f3a6c6fa17a4059d1d2134f2805090b3956200b1847245e2322afb597b95f66484da21fade2f8033e13a28c04738a87b40892c549599ac0683542f34b78133245d4ca57198e88fa427549c876720bc0525a7885a337510c4338f41914c894f1bc14dd56d720f22602ab35b72619c3d250e7fff6e805aca93724a5dd91355cfe1f109efae1b5e24b4df91d3eb44d50c647a9452265bc309e1d416c9a35125b0ac35c80dc37b17ff7aafd0203010001"

# private tx group
group1 = [pubkey1, pubkey2, pubkey3]

escrow_src = """
pragma solidity ^0.4.24;

/**
 * @title Escrow Contract for Data Trading
 *
 * @dev escrow contract keeps the money of a trade between seller and buyer, and pay
 * money to seller once buyer confirms that the seller has delivered trading items.
 *
 * It is just a very simple version.
*/
contract escrow{
    address _owner;
    uint256 _balance;

    event Recieve(address _from, uint value);
    event PayTo(address to, uint value);

    modifier onlyOwner() { require(msg.sender == _owner);_; }

    constructor() public {
        _owner = msg.sender;
    }

    /**
     * @dev Prepay money for transaction in future.
    */
    function prepay() payable public {
        _balance += msg.value;
        emit Recieve(msg.sender, msg.value);
    }

    /**
     * @dev Query the prepaied money.
     * @return A uint256 specifying the amount of tokens available.
    */
    function getBalance() view public returns (uint256) {
        return _balance;
    }

    /**
     * @dev Pay token to a specified address, only owner can invoke it.
     * @param to The address to transfer to.
     * @param value The amount to be transferred.
    */
    function payTo(address to, uint256 value) payable public onlyOwner {
        require(msg.sender == _owner);
        require(to != address(0));
        require(_balance >= value);

        _balance = _balance - value;
        to.transfer(value);

        emit PayTo(to, value);
    }
}

"""

trading_src = """
pragma solidity ^0.4.24;

/**
 * @title Trading contract for private data trading.
 */
contract Trading {
    /**
     * @dev Information about an item for sale
     */
    struct SaleItem {
        bool available;
        string name;
        address seller;
        uint price;
        string description;
    }

    /**
     * @dev Transaction record
     */
    struct Order {
        bool available;
        uint price;
        address seller;
        address buyer;
        string pubKey;
    }

    /**
     * @dev Information about delivery.
     */
    struct Delivery {
        bool available;
        string cid;
        string symKey;
        bool confirmed;
    }

    // ower of this contract, usually the agent.
    address _owner;
    // item for sale
    SaleItem public _item;
    // order information
    Order public _order;
    // delivery status
    Delivery public _delivery;

    modifier onlyOwner(){require(msg.sender == _owner);
        _;}
    modifier onlySeller(){require(msg.sender == _item.seller);
        _;}
    modifier onlyBuyer(){require(msg.sender == _order.buyer);
        _;}

    event OrderCreated(uint price, address seller, address buyer, string pubkey);
    event ItemDelivered(string cid, address seller, address buyer, string symKey);
    event Confirmed(address seller, address buyer);

    constructor() public {
        _owner = msg.sender;
    }

    /**
     * @dev Get item for sale.
     */
    function getItem() public view returns (string name, uint price, string description){
        return (_item.name, _item.price, _item.description);
    }

    function getItemName() public view returns (string){
        return _item.name;
    }

    function getItemPrice() public view returns (uint){
        return _item.price;
    }

    /**
     * @dev Set item for sale.
     */
    function setItem(uint price, string name, string description) public {
        require(_item.available == false);

        _item = SaleItem(true, name, msg.sender, price, description);
    }

    /**
     * @dev Update the price of the item for sale.
     */
    function updateItemPrice(uint price) public onlySeller {
        require(_item.available == true);

        _item.price = price;
    }

    /**
     * @dev Buy the item.
     */
    function buy(string pubkey) public {
        require(_order.available == false && _item.available == true);

        _order = Order(true, _item.price, _item.seller, msg.sender, pubkey);
        emit OrderCreated(_item.price, _item.seller, msg.sender, pubkey);
    }

    /**
     * @dev Deliver the item.
     */
    function deliver(string cid, string symKey) public onlySeller() {
        require(_delivery.available == false && _order.available == true);

        _delivery = Delivery(true, cid, symKey, false);
        emit ItemDelivered(cid, _order.seller, _order.buyer, symKey);
    }

    function confirm() public onlyBuyer {
        require(_delivery.available == true);

        _delivery.confirmed = true;
        emit Confirmed(_order.seller, _order.buyer);
    }
}
"""

compiled_escrow = compile_source(escrow_src)['<stdin>:escrow']
compiled_trading = compile_source(trading_src)['<stdin>:Trading']

GWEI = int(math.pow(10, 9))

trading_contract_addr = None
escrow_contract_addr = None


def get_web3_inst(num):
    port = 8500 + num
    return cpc.Web3(cpc.Web3.HTTPProvider(f"http://127.0.0.1:{port}"))


def get_trading_contract_inst(web3):
    return web3.cpc.contract(address=trading_contract_addr, abi=compiled_trading['abi'])


def get_escrow_contract_inst(web3):
    return web3.cpc.contract(address=escrow_contract_addr, abi=compiled_escrow['abi'])


def deploy_trading_contract():
    print('deploying private trading contract CT')
    w3 = get_web3_inst(3)
    print(w3.cpc.accounts[0])
    w3.cpc.defaultAccount = w3.cpc.accounts[0]
    print(w3.cpc.defaultAccount)
    contract = w3.cpc.contract(abi=compiled_trading['abi'], bytecode=compiled_trading['bin'])
    tx_hash = contract.constructor().transact({'from': w3.cpc.accounts[0], 'isPrivate': True, 'participants': group1})
    tx_receipt = w3.cpc.waitForTransactionReceipt(tx_hash)
    global trading_contract_addr
    trading_contract_addr = w3.toChecksumAddress(tx_receipt['contractAddress'])
    print('deployed private trading contract CT')


def deploy_escrow_contract():
    print('deploying public escrow contract CE')
    w3 = get_web3_inst(3)
    print(w3.cpc.accounts[0])
    w3.cpc.defaultAccount = w3.cpc.accounts[0]
    print(w3.cpc.defaultAccount)
    contract = w3.cpc.contract(abi=compiled_escrow['abi'], bytecode=compiled_escrow['bin'])
    tx_hash = contract.constructor().transact({'from': w3.cpc.accounts[0]})
    tx_receipt = w3.cpc.waitForTransactionReceipt(tx_hash)
    global escrow_contract_addr
    escrow_contract_addr = w3.toChecksumAddress(tx_receipt['contractAddress'])
    print('deployed public escrow contract CE')


def set_items():
    print('''
    1. Seller A registers an item via the private contract CT. An item includes name, 
    ipfs_cid, price, description and so on.
    ''')
    w3 = get_web3_inst(1)
    t = get_trading_contract_inst(w3)
    e = get_escrow_contract_inst(w3)

    tx_hash = t.functions.setItem(120000000 * GWEI, "A secret data", "You may want to get it!").transact(
        {
            'from': w3.cpc.accounts[0],
            'gas': 3000000,
            'isPrivate': True,
            'participants': group1
        }
    )

    r = w3.cpc.waitForTransactionReceipt(tx_hash)


def read_items():
    print('''
    2. Buyer B checked the registered items on contract CT and choose some items to buy.
    ''')
    w3 = get_web3_inst(2)
    t = get_trading_contract_inst(w3)
    name = t.functions.getItemName().call({'isPrivate': True, 'participants': group1})
    price = t.functions.getItemPrice().call({'isPrivate': True, 'participants': group1})
    print("item name: %s, item price: %d" % (name, price))


def trans_escrow_money():
    print('''
    3. Buyer B pays money to the escrow contract CE.
    ''')
    w3 = get_web3_inst(2)
    e = get_escrow_contract_inst(w3)
    tx_hash = e.functions.prepay().transact({
        'gas': 200000,
        'value': 120000000 * GWEI,
        'from': w3.cpc.accounts[0]})
    w3.cpc.waitForTransactionReceipt(tx_hash)

    prepaied = e.functions.getBalance().call()
    print('Buyer B paied %d' % prepaied)


def create_order():
    print('4. Party B then sends contract CT an order.')
    w3 = get_web3_inst(2)
    t = get_trading_contract_inst(w3)
    tx_hash = t.functions.buy(pubkey2).transact({
        'gas': 3000000,
        'isPrivate': True,
        'participants': group1,
        'from': w3.cpc.accounts[0]})
    w3.cpc.waitForTransactionReceipt(tx_hash)
    order = t.functions._order().call({'isPrivate': True, 'from': w3.cpc.accounts[0]})
    print(f"the order is {order}")


def deliver():
    print('''
    5. Party A sends the delivery message attached with the symmetric key encrypted by the buyer's public key
    ''')
    w3 = get_web3_inst(1)
    t = get_trading_contract_inst(w3)
    tx_hash = t.functions.deliver('cid1', 'symmetric-key-encrypted-by-pubkey').transact({
        'gas': 3000000,
        'isPrivate': True,
        'participants': group1,
        'from': w3.cpc.accounts[0],
    })
    w3.cpc.waitForTransactionReceipt(tx_hash)
    d = t.functions._delivery().call({'isPrivate': True, 'from': w3.cpc.accounts[0]})
    print(f"the delivery is {d}")


def confirm():
    print('6. Party B receives the delivery and send confirmation message')
    w3 = get_web3_inst(2)
    t = get_trading_contract_inst(w3)
    tx = t.functions.confirm().transact({
        'gas': 3000000,
        'isPrivate': True,
        'participants': group1,
        'from': w3.cpc.accounts[0],
    })
    w3.cpc.waitForTransactionReceipt(tx)
    d = t.functions._delivery().call({'isPrivate': True, 'from': w3.cpc.accounts[0]})
    print(f"status of delivery has been changed, {d}")

def done_tx():
    print('7. Agent P notice the confirmation and transfer money to Party A')
    w3 = get_web3_inst(3)
    t = get_trading_contract_inst(w3)
    e = get_escrow_contract_inst(w3)
    balance = e.functions.getBalance().call({'gas': 200000, 'from': w3.cpc.accounts[0]})
    print(f"before transfer the balance is {balance}")

    fee = t.functions.getItemPrice().call({'isPrivate': True, 'from': w3.cpc.accounts[0]})
    tx = e.functions.payTo(w3.toChecksumAddress(account1), fee).transact({'gas': 200000, 'from': w3.cpc.accounts[0]})
    w3.cpc.waitForTransactionReceipt(tx)
    balance = e.functions.getBalance().call({'gas': 200000, 'from': w3.cpc.accounts[0]})
    print(f"the fee has been transferred to seller, as a result the balance is {balance}")


def other_party_inspect():
    print('8. Other parties could not get any information about the transaction between A and B')
    w3 = get_web3_inst(4)
    t = get_trading_contract_inst(w3)
    try:
        item = t.functions.getItemName().call({'isPrivate': True, 'from': w3.cpc.accounts[0]})
    except:
        print('the thrown exception is expected, because the node does not have permission.')
        print('expect that it would be failed to get information of the private transaction from non-participate party')


if __name__ == '__main__':
    print("This user scenario describes a party A and a party B trade data with agent P's service in a private way.")
    deploy_trading_contract()
    deploy_escrow_contract()
    set_items()
    read_items()
    trans_escrow_money()
    deliver()
    confirm()
    done_tx()
    other_party_inspect()
