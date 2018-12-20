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
pubkey1 = "0x3082010a0282010100d211ba516865b11a0d6799917cbcf6653da7afa81508deb530ffd653a0d9dfcecdfda520b8c0180c8d44b904608a3939914bf4b0eccdeaa20aac9436de861c0d7c923415b82ba6a615bb8ae489a16efaa144af85f60d74800600b3766980c36fd0c9db66483c992ed8510ad860f77b2e554efd572dbd33455071568faf367b27702df0dc8aed75330d92f2897d6a4c3c69a43a6312c788584e5c63857271b941643019d4fcbbf497db68f3008829909b0f84f233972164af0f582f37a22fe4a20d047cdbd30dbab8facd24ae5ccf95f13a0bca3c061e4b35fe51b629245439a3c1132fdb5b8cfddda3823fa9da39ff1a8d052ce2759aa3f6a83c57f708ac25b10203010001"

# Party B, buyer
pubkey2 = "0x3082010a0282010100b44e1234604ab397bf1fbb220346b6a730e0b16609e447873ea33d8d8d256f3116e39d34d8b5a094a6c82799af79f4367b21683feb9c82d707a14b34538e066af73b058caa01b39064ed39eed90b8b88593fabadd652a04ae6699aa4ee9c8a04dcefc47456c25ac165fb7f7afa173b6798471e414a3b236e5062d7c323f04344e6bd766b83250c9328a6edf04202da5be0524e398252b5cca4bb1621fd3429512717b3b5be25bd12b0e1be5d4a5d380c3c6db1498c2712e44c82bbf66da5dd9b36b5725643fc167739039eb312b6bc4d3c18ccaa5e5f4db6419fb75b286aae32dffbfec7a3db5b229e5d8ec9a0d97d96cbfb9af0ce609e9b80358884bb9306250203010001"

# Agent P, e.g. PDash
pubkey3 = "0x3082010a0282010100c8f1e9ec5eb42d9fa72f4171b0f8c78f4a462671cef1eec52759e203c86d711f09fff31ce23b66e6dfd86c7350a13e532a45624c137040c7cfa3f0d27e07c8adce46ef031592167ce26403d555e0c6d75ea099df52204a9b3b4be6c9701ed272ba25834ec6eb440ef86209cbec2c80c26a6446a0376f4f7f367d37c3d7e3d9c83fe6b09a7843e6110667c428b5cf2de59bf0dc4d995ac4bf68258f9ef06d80a5293a4e798520b6bb563e52f67de4b5630afa3cfa3dd41e18b59cac1e7b9ac52483fa1eafc00572e9057a3a41510eae279eebaaa90d8244687b87fe77d15251418155edd3e50506d562a1176937d07096d96f86cfd7db68258496b96605fd51c30203010001"

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

trading_contract_addr = "0x4f8447b19cc84ef7c906a378678bb6a157227d30"
escrow_contract_addr = "0xF1c2E522e1De308B7348E8A8Ec4CC3C519e60Af8"


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
    tx_hash = contract.constructor().transact({'from': w3.cpc.accounts[0]})
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
    print(t)
    print(e)

    tx_hash = t.functions.setItem(120000000 * GWEI, "A secret data", "You may want to get it!").transact(
        {
            'from': w3.cpc.accounts[0],
            'gas': 3000000,
            'isPrivate': False,
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
    name = t.functions.getItemName().call({'isPrivate': False, 'participants': group1})
    price = t.functions.getItemPrice().call({'isPrivate': False, 'participants': group1})
    print("item name: %s, item price: %d" % (name, price))


def trans_escrow_money():
    print('''
    3. Buyer B pays money to the escrow contract CE.
    ''')
    w3 = get_web3_inst(2)
    e = get_escrow_contract_inst(w3)
    tx_hash = e.functions.prepay().transact({'gas': 200000, 'isPrivate': False, 'value': 120000000 * GWEI})
    w3.cpc.waitForTransactionReceipt(tx_hash)

    prepaied = e.functions.getBalance().call()
    print('Buyer B paied %d' % prepaied)


def create_order():
    print('4. Party B then sends contract CT an order.')
    w3 = get_web3_inst(2)
    t = get_trading_contract_inst(w3)
    tx_hash = t.functions.buy(pubkey2).transact({'gas': 3000000, 'isPrivate': False, 'participants': group1})
    w3.cpc.waitForTransactionReceipt(tx_hash)
    order = t.functions._order().call({'isPrivate': False})
    print(f"the order is {order}")


def deliver():
    print('''
    5. Party A sends the delivery message attached with the symmetric key encrypted by the buyer's public key
    ''')
    w3 = get_web3_inst(1)
    t = get_trading_contract_inst(w3)
    tx_hash = t.functions.deliver('cid1', 'symmetric-key-encrypted-by-pubkey').transact({
        'gas': 3000000,
        'isPrivate': False,
        'participants': group1,
    })
    w3.cpc.waitForTransactionReceipt(tx_hash)
    d = t.functions._delivery.call({'isPrivate': False})
    print(f"the delivery is {d}")


def confirm():
    print('6. Party B receives the delivery and send confirmation message')
    w3 = get_web3_inst(2)
    t = get_trading_contract_inst(w3)
    tx = t.functions.confirm().transact({'gas': 3000000, 'isPrivate': False, 'participants': group1})
    w3.cpc.waitForTransactionReceipt(tx)
    d = t.functions._delivery().call({'isPrivate': False})
    print(f"status of delivery has been changed, {d}")

def done_tx():
    print('7. Agent P notice the confirmation and transfer money to Party A')
    w3 = get_web3_inst(3)
    t = get_trading_contract_inst(w3)
    e = get_escrow_contract_inst(w3)
    balance = e.functions.getBalance().call({'gas': 200000})
    print(f"before transfer the balance is {balance}")

    fee = t.functions.getItemName().call({'isPrivate': True})
    tx = e.functions.payTo(account1, fee).transact({'gas': 200000})
    w3.cpc.waitForTransactionReceipt(tx)
    balance = e.functions.getBalance().call({'gas': 200000})
    print(f"the fee has been transferred to seller, as a result the balance is {balance}")


def other_party_inspect():
    print('8. Other parties could not get any information about the transaction between A and B')
    w3 = get_web3_inst(4)
    t = get_trading_contract_inst(w3)
    item = t.functions.getItemName().call({'isPrivate': False})
    print(f"expect that it would be failed to get information of the private transaction from non-participate party ")
    print(f"the result is {item}")


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
