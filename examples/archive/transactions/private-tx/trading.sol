pragma solidity ^0.4.10;

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