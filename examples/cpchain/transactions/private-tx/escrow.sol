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
