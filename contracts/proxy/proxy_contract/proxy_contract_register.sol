pragma solidity ^0.4.24;

contract ProxyContractRegister {

    address owner;

    // register proxy contract address -> real contract address
    mapping(address => address) public contractAddresses;

    modifier restricted() {
        if (msg.sender == owner) _;
    }

    // ------------------------------------------------------------------
    constructor () public {
        owner = msg.sender;
    }

    function registerProxyContract(address proxyAddress, address realAddress) public payable restricted {
        if (proxyAddress != address(this)) {
            contractAddresses[proxyAddress] = realAddress;
        }
    }

    function getRealContract(address addr) public view returns (address){
        return contractAddresses[addr];
    }
}