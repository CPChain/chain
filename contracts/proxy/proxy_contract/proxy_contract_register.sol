pragma solidity ^0.4.24;

contract ProxyContractRegister {

    address owner;

    // register proxy contract address -> real contract address
    mapping(address => address) public contractAddresses;
    mapping(address => address) public proxyContractAddress;

    modifier restricted() {
        if (msg.sender == owner) _;
    }

    // ------------------------------------------------------------------
    constructor () public {
        owner = msg.sender;
    }

    function registerProxyContract(address _proxyAddress, address _realAddress) public payable restricted {
        if (_proxyAddress != address(this)) {
            contractAddresses[_proxyAddress] = _realAddress;
            proxyContractAddress[_realAddress] = _proxyAddress;
        }
    }

    function getRealContract(address _addr) public view returns (address){
        return contractAddresses[_addr];
    }

    function getProxyContract(address _addr) public view returns (address){
            return proxyContractAddress[_addr];
    }
}