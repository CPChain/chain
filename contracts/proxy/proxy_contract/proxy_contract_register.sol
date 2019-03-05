pragma solidity ^0.4.24;

contract ProxyContractRegister {

    address owner;
    // register proxy contract address -> real contract address
    mapping(address => address) public contractAddresses;
    mapping(address => address) public proxyContractAddress;
    mapping(address => uint256) public proxyContractAddressVersion;
    mapping(address => mapping(uint => address)) public histroyContract;
    event ProxyContractAddressVersion(address _proxy, address _real,uint256 _version);

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
            proxyContractAddressVersion[_proxyAddress] = proxyContractAddressVersion[_proxyAddress] + 1;
            histroyContract[_proxyAddress][proxyContractAddressVersion[_proxyAddress]]=_realAddress;
            emit ProxyContractAddressVersion(_proxyAddress,_realAddress,proxyContractAddressVersion[_proxyAddress]);
        }
    }

    function getRealContract(address _addr) public view returns (address){
        return contractAddresses[_addr];
    }

    function getProxyContract(address _addr) public view returns (address){
            return proxyContractAddress[_addr];
    }

    function getOldContract(address _addr, uint _version)public view returns(address){
        return histroyContract[_addr][_version];
    }

    function getContractVersion(address _proxyAddress)public view returns(uint){
        return proxyContractAddressVersion[_proxyAddress];
    }
}