pragma solidity ^0.4.24;


contract ProxyContractInterface {
    function getProxyContract(address addr) public view returns (address);
}

contract PdashProxy{
    address owner;
    address public pdash;

    struct ProxyRecord {
        string fileName;
        bytes32 fileHash;
        uint fileSize;
        uint timeStamp;
    }
    ProxyContractInterface proxyContract;

    mapping(address => ProxyRecord[]) public proxyHistory;

   // _addr is the address of proxy_contract_register.sol
    constructor (address _addr) public {
        owner = msg.sender;
        pdash = 0xd81ab6b1e656550f90b2d874926b949fde97096d;
        proxyContract = ProxyContractInterface(_addr);
    }

    modifier onlyOwner() {require(msg.sender == owner);_;}
   // modifier restricted() {require(pdash == proxyContract.getProxyContract(msg.sender));_;}


    function proxyRegister(string fileName, bytes32 fileHash, uint fileSize) public{
        require(pdash == proxyContract.getProxyContract(msg.sender),"only pdash can call proxyRegister");
        proxyHistory[msg.sender].push(ProxyRecord(fileName, fileHash, fileSize, block.number));
    }

    function getProxyFileNumber(address proxy) public view returns (uint){
        return proxyHistory[proxy].length;
    }

    function getProxyFileNumberInBlock(address user, uint block_num) public view returns (uint) {
        uint count = 0;
        for (uint i = 0; i < proxyHistory[user].length; i++) {
            if (proxyHistory[user][i].timeStamp == block_num) {
                count ++;
            }
        }
        return count;
    }

    function updatePdashAddress(address addr)public onlyOwner(){
        pdash = addr;
    }
    /** set the Admission interface address. */
    function setProxyContractAddr(address _addr) public onlyOwner(){
        proxyContract = ProxyContractInterface(_addr);
    }
}