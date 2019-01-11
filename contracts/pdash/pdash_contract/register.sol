pragma solidity ^0.4.11;


contract ProxyInterface {
    function getProxyContract(address addr) public view returns (address);
}

contract Register {

    address owner;
    address pdash;

    struct UploadRecord {
        string fileName;
        bytes32 fileHash;
        uint fileSize;
        uint timeStamp;
    }

    ProxyInterface proxyContract;

    mapping(address => UploadRecord[]) public uploadHistory;

    modifier onlyOwner() {require(msg.sender == owner);_;}

    constructor (address _addr) public {
        owner = msg.sender;
        pdash = 0xd81ab6b1e656550f90b2d874926b949fde97096d;
        proxyContract = ProxyInterface(_addr);
    }

    function claimRegister(string fileName, bytes32 fileHash, uint fileSize) public {
        require(pdash == proxyContract.getProxyContract(msg.sender),"only pdash can call claimRegister");
        // require(pdash == msg.sender,"only pdash can call claimRegister");
        uploadHistory[msg.sender].push(UploadRecord(fileName, fileHash, fileSize, block.number));
    }

    function getUploadCount(address user) public view returns (uint){
        return uploadHistory[user].length;
    }

    function getUploadCountAfterBlock(address user, uint block_num) public view returns (uint) {
        uint startIdx = 0;
        for (uint i = 0; i < uploadHistory[user].length; i++) {
            if (uploadHistory[user][i].timeStamp > block_num) {
                startIdx = i;
                break;
            }
        }
        return uploadHistory[user].length - startIdx;
    }

    function updatePdashAddress(address addr)public onlyOwner(){
        pdash = addr;
    }
    /** set the Admission interface address. */
    function setAdmissionAddr(address _addr) public onlyOwner(){
        proxyContract = ProxyInterface(_addr);
    }
}