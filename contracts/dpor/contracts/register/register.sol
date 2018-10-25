pragma solidity ^0.4.11;

contract Register {

    address owner;

    struct UploadRecord {
        string fileName;
        bytes32 fileHash;
        uint fileSize;
        uint timeStamp;
    }

    mapping(address => UploadRecord[]) public uploadHistory;

    constructor () public {
        owner = msg.sender;
    }

    function claimRegister(string fileName, bytes32 fileHash, uint fileSize) public {
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
}