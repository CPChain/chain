/**
 * admission contract is to check if the performance of the nodes meets the requirements
 * the contract receives proofs and returns results
 * check is done in other go functions, the admission contract will call it by assembly
**/


pragma solidity ^0.4.24;

/** @title admission control for campaign committee */

contract Admission {
    uint cpuTarget;
    uint memoryTarget;

    uint public cpuDifficulty=12;
    uint public cpuWorkTimeout;
    uint public memoryDifficulty=6;
    uint public memoryWorkTimeout;
    address public owner;

    modifier onlyOwner(){msg.sender == owner; _;}

    constructor (uint _cpuDifficulty, uint _memoryDifficulty,uint _cpuWorkTimeout,uint _memoryWorkTimeout) public {
        // Duplicated Code
        // require(_cpuDifficulty <= 256 && _cpuDifficulty >= 0, "Difficulty must less than 256");
        // require(_memoryDifficulty <= 256 && _memoryDifficulty >= 0, "Difficulty must less than 256");
        owner = msg.sender;
        updateCPUDifficulty(_cpuDifficulty);
        updateMemoryDifficulty(_memoryDifficulty);
        updateCPUWorkTimeout(_cpuWorkTimeout);
        updateMemoryWorkTimeout(_memoryWorkTimeout);
    }

    function getAdmissionParameters() public view returns(uint,uint,uint,uint){
        // return (0,0,0,0);
        return (cpuDifficulty,memoryDifficulty,cpuWorkTimeout,memoryWorkTimeout);
    }

    function updateCPUWorkTimeout(uint _cpuWorkTimeout) public onlyOwner{
        cpuWorkTimeout = _cpuWorkTimeout;
    }

    function updateMemoryWorkTimeout(uint _memoryWorkTimeout) public onlyOwner{
        memoryWorkTimeout= _memoryWorkTimeout;
    }

    /**
     * @dev updateCPUDifficulty updates cpu difficulty
     * @param _difficulty the new cpu difficulty
     */
    function updateCPUDifficulty(uint _difficulty) public onlyOwner {
        require(_difficulty <= 256 && _difficulty >= 0, "Difficulty must less than 256");
        cpuDifficulty = _difficulty;
        cpuTarget = 1 << (256 - _difficulty);
    }

    /**
     * @dev updateMemoryDifficulty updates memory difficulty
     * @param _difficulty the new memory difficulty
     */
    function updateMemoryDifficulty(uint _difficulty) public onlyOwner {
        require(_difficulty <= 256 && _difficulty >= 0, "Difficulty must less than 256");
        memoryDifficulty = _difficulty;
        memoryTarget = 1 << (256 - _difficulty);
    }

    /**
     * @dev verify verifies the given proof
     * @param _cpuNonce the cpu nonce
     * @param _cpuBlockNumber the cpu pow input block number
     * @param _memoryNonce the memory nonce
     * @param _memoryBlockNumber the memory pow input block number
     * @return true returns true if all is ok
     */
    function verify(
        uint64 _cpuNonce,
        uint _cpuBlockNumber,
        uint64 _memoryNonce,
        uint _memoryBlockNumber,
        address _sender
        )
        public
        view
        returns (bool)
    {
        return verifyCPU(_sender, _cpuNonce, _cpuBlockNumber, cpuDifficulty)
                && verifyMemory(_sender, _memoryNonce, _memoryBlockNumber, memoryDifficulty);
    }

    /**
     * @dev verifyCPU verifies the given cpu proof
     * @param _sender the campaign participant, message sender of claimcampaign contract.
     * @param _nonce the cpu nonce
     * @param _blockNumber the cpu pow input block number
     * @return true returns true if cpu proof is ok
     */
    function verifyCPU(address _sender, uint64 _nonce, uint _blockNumber, uint _difficulty) public view returns (bool b) {
        assembly {
            let p := mload(0x40)
            mstore(p, _sender)  // NOTE: mstore stores 32 bytes regardless of the length of input paramter
            mstore(add(p, 0x20), _nonce)
            mstore(add(p, 0x40), blockhash(_blockNumber))
            mstore(add(p, 0x60), _difficulty)
            if iszero(staticcall(not(0), 0x6A, p, 0x80, p, 0x20)) {
                revert(0, 0)
            }
            b := mload(p)
        }
    }

    /**
     * @dev verifyMemory verifies the given memory proof
     * @param _sender the campaign participant, message sender of claimcampaign contract.
     * @param _nonce the memory nonce
     * @param _blockNumber the memory pow input block number
     * @param _difficulty  the difficulty of memory pow
     * @return true returns true if memory proof is ok
     */
    function verifyMemory(address _sender, uint64 _nonce, uint _blockNumber, uint _difficulty) public view returns (bool b) {
        assembly {
            let p := mload(0x40)
            mstore(p, _sender)
            mstore(add(p, 0x20), _nonce)
            mstore(add(p, 0x40), blockhash(_blockNumber))
            mstore(add(p, 0x60), _difficulty)
            if iszero(staticcall(not(0), 0x6B, p, 0x80, p, 0x20)) {
                revert(0, 0)
            }
            b := mload(p)
        }
    }
}
