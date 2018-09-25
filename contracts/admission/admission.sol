pragma solidity ^0.4.16;

/** @title admission control for campaign committee */

contract Admission {
    uint cpuTarget;
    uint memoryTarget;

    uint public cpuDifficulty;
    uint public memoryDifficulty;

    constructor (uint _cpuDifficulty, uint _memoryDifficulty) public {
	require(_cpuDifficulty <= 256 && _cpuDifficulty >= 0, "Difficulty must less than 256");
	require(_memoryDifficulty <= 256 && _memoryDifficulty >= 0, "Difficulty must less than 256");

	cpuDifficulty = _cpuDifficulty;
	memoryDifficulty = _memoryDifficulty;

        memoryTarget = 1 << (256 - _memoryDifficulty);
        cpuTarget = 1 << (256 - _cpuDifficulty);
    }

    /** @dev updateCPUDifficulty updates cpu difficulty
    * @param _difficulty the new cpu difficulty
    */
    function updateCPUDifficulty(uint _difficulty) public {
	require(_difficulty <= 256 && _difficulty >= 0, "Difficulty must less than 256");
	cpuDifficulty = _difficulty;
        cpuTarget = 1 << (256 - _difficulty);
    }

    /** @dev updateMemoryDifficulty updates memory difficulty
    * @param _difficulty the new memory difficulty
    */
    function updateMemoryDifficulty(uint _difficulty) public {
	require(_difficulty <= 256 && _difficulty >= 0, "Difficulty must less than 256");
	memoryDifficulty = _difficulty;
        memoryTarget = 1 << (256 - _difficulty);
    }

    /** @dev verify verifies the given proof
    * @param _cpuNonce the cpu nonce
    * @param _cpuBlockNumber the cpu pow input block number
    * @param _memoryNonce the memory nonce
    * @param _memoryBlockNumber the memory pow input block number
      @return true returns true if all is ok
    */
    function verify(uint64 _cpuNonce, uint _cpuBlockNumber, uint64 _memoryNonce, uint _memoryBlockNumber) public constant returns (bool) {
        return verifyCPU(_cpuNonce, _cpuBlockNumber) && verifyMemory(_memoryNonce, _memoryBlockNumber);
    }

    /** @dev verifyMemory verifies the given memory proof
    * @param _nonce the memory nonce
    * @param _blockNumber the memory pow input block number
      @return true returns true if memory proof is ok
    */
    function verifyMemory(uint64 _nonce, uint _blockNumber) public constant returns (bool) {
        return true;
    }

    /** @dev verifyCPU verifies the given cpu proof
    * @param _nonce the cpu nonce
    * @param _blockNumber the cpu pow input block number
      @return true returns true if cpu proof is ok
    */
    function verifyCPU(uint64 _nonce, uint _blockNumber) public constant returns (bool) {
        require((block.number-_blockNumber) <= 20 && (block.number-_blockNumber) >= 0, "must within 20 block");
        return sha256(abi.encodePacked(block.coinbase, blockhash(_blockNumber), _nonce)) <=  bytes32(cpuTarget);
    }
}


