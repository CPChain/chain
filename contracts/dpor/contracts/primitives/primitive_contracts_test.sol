pragma solidity ^0.4.24;

import './primitive_contracts.sol';

/**
 * library PrimitiveContractsInterface {
 * function getRank(address addr, uint256 blockNum) internal view returns (uint256 b);
 * function getMaintenance(address addr, uint256 blockNum) internal view returns (uint256 b);
 * function getProxyCount(address addr, uint256 blockNum) internal view returns (uint256 b);
 * function getUploadInfo(address addr, uint256 blockNum) internal view returns (uint256 b);
 * function getTxVolume(address addr, uint256 blockNum) internal view returns (uint256 b);
 * function isProxy(address addr, uint256 blockNum) internal view returns (uint256 b);
 * }
 */

contract PrimitiveContractsTest {
    using PrimitiveContractsInterface for address;

    function getRank(address addr, uint256 blockNum) public view returns (uint256 b) {
        return addr.getRank(blockNum);
    }

    function getMaintenance(address addr, uint256 blockNum) public view returns (uint256 b) {
        return addr.getMaintenance(blockNum);
    }

    function getProxyCount(address addr, uint256 blockNum) public view returns (uint256 b) {
        return addr.getProxyCount(blockNum);
    }

    function getUploadInfo(address addr, uint256 blockNum) public view returns (uint256 b) {
        return addr.getUploadInfo(blockNum);
    }

    function getTxVolume(address addr, uint256 blockNum) public view returns (uint256 b) {
        return addr.getTxVolume(blockNum);
    }

    function isProxy(address addr, uint256 blockNum) public view returns (uint256 b) {
        return addr.isProxy(blockNum);
    }
}


