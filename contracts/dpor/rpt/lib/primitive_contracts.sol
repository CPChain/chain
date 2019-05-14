pragma solidity ^0.4.24;

library PrimitiveContractsInterface {
    function getRank(address addr, uint256 blockNum) internal view returns (uint256 b) {
        // Call a specific contract address and evm will call the underlying Go functions instead of calling normal deployed contract.
        // For Solidity assembly, refer to https://solidity.readthedocs.io/en/v0.4.24/assembly.html?highlight=assembly
        assembly {
            let p := mload(0x40)  // Get beginning address of available memory
            mstore(p, addr)       // Put address to the stack as the first parameter. mstore() is "mem[p...(p+32)]:=v", storing 32 bytes
            mstore(add(p, 0x20), blockNum)
            if iszero(staticcall(not(0), 0x64, p, 0x40, p, 0x20)) {
                revert(0, 0)
            }
            b := mload(p)
        }
    }

    function getMaintenance(address addr, uint256 blockNum) internal view returns (uint256 b) {
        assembly {
            let p := mload(0x40)
            mstore(p, addr)
            mstore(add(p, 0x20), blockNum)
            if iszero(staticcall(not(0), 0x65, p, 0x40, p, 0x20)) {
                revert(0, 0)
            }
            b := mload(p)
        }
    }

    function getProxyCount(address addr, uint256 blockNum) internal view returns (uint256 b) {
        assembly {
            let p := mload(0x40)
            mstore(p, addr)
            mstore(add(p, 0x20), blockNum)
            if iszero(staticcall(not(0), 0x66, p, 0x40, p, 0x20)) {
                revert(0, 0)
            }
            b := mload(p)
        }
    }

    function getUploadInfo(address addr, uint256 blockNum) internal view returns (uint256 b) {
        assembly {
            let p := mload(0x40)
            mstore(p, addr)
            mstore(add(p, 0x20), blockNum)
            if iszero(staticcall(not(0), 0x67, p, 0x40, p, 0x20)) {
                revert(0, 0)
            }
            b := mload(p)
        }
    }

    function getTxVolume(address addr, uint256 blockNum) internal view returns (uint256 b) {
        assembly {
            let p := mload(0x40)
            mstore(p, addr)
            mstore(add(p, 0x20), blockNum)
            if iszero(staticcall(not(0), 0x68, p, 0x40, p, 0x20)) {
                revert(0, 0)
            }
            b := mload(p)
        }
    }

    function isProxy(address addr, uint256 blockNum) internal view returns (uint256 b) {
        assembly {
            let p := mload(0x40)
            mstore(p, addr)
            mstore(add(p, 0x20), blockNum)
            if iszero(staticcall(not(0), 0x69, p, 0x40, p, 0x20)) {
                revert(0, 0)
            }
            b := mload(p)
        }
    }
}
