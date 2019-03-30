#!/usr/bin/python3

from cpc_fusion import Web3
import time
import sys
import os

acConfig ={
    "abi":"[{\"constant\":true,\"inputs\":[],\"name\":\"memoryDifficulty\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_cpuWorkTimeout\",\"type\":\"uint256\"}],\"name\":\"updateCPUWorkTimeout\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_cpuNonce\",\"type\":\"uint64\"},{\"name\":\"_cpuBlockNumber\",\"type\":\"uint256\"},{\"name\":\"_memoryNonce\",\"type\":\"uint64\"},{\"name\":\"_memoryBlockNumber\",\"type\":\"uint256\"},{\"name\":\"_sender\",\"type\":\"address\"}],\"name\":\"verify\",\"outputs\":[{\"name\":\"\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_sender\",\"type\":\"address\"},{\"name\":\"_nonce\",\"type\":\"uint64\"},{\"name\":\"_blockNumber\",\"type\":\"uint256\"},{\"name\":\"_difficulty\",\"type\":\"uint256\"}],\"name\":\"verifyMemory\",\"outputs\":[{\"name\":\"b\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"cpuWorkTimeout\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[{\"name\":\"_sender\",\"type\":\"address\"},{\"name\":\"_nonce\",\"type\":\"uint64\"},{\"name\":\"_blockNumber\",\"type\":\"uint256\"},{\"name\":\"_difficulty\",\"type\":\"uint256\"}],\"name\":\"verifyCPU\",\"outputs\":[{\"name\":\"b\",\"type\":\"bool\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"memoryWorkTimeout\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_memoryWorkTimeout\",\"type\":\"uint256\"}],\"name\":\"updateMemoryWorkTimeout\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"cpuDifficulty\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"owner\",\"outputs\":[{\"name\":\"\",\"type\":\"address\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_difficulty\",\"type\":\"uint256\"}],\"name\":\"updateCPUDifficulty\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"constant\":true,\"inputs\":[],\"name\":\"getAdmissionParameters\",\"outputs\":[{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"},{\"name\":\"\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"view\",\"type\":\"function\"},{\"constant\":false,\"inputs\":[{\"name\":\"_difficulty\",\"type\":\"uint256\"}],\"name\":\"updateMemoryDifficulty\",\"outputs\":[],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[{\"name\":\"_cpuDifficulty\",\"type\":\"uint256\"},{\"name\":\"_memoryDifficulty\",\"type\":\"uint256\"},{\"name\":\"_cpuWorkTimeout\",\"type\":\"uint256\"},{\"name\":\"_memoryWorkTimeout\",\"type\":\"uint256\"}],\"payable\":false,\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"}]",
    "address": "0x8f01875F462CBBc956CB9C0392dE6053A31C9C99"
}
cf = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))
ac = cf.cpc.contract(address=acConfig['address'], abi=acConfig['abi'])

def main(cpuDifficulty,memoryDifficulty):
    cd = int(cpuDifficulty)
    md = int(memoryDifficulty)

    ac.functions.updateCPUDifficulty(cd).transact({
        'gas': 3000000,
        'from': cf.cpc.accounts[0],
    })
    time.sleep(5)

    ac.functions.updateMemoryDifficulty(md).transact({
        'gas': 3000000,
        'from': cf.cpc.accounts[0],
    })
    time.sleep(5)


if __name__ == '__main__':
    if len(sys.argv) == 3:
        try:
            main(sys.argv[1], sys.argv[2])
            os._exit(0)
        except Exception as e:
            print(e)
            os._exit(1)
    else:
        os._exit(1)