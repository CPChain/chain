#!/usr/bin/env python
import sys
from cpc_fusion import Web3


def check_block(url, start=0, end=0):
    cf = Web3(Web3.HTTPProvider(url))
    found = 0
    for i in range(int(start), int(end)+1):
        b = cf.cpc.getBlock(i)
        if b is None:
            print("The block #%d does not exist." % i)
        else:
            print(b)
            found += 1

    total = int(end) - int(start) + 1
    print("Scanned %d blocks, found %d blocks, %d blocks do not exist." % (total, found, total - found))


if __name__ == "__main__":
    if len(sys.argv) == 4:
        check_block(*sys.argv[1:4])
    else:
        print('''
        Usage: 
        check_block <rpc url> <start block number> <end block number>
        
        Example:
        check_blocks.py http://localhost:8501 1 100
        ''')
