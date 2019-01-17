#!/usr/bin/env python3

import cpc_fusion as cpc
import sys
import time


def get_web3_inst(num):
    port = 8500 + num
    return cpc.Web3(cpc.Web3.HTTPProvider(f"http://127.0.0.1:{port}"))


def start_mining(w3):
    w3.miner.start(1)
    w3.cpc.mining

def stop_mining(w3):
    w3.miner.stop()


def handle(cmd, num=1):
    w3 = get_web3_inst(int(num))

    if cmd == 'start':
        start_mining(w3)
    elif cmd == 'stop':
        stop_mining(w3)


if __name__ == '__main__':
    if len(sys.argv) in (2, 3):
        handle(*sys.argv[1:3])
    else:
        print('''
         Usage: 
         ./miner_console.py <subcommand> [node number]

         Subcommand:
         start - start mining
         stop  - stop mining
         
         Example:
         miner_console.py start 1
         ''')

