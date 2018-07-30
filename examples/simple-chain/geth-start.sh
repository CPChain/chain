#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

# https://github.com/ethereum/go-ethereum/issues/16342
ipc_path_base=/tmp/go-ethereum-ipc

echo "[*] Starting Ethereum nodes"
ARGS="--nodiscover --rpc --rpcaddr 127.0.0.1 --rpcapi admin,db,eth,debug,miner,net,shh,txpool,personal,web3"
$proj_dir/build/bin/geth --datadir data/dd1 $ARGS --ipcpath ${ipc_path_base}1 --rpcport 22000 --port 21000 --unlock 0 --password conf/password 2>data/logs/1.log --mine --minerthreads 1&
$proj_dir/build/bin/geth --datadir data/dd2 $ARGS --ipcpath ${ipc_path_base}2 -rpcport 22001 --port 21001 --unlock 0 --password conf/password 2>data/logs/2.log --mine --minerthreads 1&
$proj_dir/build/bin/geth --datadir data/dd3 $ARGS --ipcpath ${ipc_path_base}3 -rpcport 22002 --port 21002 --unlock 0 --password conf/password 2>data/logs/3.log &

echo "All nodes configured. See 'data/logs' for logs, and run e.g. 'geth attach data/dd1/geth.ipc' to attach to the first Geth node."
echo "To test sending a transaction from Node 1 to Node 2, run './runscript.sh simple-transaction.js'"
