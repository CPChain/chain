#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

# https://github.com/ethereum/go-ethereum/issues/16342
ipc_path_base=/tmp/go-ethereum-ipc

echo "[*] Starting Ethereum nodes"
ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 19527 --gasprice 1 "

#start bootnode service
$proj_dir/build/bin/bootnode -nodekey boot.key -verbosity 9 -addr :30310 2>data/logs/bootnode.log &


data_dir=`pwd`
$proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd3 --rpcport 8503 --port 30313 --unlock "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a" --mine --minerthreads 1 --cpchain --password conf/password 2>data/logs/3.log &
$proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd4 --rpcport 8504 --port 30314 --unlock "0xc05302acebd0730e3a18a058d7d1cb1204c4a092" --mine --minerthreads 1 --cpchain --password conf/password 2>data/logs/4.log &
$proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd5 --rpcport 8505 --port 30315 --unlock "0xef3dd127de235f15ffb4fc0d71469d1339df6465" --mine --minerthreads 1 --cpchain --password conf/password1 2>data/logs/5.log &
$proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd6 --rpcport 8506 --port 30316 --unlock "0x3a18598184ef84198db90c28fdfdfdf56544f747"  --cpchain --password conf/password2 2>data/logs/6.log &

echo ""
echo "All nodes configured. See 'data/logs' for logs, and run e.g. 'geth attach data/dd1/geth.ipc' to attach to the first Geth node."

echo "To test sending a transaction from Node 1 to Node 2, run './runscript.sh simple-transaction.js'"
