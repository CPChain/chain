#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

# https://github.com/ethereum/go-ethereum/issues/16342
ipc_path_base=/tmp/go-ethereum-ipc

echo "[*] Starting Ethereum nodes"
# ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 42 --gasprice 1 "
ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 42 --gasprice 1 "
# ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 42 --gasprice 1 --maxpeers 8"

#start bootnode service
$proj_dir/build/bin/bootnode -nodekey boot.key -verbosity 9 -addr :30310 2>data/logs/bootnode.log &


data_dir=`pwd`

#$proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd1 --ipcpath ${ipc_path_base}1 --rpcport 8501 --port 30311 --unlock "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a" --mine --minerthreads 1 --cpchain --password conf/password 2>data/logs/1.log &
$proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd2 --ipcpath ${ipc_path_base}2 --rpcport 8502 --port 30312 --unlock "0xc05302acebd0730e3a18a058d7d1cb1204c4a092" --mine --minerthreads 1 --cpchain --password conf/password 2>data/logs/2.log &
$proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd3 --ipcpath ${ipc_path_base}3 --rpcport 8503 --port 30313 --unlock "0xef3dd127de235f15ffb4fc0d71469d1339df6465" --mine --minerthreads 1 --cpchain --password conf/password1 2>data/logs/3.log &
$proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd4 --ipcpath ${ipc_path_base}4 --rpcport 8504 --port 30314 --unlock "0x3a18598184ef84198db90c28fdfdfdf56544f747"  --cpchain --password conf/password2 2>data/logs/4.log &


$proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd5 --ipcpath ${ipc_path_base}5 --rpcport 8505 --port 30315 --unlock "0x6e31e5b68a98dcd17264bd1ba547d0b3e874da1e"  --mine --minerthreads 1 --cpchain --password conf/password 2>data/logs/5.log &
# $proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd6 --ipcpath ${ipc_path_base}6 --rpcport 8506 --port 30316 --unlock "0x22a672eab2b1a3ff3ed91563205a56ca5a560e08"  --cpchain --password conf/password 2>data/logs/6.log &
# $proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd7 --ipcpath ${ipc_path_base}7 --rpcport 8507 --port 30317 --unlock "0x7b2f052a372951d02798853e39ee56c895109992"  --cpchain --password conf/password 2>data/logs/7.log &
# $proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd8 --ipcpath ${ipc_path_base}8 --rpcport 8508 --port 30318 --unlock "0x2f0176cc3a8617b6ddea6a501028fa4c6fc25ca1"  --cpchain --password conf/password 2>data/logs/8.log &
# $proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd9 --ipcpath ${ipc_path_base}9 --rpcport 8509 --port 30319 --unlock "0xe4d51117832e84f1d082e9fc12439b771a57e7b2"  --cpchain --password conf/password 2>data/logs/9.log &
# $proj_dir/build/bin/geth $ARGS --datadir $data_dir/data/dd10 --ipcpath ${ipc_path_base}10 --rpcport 8510 --port 30320 --unlock "0x32bd7c33bb5060a85f361caf20c0bda9075c5d51"  --cpchain --password conf/password 2>data/logs/10.log &

# dlv --headless --listen=:2345 --api-version=2 debug github.com/ethereum/go-ethereum/cmd/geth -- $ARGS  --datadir $data_dir/data/dd3 --ipcpath ${ipc_path_base}3 --rpcport 8503 --port 30313 --unlock "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a" --mine --minerthreads 1 --password conf/password 


echo ""
echo "All nodes configured. See 'data/logs' for logs, and run e.g. 'geth attach /path/to/geth.ipc' to attach to the first Geth node."

echo "To test sending a transaction from Node 1 to Node 2, run './run-script.sh transactions/simple-transaction.js'"
