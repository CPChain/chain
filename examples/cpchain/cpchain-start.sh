#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

# https://github.com/ethereum/go-ethereum/issues/16342
ipc_path_base=/tmp/go-ethereum-ipc

echo "[*] Starting Ethereum nodes"
# ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 42 --gasprice 1 "
#ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 42 --gasprice 1  "
ARGS="run --networkid 42  "

# ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 42 --gasprice 1 --verbosity 4 "
# ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 42 --gasprice 1 --verbosity 4 --maxpeers 5"
# ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 42 --gasprice 1 --maxpeers 8"

#start bootnode service
$proj_dir/build/bin/bootnode -nodekey boot.key -addr :30310 2>data/logs/bootnode.log &


data_dir=`pwd`

echo "Please check the IPFS daemon running on localhost."

$proj_dir/build/bin/cpchain $ARGS --datadir $data_dir/data/dd1  --rpcaddr 127.0.0.1:8501 --grpcaddr 127.0.0.1:8601 --gatewayaddr 127.0.0.1:8701 --port 30311 --unlock "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a" --mine  --password conf/password 2>data/logs/1.log &
$proj_dir/build/bin/cpchain $ARGS --datadir $data_dir/data/dd2  --rpcaddr 127.0.0.1:8502 --grpcaddr 127.0.0.1:8602 --gatewayaddr 127.0.0.1:8702 --port 30312 --unlock "0xc05302acebd0730e3a18a058d7d1cb1204c4a092" --mine  --password conf/password 2>data/logs/2.log &
$proj_dir/build/bin/cpchain $ARGS --datadir $data_dir/data/dd3  --rpcaddr 127.0.0.1:8503 --grpcaddr 127.0.0.1:8603 --gatewayaddr 127.0.0.1:8703 --port 30313 --unlock "0xef3dd127de235f15ffb4fc0d71469d1339df6465" --mine  --password conf/password1 2>data/logs/3.log &
$proj_dir/build/bin/cpchain $ARGS --datadir $data_dir/data/dd4  --rpcaddr 127.0.0.1:8504 --grpcaddr 127.0.0.1:8604 --gatewayaddr 127.0.0.1:8704 --port 30314 --unlock "0x3a18598184ef84198db90c28fdfdfdf56544f747" --mine  --password conf/password2 2>data/logs/4.log &


$proj_dir/build/bin/cpchain $ARGS --datadir $data_dir/data/dd5  --rpcaddr 127.0.0.1:8505 --grpcaddr 127.0.0.1:8605 --gatewayaddr 127.0.0.1:8705 --port 30315 --unlock "0x6e31e5b68a98dcd17264bd1ba547d0b3e874da1e"  --mine  --password conf/password 2>data/logs/5.log &
$proj_dir/build/bin/cpchain $ARGS --datadir $data_dir/data/dd6  --rpcaddr 127.0.0.1:8506 --grpcaddr 127.0.0.1:8606 --gatewayaddr 127.0.0.1:8706 --port 30316 --unlock "0x22a672eab2b1a3ff3ed91563205a56ca5a560e08"  --mine  --password conf/password 2>data/logs/6.log &
$proj_dir/build/bin/cpchain $ARGS --datadir $data_dir/data/dd7  --rpcaddr 127.0.0.1:8507 --grpcaddr 127.0.0.1:8607 --gatewayaddr 127.0.0.1:8707 --port 30317 --unlock "0x7b2f052a372951d02798853e39ee56c895109992"  --mine  --password conf/password 2>data/logs/7.log &
$proj_dir/build/bin/cpchain $ARGS --datadir $data_dir/data/dd8  --rpcaddr 127.0.0.1:8508 --grpcaddr 127.0.0.1:8608 --gatewayaddr 127.0.0.1:8708 --port 30318 --unlock "0x2f0176cc3a8617b6ddea6a501028fa4c6fc25ca1"  --mine  --password conf/password 2>data/logs/8.log &
$proj_dir/build/bin/cpchain $ARGS --datadir $data_dir/data/dd9  --rpcaddr 127.0.0.1:8509 --grpcaddr 127.0.0.1:8609 --gatewayaddr 127.0.0.1:8709 --port 30319 --unlock "0xe4d51117832e84f1d082e9fc12439b771a57e7b2"  --mine  --password conf/password 2>data/logs/9.log &
$proj_dir/build/bin/cpchain $ARGS --datadir $data_dir/data/dd10  --rpcaddr 127.0.0.1:8510 --grpcaddr 127.0.0.1:8610 --gatewayaddr 127.0.0.1:8710 --port 30320 --unlock "0x32bd7c33bb5060a85f361caf20c0bda9075c5d51"  --mine  --password conf/password 2>data/logs/10.log &

# dlv --headless --listen=:2345 --api-version=2 debug github.com/ethereum/go-ethereum/cmd/cpchain -- $ARGS  --datadir $data_dir/data/dd3 --ipcpath ${ipc_path_base}3 --rpcport 8503 --port 30313 --unlock "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a" --mine --minerthreads 1 --password conf/password


echo ""
echo "All nodes configured. See 'data/logs' for logs, and run e.g. 'cpchain attach /path/to/cpchain.ipc' to attach to the first cpchain node."

echo "To test sending a transaction from Node 1 to Node 2, run './run-script.sh transactions/simple-transaction.js'"
