#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting cpchain nodes"
# ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 42 --gasprice 1 "
# ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 42 --gasprice 1  "
# ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 42 --gasprice 1 --verbosity 4 "
# ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 42 --gasprice 1 --verbosity 4 --maxpeers 5"
# ARGS=" --syncmode full --rpc --rpcaddr 127.0.0.1 --rpcapi personal,db,eth,net,web3,txpool,miner --networkid 42 --gasprice 1 --maxpeers 8"

#set log level by add parameter:--verbosity 4
# or spec env like this:env CPC_VERBOSITY=4  ./cpchain-start.sh
#PanicLevel	0
#FatalLevel	1
#ErrorLevel	2
#WarnLevel	3
#InfoLevel	4
#DebugLevel	5


args="run --networkid 42  --rpcapi personal,eth,cpc,net,web3,db,txpool,miner --linenumber"

#start bootnode service
./bootnode-start.sh 2>data/logs/bootnode.log &


echo "Please check the IPFS daemon running on localhost."

cpchain=$proj_dir/build/bin/cpchain

$cpchain $args --datadir data/data1  --rpcaddr 0.0.0.0:8501 --grpcaddr 0.0.0.0:8601 --jsonrpchttpaddr 0.0.0.0:8701 --port 30311 --mine \
         --unlock "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a" --password conf/password --rpccorsdomain "http://orange:8000" 2>data/logs/1.log &

$cpchain $args --datadir data/data2  --rpcaddr 127.0.0.1:8502 --grpcaddr 127.0.0.1:8602 --jsonrpchttpaddr 127.0.0.1:8702 --port 30312 --mine \
         --unlock "0xc05302acebd0730e3a18a058d7d1cb1204c4a092" --password conf/password 2>data/logs/2.log &

$cpchain $args --datadir data/data3  --rpcaddr 127.0.0.1:8503 --grpcaddr 127.0.0.1:8603 --jsonrpchttpaddr 127.0.0.1:8703 --port 30313 --mine \
         --unlock "0xef3dd127de235f15ffb4fc0d71469d1339df6465" --password conf/password1 2>data/logs/3.log &

$cpchain $args --datadir data/data4  --rpcaddr 127.0.0.1:8504 --grpcaddr 127.0.0.1:8604 --jsonrpchttpaddr 127.0.0.1:8704 --port 30314 --mine \
         --unlock "0x3a18598184ef84198db90c28fdfdfdf56544f747" --password conf/password2 2>data/logs/4.log &

$cpchain $args --datadir data/data5  --rpcaddr 127.0.0.1:8505 --grpcaddr 127.0.0.1:8605 --jsonrpchttpaddr 127.0.0.1:8705 --port 30315 --mine \
         --unlock "0x6e31e5b68a98dcd17264bd1ba547d0b3e874da1e" --password conf/password 2>data/logs/5.log &

$cpchain $args --datadir data/data6  --rpcaddr 127.0.0.1:8506 --grpcaddr 127.0.0.1:8606 --jsonrpchttpaddr 127.0.0.1:8706 --port 30316 --mine \
         --unlock "0x22a672eab2b1a3ff3ed91563205a56ca5a560e08" --password conf/password 2>data/logs/6.log &

$cpchain $args --datadir data/data7  --rpcaddr 127.0.0.1:8507 --grpcaddr 127.0.0.1:8607 --jsonrpchttpaddr 127.0.0.1:8707 --port 30317 --mine \
         --unlock "0x7b2f052a372951d02798853e39ee56c895109992" --password conf/password 2>data/logs/7.log &

$cpchain $args --datadir data/data8  --rpcaddr 127.0.0.1:8508 --grpcaddr 127.0.0.1:8608 --jsonrpchttpaddr 127.0.0.1:8708 --port 30318 --mine \
         --unlock "0x2f0176cc3a8617b6ddea6a501028fa4c6fc25ca1"  --password conf/password 2>data/logs/8.log &

$cpchain $args --datadir data/data9  --rpcaddr 127.0.0.1:8509 --grpcaddr 127.0.0.1:8609 --jsonrpchttpaddr 127.0.0.1:8709 --port 30319 --mine \
         --unlock "0xe4d51117832e84f1d082e9fc12439b771a57e7b2"  --password conf/password 2>data/logs/9.log &

$cpchain $args --datadir data/data10  --rpcaddr 127.0.0.1:8510 --grpcaddr 127.0.0.1:8610 --jsonrpchttpaddr 127.0.0.1:8710 --port 30320 --mine \
         --unlock "0x32bd7c33bb5060a85f361caf20c0bda9075c5d51"  --password conf/password 2>data/logs/10.log &


# dlv is useful for debugging.  do not remove.
# dlv --headless --listen=:2345 --api-version=2 debug github.com/ethereum/go-ethereum/cmd/cpchain -- $ARGS  --datadir $data_dir/data/dd3 --ipcpath ${ipc_path_base}3 --rpcport 8503 --port 30313 --unlock "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a" --mine --minerthreads 1 --password conf/password


printf "\nAll nodes configured. See 'data/logs' for logs"

echo "To test sending transactions, check out transactions/"
