#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting cpchain viewer nodes"
#set log level by add parameter:--verbosity 4
# or spec env like this:env CPC_VERBOSITY=4  ./cpchain-start.sh
#PanicLevel	0
#FatalLevel	1
#ErrorLevel	2
#WarnLevel	3
#InfoLevel	4
#DebugLevel	5


args="run --networkid 42 --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner --linenumber"

cpchain=$proj_dir/build/bin/cpchain
ipc_path_base=data/

echo "start viewer unlock"
nohup $cpchain $args --ipcaddr ${ipc_path_base}11 --datadir data/data11  --rpcaddr 127.0.0.1:8511 --grpcaddr 127.0.0.1:8611 --jsonrpchttpaddr 127.0.0.1:8711 --port 30321 \
         --unlock "0xbc131722d837b7d867212568baceb3a981181443"  --password conf/password --logfile data/logs/11.log 2>/dev/null &

echo "start viewer no unlock"
nohup $cpchain $args --ipcaddr ${ipc_path_base}12 --datadir data/data12  --rpcaddr 127.0.0.1:8512 --grpcaddr 127.0.0.1:8612 --jsonrpchttpaddr 127.0.0.1:8712 --port 30322 \
    --logfile data/logs/12.log 2>/dev/null &

