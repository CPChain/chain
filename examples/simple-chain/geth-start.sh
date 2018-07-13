#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..
data_dir=/tmp/simple-chain
rm $data_dir >/dev/null
ln -sfv $(pwd) $data_dir

#https://github.com/ethereum/go-ethereum/issues/16342

echo "[*] Starting Ethereum nodes"
ARGS="--nodiscover --rpc --rpcaddr 127.0.0.1 --rpcapi admin,db,eth,debug,miner,net,shh,txpool,personal,web3"
$proj_dir/build/bin/geth --datadir $data_dir/data/dd1 $ARGS --rpcport 22000 --port 21000 --unlock 0 --password conf/password 2>data/logs/1.log --mine --minerthreads 1&
$proj_dir/build/bin/geth --datadir $data_dir/data/dd2 $ARGS --rpcport 22001 --port 21001 --unlock 0 --password conf/password 2>data/logs/2.log --mine --minerthreads 1&
$proj_dir/build/bin/geth --datadir $data_dir/data/dd3 $ARGS --rpcport 22002 --port 21002 --unlock 0 --password conf/password 2>data/logs/3.log &
#./../../build/bin/geth --datadir data/dd4 $ARGS --rpcport 22003 --port 21003 --unlock 0 --password conf/password 2>>data/logs/4.log &
#./../../build/bin/geth --datadir data/dd5 $ARGS --rpcport 22004 --port 21004 --unlock 0 --password conf/password 2>>data/logs/5.log &
#./../../build/bin/geth --datadir data/dd6 $ARGS --rpcport 22005 --port 21005 --unlock 0 --password conf/password 2>>data/logs/6.log &
#./../../build/bin/geth --datadir data/dd7 $ARGS --rpcport 22006 --port 21006 --unlock 0 --password conf/password 2>>data/logs/7.log &

echo "All nodes configured. See 'data/logs' for logs, and run e.g. 'geth attach data/dd1/geth.ipc' to attach to the first Geth node."
echo "To test sending a transaction from Node 1 to Node 2, run './runscript.sh simple-transaction.js'"