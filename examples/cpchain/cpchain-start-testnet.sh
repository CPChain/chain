#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting cpchain nodes"
#set log level by add parameter:--verbosity 4
# or spec env like this:env CPC_VERBOSITY=4  ./cpchain-start.sh
#PanicLevel	0
#FatalLevel	1
#ErrorLevel	2
#WarnLevel	3
#InfoLevel	4
#DebugLevel	5

bootnodes="enode://ebe4f6b0485f906aecc7fe35234d2d4f11bdb0a4965f5b3214f0301b58b76a3711290cfb1beb44c314e73f18af5d68fd7b34a930117a28aa76ffd92bb55cc13b@127.0.0.1:30310"

validators="enode://5f11492af45df3c06fbdc435e4a66615baa58dc58a4918a3b693bf67c5baad4098ea5e0ca63a26ed55890865b8aa30550727ebff32b6826b72ad5c9dd28b4313@127.0.0.1:30317,\
enode://f22094e4153d73d304d0e362704ecfec5fa928e56b62703b599a66e445c7bfa5b7a525118dc7e41fdf98267e428bda4d98cb3405f50ae509add6fc5aa87c98b9@127.0.0.1:30318,\
enode://13925c2c99a2bc8ebb05d0946ee673d18fb1e2905b3e1e7ea4c840dd6cac5fc769ac54d1c791b158dbba3734494422fb0110aac4384f932d214aba69e0b49518@127.0.0.1:30319,\
enode://d4175e2c796a6591e52e788483261bb54cfc337e0ba881f033cafd12a3ea94d22f3c84fa8652a343b2cb155b6443d3494a9010a1b993e63841374e9311382513@127.0.0.1:30320,"

args="run --networkid 2 --bootnodes ${bootnodes} --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner --linenumber --runmode testnet"

#start bootnode service
nohup ./bootnode-start.sh 3 testnet &


echo "Please check the IPFS daemon running on localhost."

cpchain=$proj_dir/build/bin/cpchain
ipc_path_base=data/cpc-

nohup $cpchain $args --ipcaddr ${ipc_path_base}1 --datadir data/data1  --rpcaddr 0.0.0.0:8501 --grpcaddr 0.0.0.0:8601 --jsonrpchttpaddr 0.0.0.0:8701 --port 30311 --mine \
         --unlock "0x2a15146f434c0205cfae639de2ac4bb543539b24" --password conf-testnet/passwords/password1 \
         --validators "${validators}" \
         --rpccorsdomain "http://orange:8000" --logfile data/logs/1.log 2>/dev/null &

nohup $cpchain $args --ipcaddr ${ipc_path_base}2 --datadir data/data2  --rpcaddr 127.0.0.1:8502 --grpcaddr 127.0.0.1:8602 --jsonrpchttpaddr 127.0.0.1:8702 --port 30312 --mine \
         --unlock "0xb436e2feffa76c30beb9d89e825281baa9956d4c" --password conf-testnet/passwords/password2 \
         --logfile data/logs/2.log 2>/dev/null &

nohup $cpchain $args --ipcaddr ${ipc_path_base}3 --datadir data/data3  --rpcaddr 127.0.0.1:8503 --grpcaddr 127.0.0.1:8603 --jsonrpchttpaddr 127.0.0.1:8703 --port 30313 --mine \
         --unlock "0xf675b1e939892cad974a17da6bcd1cceae3b73dd" --password conf-testnet/passwords/password3 --logfile data/logs/3.log 2>/dev/null &

nohup $cpchain $args --ipcaddr ${ipc_path_base}4 --datadir data/data4  --rpcaddr 127.0.0.1:8504 --grpcaddr 127.0.0.1:8604 --jsonrpchttpaddr 127.0.0.1:8704 --port 30314 --mine \
         --unlock "0xe7a992e4187e95f28f8f69d44487fb16c465071c" --password conf-testnet/passwords/password4 --logfile data/logs/4.log 2>/dev/null &

nohup $cpchain $args --ipcaddr ${ipc_path_base}5 --datadir data/data5  --rpcaddr 127.0.0.1:8505 --grpcaddr 127.0.0.1:8605 --jsonrpchttpaddr 127.0.0.1:8705 --port 30315 --mine \
         --unlock "0x7326d5248928b87f63a80e424a1c6d39cb334624" --password conf-testnet/passwords/password5 --logfile data/logs/5.log 2>/dev/null &

nohup $cpchain $args --ipcaddr ${ipc_path_base}6 --datadir data/data6  --rpcaddr 127.0.0.1:8506 --grpcaddr 127.0.0.1:8606 --jsonrpchttpaddr 127.0.0.1:8706 --port 30316 --mine \
         --unlock "0x2661177788fe63888e93cf18b5e4e31306a01170" --password conf-testnet/passwords/password6 --logfile data/logs/6.log 2>/dev/null &

nohup $cpchain $args --ipcaddr ${ipc_path_base}7 --datadir data/data7  --rpcaddr 127.0.0.1:8507 --grpcaddr 127.0.0.1:8607 --jsonrpchttpaddr 127.0.0.1:8707 --port 30317 --mine \
         --unlock "0x177b2a835f27a8989dfca814b37d08c54e1de889" --password conf-testnet/passwords/password7 --logfile data/logs/7.log  --nodekey conf-testnet/validators/node7.key 2>/dev/null &

nohup $cpchain $args --ipcaddr ${ipc_path_base}8 --datadir data/data8  --rpcaddr 127.0.0.1:8508 --grpcaddr 127.0.0.1:8608 --jsonrpchttpaddr 127.0.0.1:8708 --port 30318 --mine \
         --unlock "0x832062f84f982050c820b5ec986c1825d000ec8e"  --password conf-testnet/passwords/password8 --logfile data/logs/8.log  --nodekey conf-testnet/validators/node8.key 2>/dev/null &

nohup $cpchain $args --ipcaddr ${ipc_path_base}9 --datadir data/data9  --rpcaddr 127.0.0.1:8509 --grpcaddr 127.0.0.1:8609 --jsonrpchttpaddr 127.0.0.1:8709 --port 30319 --mine \
         --unlock "0x2da372d6026573aa5e1863ba3fa724a231c477d6"  --password conf-testnet/passwords/password9 --logfile data/logs/9.log  --nodekey conf-testnet/validators/node9.key 2>/dev/null &

nohup $cpchain $args --ipcaddr ${ipc_path_base}10 --datadir data/data10  --rpcaddr 127.0.0.1:8510 --grpcaddr 127.0.0.1:8610 --jsonrpchttpaddr 127.0.0.1:8710 --port 30320 --mine \
         --unlock "0x08e86c815665de506a210ff4b8e8572b8c201009"  --password conf-testnet/passwords/password10 --logfile data/logs/10.log --nodekey conf-testnet/validators/node10.key 2>/dev/null &


# dlv is useful for debugging.  do not remove.
# dlv --headless --listen=:2345 --api-version=2 debug github.com/ethereum/go-ethereum/cmd/cpchain -- $ARGS  --datadir $data_dir/data/dd3  --rpcport 8503 --port 30313 --unlock "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a" --mine --minerthreads 1 --password conf-testnet/passwords/password


printf "\nAll nodes configured. See 'data/logs' for logs"

echo "To test sending transactions, check out transactions/"
