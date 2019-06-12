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

validators="enode://9826a2f72c63eaca9b7f57b169473686f5a133dc24ffac858b4e5185a5eb60b144a414c35359585d9ea9d67f6fcca29578f9e002c89e94cc4bcc46a2b336c166@127.0.0.1:30317,\
enode://7ce9c4fee12b12affbbe769a0faaa6e256bbae3374717fb94e1fb4be308fae3795c3abae023a587d8e14b35d278bd3d10916117bb8b3f5cfa4c951c5d56eeed7@127.0.0.1:30318,\
enode://1db32421dc881357c282091960fdbd13f3635f8e3f87a953b6d9c429e53469727018bd0bb02da48acc4f1b4bec946b8f158705262b37163b4ab321a1c932d8f9@127.0.0.1:30319,\
enode://fd0f365cec4e052040151f2a4a9ba23e8592acd3cacfdc4af2e8b6dbc6fb6b25ca088151889b19729d02c48e390de9682b316db2351636fdd1ee5ea1cd32bf46@127.0.0.1:30320"

# http://192.168.50.251:9091 is prometheus gateway address
# --metricgateway http://192.168.50.251:9091
#args="run --networkid 1 --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner,admin --linenumber --metricgateway http://192.168.50.251:9091"
args="run --networkid 1 --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner,admin --linenumber  --runmode dev "

#start bootnode service
nohup ./bootnode-start.sh 1 dev &


echo "Please check the IPFS daemon running on localhost."

cpchain=$proj_dir/build/bin/cpchain
ipc_path_base=data/cpc-


nohup $cpchain $args  --ipcaddr ${ipc_path_base}1 --datadir data/data1  --rpcaddr   0.0.0.0:8501 --port 30311 --mine \
         --unlock "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a" --password conf-dev/passwords/password \
         --validators "${validators}" \
         --profile data/data1 \
         --profileaddr "0.0.0.0:8931" \
         --rpccorsdomain "http://orange:8000" --logfile data/logs/1.log 2> data/logs/1.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}2 --datadir data/data2  --rpcaddr 0.0.0.0:8502 --port 30312 --mine \
         --unlock "0xc05302acebd0730e3a18a058d7d1cb1204c4a092" --password conf-dev/passwords/password \
         --runmode dev \
         --profile data/data2 \
         --profileaddr "0.0.0.0:8932" \
         --logfile data/logs/2.log 2> data/logs/2.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}3 --datadir data/data3  --rpcaddr 0.0.0.0:8503 --port 30313 --mine \
         --profile data/data3 \
         --profileaddr "0.0.0.0:8933" \
         --unlock "0xef3dd127de235f15ffb4fc0d71469d1339df6465" --password conf-dev/passwords/password1 --logfile data/logs/3.log 2> data/logs/3.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}4 --datadir data/data4  --rpcaddr 0.0.0.0:8504 --port 30314 --mine \
         --profile data/data4 \
         --profileaddr "0.0.0.0:8934" \
         --unlock "0x3a18598184ef84198db90c28fdfdfdf56544f747" --password conf-dev/passwords/password2 --logfile data/logs/4.log 2> data/logs/4.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}5 --datadir data/data5  --rpcaddr 0.0.0.0:8505 --port 30315 --mine \
         --profile data/data5 \
         --profileaddr "0.0.0.0:8935" \
         --unlock "0x6e31e5b68a98dcd17264bd1ba547d0b3e874da1e" --password conf-dev/passwords/password --logfile data/logs/5.log 2> data/logs/5.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}6 --datadir data/data6  --rpcaddr 0.0.0.0:8506 --port 30316 --mine \
         --profile data/data6 \
         --profileaddr "0.0.0.0:8936" \
         --unlock "0x22a672eab2b1a3ff3ed91563205a56ca5a560e08" --password conf-dev/passwords/password --logfile data/logs/6.log 2> data/logs/6.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}7 --datadir data/data7  --rpcaddr 0.0.0.0:8507 --port 30317 \
         --profile data/data7 \
         --profileaddr "0.0.0.0:8937" \
         --validator \
         --unlock "0x7b2f052a372951d02798853e39ee56c895109992" --password conf-dev/passwords/password --logfile data/logs/7.log  --nodekey conf-dev/validators/node7.key 2> data/logs/7.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}8 --datadir data/data8  --rpcaddr 0.0.0.0:8508 --port 30318 \
         --profile data/data8 \
         --profileaddr "0.0.0.0:8938" \
         --validator \
         --unlock "0x2f0176cc3a8617b6ddea6a501028fa4c6fc25ca1"  --password conf-dev/passwords/password --logfile data/logs/8.log  --nodekey conf-dev/validators/node8.key 2> data/logs/8.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}9 --datadir data/data9  --rpcaddr 0.0.0.0:8509 --port 30319 \
         --profile data/data9 \
         --profileaddr "0.0.0.0:8939" \
         --validator \
         --unlock "0xe4d51117832e84f1d082e9fc12439b771a57e7b2"  --password conf-dev/passwords/password --logfile data/logs/9.log  --nodekey conf-dev/validators/node9.key 2> data/logs/9.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}10 --datadir data/data10  --rpcaddr 0.0.0.0:8510 --port 30320 \
         --profile data/data10 \
         --profileaddr "0.0.0.0:8940" \
         --validator \
         --unlock "0x32bd7c33bb5060a85f361caf20c0bda9075c5d51"  --password conf-dev/passwords/password --logfile data/logs/10.log --nodekey conf-dev/validators/node10.key 2> data/logs/10.err.log &

echo "start contract admin node"
nohup $cpchain $args --ipcaddr ${ipc_path_base}21 --datadir data/data21 --rpcaddr 0.0.0.0:8521 --port 30331 \
         --unlock "0xb3801b8743dea10c30b0c21cae8b1923d9625f84"  --password conf-dev/passwords/password \
         --profile data/data21 \
         --profileaddr "0.0.0.0:8951" \
         --logfile data/logs/21.log 2>/dev/null &

# dlv is useful for debugging.  do not remove.
# dlv --headless --listen=:2345 --api-version=2 debug github.com/ethereum/go-ethereum/cmd/cpchain -- $ARGS  --datadir $data_dir/data/dd3  --rpcport 8503 --port 30313 --unlock "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a" --mine --minerthreads 1 --password conf-dev/passwords/password


printf "\nAll nodes configured. See 'data/logs' for logs"

echo "To test sending transactions, check out transactions/"
