#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting Validators."

cpchain=$proj_dir/build/bin/cpchain
ipc_path_base=data/cpc-

# validator
nohup $cpchain $args --ipcaddr ${ipc_path_base}7 --datadir data/data7  --rpcaddr 0.0.0.0:8507 --port 30317 --validator \
         --unlock "0x422dd016ccad93deb8ffe07416827371c37cbfe6" --password conf-mainnet/passwords/password7 --logfile data/logs/7.log  --nodekey conf-mainnet/validators/node7.key 2> data/logs/7.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}8 --datadir data/data8  --rpcaddr 0.0.0.0:8508 --port 30318 --validator \
         --unlock "0x3119d0a401ba28eb5b8269b03cdf73e1ff8942eb"  --password conf-mainnet/passwords/password8 --logfile data/logs/8.log  --nodekey conf-mainnet/validators/node8.key 2> data/logs/8.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}9 --datadir data/data9  --rpcaddr 0.0.0.0:8509 --port 30319 --validator \
         --unlock "0x7ef70538c237e571ef35cdc600d2d01cdac3af27"  --password conf-mainnet/passwords/password9 --logfile data/logs/9.log  --nodekey conf-mainnet/validators/node9.key 2> data/logs/9.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}10 --datadir data/data10  --rpcaddr 0.0.0.0:8510 --port 30320 --validator \
         --unlock "0x9d6ceb3827e6a276ce655bda7281ccff97364d44"  --password conf-mainnet/passwords/password10 --logfile data/logs/10.log --nodekey conf-mainnet/validators/node10.key 2> data/logs/10.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}11 --datadir data/data11 --rpcaddr 0.0.0.0:8511 --port 30321 --validator \
         --unlock "0x274ce385b87681e44c716001017e3e58c4b6864a" --password conf-mainnet/passwords/password11 \
         --logfile data/logs/11.log  --nodekey conf-mainnet/validators/node11.key 2> data/logs/11.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}12 --datadir data/data12 --rpcaddr 0.0.0.0:8512 --port 30322 --validator \
         --unlock "0xfe1fedc1205a4484d4981b690ab8b7fdabd57890" --password conf-mainnet/passwords/password12 \
         --logfile data/logs/12.log  --nodekey conf-mainnet/validators/node12.key 2> data/logs/12.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}13 --datadir data/data13 --rpcaddr 0.0.0.0:8513 --port 30323 --validator \
         --unlock "0x37163cba895198757c222f1e836d92cc1b39480f" --password conf-mainnet/passwords/password13 \
         --logfile data/logs/13.log --nodekey conf-mainnet/validators/node13.key 2> data/logs/13.err.log &


printf "\nAll nodes configured. See 'data/logs' for logs"
