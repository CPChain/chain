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
         --unlock "0x0b2ee61452cc951565ed4b8eabff85c3f585c149" --password conf-mainnet/passwords/password7 --logfile data/logs/7.log  --nodekey conf-mainnet/validators/node7.key 2> data/logs/7.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}8 --datadir data/data8  --rpcaddr 0.0.0.0:8508 --port 30318 --validator \
         --unlock "0x6a3678cac50b9266f82abe1a12bd26edc8e743a3"  --password conf-mainnet/passwords/password8 --logfile data/logs/8.log  --nodekey conf-mainnet/validators/node8.key 2> data/logs/8.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}9 --datadir data/data9  --rpcaddr 0.0.0.0:8509 --port 30319 --validator \
         --unlock "0xc6bfd405a99a39fa06f3cf0f568c3a2a40c29882"  --password conf-mainnet/passwords/password9 --logfile data/logs/9.log  --nodekey conf-mainnet/validators/node9.key 2> data/logs/9.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}10 --datadir data/data10  --rpcaddr 0.0.0.0:8510 --port 30320 --validator \
         --unlock "0xaee4ecd7edd59f5a2a0fe1fc786d217bea6ac3d9"  --password conf-mainnet/passwords/password10 --logfile data/logs/10.log --nodekey conf-mainnet/validators/node10.key 2> data/logs/10.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}11 --datadir data/data11 --rpcaddr 0.0.0.0:8511 --port 30321 --validator \
         --unlock "0xd7be125f3c60105b44e3242f5c5509d6c993ebb8" --password conf-mainnet/passwords/password11 \
         --logfile data/logs/11.log  --nodekey conf-mainnet/validators/node11.key 2> data/logs/11.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}12 --datadir data/data12 --rpcaddr 0.0.0.0:8512 --port 30322 --validator \
         --unlock "0x30a36525ca46504939e944e89422bdac745dd050" --password conf-mainnet/passwords/password12 \
         --logfile data/logs/12.log  --nodekey conf-mainnet/validators/node12.key 2> data/logs/12.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}13 --datadir data/data13 --rpcaddr 0.0.0.0:8513 --port 30323 --validator \
         --unlock "0x8341844d109c938f70d1ff4e621bc8da097b8d83" --password conf-mainnet/passwords/password13 \
         --logfile data/logs/13.log --nodekey conf-mainnet/validators/node13.key 2> data/logs/13.err.log &


printf "\nAll nodes configured. See 'data/logs' for logs"
