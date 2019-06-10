#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting Proposers."

cpchain=$proj_dir/build/bin/cpchain
ipc_path_base=data/cpc-


# proposer 5-6-14-15
nohup $cpchain $args --ipcaddr ${ipc_path_base}5 --datadir data/data5  --rpcaddr 0.0.0.0:8505 --port 30315 --mine \
         --unlock "0xf7b77be329185194520fc4447ea527217eae3974" --password conf-mainnet/passwords/password5 \
         --logfile data/logs/5.log 2> data/logs/5.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}6 --datadir data/data6  --rpcaddr 0.0.0.0:8506 --port 30316 --mine \
         --unlock "0x352201b0e6b19b6c7e0fda80c0c3d462bcc0b81f" --password conf-mainnet/passwords/password6 \
         --logfile data/logs/6.log 2> data/logs/6.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}14 --datadir data/data14 --rpcaddr 0.0.0.0:8514 --port 30324 --mine \
         --unlock "0xd5a344b55a85b02c285fa4340dff4f54af0cb71f" --password conf-mainnet/passwords/password14 \
         --logfile data/logs/14.log 2> data/logs/14.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}15 --datadir data/data15 --rpcaddr 0.0.0.0:8515 --port 30325 --mine \
         --unlock "0x809471f4794c633dd6c9d4b02c6c2c3fb7bdf01f" --password conf-mainnet/passwords/password15 \
         --logfile data/logs/15.log 2> data/logs/15.err.log &

printf "\nAll nodes configured. See 'data/logs' for logs"

