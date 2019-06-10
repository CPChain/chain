#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting Proposers."

cpchain=$proj_dir/build/bin/cpchain
ipc_path_base=data/cpc-


# proposer 1-4
nohup $cpchain $args  --ipcaddr ${ipc_path_base}1 --datadir data/data1  --rpcaddr 0.0.0.0:8501 --port 30311 --mine \
         --unlock "0x5f1fa0804bf76f71d5cfb621fac1f6fe27c8e80e" --password conf-mainnet/passwords/password1 \
         --logfile data/logs/1.log 2> data/logs/1.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}2 --datadir data/data2  --rpcaddr 0.0.0.0:8502 --port 30312 --mine \
         --unlock "0xb5edbc5a1e680e660dc78659613df7704bc198d2" --password conf-mainnet/passwords/password2 \
         --logfile data/logs/2.log 2> data/logs/2.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}3 --datadir data/data3  --rpcaddr 0.0.0.0:8503 --port 30313 --mine \
         --unlock "0x3868a7b3c55ac0d4f85fc869a2a444ae0f39a1e7" --password conf-mainnet/passwords/password3 \
         --logfile data/logs/3.log 2> data/logs/3.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}4 --datadir data/data4  --rpcaddr 0.0.0.0:8504 --port 30314 --mine \
         --unlock "0x9ffa9e60feaab7acdb460c4b938d5d57b19b2e10" --password conf-mainnet/passwords/password4 \
         --logfile data/logs/4.log 2> data/logs/4.err.log &


printf "\nAll nodes configured. See 'data/logs' for logs"

