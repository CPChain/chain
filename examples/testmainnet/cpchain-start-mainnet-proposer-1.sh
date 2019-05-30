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
         --unlock "0x9e61732d0b1c1674151a01ac0bba824c5b6258fb" --password conf-testmainnet/passwords/password1 \
         --logfile data/logs/1.log 2> data/logs/1.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}2 --datadir data/data2  --rpcaddr 0.0.0.0:8502 --port 30312 --mine \
         --unlock "0xaa6cf4f0338e04a40709dfa3c653efc6cd9e65c9" --password conf-testmainnet/passwords/password2 \
         --logfile data/logs/2.log 2> data/logs/2.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}3 --datadir data/data3  --rpcaddr 0.0.0.0:8503 --port 30313 --mine \
         --unlock "0x7170f578ca82897375f009ddea399df08f31bcff" --password conf-testmainnet/passwords/password3 \
         --logfile data/logs/3.log 2> data/logs/3.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}4 --datadir data/data4  --rpcaddr 0.0.0.0:8504 --port 30314 --mine \
         --unlock "0x4c61559aa727380e3fa516b6a7ae397b87ec2384" --password conf-testmainnet/passwords/password4 \
         --logfile data/logs/4.log 2> data/logs/4.err.log &


printf "\nAll nodes configured. See 'data/logs' for logs"

