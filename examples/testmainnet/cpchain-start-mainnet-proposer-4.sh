#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting Proposers."

cpchain=$proj_dir/build/bin/cpchain
ipc_path_base=data/cpc-

# other proposer 23-24
nohup $cpchain $args --ipcaddr ${ipc_path_base}23 --datadir data/data23 --rpcaddr 0.0.0.0:8523 --port 30333 --mine \
         --unlock "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a" --password conf-testmainnet/passwords/password23 \
         --logfile data/logs/23.log 2> data/logs/23.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}24 --datadir data/data24 --rpcaddr 0.0.0.0:8524 --port 30334 --mine \
         --unlock "0xc05302acebd0730e3a18a058d7d1cb1204c4a092" --password conf-testmainnet/passwords/password24 \
         --logfile data/logs/24.log 2> data/logs/24.err.log &


printf "\nAll nodes configured. See 'data/logs' for logs"

