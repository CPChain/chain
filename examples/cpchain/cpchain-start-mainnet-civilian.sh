#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting civilian node."

cpchain=$proj_dir/build/bin/cpchain
ipc_path_base=data/cpc-

# civilian
nohup $cpchain $args --ipcaddr ${ipc_path_base}20 --datadir data/data20 --rpcaddr 0.0.0.0:8520 --port 30330 \
         --logfile data/logs/20.log 2> data/logs/20.err.log &

printf "\nAll nodes configured. See 'data/logs' for logs"
