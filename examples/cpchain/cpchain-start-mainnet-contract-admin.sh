#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting contract admin."

cpchain=$proj_dir/build/bin/cpchain
ipc_path_base=data/cpc-

# contract admin
nohup $cpchain $args --ipcaddr ${ipc_path_base}21 --datadir data/data21 --rpcaddr 0.0.0.0:8521 --port 30331 \
         --unlock "0xb3801b8743dea10c30b0c21cae8b1923d9625f84" --password conf-mainnet/passwords/password21 \
         --logfile data/logs/21.log 2> data/logs/21.err.log &

printf "\nAll nodes configured. See 'data/logs' for logs"