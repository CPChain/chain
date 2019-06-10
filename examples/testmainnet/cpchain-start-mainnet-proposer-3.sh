#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting Proposers."

cpchain=$proj_dir/build/bin/cpchain
ipc_path_base=data/cpc-


# proposer 16-19
nohup $cpchain $args --ipcaddr ${ipc_path_base}16 --datadir data/data16 --rpcaddr 0.0.0.0:8516 --port 30326 --mine \
         --unlock "0x030352bba36c0c7cec8669f64a26d96d5d679bdb" --password conf-testmainnet/passwords/password16 \
         --logfile data/logs/16.log 2> data/logs/16.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}17 --datadir data/data17 --rpcaddr 0.0.0.0:8517 --port 30327 --mine \
         --unlock "0xf561ebb8a40814c1cf3cc0a628df5a1bd7663b26" --password conf-testmainnet/passwords/password17 \
         --logfile data/logs/17.log 2> data/logs/17.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}18 --datadir data/data18 --rpcaddr 0.0.0.0:8518 --port 30328 --mine \
         --unlock "0xca8e011de0edea4929328bb86e35daa686c47ed0" --password conf-testmainnet/passwords/password18 \
         --logfile data/logs/18.log 2> data/logs/18.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}19 --datadir data/data19 --rpcaddr 0.0.0.0:8519 --port 30329 --mine \
         --unlock "0xcc9cd266776b331fd424ea14dc30fc8561bec628" --password conf-testmainnet/passwords/password19 \
         --logfile data/logs/19.log 2> data/logs/19.err.log &



printf "\nAll nodes configured. See 'data/logs' for logs"

