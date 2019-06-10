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
         --unlock "0xd0d39b67cad41642920fa0db66232709a8ce12c7" --password conf-mainnet/passwords/password16 \
         --logfile data/logs/16.log 2> data/logs/16.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}17 --datadir data/data17 --rpcaddr 0.0.0.0:8517 --port 30327 --mine \
         --unlock "0x15676f1f87d0c64cac3892afc4268490b4bd3243" --password conf-mainnet/passwords/password17 \
         --logfile data/logs/17.log 2> data/logs/17.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}18 --datadir data/data18 --rpcaddr 0.0.0.0:8518 --port 30328 --mine \
         --unlock "0x9e59ef188eb3e40e0540b713310fe4de70252ded" --password conf-mainnet/passwords/password18 \
         --logfile data/logs/18.log 2> data/logs/18.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}19 --datadir data/data19 --rpcaddr 0.0.0.0:8519 --port 30329 --mine \
         --unlock "0x360db7f7b3d6db2a9c97738075dca2c4f668382a" --password conf-mainnet/passwords/password19 \
         --logfile data/logs/19.log 2> data/logs/19.err.log &



printf "\nAll nodes configured. See 'data/logs' for logs"

