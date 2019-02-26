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
         --unlock "0xc5b481361bbcabb96ed0c835cee69b471449f49c" --password conf-mainnet/passwords/password5 \
         --logfile data/logs/5.log 2> data/logs/5.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}6 --datadir data/data6  --rpcaddr 0.0.0.0:8506 --port 30316 --mine \
         --unlock "0x6e7fdba0fe5067a25a3cf1df90429e3c949411e3" --password conf-mainnet/passwords/password6 \
         --logfile data/logs/6.log 2> data/logs/6.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}14 --datadir data/data14 --rpcaddr 0.0.0.0:8514 --port 30324 --mine \
         --unlock "0x27e81a296f5b80d319d2f3008f2d5998530e79e4" --password conf-mainnet/passwords/password14 \
         --logfile data/logs/14.log 2> data/logs/14.err.log &

nohup $cpchain $args --ipcaddr ${ipc_path_base}15 --datadir data/data15 --rpcaddr 0.0.0.0:8515 --port 30325 --mine \
         --unlock "0x52e584b4fba8688eb7edcabb18e65661a99acc67" --password conf-mainnet/passwords/password15 \
         --logfile data/logs/15.log 2> data/logs/15.err.log &

printf "\nAll nodes configured. See 'data/logs' for logs"

