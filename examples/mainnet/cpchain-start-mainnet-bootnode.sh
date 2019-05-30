#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting cpchain bootnode"

#start bootnode service
nohup ./bootnode-start.sh 1 mainnet &
nohup ./bootnode-start.sh 2 mainnet &
nohup ./bootnode-start.sh 3 mainnet &
nohup ./bootnode-start.sh 4 mainnet &
