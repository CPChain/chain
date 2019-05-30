#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting cpchain bootnode"

#start bootnode service
nohup ./bootnode-start.sh 1 testmainnet &
nohup ./bootnode-start.sh 2 testmainnet &
nohup ./bootnode-start.sh 3 testmainnet &
nohup ./bootnode-start.sh 4 testmainnet &
