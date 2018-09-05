#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting bootnode"

#start bootnode service
$proj_dir/build/bin/bootnode -nodekey boot.key -verbosity 9 -addr :30310 2>data/logs/bootnode.log &
