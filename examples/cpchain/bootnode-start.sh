#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting bootnode"
bootnode=$proj_dir/build/bin/bootnode
$bootnode -nodekey conf/boot.key -verbosity 9 -addr :30310
