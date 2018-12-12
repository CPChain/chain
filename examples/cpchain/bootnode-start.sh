#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting bootnode"
bootnode=$proj_dir/build/bin/bootnode
boot_key="boot.key"
all_params=$@
if [ $all_params ]; then
    idx=${1}

    if [ ${idx} ]; then
        boot_key="boot${idx}.key"
    fi
fi
echo "boot_key:${boot_key}"

$bootnode -nodekey conf/${boot_key} -verbosity 9 -addr :30310 -logfile data/logs/bootnode.log