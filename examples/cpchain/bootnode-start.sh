#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Starting bootnode"
bootnode=$proj_dir/build/bin/bootnode
boot_key="boot${1}.key"
runmode="${2}"

echo "boot_key:${boot_key},runmode:${runmode}"

$bootnode -nodekey conf-${runmode}/bootnodes/${boot_key} -verbosity 9 -addr :3038${1} -logfile data/logs/bootnode${1}.log