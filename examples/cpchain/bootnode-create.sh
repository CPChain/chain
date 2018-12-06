#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

echo "[*] Create bootnode"
bootnode=$proj_dir/build/bin/bootnode
$bootnode -genkey boot1.key
$bootnode -genkey boot2.key
$bootnode -genkey boot3.key
$bootnode -genkey boot4.key
