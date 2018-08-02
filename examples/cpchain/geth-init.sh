#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

echo "[*] Cleaning up temporary data directories"
rm -rf data
mkdir -p data/logs

proj_dir=../..

for i in {1..4}
do
    echo "[*] Configuring node $i"
    rm -rf data/dd$i/geth
    mkdir -p data/dd$i/keystore
    cp keys/key$i data/dd$i/keystore

    # not needed.
    # $proj_dir/build/bin/geth --datadir data/dd$i init conf/genesis.json
done
