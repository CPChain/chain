#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"
set -ue

echo "[*] Cleaning up temporary data directories"
rm -rf data
mkdir -p data/logs

# proj_dir=../..
executable=geth

for i in {1..7}
do
    echo "[*] Configuring node $i"
    $executable --datadir data/data$i init conf/genesis.json

    cp keys/key$i data/data$i/keystore/
done
