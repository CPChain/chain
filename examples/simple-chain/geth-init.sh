#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

echo "[*] Cleaning up temporary data directories"
rm -rf data
mkdir -p data/logs

proj_dir=../..

for i in {1..7}
do
    echo "[*] Configuring node $i"
    mkdir -p data/dd$i/{keystore,geth}
    cp conf/nodes.json data/dd$i/static-nodes.json
    cp conf/nodes.json data/dd$i/
    cp keys/key$i data/dd$i/keystore
    cp geth/nodekey$i data/dd$i/geth/nodekey
    $proj_dir/build/bin/geth --datadir data/dd$i init conf/genesis.json
done