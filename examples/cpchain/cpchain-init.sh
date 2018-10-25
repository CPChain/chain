#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

echo "[*] Cleaning up temporary data directories"
rm -rf data
mkdir -p data/logs

proj_dir=../..
cpchain=$proj_dir/build/bin/cpchain

for i in {1..10}
do
    echo "[*] Configuring node $i"
    mkdir -p data/data$i/keystore && cp conf/keys/key$i data/data$i/keystore/

    # no longer needed
    # $cpchain chain init --datadir data/data$i conf/genesis.toml
done
