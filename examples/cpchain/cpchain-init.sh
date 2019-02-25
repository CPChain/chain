#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

echo "[*] Cleaning up temporary data directories"
rm -rf data/data*
rm -rf data/logs/*
mkdir -p data/logs

proj_dir=../..
cpchain=$proj_dir/build/bin/cpchain
runmode=$1

echo "== runmode:${runmode}"

nodenumber=10

if [ "mainnet" == ${runmode} -o  "dev" == ${runmode} ]; then
    for i in {1..24}
    do
#   21: contract admin node,22: faucet node
        echo "[*] Configuring node $i"
        mkdir -p data/data$i/keystore && cp conf-${runmode}/keys/key$i data/data$i/keystore/
        if [ -f conf-${runmode}/genesis.toml ]; then
            echo "[*] init chain"
            $cpchain chain init --runmode ${runmode} --datadir data/data$i conf-${runmode}/genesis.toml
        fi
    done
else
    for i in {1..10}
    do
        echo "[*] Configuring node $i"
        mkdir -p data/data$i/keystore && cp conf-${runmode}/keys/key$i data/data$i/keystore/
        if [ -f conf-${runmode}/genesis.toml ]; then
            echo "[*] init chain"
            $cpchain chain init --runmode ${runmode} --datadir data/data$i conf-${runmode}/genesis.toml
        fi
    done
fi
