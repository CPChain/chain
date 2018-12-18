#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..
cpchain=$proj_dir/build/bin/cpchain
runmode=$1

for i in {11..12}
do
    echo "[*] Configuring node $i"
    mkdir -p data/data$i/keystore && cp conf-${runmode}/keys/key$i data/data$i/keystore/

#    $cpchain chain init --datadir data/data$i conf-dev/genesis.toml
done
