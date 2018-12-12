#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..
cpchain=$proj_dir/build/bin/cpchain

for i in {11..12}
do
    echo "[*] Configuring node $i"
    mkdir -p data/data$i/keystore && cp conf/keys/key$i data/data$i/keystore/
done
