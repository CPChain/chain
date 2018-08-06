#!/usr/bin/env bash
# create 4 bootnode key
# make sure $proj_dir/build/bin/bootnode exist,otherwise build it with "make all"

cd "$(dirname "${BASH_SOURCE[0]}")"

proj_dir=../../..

for i in {1..4}
do
    echo "[*] Create boot node $i"
    $proj_dir/build/bin/bootnode -genkey boot${i}.key
done