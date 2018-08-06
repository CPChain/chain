#!/usr/bin/env bash
# make sure $proj_dir/build/bin/bootnode exist,otherwise build it with "make all"

cd "$(dirname "${BASH_SOURCE[0]}")"

proj_dir=../../..

if [ -d "logs" ];then
    echo "existing logs directory"
else
    echo "create logs directory"
    mkdir logs
fi

bootnode_idx=$1
echo "start bootnode ${bootnode_idx}"

$proj_dir/build/bin/bootnode -nodekey key/boot${bootnode_idx}.key -verbosity 9 -addr :3031${bootnode_idx} 2>logs/bootnode${bootnode_idx}.log &