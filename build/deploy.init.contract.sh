#!/usr/bin/env bash

now=`date '+%Y-%m-%d %H:%M:%S'`
echo ""
echo ""
echo "start deploy ini contract"
echo "deploy time:$now"

cd ..
cur_dir=$(cd "$(dirname "$0")";pwd)
#echo ${cur_dir}

cd ../../../../
shell_dir=$(cd "$(dirname "$0")";pwd)
#echo "shell_dir:${shell_dir}"
export GOPATH=${shell_dir}


cd ${cur_dir}

echo "" >> /tmp/init_contract.log
echo "" >> /tmp/init_contract.log
echo "Current time : $now" >> /tmp/init_contract.log
go run ${GOPATH}/src/github.com/ethereum/go-ethereum/cmd/smartcontract/main.go >> /tmp/init_contract.log