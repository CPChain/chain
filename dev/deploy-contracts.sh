#!/usr/bin/env bash

now=`date '+%Y-%m-%d %H:%M:%S'`
echo ""
echo ""
echo "start deploy ini contract"
echo "deploy time:$now"

cd ..
cur_dir=$(cd "$(dirname "$0")";pwd)
echo "current dir:${cur_dir}"

cd build/_workspace

pwd

shell_dir=$(cd "$(dirname "$0")";pwd)
echo "shell_dir:${shell_dir}"

export GOPATH=${shell_dir}
echo "GOPATH:${GOPATH}"



echo "Current time : $now"
go run ${GOPATH}/src/bitbucket.org/cpchain/chain/tools/smartcontract/main.go