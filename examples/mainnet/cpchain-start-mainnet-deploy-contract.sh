#!/usr/bin/env bash

run_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"
proj_dir=$run_dir/../..


contract_admin_ip=""
if [ ! $1 ]; then
    contract_admin_ip='127.0.0.1'
else
    contract_admin_ip=$1
fi

echo "contract_admin_ip:${contract_admin_ip}"

pwd="LNObolATs8tcVp9j"
echo "password:${pwd}"
cd $run_dir
set -u
set -e

echo "=========================================================="
echo "chain node number:"
echo `ps -ef|grep -v grep |grep "cpchain run "|wc -l`
echo "=========================================================="

# deploy smartcontracts
echo  "Deploy smartcontracts start"
sleep 5
smartcontract=$proj_dir/build/bin/smartcontract
$smartcontract http://${contract_admin_ip}:8521 data/data21/keystore/ ${pwd}


echo "Deploy smartcontracts stop"