#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

# deploy smartcontracts
echo  "Deploy smartcontracts start"
echo "password is $1"
sleep 5
smartcontract=$proj_dir/build/bin/smartcontract
$smartcontract http://127.0.0.1:8521 data/data21/keystore/ $1


echo "Deploy smartcontracts stop"