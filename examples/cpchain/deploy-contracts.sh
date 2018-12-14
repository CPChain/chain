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
$smartcontract http://localhost:8501 data/data1/keystore/ $1


echo "Deploy smartcontracts stop"