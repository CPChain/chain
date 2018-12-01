#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

proj_dir=../..

# deploy smartcontracts
echo  "Deploy smartcontracts start"
sleep 5
smartcontract=$proj_dir/build/bin/smartcontract
$smartcontract http://localhost:8501 data/data1/keystore/


echo "Deploy smartcontracts stop"