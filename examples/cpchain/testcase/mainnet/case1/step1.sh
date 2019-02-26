#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

curr_dir=`pwd`
echo "curr_dir:${curr_dir}"

cd ../../../

validator_ip=""
if [ $# == 0 ]; then
    validator_ip='127.0.0.1'
else
    validator_ip="$1"
fi

source ./cpchain-start-mainnet-config.sh ${validator_ip}

./cpchain-start-mainnet-init.sh

./cpchain-start-mainnet-bootnode.sh

./cpchain-start-mainnet-validator.sh

./cpchain-start-mainnet-proposer-1.sh

./cpchain-start-mainnet-contract-admin.sh

./cpchain-start-mainnet-deploy-contract.sh ${validator_ip}

echo "back to dir"
cd  ${curr_dir}