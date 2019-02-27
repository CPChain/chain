#!/usr/bin/env bash

set -u
set -e

cd "$(dirname "${BASH_SOURCE[0]}")"
curr_dir=`pwd`
echo "curr_dir:${curr_dir}"

cd ../../../
pwd


validator_ip=""
if [ $# == 0 ]; then
    validator_ip='127.0.0.1'
else
    validator_ip="$1"
fi

source ./cpchain-start-mainnet-config.sh ${validator_ip}

./cpchain-start-mainnet-init.sh

./cpchain-start-mainnet-proposer-2.sh

./cpchain-start-mainnet-proposer-3.sh

./cpchain-start-mainnet-proposer-4.sh

./cpchain-start-mainnet-bank.sh

./cpchain-start-mainnet-civilian.sh

echo "back to dir"
cd  ${curr_dir}