#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

#set log level by add parameter:--verbosity 4
# or spec env like this:env CPC_VERBOSITY=4  ./cpchain-start-mainnet-test.sh
#PanicLevel	0
#FatalLevel	1
#ErrorLevel	2
#WarnLevel	3
#InfoLevel	4
#DebugLevel	5


set -u
set -e

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

