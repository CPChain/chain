#!/usr/bin/env bash

run_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"
proj_dir=$run_dir/../../
# mac doesn't have the -f option
# proj_dir="$(readlink -f $proj_dir)"

init=$run_dir/cpchain-init.sh
start=$run_dir/cpchain-start.sh
stop=$run_dir/cpchain-stop.sh
deploy=$run_dir/deploy-contracts.sh

echo $run_dir
echo $proj_dir

cd $run_dir
set -u
set -e

echo "[*] stopping"
echo $($stop)

cd $proj_dir
echo "[*] making"
make all

cd $run_dir

echo "[*] initing"
eval $init

eval $run_dir/cpchain-init-viewer.sh

echo "[*] starting"
eval "env CPC_VERBOSITY=5 $start"

$run_dir/cpchain-start-viewer.sh

sleep 1

echo "[*] deploying"
# smart contract deploy
eval "env CPCHAIN_KEYSTORE_FILEPATH=data/data1/keystore/ $deploy"
