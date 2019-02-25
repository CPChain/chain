#!/usr/bin/env bash

run_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"
proj_dir=$run_dir/../../
# mac doesn't have the -f option
# proj_dir="$(readlink -f $proj_dir)"

runmode=""
pwd=""
if [ ! $1 ]; then
    runmode='dev'
else
    runmode=$1
fi
if [ ! $2 ]; then
    pwd='password'
else
    pwd=$2
fi

echo "runmode:${runmode}"
echo "password:${pwd}"

init="$run_dir/cpchain-init.sh ${runmode}"
echo "init: ${init}"
start="$run_dir/cpchain-start-${runmode}.sh"
stop="$run_dir/cpchain-stop.sh"
deploy="$run_dir/deploy-contracts.sh ${pwd}"

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
eval $init $runmode

echo "[*] starting"
eval "env CPC_VERBOSITY=5 $start"

#if [ "dev" == ${runmode} ]; then
#    echo "[*] start civilians"
#    $run_dir/cpchain-start-dev-viewer.sh
#fi

echo "=========================================================="
echo "chain node number:"
echo `ps -ef|grep -v grep |grep "cpchain run "|wc -l`
echo "=========================================================="

echo "[*] deploying ${deploy}"
# smart contract deploy
eval "env CPCHAIN_KEYSTORE_FILEPATH=data/data21/keystore/ ${deploy}"


