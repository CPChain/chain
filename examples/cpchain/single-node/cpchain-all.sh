#!/usr/bin/env bash

run_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"
proj_dir=$run_dir/../../../

runmode=""
if [ ! $1 ]; then
    runmode='dev'
else
    runmode=$1
fi

echo "runmode:${runmode}"

init="$run_dir/cpchain-init.sh ${runmode}"
echo "init: ${init}"
start="$run_dir/cpchain-start-${runmode}.sh"
stop="$run_dir/cpchain-stop.sh"

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
