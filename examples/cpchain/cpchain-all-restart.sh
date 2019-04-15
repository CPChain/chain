#!/usr/bin/env bash

run_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"
proj_dir=$run_dir/../../
# mac doesn't have the -f option
# proj_dir="$(readlink -f $proj_dir)"

runmode=""
if [ ! $1 ]; then
    runmode='dev'
else
    runmode=$1
fi

echo "runmode:${runmode}"

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

echo "[*] starting"
eval "$start"

echo "=========================================================="
echo "chain node number:"
echo `ps -ef|grep -v grep |grep "cpchain run "|wc -l`
echo "=========================================================="

