#!/usr/bin/env bash

echo "[*] Modify conf.py version"

run_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"



output=$(python3 $run_dir/version_modify.py 2>&1 >/dev/null)
echo "[*] The latest version is $output"
sed -i "s/version[ ]*=.*/version= \'$output\' /g" $run_dir/conf.py


