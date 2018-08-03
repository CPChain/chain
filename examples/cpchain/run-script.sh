#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

#scriptfile="./transactions/$1"
scriptfile="$1"

proj_dir=../..

ipc_path_base=/tmp/go-ethereum-ipc

$proj_dir/build/bin/geth --exec "loadScript(\"$scriptfile\")" attach ipc:${ipc_path_base}1
