#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

scriptfile="./transactions/$1"

proj_dir=../..

$proj_dir/build/bin/geth --exec "loadScript(\"$scriptfile\")" attach ipc:data/dd1/geth.ipc
