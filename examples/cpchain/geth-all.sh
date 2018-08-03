#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"


./geth-stop.sh 
./geth-init.sh
./geth-start.sh 
