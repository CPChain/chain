#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"


./cpchain-stop.sh 
./cpchain-init.sh
./cpchain-start.sh
