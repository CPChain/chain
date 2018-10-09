#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"


./cpchani-stop.sh 
./cpchani-init.sh
./cpchani-start.sh 
