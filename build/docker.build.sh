#!/bin/bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

echo "[*] Build cpchain"
cd ..
docker build -t cpchain:v1 .
#docker build --no-cache -t cpchain:v1 .
#docker run --rm cpchain:v1
cd -
