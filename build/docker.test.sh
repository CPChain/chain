#!/bin/bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

echo "[*] Build cpchain"
cd ..

docker build -f Dockerfile.dev  -t cpchaintest:v1 .
#docker build --no-cache -f Dockerfile.dev  -t cpchaintest:v1 .

cd -


