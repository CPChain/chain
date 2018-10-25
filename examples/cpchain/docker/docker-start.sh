#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

./docker-stop.sh

docker build . -t cpchain_blockchain_explorer:latest
docker run --name cpchain_blockchain_explorer -p 8000:8000 -d cpchain_blockchain_explorer:latest
