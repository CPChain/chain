#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

docker container stop cpchain_blockchain_explorer
docker container rm cpchain_blockchain_explorer
