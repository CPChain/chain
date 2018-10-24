#!/usr/bin/env bash

docker container stop cpchain_blockchain_explorer
docker container rm cpchain_blockchain_explorer

docker build . -t cpchain_blockchain_explorer:latest
docker run --name cpchain_blockchain_explorer -p 8000:8000 -d cpchain_blockchain_explorer:latest

