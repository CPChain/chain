#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

pkill dlv 
pkill dlv-cpchain
pkill bootnode
pkill cpchain

