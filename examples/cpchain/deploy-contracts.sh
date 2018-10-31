#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

echo "[*] deploy contracts"
go run launch/deploy/deploy-contracts.go
