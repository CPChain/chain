#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

./stop.sh

rm -rf datadir
rm -rf logs
rm nohup.out
