#!/usr/bin/env bash

echo "[*] Modify conf.py version"

tag=`git describe --tags $(git rev-list --tags --max-count=1)`


