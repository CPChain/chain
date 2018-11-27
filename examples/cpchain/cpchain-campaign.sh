#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

set -u
set -e

# launch campaign for proposer committee
echo "launch committee start"
sleep 5   # sleep 5 seconds to wait cpchain get ready
curl -X POST '0.0.0.0:8501' -H 'content-type: application/json' --data '{"jsonrpc":"2.0","method":"admission_campaign","params":[],"id":64}'
curl -X POST '0.0.0.0:8502' -H 'content-type: application/json' --data '{"jsonrpc":"2.0","method":"admission_campaign","params":[],"id":64}'
curl -X POST '0.0.0.0:8503' -H 'content-type: application/json' --data '{"jsonrpc":"2.0","method":"admission_campaign","params":[],"id":64}'
curl -X POST '0.0.0.0:8504' -H 'content-type: application/json' --data '{"jsonrpc":"2.0","method":"admission_campaign","params":[],"id":64}'
curl -X POST '0.0.0.0:8505' -H 'content-type: application/json' --data '{"jsonrpc":"2.0","method":"admission_campaign","params":[],"id":64}'
curl -X POST '0.0.0.0:8506' -H 'content-type: application/json' --data '{"jsonrpc":"2.0","method":"admission_campaign","params":[],"id":64}'
curl -X POST '0.0.0.0:8507' -H 'content-type: application/json' --data '{"jsonrpc":"2.0","method":"admission_campaign","params":[],"id":64}'
curl -X POST '0.0.0.0:8508' -H 'content-type: application/json' --data '{"jsonrpc":"2.0","method":"admission_campaign","params":[],"id":64}'


# dlv is useful for debugging.  do not remove.
# dlv --headless --listen=:2345 --api-version=2 debug github.com/ethereum/go-ethereum/cmd/cpchain -- $ARGS  --datadir $data_dir/data/dd3 --ipcpath ${ipc_path_base}3 --rpcport 8503 --port 30313 --unlock "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a" --mine --minerthreads 1 --password conf/password


echo "launch committee stop"