#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

cpchain=../../build/bin/cpchain
runmode=mini

datadir=datadir

mkdir -p $datadir/v1/keystore
mkdir -p $datadir/v2/keystore
mkdir -p $datadir/v3/keystore
mkdir -p $datadir/v4/keystore

mkdir -p $datadir/p1/keystore
mkdir -p logs

cp ../cpchain/conf-dev/keys/key7 $datadir/v1/keystore
cp ../cpchain/conf-dev/validators/node7.key $datadir/v1/node.key

cp ../cpchain/conf-dev/keys/key8 $datadir/v2/keystore
cp ../cpchain/conf-dev/validators/node8.key $datadir/v2/node.key

cp ../cpchain/conf-dev/keys/key9 $datadir/v3/keystore
cp ../cpchain/conf-dev/validators/node9.key $datadir/v3/node.key

cp ../cpchain/conf-dev/keys/key10 $datadir/v4/keystore
cp ../cpchain/conf-dev/validators/node10.key $datadir/v4/node.key

cp ../cpchain/conf-dev/passwords/password $datadir/v1/password
cp ../cpchain/conf-dev/passwords/password $datadir/v2/password
cp ../cpchain/conf-dev/passwords/password $datadir/v3/password
cp ../cpchain/conf-dev/passwords/password $datadir/v4/password

cp ../cpchain/conf-dev/keys/key1 $datadir/p1/keystore

cp ../cpchain/conf-dev/passwords/password $datadir/p1/password

# start validator
nohup $cpchain run --verbosity 4 --runmode $runmode --datadir $datadir/v1 --nodekey $datadir/v1/node.key --validator --port 30317 --password $datadir/v1/password --unlock 0x7b2f052a372951d02798853e39ee56c895109992 2> logs/v1.log &
sleep 1
nohup $cpchain run --verbosity 4 --runmode $runmode --datadir $datadir/v2 --nodekey $datadir/v2/node.key --validator --port 30318 --password $datadir/v2/password --unlock 0x2f0176cc3a8617b6ddea6a501028fa4c6fc25ca1 2> logs/v2.log &
sleep 1
nohup $cpchain run --verbosity 4 --runmode $runmode --datadir $datadir/v3 --nodekey $datadir/v3/node.key --validator --port 30319 --password $datadir/v3/password --unlock 0xe4d51117832e84f1d082e9fc12439b771a57e7b2 2> logs/v3.log &
sleep 1
nohup $cpchain run --verbosity 4 --runmode $runmode --datadir $datadir/v4 --nodekey $datadir/v4/node.key --validator --port 30320 --password $datadir/v4/password --unlock 0x32bd7c33bb5060a85f361caf20c0bda9075c5d51 2> logs/v4.log &

sleep 3

# start proposer
nohup $cpchain run --verbosity 4 --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner,admin --rpcaddr 0.0.0.0:8501 --runmode $runmode --datadir $datadir/p1 --mine --port 30310 --password $datadir/p1/password --unlock 0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a 2> logs/p1.log &
