#!/usr/bin/env bash

cd "$(dirname "${BASH_SOURCE[0]}")"

scriptfile="private-transaction-user-scenario.js"

proj_dir=../../../../

ipc_path_base=/tmp/go-ethereum-ipc

case $1 in
1)
echo "scene 1: Agent P deploys a trading contract CT involving party A and party B on private"
$proj_dir/build/bin/cpchani --exec "Scene = 1;loadScript(\"$scriptfile\")" attach ipc:${ipc_path_base}3
;;
2)
echo "scene 2: Agent P deploys an escrow contract CE on public"
$proj_dir/build/bin/cpchani --exec "Scene = 2;loadScript(\"$scriptfile\")" attach ipc:${ipc_path_base}3
;;
3)
echo "scene 3: Party A sets the item for sale"
$proj_dir/build/bin/cpchani --exec "Scene = 3;loadScript(\"$scriptfile\")" attach ipc:${ipc_path_base}1
;;
4)
echo "scene 4: Party B pays money to the escrow contract CE"
$proj_dir/build/bin/cpchani --exec "Scene = 4;loadScript(\"$scriptfile\")" attach ipc:${ipc_path_base}2
;;
5)
echo "scene 5: Party B then sends contract CT an order"
$proj_dir/build/bin/cpchani --exec "Scene = 5;loadScript(\"$scriptfile\")" attach ipc:${ipc_path_base}2
;;
6)
echo "scene 6: Party A sends the delivery message attached with the symmetric key encrypted by the buyer's public key"
$proj_dir/build/bin/cpchani --exec "Scene = 6;loadScript(\"$scriptfile\")" attach ipc:${ipc_path_base}1
;;
7)
echo "scene 7: Party B receives the delivery and send confirmation message"
$proj_dir/build/bin/cpchani --exec "Scene = 7;loadScript(\"$scriptfile\")" attach ipc:${ipc_path_base}2
;;
8)
echo "scene 8: Agent P notice the confirmation and transfer money to Party A"
$proj_dir/build/bin/cpchani --exec "Scene = 8;loadScript(\"$scriptfile\")" attach ipc:${ipc_path_base}3
;;
9)
echo "scene 9: Other parties could not get any information about the transaction between A and B"
$proj_dir/build/bin/cpchani --exec "Scene = 9;loadScript(\"$scriptfile\")" attach ipc:${ipc_path_base}4
;;
*)
echo "Need argument 1-9"
esac