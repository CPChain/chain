It contains a simple example of geth that starts 4 nodes and issues a transaction from node 1 to
node 2.  node1 and node2 are the initial signers.



# Usage

- `geth-init.sh` initializes accounts and keystore.
- `geth-start.sh` launches 4 geth nodes, and node 1 and 2 are mining. logs of all nodes are printed in `data/logs`.
- `geth-stop.sh` stops all geth nodes.

# testing simple transaction

`./run-script.sh transactions/simple-transaction.js` issues a transaction from node 1 to node 2.