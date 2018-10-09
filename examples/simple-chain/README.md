It contains a simple example of cpchain that starts 7 nodes and issues a transaction from node 1 to node 2.

# Usage

- `cpchain-init.sh` initializes accounts and keystore.
- `cpchain-start.sh` launches 7 cpchain nodes, and node 1 and 2 are mining. logs of all nodes are printed in `data/logs`.
- `cpchain-stop.sh` stops all cpchain nodes.

# testing simple transaction

`run-script.sh simple-transaction.js` issues a transaction from node 1 to node 2.