It contains a simple example of cpchani that starts 7 nodes and issues a transaction from node 1 to node 2.

# Usage

- `cpchani-init.sh` initializes accounts and keystore.
- `cpchani-start.sh` launches 7 cpchani nodes, and node 1 and 2 are mining. logs of all nodes are printed in `data/logs`.
- `cpchani-stop.sh` stops all cpchani nodes.

# testing simple transaction

`run-script.sh simple-transaction.js` issues a transaction from node 1 to node 2.