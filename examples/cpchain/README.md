It contains a simple example of cpchani that starts 4 nodes and issues a transaction from node 1 to
node 2.  node1 and node2 are the initial signers.



# Usage

- `cpchani-init.sh` initializes accounts and keystore.
- `cpchani-start.sh` launches 4 cpchani nodes, and node 1 and 2 are mining. logs of all nodes are printed in `data/logs`.
- `cpchani-stop.sh` stops all cpchani nodes.

# testing simple transaction

`./run-script.sh transactions/simple-transaction.js` issues a transaction from node 1 to node 2.