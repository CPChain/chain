Quick Start
~~~~~~~~~~~~~

We are going to install CPChain and run a node on the testnet. 

Building the Source
####################

First, make sure you have installed `go <https://golang.org/>`_, and configured the $GOPATH.

.. code::

    $ git clone https://github.com/CPChain/chain

    $ cd chain
    $ make clean
    $ make all

Running CPChain
#################

Connect to Alpha Mainnet
^^^^^^^^^^^^^^^^^^^^^^^

.. code::

    $ cd build/bin
    $ ./cpchain run --runmode testnet

**WARNING:** The current master version is not compatible with Alpha Mainnet.
Interested users can refer to commit 7d29a2b to sync with Alpha Mainnet.
After cloning from github repository, you can checkout the commit 7d29a2b by following command:

.. code::

    $ git checkout 7d29a2b
    $ sudo make all

Then use the commands above to connect to Alpha Mainnet.

Create an Account
^^^^^^^^^^^^^^^^^^^^^^

.. code::

    $ ./cpchain account new --datadir ./datadir

Run a Private Network
^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code::

    $ cd examples/cpchain
    $ ./cpchain-all.sh

    # check logs
    $ tail -f data/logs/*.log | grep number=

Run a Local Node
^^^^^^^^^^^^^^^^^^^^^^^

.. code::

    $ ./cpchain run --datadir ./datadir --unlock <You Address>










