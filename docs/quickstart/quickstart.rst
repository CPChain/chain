Quick Start
~~~~~~~~~~~~~

We are going to install CPChain and run a node on the testnet. 

Building the source
####################

First, make sure you have installed `go <https://golang.org/>`_, and configured the $GOPATH.

.. code::

    $ git clone https://github.com/CPChain/chain

    $ cd chain
    $ make clean
    $ make all

Running CPChain
#################

Connect to testnet
^^^^^^^^^^^^^^^^^^^^^^^

.. code::

    $ cd build/bin
    $ ./cpchain run --runmode testnet

Create an account
^^^^^^^^^^^^^^^^^^^^^^

.. code::

    $ ./cpchain account new --datadir ./datadir

Run a private network
^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code::

    $ cd examples/cpchain
    $ ./cpchain-all.sh

    # check logs
    $ tail -f data/logs/*.log | grep number=

Run a local node
^^^^^^^^^^^^^^^^^^^^^^^

.. code::

    $ ./cpchain run --datadir ./datadir --unlock <You Address>










