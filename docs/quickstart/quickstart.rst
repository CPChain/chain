Quick Start
~~~~~~~~~~~~~



Readers can choose either to use binary release or build from source code.
Both methods require a Linux working environment,
and have been tested on Ubuntu 18.04.
Earlier Linux releases may incur problems or lack necessary dependencies.

Binary Release
+++++++++++++++++++

Download address for Binary release is coming soon.



As Civilian
##############

After you download `cpchain` binary file, you can run it as a civilian.
Go the directory you store `cpchain` and type in:

.. code-block:: shell

    $ ./cpchain run

Now you have connected to cpchain P2P network.
Employing either :ref:`fusion-api` or :ref:`rpc-api` to
wield the power as a civilian as well as assume corresponding responsibility.


Source Code Building
+++++++++++++++++++++++++


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










