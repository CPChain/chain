.. _quick-start-beginner:

Quick Start for Beginner
=============================



Refer to `Download page`_ for binary releases of CPChain and Console.

.. _`Download Page`: https://github.com/CPChain/chain/releases/tag/v0.2.1


Apply for Wallet
------------------

.. code-block:: shell

    $ mkdir datadir
    $ echo "YOU_PASSWORD" > datadir/password
    $ ./cpchain account new account --datadir ./datadir

A keystore file is generated in ``datadir/keystore``,
and a password file is ``data/password``.
The wallet address is written in the ``keystore`` file.


Connect to Mainnet
--------------------

Get Block Mined
~~~~~~~~~~~~~~~~~~

If you will to propose new block, use the command below:

.. code-block:: shell

    $ ./cpchain run --datadir ./datadir --unlock WALLET_ADDRESS \
        --rpcaddr 127.0.0.1:8501 --port 30311 --mine \
        --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner --linenumber

Get Chain Synced
~~~~~~~~~~~~~~~~~~~~

If you only want to sync with the Mainnet, review or sending transactions,
use the command below:

.. code-block:: shell

    $ ./cpchain run --rpcaddr 127.0.0.1:8501 --port 30311

