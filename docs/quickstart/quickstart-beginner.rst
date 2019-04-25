.. _quick-start-beginner:

Quick Start for Beginner
=============================



Refer to `Download page`_ for binary releases of cpchain and console.

.. _`Download Page`: https://github.com/CPChain/chain/releases/tag/v0.2.1

For ease of reading, we use ``cpchain`` to represent all available cpchain versions.
The instructions below are demonstrated on Linux.

If you are using Windows platform, all commands below are also viable.
Just replace ``chchain`` with ``cpchain-windows-4.0-386.exe`` or ``cpchain-windows-4.0-amd64.exe``.

For 32-bit PC user, please select 386 version.
And 64-bit PC users should download amd64 version.


Apply for a Wallet
--------------------

.. code-block:: shell

    $ mkdir datadir
    $ ./cpchain account new account --datadir ./datadir

A keystore file is generated in ``datadir/keystore``,
in which you can find the wallet address.


Connect to Mainnet
--------------------

.. note::

    The line with highlight requires you to modify VARIABLES
    which are capitalized according to your own settings.

Refer to :ref:`FAQ` if you encounter any problem.

Get Block Mined
~~~~~~~~~~~~~~~~~~

If you are willing to propose new blocks, use the command below:

.. code-block:: shell
    :emphasize-lines: 2

    $ ./cpchain run --datadir ./datadir \
        --unlock WALLET_ADDRESS \
        --rpcaddr 127.0.0.1:8501 --port 30311 --mine \
        --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner --linenumber





Get Chain Synced
~~~~~~~~~~~~~~~~~~~~

If you only want to sync with the Mainnet, review or sending transactions,
use the command below:

.. code-block:: shell

    $ ./cpchain run --rpcaddr 127.0.0.1:8501 --port 30311



Check Your Status
~~~~~~~~~~~~~~~~~~~~

After you use ``./cpchain run`` command, you have connected to Mainnet.
Use the commands below to check your status.

.. code-block:: shell
    :emphasize-lines: 1,3,4

    $ echo "YOUR_PASSWORD" > datadir/password
    $ ./console status \
    --keystore ./datadir/keystore/YOUR_ACCOUNT \
    --password ./datadir/password

The first command generates a file containing your password,
which are located in ``datadir/password``.
The second command is to check your account status given the ``keystore`` file
as well as the ``password`` file you just generate.


