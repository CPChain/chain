.. _quick-start-beginner:

Quick Start for Beginner
=============================



Refer to `Download page`_ for binary releases of cpchain and console.

.. _`Download Page`: https://github.com/CPChain/chain/releases

For ease of reading, we use ``cpchain`` to represent all available cpchain versions.
The instructions below are demonstrated on Linux.

If you are using Windows platform, all commands below are also viable.
Just replace ``chchain`` with ``cpchain-windows-4.0-386.exe`` or ``cpchain-windows-4.0-amd64.exe``.

For 32-bit PC user, please select ``386`` version.
And 64-bit PC users should download ``amd64`` version.


.. NOTE::

    All code starting with a ``$`` is meant to run in your terminal or cmd.
    Do not copy ``$``, as it is not a part of a command.


Apply for a Wallet
--------------------

Use the ``cd`` command to enter the directory containing ``cpchain`` binary file.

For Windows users, use the commands below in cmd.

.. code-block:: shell

    $ mkdir datadir
    $ cpchain-windows-4.0-amd64.exe account new account --datadir ./datadir

.. note::

    Change ``cpchain-windows-4.0-amd64.exe`` to ``cpchain-windows-4.0-386.exe``
    if you are using on 32 bit operation system.

For Linux and Mac users, use the commands below in terminal:

.. code-block:: shell

    $ mkdir datadir
    $ ./cpchain account new account --datadir ./datadir

The first command is to generate a keystore file
located in ``datadir/keystore``,
in which you can find the wallet address.
The second command create a new account, and return the wallet address.


Connect to Mainnet
--------------------

.. note::

    The line with highlight requires you to modify VARIABLES
    which are capitalized according to your own settings.

Refer to :ref:`FAQ` if you encounter any problem.

Get Block Mined
~~~~~~~~~~~~~~~~~~

This section is for users that are willing to propose new blocks.

.. note::

    Before mining a block,
    make sure that you the balance in your account is large enough (at least 200,000 cpc).

Windows user the command below.
(Here we use ``amd64`` version as demonstration.)

.. code-block:: shell
    :emphasize-lines: 2

    $ cpchain-windows-4.0-amd64.exe run --datadir ./datadir ^
        --unlock WALLET_ADDRESS ^
        --rpcaddr 127.0.0.1:8501 --port 30311 --mine ^
        --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner --linenumber


Linux and Mac users please use the following command:

.. code-block:: shell
    :emphasize-lines: 2

    $ ./cpchain run --datadir ./datadir \
        --unlock WALLET_ADDRESS \
        --rpcaddr 127.0.0.1:8501 --port 30311 --mine \
        --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner --linenumber


.. note::

    ``^`` and ``\`` are splitters for long command for Windows and Linux (Mac), respectively.
    You do not need to type them if you put the command in a single line.


Get Chain Synced
~~~~~~~~~~~~~~~~~~~~

This section is for users that only want to sync with the Mainnet, review or sending transactions.

Windows users can utilize the command below:

.. code-block:: shell

    $ cpchain-windows-4.0-amd64.exe run --rpcaddr 127.0.0.1:8501 --port 30311


Linux and Mac users please try this command:

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


