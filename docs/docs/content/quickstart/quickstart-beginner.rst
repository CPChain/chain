.. _quick-start-beginner:

Quick Start for Beginner
=============================



Refer to `Download page`_ for binary releases of ``cpchain``.

.. _`Download Page`: https://github.com/CPChain/chain/releases

For ease of reading, we use ``cpchain`` to represent all available cpchain versions.
The instructions below are demonstrated on Linux.

If you are using Windows platform, all commands below are also viable.
Just replace ``cpchain`` with ``cpchain-windows-4.0-386.exe`` or ``cpchain-windows-4.0-amd64.exe``.

For 32-bit PC user, please select ``386`` version.
And 64-bit PC users should download ``amd64`` version.

For Mac user, please download ``darwin`` version.
(Darwin forms the core of macOS)


.. NOTE::

    All code starting with a ``$`` is meant to run in your terminal or cmd.
    Do not copy ``$``, as it is not a part of a command.


Apply for a Wallet
--------------------

Use the ``cd`` command to enter the directory containing ``cpchain`` binary file.

For Windows users, use the commands below in cmd.

.. code-block:: shell

    $ cpchain-windows-4.0-amd64.exe account new


.. note::

    Change ``cpchain-windows-4.0-amd64.exe`` to ``cpchain-windows-4.0-386.exe``
    if you are using on 32 bit operation system.

For Linux and Mac users, use the commands below in terminal:

.. code-block:: shell

    $ ./cpchain account new

Your account will be generated in default directory.
Use the help command below to check the manuel which includes the path of default directory for your environment.

For Windows users:

.. code-block:: shell

    $ cpchain-windows-4.0-amd64.exe account new -h

For Linux and Mac users:

.. code-block:: shell

    $ ./cpchain account new -h

.. note::

    You may use ``--datadir`` option to specify the keystore directory.





Connect to Mainnet
--------------------

.. note::

    The capitalized VARIABLES requires your modification
    according to your own settings.

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

    $ cpchain-windows-4.0-amd64.exe run --unlock WALLET_ADDRESS --mine


Linux and Mac users please use the following command:

.. code-block:: shell

    $ ./cpchain run --unlock WALLET_ADDRESS --mine

.. note::

    The default port 30310 (or the port you specified using ``--port``)
    should be opened.
    Otherwise, other nodes cannot connect you in the P2P network.

.. note::

    If you use ``--datadir`` option, the account file is read from your specified path.

.. note::

    A flag ``--account WALLET_ADDRESS`` is required
    in case your keystore directory contains more than one account file.


If you also willing to utilize API, please check :ref:`as-proposer`.

Get Chain Synced
~~~~~~~~~~~~~~~~~~~~

This section is for users that only want to sync with the Mainnet, review or sending transactions.

Windows users can utilize the command below:

.. code-block:: shell

    $ cpchain-windows-4.0-amd64.exe run


Linux and Mac users please try this command:

.. code-block:: shell

    $ ./cpchain run

If you are willing to use API, please check :ref:`as-civilian`.

Check Your Status
~~~~~~~~~~~~~~~~~~~~

After you use ``./cpchain run`` command, you have connected to Mainnet.
Use the commands below to check your status.

For Linux and Mac users:

.. code-block:: shell

    $ ./cpchain campaign status --keystore ./datadir/keystore/YOUR_ACCOUNT


For Windows users:

.. code-block:: shell

    $ cpchain-windows-4.0-amd64.exe campaign status --keystore ./datadir/keystore/YOUR_ACCOUNT



This command is to check your account status given the ``keystore`` file.

Stop Your Node from Mining
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Generally, it is safe to quit the node use ``ctrl+c``.
Using commands like ``kill -9`` or ``killall`` may incur impeached blocks.
Refer to :ref:`sig-ctrl-c` for detailed explanation.

To stop mining without quitting the node, use the command below.

Windows users:

.. code-block:: shell

    $ cpchain-windows-4.0-amd64.exe campaign stop --keystore ./datadir/keystore/YOUR_ACCOUNT


Linux and Mac users:

.. code-block:: shell

    $ ./cpchain campaign stop --keystore ./datadir/keystore/YOUR_ACCOUNT


Upgrade
----------

If you receive any error message under good network condition,
the first thing you need to do is to check if your node version is out-dated.

The upgrade is simple.
All you need is to download the latest version from `Download page`_,
and stop your currently running node,
and replace the old version with the latest one.

.. note::

    Please check :ref:`sig-ctrl-c`, if you cannot stop the node properly.

You can always use ``--version`` flag to check the version.

For Linux and Mac users, use the command as below:

.. code-block:: shell

    $ ./cpchain --version


Windows users use the following command.

.. code-block:: shell

    $ cpchain.exe --version


After you upgrade, your node can continue syncing with the chain.

