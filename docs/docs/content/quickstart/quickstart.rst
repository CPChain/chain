.. _quick-start:

Quick Start in Detail
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



Readers can choose either to use binary release or build from source code.
Both methods can been conducted on Linux, Mac or Windows operation system.
Without loss of generality, all commands below are in Linux terminal format.

.. NOTE::

    All code starting with a ``$`` is meant to run in your terminal.
    All code starting with a ``>>>`` is meant to run in a python interpreter,
    like `ipython <https://pypi.org/project/ipython/>`_.


Installation
=================

.. Note::

    The functions of ``console`` has been integrated into ``cpchain``.
    Versions after 0.2.11 no longer contains ``console``.


Binary Release
+++++++++++++++++++

Refer to `Download page`_ for latest binary releases of CPChain.

.. _`Download Page`: https://github.com/CPChain/chain/releases

``cpchain`` is the binary release for the chain.

In principle, version 0.a.b is compatible with version 0.a.c, where a, b, c, are natural numbers.
For example 0.4.8 is compatible with 0.4.6.
The word **"compatible"** here means no conflicts in the level of consensus,
but older versions certainly contain more bugs and lack new features.

Thus, We **strongly** encourage the users to adopt the latest version.
But it is feasible to downgrade to a previous compatible version to circumvent certain bugs in the newer ones.


You need to utilize either :ref:`fusion-api` or :ref:`rpc-api` for all available operations.

You can always refer to

.. code-block:: shell

    $ ./cpchain -h



for help.



Source Code Building
+++++++++++++++++++++++++


We are going to install CPChain and run a node on the testnet.


First, make sure you have installed `go <https://golang.org/>`_, and configured the $GOPATH.

.. code::

    $ git clone https://github.com/CPChain/chain

    $ cd chain
    $ make clean
    $ make all

Now you can find binary files in ``build/bin``,
and utilize them as stated in `Binary Release`_.


Running CPChain
=====================

Nodes in CPChain have three possible roles:
**Civilian**, **Proposer**, or **Validator**.
Interested readers can refer to :ref:`bipartite` for detailed information.
Note that validators are not available for public use at the current stage.
Thus, we do not state how to launch a validator node.

Create an Account
++++++++++++++++++++++

If you do not have an account, you create one with ``cpchain``

.. code-block:: shell

    $ ./cpchain account new



A successful execution returns the wallet address.
And a keystore file is generated in default directory.
Its file name is something like
``UTC--2019-03-27T07-32-49.561001045Z--5d6477ecd219bfe0ba44bf1b16272e72bd200e51``.
And you can also refer to the name of this file to retrieve the wallet address.
``5d6477ecd219bfe0ba44bf1b16272e72bd200e51`` is the wallet address for the example above.

You can use the following command for more detailed explanation,
as well as the path for default directory.

.. code-block:: shell

    $ ./cpchain account new -h

.. note::

    You can add ``--datadir`` option to specify the keystore directory.


.. _as-civilian:

Run a Node as Civilian
+++++++++++++++++++++++++

Connect to P2P Network as Civilian
**************************************

If you hold an account,
you can run a very simple command to **connect to the chain**:

.. code-block:: shell

    $ ./cpchain run

However, the main purpose of a user to deploy a civilian is to invoke API.
Thus, the following command is more suitable.

.. code-block:: shell

    $ ./cpchain run --rpcaddr 127.0.0.1:8501 \
        --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner

.. note::

    Please check the availability of
    the the default port ``30310`` (or the port you specified using ``--port``) before connection.
    You may nominate other port as you wish.

.. note::

    Flags ``--rpcaddr`` and ``--rpcapi`` make APIs available in your node.
    You may discard them if you do not need any API.
    Please make sure the availability of the port 8501 if you are willing to use APIs.

If you cannot get successfully connected.
You may try delete some temporary files by


.. code-block:: shell

    $ ./cpchain chain cleandb

.. note::

    You could specify datadir by adding ``--datadir ./datadir``.
    Otherwise, this command will remove detabase in the default datadir.
    The port 8051 is required if you are using APIs.

You can refer to :ref:`cpchain-run-fail` in :ref:`FAQ` for detailed solutions.

Now you have connected to cpchain P2P network.
And the progress is going to running for a while to sync with the chain.


Employ either :ref:`fusion-api` or :ref:`rpc-api` to
wield the power as a civilian as well as assume corresponding responsibility.

Check Status
*********************

You can also utilize ``cpchain``
to **check the status** of your account by the following command:


.. code-block:: shell

    $ ./cpchain campaign status --keystore ./datadir/keystore/YOUR_ACCOUNT

Here ``YOU_ACCOUNT`` is the file generated previously in ``datadir/keystore/`` (or default path).
And you can obtain the information about your account status like


.. code-block:: shell

    INFO[03-26|19:53:54.921] proposer                                      addr=0x52e584B4fBa8688eb7EDcaBb18e65661A99acC67 c.addr=0x5A8a1a86b086c062a87B0883F78a078f2Bf74609
    // a bunch of proposers like the line above
    --------------------------

    Mining:           false

    RNode:            false

    Proposer:         false
    --------------------------





.. _as-proposer:

Run a Node as Proposer
++++++++++++++++++++++++


Connect to P2P Network as Proposer
************************************

The command for proposers connecting P2P network is slightly different than the counterpart for civilians

.. code-block:: shell

    $ ./cpchain run --unlock WALLET_ADDRESS --mine


, where you should fill ``WALLET_ADDRESS`` with your wallet address.
It requires you to enter the password to further proceed.
You may use an argument ``--password`` to indicate a file storing your plaintext password.
But it is risky, and we do not recommend it.

If you are willing to use :ref:`fusion-api` and :ref:`rpc-api`,
please use the following command:

.. code-block:: shell
    :emphasize-lines: 2

    $ ./cpchain run \
        --unlock WALLET_ADDRESS \
        --rpcaddr 127.0.0.1:8501 --mine \
        --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner

.. note::

    Please check the availability of
    the the default port ``30310`` (or the port you specified using ``--port``) before connection.
    You may nominate other port as you wish.

.. note::

    You should use ``--datadir`` option, if the account file is not read from default user directory.

.. note::

    A flag ``--account WALLET_ADDRESS`` is required
    in case your ``./datadir`` directory contains more than one account file.

.. NOTE::

    The argument ``--mine`` indicates this connection can be used for proposing blocks.

.. note::

    Flags ``--rpcaddr`` and ``--rpcapi`` make APIs available in your node.
    You may discard them if you do not need any API.
    Make sure the availability of port 8501 if you are using APIs.


And via this connection,
a node with insufficient deposit automatically sets its deposit to 200,000 CPC (if its balance is enough).
And then the node claims campaign to become a proposer.


Check Status, Start and Stop Mining
*************************************


Using commands ``./cpchain campaign status`` to check
the status about this node, similar to civilians.

A node can using following commands to start mining.

.. code-block:: shell

    $ ./cpchain campaign start --keystore ./datadir/keystore/YOUR_ACCOUNT

It returns info like

.. code-block:: shell

    INFO[06-10|14:44:47.474] You are not rnode yet, you will spend 200000 cpc to be rnode first
    INFO[06-10|14:44:47.474] Start Mining...
    INFO[06-10|14:44:47.474] Start Success.



To stop mining, use the command below

.. code-block:: shell

    $ ./cpchain campaign stop --keystore ./datadir/keystore/YOUR_ACCOUNT

Then you may check the status of the account, the attribute ``Mining`` of which should shifted to ``false``.

After you stop mining, your deposit in RNode pool will be automatically refunded.

.. note::

    Similar to ``./cpchain run``, you can use the command ``./cpchain campaign --password YOUR_PASSWORD_FILE``
    where ``YOUR_PASSWORD_FILE`` is the file containing your account password.


Run a Private Network
++++++++++++++++++++++++++++



.. code::

    $ cd examples/cpchain
    $ ./cpchain-all.sh

    # check logs
    $ tail -f data/logs/*.log | grep number=

.. note::

    ``cpchain-all.sh`` launches the chain in dev mode.

The command below is to run a local node.


.. code::

    $ ./cpchain run --datadir ./datadir --unlock YOUR_ADDRESS --runmode dev

Here ``--runmode dev`` is to prevent the node from connecting to Mainnet.


Smart Contract
======================

.. warning::
    The solidity version for CPChain is 0.4.25.
    Other version is not guaranteed compatible with CPChain.

.. note::
    Refer to `Solidity`_ for detailed information.

.. _Solidity: ../solidity/index.html

.. _solc-download:

Solidity Binary Release
+++++++++++++++++++++++++

You can download corresponding solidity binary files from
`Solc Releases <https://github.com/CPChain/solidity/releases>`_.


And copy the solc binary file to ``/user/bin``.

.. code-block:: shell

    $ cp solc /usr/bin

Source Code Build
++++++++++++++++++++

If you are willing to build solidity 0.4.25 from source code,
please refer to the `Solidity Installation`_

.. _Solidity Installation: ../solidity/installing-solidity.html


.. note::
    If you encounter any problem when running ``solc``,
    please check :ref:`FAQ` page.

Install `py-solc`
++++++++++++++++++

Use the command below to install ``py-solc``.
This module connects python functions with ``solc`` in your computer.

.. code-block:: shell

    $ pip3 install py-solc

You may also be required to install `libz3.so.4` by following command:

.. code-block:: shell

    $ sudo apt-get install libz3-dev

Smart Contract Examples
++++++++++++++++++++++++++++++++++++

In our repository, we have several examples for smart contract.
Please check files in ``/docs/quickstart/``.


.. note::
    Please replace the values of ``keystore``, ``password`` as well as ``address``
    to yours.




