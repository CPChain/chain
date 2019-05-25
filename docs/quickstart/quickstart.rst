.. _quick-start:

Quick Start in Detail
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



Readers can choose either to use binary release or build from source code.
Both methods require a Linux working environment,
and have been tested on Ubuntu 18.04.
Earlier Linux releases may incur problems or lack necessary dependencies.


.. NOTE::

    All code starting with a ``$`` is meant to run in your terminal.
    All code starting with a ``>>>`` is meant to run in a python interpreter,
    like `ipython <https://pypi.org/project/ipython/>`_.


Cpchain and Console
============================


Binary Release
+++++++++++++++++++

`Download page`_ of binary releases for CPChain and Solidity.

.. _`Download Page`: https://github.com/CPChain/chain/releases

``cpchain`` is the binary release for the chain.
And ``console`` provides command line interface for operations on the chain,
like checking account status, deposit and claiming campaign.

.. NOTE::

    ``console`` does not support transaction operations.

You need to utilize either :ref:`fusion-api` or :ref:`rpc-api` for all available operations.

You can always refer to

.. code-block:: shell

    $ ./cpchain -h

and

.. code-block:: shell

    $ ./console -h

for help.

As Civilian
##############

After you download ``cpchain`` binary file, you can run it as a civilian.
Go the directory you store ``cpchain`` and type in:

If you do not have an account, you can **create a new account** with ``cpchain``.

For Linux and Mac users:

.. code-block:: shell

    $ mkdir datadir
    $ echo YOUR_PASSWORD > datadir/password
    $ ./cpchain account new account --datadir ./datadir

For Windows users:

.. code-block:: shell

    $ mkdir datadir
    $ echo|set /p="YOUR_PASSWORD"> datadir/password
    $ cpchain.exe account new account --datadir ./datadir


Here we first create a directory named as ``datadir`` and
create a file containing the password you prefer.
Command ``./cpchain account new account --datadir ./datadir`` requires
you to enter a password, which should be same as ``YOUR_PASSWORD`` in previous echo command.

A successful execution returns the wallet address.
And a keystore file is generated in ``datadir/keystore/``.
Its file name is something like
``UTC--2019-03-27T07-32-49.561001045Z--5d6477ecd219bfe0ba44bf1b16272e72bd200e51``.
And you can also refer to the name of this file to retrieve the wallet address.
``5d6477ecd219bfe0ba44bf1b16272e72bd200e51`` is the wallet address for the example above.

.. note::

    If you discard ``--datadir`` option, the account file is created under default user directory.

After you register a wallet address,
you can run the following command to **connect to the chain**:

.. code-block:: shell

    $ ./cpchain run --rpcaddr 127.0.0.1:8501 --port 30311

.. note::

    Please check the availability of both ports 8501 and 30311 before connection.
    You may nominate other ports as you wish.

If you cannot get successfully successfully connected.
You may try delete some temporary files by


.. code-block:: shell

    $ ./cpchain chain cleandb

You can refer to :ref:`cpchain-run-fail` in :ref:`FAQ` for detailed solutions.

Now you have connected to cpchain P2P network.
And the progress is going to running for a while to sync with the chain.


Employ either :ref:`fusion-api` or :ref:`rpc-api` to
wield the power as a civilian as well as assume corresponding responsibility.

You can also choose to use **console** to run as a civilian.

To **check the status** of your account, you can use the following command:


.. code-block:: shell

    $ ./console status --keystore ./datadir/keystore/YOUR_ACCOUNT --password ./datadir/password

Here ``YOU_ACCOUNT`` is the file generated previously in ``datadir/keystore/``.
And you can obtain the information about your account status like


.. code-block:: shell

    INFO[03-26|19:53:54.921] proposer                                      addr=0x52e584B4fBa8688eb7EDcaBb18e65661A99acC67 c.addr=0x5A8a1a86b086c062a87B0883F78a078f2Bf74609
    // a bunch of proposers like the line above
    --------------------------

    Mining:           false

    RNode:            false

    Proposer:         false

    Locked:           true

    SupportPrivateTx: false
    --------------------------



And you can also **check your account information** using the command:


.. code-block:: shell

    $ ./console account --keystore ./datadir/keystore/YOUR_ACCOUNT --password ./datadir/password


It returns results like

.. code-block:: shell

    --------------------------

    Balance: 400000 CPC // this account contains 400000 CPC

    Reward:
    	Total:  0 CPC
    	Free:   0 CPC
    	Locked: 0 CPC

    --------------------------




As Proposer
################



Similar to operations in `As Civilian`_,
a node willing to become proposer can also utilize the following commands to create an account.


For Linux and Mac users:

.. code-block:: shell

    $ mkdir datadir
    $ echo YOUR_PASSWORD > datadir/password
    $ ./cpchain account new account --datadir ./datadir

For Windows users:

.. code-block:: shell

    $ mkdir datadir
    $ echo|set /p="YOUR_PASSWORD"> datadir/password
    $ cpchain.exe account new account --datadir ./datadir

The command for proposers connecting P2P network is slightly different than the counterpart for civilians

.. code-block:: shell

    $ ./cpchain run --datadir ./datadir --unlock 5d6477ecd219bfe0ba44bf1b16272e72bd200e51 \
        --rpcaddr 127.0.0.1:8501 --port 30311 --mine \
        --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner --linenumber

, where ``5d6477ecd219bfe0ba44bf1b16272e72bd200e51`` is a wallet address.
It requires you to enter the password to further proceed.
You may use an argument ``--password`` to indicate a file storing your plaintext password.
But it is risky, and we do not recommend it.

.. note::

    If you discard ``--datadir`` option, the account file is read from default user directory.

.. note::

    A flag ``--account WALLET_ADDRESS`` is required
    in case your ``./datadir`` directory contains more than one account file.

.. NOTE::

    The argument ``--mine`` indicates this connection can be used for proposing blocks.


And via this connection,
a node with insufficient deposit automatically sets its deposit to 200,000 CPC (if its balance is enough).
And then the node claims campaign to become a proposer.


Using commands ``./console account`` and ``./console status`` to check
the account info and status about this node, similar to civilians.

A node can using following commands to deposit more CPC

.. code-block:: shell

    $ ./console reward deposit --keystore ./datadir/keystore/YOUR_ACCOUNT --password ./datadir/password VALUE

, where ``VALUE`` is the number of CPC you willing to deposit.

To stop mining, use the command below

.. code-block:: shell

    $ ./console miner stop --keystore ./datadir/keystore/YOUR_ACCOUNT  --password ./datadir/password

Then you may check the status of the account, the attribute ``Mining`` of which should shifted to ``false``.

After you stop mining, you are free to withdraw deposit by the following command:

.. code-block:: shell

    $ ./console reward withdraw --keystore ./datadir/keystore/YOUR_ACCOUNT --password ./datadir/password VALUE

If you do not present the argument ``VALUE``, all deposit will be withdrew by default.



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

Now you can find binary files in ``build/bin``,
and utilize them as stated in `Binary Release`_.

Running CPChain
#################

Connect to Beta Mainnet
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code::

    $ cd build/bin
    $ ./cpchain run --runmode testnet



Then use the commands above to connect to Beta Mainnet.

Create an Account
^^^^^^^^^^^^^^^^^^^^^^


For Linux and Mac users:

.. code-block:: shell

    $ mkdir datadir
    $ echo YOUR_PASSWORD > datadir/password
    $ ./cpchain account new account --datadir ./datadir

For Windows users:

.. code-block:: shell

    $ mkdir datadir
    $ echo|set /p="YOUR_PASSWORD"> datadir/password
    $ cpchain.exe account new account --datadir ./datadir

Run a Private Network
^^^^^^^^^^^^^^^^^^^^^^^^^^^



.. code::

    $ cd examples/cpchain
    $ ./cpchain-all.sh

    # check logs
    $ tail -f data/logs/*.log | grep number=

.. note::

    ``cpchain-all.sh`` launches the chain in dev mode.

Run a Local Node
^^^^^^^^^^^^^^^^^^^^^^^

.. code::

    $ ./cpchain run --datadir ./datadir --unlock <You Address>

CPC Faucet
=================

CPC faucet is an application that you can collect CPC test coins for free.
The test coins can be used in newly-published CPChain Alpha Mainnet.
Refer to `Faucet`_ to try it now.


Claim Test Coins
++++++++++++++++++++++

1. Copy the wallet address and paste it in `Faucet`_. Now you can claim test coins.
#. The password it requires is *cpchain2019*.
#. Following a successful claim, this transaction is inserted into the test chain. In the site `Explorer`_, the transaction details can be searched.

.. _`Faucet`: https://cpchain.io/faucet/
.. _`Explorer`: https://cpchain.io/explorer/


Smart Contract
======================

.. warning::
    The solidity version for CPChain is 0.4.25.
    Other version is not guaranteed compatible with CPChain.

.. note::
    Refer to `Solidity`_ for detailed information.

.. _Solidity: ../solidity/index.html

Solidity Binary Release
+++++++++++++++++++++++++

You can download corresponding solidity binary release from `Download Page`_.

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

    $ sudo  apt-get  install  libz3-dev

Smart Contract Examples
++++++++++++++++++++++++++++++++++++

In our repository, we have several examples for smart contract.
Please check files in ``/docs/quickstart/``.
You may also find it in `Download Page`_.

.. note::
    Please replace the values of ``keystore``, ``password`` as well as ``address``
    to yours.




