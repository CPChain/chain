.. _FAQ:

FAQ
~~~~~~~~~~~

How to interact with CPChain?
*********************************

You can utilize ``cpc_fusion`` to interact with CPChain in a python interpreter.

.. code-block:: python

    >>> from cpc_fusion import Web3
    >>> cf = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))
    >>> cf.cpc.blockNumber
    34341



Why does fusion return an error (Errno 111) indicating connection is refused?
****************************************************************************************

The Errno 111 can be returned when you call ``Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))`` in fusion.

Before connecting http://127.0.0.1:8501, you should either set up a local chain or sync with our Mainnet.
Refer to :ref:`fusion-api-using` to detailed explanations.


.. _cpchain-run-fail:

Why ``./cpchain run`` command cannot be executed successfully?
*********************************************************************


Several reasons can account for this problem.
You may try the following means to solve the problem.

1. Confirm that you are connecting to the network and the ports you nominated are available.

If you use the command in :ref:`quick-start` as

.. code-block:: shell

    $ ./cpchain run --rpcaddr 127.0.0.1:8501 --port 30311

, make sure both port ``8501`` and ``30311`` have not be occupied yet.
You may also use other ports as you wish.

2. Remove temporary user files.

The existence of some temporary files get ``cpchain`` skip some initialization processes,
which may result in an unsuccessful execution.

Type in the following to remove temporary files.


.. code-block:: shell

    $ ./cpchain chain cleandb

3. Manually kill all ``cpchain`` processes.

An incomplete abort of ``cpchain`` can incur a failure in starting a new process.
If you receive an error message indicating your port or datadir being occupied,
it is highly possible that there are some ``cpchain`` processes still running in background.

You can may either use ``ps`` command paired with ``kill`` to terminate ``cpchain`` processes,
or choose to kill all cpchain processes by

.. code-block:: shell

    $ killall -9 cpchain



Message ``The file "./cpchain" is not executable by this user`` pops when running ``cpchain``
*************************************************************************************************

This problem is due to a wrong access permission of the binary file.
You can fix this problem by using the command below:

.. code-block:: shell

    $ chmod +x cpchain


Message ``error  while  loading  shared  libraries:  libz3.so.4`` pops when running ``solc``
************************************************************************************************

It can be resolved by running the command below:

.. code-block:: shell

    $ sudo  apt-get  install  libz3-dev

The default ``solc`` is not a compatible version
**************************************************

To check the version of solidity, you may utilize the following command:

.. code-block:: shell

    $ solc --version

And by using ``$ which solc`` command, you can locate the path for default ``solc``,
and replace it with a 0.4.25 version.

.. code-block:: shell

    $ which solc
    /usr/bin/solc
    $ rm -f /usr/bin/solc
    // copy solc 0.4.25 to /user/bin
    $ cp solc /usr/bin

