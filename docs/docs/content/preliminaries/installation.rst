Installation
~~~~~~~~~~~~~~

In this section, you are going to learn how to download our code, build the project and run it on you own system.

.. NOTE::

    All code starting with a ``$`` is meant to run in your terminal.
    All code starting with a ``>>>`` is meant to run in a python interpreter,
    like `ipython <https://pypi.org/project/ipython/>`_.


First, make sure you have installed `go <https://golang.org/>`_, and configured the $GOPATH.

Getting Repository
************************

You can click `here <https://github.com/CPChain/chain>`_ to access source code,
or execute the following commands to clone code on github.

.. code::
    
    # open a $GOPATH
    $ cd $GOPATH/src

    $ mkdir -p bitbucket.org/cpchain/
    
    $ cd bitbucket/cpchain
    
    # TODO: chain url
    $ git clone https://github.com/CPChain/chain


Building
************

Run the command to compile and generate binary file in the ``chain`` directory.

.. code::

    $ cd chain
    $ make clean
    $ make all

Executables
*************

You can find several executables in ``build/bin`` directory after building the project.

.. code::

    $ cd build/bin
    $ ls


.. code-block:: table
	+------------------+------------------------------------+
	|Command           | Description                        |
	+==================+====================================+
	|cpchain           | Executable for the cpchain         |
	|                  | blockchain networks.               |
	+------------------+------------------------------------+
	|abigen            | Source code generator to convert   |
	|                  | CPChain contract definitions into  |
	|                  | easy to use, compile-time type-safe|
	|                  | Go packages.                       |
	+------------------+------------------------------------+
	|bootnode          | A lightweight bootstrap node to    |
	|                  | aid in finding peers in private    |
	|                  | networks.                          |
	+------------------+------------------------------------+
	|contract-admin    | Executable for the cpchain         |
	|                  | official contract admin.           |
	|                  |                                    |
	+------------------+------------------------------------+
	|testtool          | Executable command tool for easy   |
	|                  | test.                              |
	|                  |                                    |
	+------------------+------------------------------------+
	|transfer          | Executable for CPC transfer.       |
	|                  |                                    |
	|                  |                                    |
	+------------------+------------------------------------+
	|ecpubkey          | Return the public key given a      |
	|                  | keystore file and its password.    |
	|                  |                                    |
	+------------------+------------------------------------+
	|findimpeach       | Only for test purpose.             |
	|                  |                                    |
	|                  |                                    |
	+------------------+------------------------------------+
	|smartcontract     | For deploying smart contract.      |
	|                  |                                    |
	|                  |                                    |
	+------------------+------------------------------------+
