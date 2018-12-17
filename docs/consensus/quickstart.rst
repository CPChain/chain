Quickstart
==========

.. contents:: :local:

.. NOTE:: All code starting with a ``$`` is meant to run on your terminal.
    All code starting with a ``>>>`` is meant to run in a python interpreter,
    like `ipython <https://pypi.org/project/ipython/>`_.

Installation
------------

Web3.py can be installed (preferably in a :ref:`virtualenv <setup_environment>`)
using ``pip`` as follows:

.. code-block:: shell

   $ pip install cpc_fusion



Installation from source can be done from the root of the project with the
following command.

.. code-block:: shell

   $ pip install .


Using Fusion
------------

To use the web3 library you will need to initialize the
:class:`~web3.Web3` class.

Use the ``auto`` module to :ref:`guess at common node connection options
<automatic_provider_detection>`.

.. code-block:: python

    >>> from cpc_fusion import Web3
    >>> cf = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))
    >>> cf.cpc.blockNumber
    34341


.. NOTE:: If you get the result ``UnhandledRequest: No providers responded to the RPC request``
    then you are not connected to a node.
.. _first_w3_use:

Getting Blockchain Info
----------------------------------------

It's time to start using Web3.py! Try getting all the information about the latest block.

.. code-block:: python

    >>> cf.cpc.getBlock('latest')
   cf.cpc.getBlock('latest')
AttributeDict({'difficulty': 1, 'dpor': AttributeDict({'seal': [144, 146, 95, 19, 69, 5,...],
'sigs': [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,...],
'proposers':
 ['0xc05302acebd0730e3a18a058d7d1cb1204c4a092', '0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a', ..,
 'validators': []}),
 'extraData': HexBytes('0x0000000000000000000000000000000000000000000000000000000000000000'),
 'gasLimit': 4712388,
 'gasUsed': 0,
 'hash': HexBytes('0x7ad848f460c6fdab0e2da1437c495281da31ebb382e9aa7d246e82e12b0ef5fa'),
 'logsBloom': HexBytes('0x000000000000000000000000000000000000000000000000000000000000000000000000000000000...
 , 'miner': '0xc05302AceBd0730E3A18A058d7d1CB1204C4a092',
 'mixHash': HexBytes('0x0000000000000000000000000000000000000000000000000000000000000000'),
 'nonce': HexBytes('0x0000000000000000'),
 'number': 34477,
 'parentHash': HexBytes('0x796f955c93a28a0bb46444272f8294244b9d7b437f902bea208af29f896b253d'),
 'receiptsRoot': HexBytes('0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421'),
 'size': 936,
 'stateRoot': HexBytes('0xdde168d53ddecddfaeaaeb8d74e1dd904324d2e1ae806002dca867cb17be5d2f'),
 'timestamp': 1544696186, 'totalDifficulty': 34478,
 'transactions': [],
  'transactionsRoot': HexBytes('0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')})


Many of the typical things you'll want to do will be in the :class:`cf.cpc <cpc_fusion.cpc.Cpc>` API,
so that is a good place to start.

If you want to dive straight into contracts, check out the section on :ref:`contracts`,
including a :ref:`contract_example`, and how to create a contract instance using
:meth:`cf.cpc.contract() <cpc_fusion.cpc.Cpc.contract>`.
