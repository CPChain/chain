.. _fusion-api:

Fusion API
=============


Installation
---------------

CPC fusion can be installed by
using ``pip`` as follows:

.. code-block:: shell

   $ pip install cpc-fusion

.. Note::

    If you ``pip`` is referring to the one in python2, please use the following command instead.

.. code-block:: shell

   $ pip3 install cpc-fusion

Note that CPC fusion is  tested on Ubuntu 18.04 and python 3.6.7.
A lower version of Ubuntu and python may incur an error or unsuccessful installation.


Installation from source can be done from the root of the project with the
following command.

.. code-block:: shell

   $ pip install .


.. _fusion-api-using:

Using Fusion
----------------

To use the web3 library, you are required to initialize the
:class:`~web3.Web3` class.

Before connecting, you must set up a local chain or sync with our Mainnet.
Please check :ref:`quick-start` for detailed information.



Use the ``auto`` module to :ref:`guess at common node connection options
<automatic_provider_detection>`.

.. code-block:: python

    >>> from cpc_fusion import Web3
    >>> cf = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))
    >>> cf.cpc.blockNumber
    34341


.. NOTE::

    If you get the result ``UnhandledRequest: No providers responded to the RPC request``,
    then you are not connected to a node.

.. _first_w3_use:





.. py:module:: cpc_fusion.cpc

.. py:class:: Cpc

The ``cpc_fusion.cpc`` object exposes the following properties and methods to
interact with the RPC APIs under the ``cpc_`` namespace.

Often, when a property or method returns a map from keys to values, it
also returns an ``AttributeDict`` which acts like a ``dict`` that you can
access the keys as attributes but cannot modify its fields. For example,
you can find the latest block number in these two ways:

    .. code-block:: python

        >>> block = cf.cpc.getBlock('latest')
        AttributeDict({
          'hash': '0xe8ad537a261e6fff80d551d8d087ee0f2202da9b09b64d172a5f45e818eb472a',
          'number': 4022281,
          # ... etc ...
        })

        >>> block['number']
        4022281
        >>> block.number
        4022281

        >>> block.number = 4022282
        Traceback # ... etc ...
        TypeError: This data is immutable -- create a copy instead of modifying

The following methods are available on the ``cpc_fusion.cpc`` namespace.

Transaction API
------------------


Cpc.getBlockTransactionCount
++++++++++++++++++++++++++++++++++++++++++++++++++++++

.. py:method:: Cpc.getBlockTransactionCount(block_identifier)


    * Delegates to ``eth_getBlockTransactionCountByNumber`` or
      ``eth_getBlockTransactionCountByHash`` RPC Methods

    Returns the number of transactions in the block specified by
    ``block_identifier``.  Delegates to
    ``eth_getBlockTransactionCountByNumber`` if ``block_identifier`` is an
    integer or one of the predefined block parameters ``'latest', 'earliest',
    'pending'``, otherwise delegates to ``eth_getBlockTransactionCountByHash``.

    .. code-block:: python

        >>> cf.cpc.getBlockTransactionCount(46147)
        1
        >>> cf.cpc.getBlockTransactionCount('0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd')  # block 46147
        1



Cpc.getTransaction
+++++++++++++++++++++++++++++++++++++++++++


.. py:method:: Cpc.getTransaction(transaction_hash)

    * Delegates to ``eth_getTransactionByHAsh`` RPC Method

    Returns the transaction specified by ``transaction_hash``

    .. code-block:: python

        >>> cf.cpc.getTransaction('0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060')
        AttributeDict({
            'blockHash': '0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd',
            'blockNumber': 46147,
            'from': '0xa1e4380a3b1f749673e270229993ee55f35663b4',
            'gas': 21000,
            'gasPrice': 50000000000000,
            'hash': '0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060',
            'input': '0x',
            'nonce': 0,
            'to': '0x5df9b87991262f6ba471f09758cde1c0fc1de734',
            'transactionIndex': 0,
            'value': 31337,
        })



Cpc.getTransactionFromBlock
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++


.. py:method:: Cpc.getTransactionFromBlock(block_identifier, transaction_index)

  .. note:: This method is obsolete and replaced by
    ``Cpc.getTransactionByBlock``

Cpc.getTransactionByBlock
+++++++++++++++++++++++++++++



.. py:method:: Cpc.getTransactionByBlock(block_identifier, transaction_index)

    * Delegates to ``eth_getTransactionByBlockNumberAndIndex`` or
      ``eth_getTransactionByBlockHashAndIndex`` RPC Methods

    Returns the transaction at the index specified by ``transaction_index``
    from the block specified by ``block_identifier``.  Delegates to
    ``eth_getTransactionByBlockNumberAndIndex`` if ``block_identifier`` is an
    integer or one of the predefined block parameters ``'latest', 'earliest',
    'pending'``, otherwise delegates to
    ``eth_getTransactionByBlockHashAndIndex``.

    .. code-block:: python

        >>> cf.cpc.getTransactionFromBlock(46147, 0)
        AttributeDict({
            'blockHash': '0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd',
            'blockNumber': 46147,
            'from': '0xa1e4380a3b1f749673e270229993ee55f35663b4',
            'gas': 21000,
            'gasPrice': 50000000000000,
            'hash': '0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060',
            'input': '0x',
            'nonce': 0,
            'to': '0x5df9b87991262f6ba471f09758cde1c0fc1de734',
            'transactionIndex': 0,
            'value': 31337,
        })
        >>> cf.cpc.getTransactionFromBlock('0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd', 0)
        AttributeDict({
            'blockHash': '0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd',
            'blockNumber': 46147,
            'from': '0xa1e4380a3b1f749673e270229993ee55f35663b4',
            'gas': 21000,
            'gasPrice': 50000000000000,
            'hash': '0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060',
            'input': '0x',
            'nonce': 0,
            'to': '0x5df9b87991262f6ba471f09758cde1c0fc1de734',
            'transactionIndex': 0,
            'value': 31337,
        })

Cpc.waitForTransactionReceipt
+++++++++++++++++++++++++++++++++++

.. py:method:: Cpc.waitForTransactionReceipt(transaction_hash, timeout=120)

    Waits for the transaction specified by ``transaction_hash`` to be included in a block, then
    returns its transaction receipt.

    Optionally, specify a ``timeout`` in seconds. If timeout elapses before the transaction
    is added to a block, then :meth:`~Cpc.waitForTransactionReceipt` raises a
    :class:`cpc_fusion.exceptions.TimeExhausted` exception.

    .. code-block:: python

        >>> cf.cpc.waitForTransactionReceipt('0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060')
        # If transaction is not yet in a block, time passes, while the thread sleeps...
        # ...
        # Then when the transaction is added to a block, its receipt is returned:
        AttributeDict({
            'blockHash': '0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd',
            'blockNumber': 46147,
            'contractAddress': None,
            'cumulativeGasUsed': 21000,
            'from': '0xa1e4380a3b1f749673e270229993ee55f35663b4',
            'gasUsed': 21000,
            'logs': [],
            'root': '96a8e009d2b88b1483e6941e6812e32263b05683fac202abc622a3e31aed1957',
            'to': '0x5df9b87991262f6ba471f09758cde1c0fc1de734',
            'transactionHash': '0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060',
            'transactionIndex': 0,
        })




Cpc.getTransactionReceipt
++++++++++++++++++++++++++++++


.. py:method:: Cpc.getTransactionReceipt(transaction_hash)

    * Delegates to ``eth_getTransactionReceipt`` RPC Method

    Returns the transaction receipt specified by ``transaction_hash``.  If the transaction has not yet been mined returns ``None``

    .. code-block:: python

        >>> cf.cpc.getTransactionReceipt('0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060')  # not yet mined
        None
        # wait for it to be mined....
        >>> cf.cpc.getTransactionReceipt('0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060')
        AttributeDict({
            'blockHash': '0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd',
            'blockNumber': 46147,
            'contractAddress': None,
            'cumulativeGasUsed': 21000,
            'from': '0xa1e4380a3b1f749673e270229993ee55f35663b4',
            'gasUsed': 21000,
            'logs': [],
            'root': '96a8e009d2b88b1483e6941e6812e32263b05683fac202abc622a3e31aed1957',
            'to': '0x5df9b87991262f6ba471f09758cde1c0fc1de734',
            'transactionHash': '0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060',
            'transactionIndex': 0,
        })

Cpc.getTransactionCount
++++++++++++++++++++++++++++++



.. py:method:: Cpc.getTransactionCount(account, block_identifier=cpc_fusion.cpc.defaultBlock)

    * Delegates to ``eth_getTransactionCount`` RPC Method

    Returns the number of transactions that have been sent from ``account`` as
    of the block specified by ``block_identifier``.

    ``account`` may be a hex address or an ENS name

    .. code-block:: python

        >>> cf.cpc.getTransactionCount('0xd3cda913deb6f67967b99d67acdfa1712c293601')
        340



Cpc.sendTransaction
++++++++++++++++++++++



.. py:method:: Cpc.sendTransaction(transaction)

    * Delegates to ``eth_sendTransaction`` RPC Method

    Signs and sends the given ``transaction``

    The ``transaction`` parameter should be a dictionary with the following fields.

    * ``from``: ``bytes or text``, hex address or ENS name - (optional, default:
      ``cpc_fusion.cpc.defaultAccount``) The address the transaction is send from.
    * ``to``: ``bytes or text``, hex address or ENS name - (optional when creating new
      contract) The address the transaction is directed to.
    * ``gas``: ``integer`` - (optional, default: 90000) Integer of the gas
      provided for the transaction execution. It will return unused gas.
    * ``gasPrice``: ``integer`` - (optional, default: To-Be-Determined) Integer
      of the gasPrice used for each paid gas
    * ``value``: ``integer`` - (optional) Integer of the value send with this
      transaction
    * ``data``: ``bytes or text`` - The compiled code of a contract OR the hash
      of the invoked method signature and encoded parameters. For details see
      `Ethereum Contract ABI <https://github.com/ethereum/wiki/wiki/Ethereum-Contract-ABI>`_.
    * ``nonce``: ``integer`` - (optional) Integer of a nonce. This allows to
      overwrite your own pending transactions that use the same nonce.

    If the ``transaction`` specifies a ``data`` value but does not specify
    ``gas`` then the ``gas`` value will be populated using the
    :meth:`~cpc_fusion.cpc.Cpc.estimateGas()` function with an additional buffer of ``100000``
    gas up to the ``gasLimit`` of the latest block.  In the event that the
    value returned by :meth:`~cpc_fusion.cpc.Cpc.estimateGas()` method is greater than the
    ``gasLimit`` a ``ValueError`` will be raised.


    .. code-block:: python

        >>> cf.cpc.sendTransaction({'to': '0xd3cda913deb6f67967b99d67acdfa1712c293601', 'from': cf.cpc.coinbase, 'value': 12345})
        '0xe670ec64341771606e55d6b4ca35a1a6b75ee3d5145a99d05921026d1527331'



Cpc.sendRawTransaction
+++++++++++++++++++++++++


.. py:method:: Cpc.sendRawTransaction(raw_transaction)

    * Delegates to ``eth_sendRawTransaction`` RPC Method

    Sends a signed and serialized transaction. Returns the transaction hash.

    .. code-block:: python

        >>> signed_txn = cf.cpc.account.signTransaction(dict(
            nonce=cf.cpc.getTransactionCount(cf.cpc.coinbase),
            gasPrice=cf.cpc.gasPrice,
            gas=100000,
            to='0xd3cda913deb6f67967b99d67acdfa1712c293601',
            value=12345,
            data=b'',
          ),
          private_key_for_senders_account,
        )
        >>> cf.cpc.sendRawTransaction(signed_txn.rawTransaction)
        '0xe670ec64341771606e55d6b4ca35a1a6b75ee3d5145a99d05921026d1527331'




Block API
------------------------

Cpc.blockNumber
+++++++++++++++++++++

.. py:attribute:: Cpc.blockNumber

    * Delegates to ``eth_blockNumber`` RPC Method

    Returns the number of the most recent block

    .. code-block:: python

        >>> cf.cpc.blockNumber
        2206939



Cpc.getBlock
++++++++++++++++++++++

.. py:method:: Cpc.getBlock(block_identifier=cpc.defaultBlock, full_transactions=False)

    * Delegates to ``eth_getBlockByNumber`` or ``eth_getBlockByHash`` RPC Methods

    Returns the block specified by ``block_identifier``.  Delegates to
    ``eth_getBlockByNumber`` if ``block_identifier`` is an integer or one of
    the predefined block parameters ``'latest', 'earliest', 'pending'``,
    otherwise delegates to ``eth_getBlockByHash``.

    If ``full_transactions`` is ``True`` then the ``'transactions'`` key will
    contain full transactions objects.  Otherwise it will be an array of
    transaction hashes.

    .. code-block:: python

        >>> cf.cpc.getBlock(100)
        AttributeDict({'difficulty': 2,
         'extraData': HexBytes('0xdd85302e302e31876370636861696e88676f312e31302e34856c696e75780000'),
         'gasLimit': 4712388,
         'gasUsed': 0,
         'hash': HexBytes('0xf52f56f96b704e02cf67f797ccbf33a42a095cc00aa9c2be6530ee02b9d34ad7'),
         'logsBloom': HexBytes('0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'),
         'miner': '0xc05302AceBd0730E3A18A058d7d1CB1204C4a092',
         'number': 100,
         'parentHash': HexBytes('0x7ff55edcbd638510900c0b4a5d5c6cbe66f8f1ff61f66a30f12bd4e1d263d89a'),
         'receiptsRoot': HexBytes('0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421'),
         'size': 934,
         'stateRoot': HexBytes('0x7761096fe7777161e4e66463e17df6a2b555054c369418295703a9ea93008bca'),
         'timestamp': 1543488712,
         'totalDifficulty': 201,
         'transactions': [],
         'transactionsRoot': HexBytes('0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')})


Account API
------------------------

Cpc.getBalance
+++++++++++++++++++++


.. py:method:: Cpc.getBalance(account, block_identifier=cpc.defaultBlock)

    * Delegates to ``eth_getBalance`` RPC Method

    Returns the balance of the given ``account`` at the block specified by
    ``block_identifier``.

    ``account`` may be a hex address or an ENS name

    .. code-block:: python

        >>> cf.cpc.getBalance('0xd3cda913deb6f67967b99d67acdfa1712c293601')
        77320681768999138915

Cpc.newAccount
+++++++++++++++++



.. py:method:: newAccount(self, password)

    * Delegates to ``personal_newAccount`` RPC Method

    Generates a new account in the node's keychain encrypted with the
    given ``passphrase``.  Returns the address of the created account.

    .. code-block:: python

        >>> cf.personal.newAccount('1')
        '0x062F4db4DDbE5618412ADffa33b4CbC680634Fc8'



Cpc.lockAccount
++++++++++++++++

.. py:method:: lockAccount(self, account)

    * Delegates to ``personal_lockAccount`` RPC Method

    Locks the given ``account``.

    .. code-block:: python

        >>> cf.personal.lockAccount('0xd3cda913deb6f67967b99d67acdfa1712c293601')




Cpc.unlockAccount
+++++++++++++++++


.. py:method:: unlockAccount(self, account, passphrase, duration=None)

    * Delegates to ``personal_unlockAccount`` RPC Method

    Unlocks the given ``account`` for ``duration`` seconds.  If ``duration`` is
    ``None`` then the account will remain unlocked indefinitely.  Returns
    boolean as to whether the account was successfully unlocked.

    .. code-block:: python

        >>> cf.personal.unlockAccount('0xd3cda913deb6f67967b99d67acdfa1712c293601', 'wrong-passphrase')
        False
        >>> cf.personal.unlockAccount('0xd3cda913deb6f67967b99d67acdfa1712c293601', 'the-passphrase')
        True



Cpc.sendTransaction
++++++++++++++++++



.. py:method:: sendTransaction(self, transaction, passphrase)

    * Delegates to ``personal_sendTransaction`` RPC Method

    Sends the transaction.


Contract API
-----------------


Cpc.contract
+++++++++++++++++


.. py:method:: Cpc.contract(address=None, contract_name=None, ContractFactoryClass=Contract, **contract_factory_kwargs)

    If ``address`` is provided, then this method will return an instance of the
    contract defined by ``abi``. The address may be a hex string,
    or an ENS name like ``'mycontract.cpc'``.

    .. code-block:: python

        from cpc_fusion import Web3

        cf = Web3(...)

        contract = cf.cpc.contract(address='0x000000000000000000000000000000000000dead', abi=...)

        # alternatively:
        contract = cf.cpc.contract(address='mycontract.cpc', abi=...)

    .. note::

        If you use an ENS name to initialize a contract, the contract will be looked up by
        name on each use. If the name could ever change maliciously, first
        :ref:`ens_get_address`, and then create the contract with the hex address.


    If ``address`` is *not* provided, the newly created contract class will be returned. That
    class will then be initialized by supplying the address.

    .. code-block:: python

        from cpc_fusion import Web3

        cf = Web3(...)

        Contract = cf.cpc.contract(abi=...)

        # later, initialize contracts with the same metadata at different addresses:
        contract1 = Contract(address='0x000000000000000000000000000000000000dead')
        contract2 = Contract(address='mycontract.cpc')

    ``contract_name`` will be used as the name of the contract class.  If it is
    ``None`` then the name of the ``ContractFactoryClass`` will be used.

    ``ContractFactoryClass`` will be used as the base Contract class.

    The following arguments are accepted for contract class creation.

    - ``abi``
    - ``asm``
    - ``ast``
    - ``bytecode``
    - ``bytecode_runtime``
    - ``clone_bin``
    - ``dev_doc``
    - ``interface``
    - ``metadata``
    - ``opcodes``
    - ``src_map``
    - ``src_map_runtime``
    - ``user_doc``

    See :doc:`./contracts` for more information about how to use contracts.

.. py:method:: Cpc.setContractFactory(contractFactoryClass)

    Modifies the default contract factory from ``Contract`` to ``contractFactoryClass``.
    Future calls to ``Cpc.contract()`` will then default to ``contractFactoryClass``.

    An example of an alternative Contract Factory is ``ConciseContract``.



RNode API
----------------


Cpc.getRNodes
++++++++++++++++++++

.. py:method:: Cpc.getRNodes

    * Delegates to ``eth_getRNodes`` RPC Method

    Returns the array of address that become ``rnode`` as
    of the candidate of committee.

    .. code-block:: python

        >>> cf.cpc.getRNodes
        [{'Address': '0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a','Rpt': 16,'Status': 0},{'Address': '0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a','Rpt': 16,'Status': 1},]

        #!/usr/bin/env python
        # -*- coding: utf-8 -*-
        from cpc_fusion import Web3
        from cpc_fusion.middleware import geth_poa_middleware

        cf = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))
        # inject the poa compatibility middleware to the innermost layer
        cf.middleware_stack.inject(geth_poa_middleware, layer=0)

        print("rnode:")
        print(cf.cpc.getRNodes)


Cpc.getCurrentTerm
++++++++++++++++++++++++

.. py:method:: Cpc.getCurrentTerm

    * Delegates to ``eth_getCurrentTerm`` RPC Method

    Returns CurrentTerm.

    .. code-block:: python

        >>> cf.cpc.getCurrentTerm
        166


Cpc.getCurrentView
++++++++++++++++++++++

.. py:method:: Cpc.getCurrentView

    * Delegates to ``eth_getCurrentRound`` RPC Method

    Returns CurrentView.

    .. code-block:: python

        >>> cf.cpc.getCurrentView
        1


Cpc.getBlockGenerationInfo
+++++++++++++++++++++++++++++


.. py:method:: Cpc.getBlockGenerationInfo

    * Delegates to ``eth_getBlockGenerationInfo`` RPC Method

    Returns Committee Slice.

    .. code-block:: python

        >>> cf.cpc.getBlockGenerationInfo
        [{'View': 2, 'Term': 250, 'Proposer': '0x3a18598184ef84198db90c28fdfdfdf56544f747', 'BlockNumber': 3000, 'TermLen': 4}, {'View': 2, 'Term': 250, 'Proposer': '0xc05302acebd0730e3a18a058d7d1cb1204c4a092', 'BlockNumber': 3001, 'TermLen': 4}, {'View': 2, 'Term': 250, 'Proposer': '0xc05302acebd0730e3a18a058d7d1cb1204c4a092', 'BlockNumber': 3002, 'TermLen': 4}, {'View': 2, 'Term': 250, 'Proposer': '0xc05302acebd0730e3a18a058d7d1cb1204c4a092', 'BlockNumber': 3003, 'TermLen': 4}, {'View': 2, 'Term': 250, 'Proposer': '0x3a18598184ef84198db90c28fdfdfdf56544f747', 'BlockNumber': 3004, 'TermLen': 4}, {'View': 2, 'Term': 250, 'Proposer': '0x3a18598184ef84198db90c28fdfdfdf56544f747', 'BlockNumber': 3005, 'TermLen': 4}, {'View': 2, 'Term': 250, 'Proposer': '0x3a18598184ef84198db90c28fdfdfdf56544f747', 'BlockNumber': 3006, 'TermLen': 4}, {'View': 2, 'Term': 250, 'Proposer': '0x6e31e5b68a98dcd17264bd1ba547d0b3e874da1e', 'BlockNumber': 3007, 'TermLen': 4}]

