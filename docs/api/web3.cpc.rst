web3.cpc API
=============

.. py:module:: web3.cpc

.. py:class:: Cpc

The ``web3.cpc`` object exposes the following properties and methods to
interact with the RPC APIs under the ``cpc_`` namespace.

Often, when a property or method returns a mapping of keys to values, it
will return an ``AttributeDict`` which acts like a ``dict`` but you can
access the keys as attributes and cannot modify its fields. For example,
you can find the latest block number in these two ways:

    .. code-block:: python

        >>> block = web3.cpc.getBlock('latest')
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


Properties
----------

The following properties are available on the ``web3.cpc`` namespace.


.. py:attribute:: Cpc.defaultAccount

    The ethereum address that will be used as the default ``from`` address for
    all transactions.


.. py:attribute:: Cpc.defaultBlock

    The default block number that will be used for any RPC methods that accept
    a block identifier.  Defaults to ``'latest'``.


.. py:attribute:: Cpc.syncing

    * Delegates to ``cpc_syncing`` RPC Method

    Returns either ``False`` if the node is not syncing or a dictionary
    showing sync status.

    .. code-block:: python

        >>> web3.cpc.syncing
        AttributeDict({
            'currentBlock': 2177557,
            'highestBlock': 2211611,
            'knownStates': 0,
            'pulledStates': 0,
            'startingBlock': 2177365,
        })


.. py:attribute:: Cpc.coinbase

    * Delegates to ``cpc_coinbase`` RPC Method

    Returns the current *Coinbase* address.

    .. code-block:: python

        >>> web3.cpc.coinbase
        '0xd3cda913deb6f67967b99d67acdfa1712c293601'


.. py:attribute:: Cpc.mining

    * Delegates to ``cpc_mining`` RPC Method

    Returns boolean as to whether the node is currently mining.

    .. code-block:: python

        >>> web3.cpc.mining
        False


.. py:attribute:: Cpc.hashrate

    * Delegates to ``cpc_hashrate`` RPC Method

    Returns the current number of hashes per second the node is mining with.

    .. code-block:: python

        >>> web3.cpc.hashrate
        906


.. py:attribute:: Cpc.gasPrice

    * Delegates to ``eth_gasPrice`` RPC Method

    Returns the current gas price in Wei.

    .. code-block:: python

        >>> web3.cpc.gasPrice
        20000000000


.. py:attribute:: Cpc.accounts

    * Delegates to ``eth_accounts`` RPC Method

    Returns the list of known accounts.

    .. code-block:: python

        >>> web3.cpc.accounts
        ['0xd3cda913deb6f67967b99d67acdfa1712c293601']


.. py:attribute:: Cpc.blockNumber

    * Delegates to ``eth_blockNumber`` RPC Method

    Returns the number of the most recent block

    .. code-block:: python

        >>> web3.cpc.blockNumber
        2206939


Methods
-------

The following methods are available on the ``web3.cpc`` namespace.


.. py:method:: Cpc.getBalance(account, block_identifier=cpc.defaultBlock)

    * Delegates to ``eth_getBalance`` RPC Method

    Returns the balance of the given ``account`` at the block specified by
    ``block_identifier``.

    ``account`` may be a hex address or an ENS name

    .. code-block:: python

        >>> web3.cpc.getBalance('0xd3cda913deb6f67967b99d67acdfa1712c293601')
        77320681768999138915


.. py:method:: Cpc.getStorageAt(account, position, block_identifier=cpc.defaultBlock)

    * Delegates to ``eth_getStorageAt`` RPC Method

    Returns the value from a storage position for the given ``account`` at the
    block specified by ``block_identifier``.

    ``account`` may be a hex address or an ENS name

    .. code-block:: python

        >>> web3.cpc.getStorageAt('0x6c8f2a135f6ed072de4503bd7c4999a1a17f824b', 0)
        '0x00000000000000000000000000000000000000000000000000120a0b063499d4'


.. py:method:: Cpc.getCode(account, block_identifier=cpc.defaultBlock)

    * Delegates to ``eth_getCode`` RPC Method

    Returns the bytecode for the given ``account`` at the block specified by
    ``block_identifier``.

    ``account`` may be a hex address or an ENS name

    .. code-block:: python

        # For a contract address.
        >>> web3.cpc.getCode('0x6c8f2a135f6ed072de4503bd7c4999a1a17f824b')
        '0x6060604052361561027c5760e060020a60003504630199.....'
        # For a private key address.
        >>> web3.cpc.getCode('0xd3cda913deb6f67967b99d67acdfa1712c293601')
        '0x'


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
         'mixHash': HexBytes('0x0000000000000000000000000000000000000000000000000000000000000000'),
         'nonce': HexBytes('0x0000000000000000'),
         'number': 100,
         'parentHash': HexBytes('0x7ff55edcbd638510900c0b4a5d5c6cbe66f8f1ff61f66a30f12bd4e1d263d89a'),
         'receiptsRoot': HexBytes('0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421'),
         'size': 934,
         'stateRoot': HexBytes('0x7761096fe7777161e4e66463e17df6a2b555054c369418295703a9ea93008bca'),
         'timestamp': 1543488712,
         'totalDifficulty': 201,
         'transactions': [],
         'transactionsRoot': HexBytes('0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')})


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


.. py:method:: Cpc.getCurrentTerm

    * Delegates to ``eth_getCurrentTerm`` RPC Method

    Returns CurrentTerm.

    .. code-block:: python

        >>> cf.cpc.getCurrentTerm
        166


.. py:method:: Cpc.getCurrentView

    * Delegates to ``eth_getCurrentRound`` RPC Method

    Returns CurrentView.

    .. code-block:: python

        >>> cf.cpc.getCurrentView
        1


.. py:method:: Cpc.getCommittees

    * Delegates to ``eth_getCommittees`` RPC Method

    Returns Committee Slice.

    .. code-block:: python

        >>> cf.cpc..getCommittees
        [{'Epoch': 1, 'Round': 1, 'Producer': '0x0000000000000000000000000000000000000001', 'PublicKey': '012345', 'Block': 1111}, {'Epoch': 1, 'Round': 2, 'Producer': '0x0000000000000000000000000000000000000002', 'PublicKey': '012345', 'Block': 1112}, {'Epoch': 1, 'Round': 3, 'Producer': '0x0000000000000000000000000000000000000003', 'PublicKey': '012345', 'Block': 1113}, {'Epoch': 1, 'Round': 4, 'Producer': '0x0000000000000000000000000000000000000004', 'PublicKey': '012345', 'Block': 1114}, {'Epoch': 1, 'Round': 5, 'Producer': '0x0000000000000000000000000000000000000005', 'PublicKey': '012345', 'Block': 1115}, {'Epoch': 1, 'Round': 6, 'Producer': '0x0000000000000000000000000000000000000006', 'PublicKey': '012345', 'Block': 1116}, {'Epoch': 1, 'Round': 7, 'Producer': '0x0000000000000000000000000000000000000007', 'PublicKey': '012345', 'Block': 1117}]



.. py:method:: Cpc.getBlockTransactionCount(block_identifier)

    * Delegates to ``eth_getBlockTransactionCountByNumber`` or
      ``eth_getBlockTransactionCountByHash`` RPC Methods

    Returns the number of transactions in the block specified by
    ``block_identifier``.  Delegates to
    ``eth_getBlockTransactionCountByNumber`` if ``block_identifier`` is an
    integer or one of the predefined block parameters ``'latest', 'earliest',
    'pending'``, otherwise delegates to ``eth_getBlockTransactionCountByHash``.

    .. code-block:: python

        >>> web3.cpc.getBlockTransactionCount(46147)
        1
        >>> web3.cpc.getBlockTransactionCount('0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd')  # block 46147
        1




.. py:method:: Cpc.getTransaction(transaction_hash)

    * Delegates to ``eth_getTransactionByHAsh`` RPC Method

    Returns the transaction specified by ``transaction_hash``

    .. code-block:: python

        >>> web3.cpc.getTransaction('0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060')
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


.. py:method:: Cpc.getTransactionFromBlock(block_identifier, transaction_index)

  .. note:: This method is deprecated and replaced by
    ``Cpc.getTransactionByBlock``


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

        >>> web3.cpc.getTransactionFromBlock(46147, 0)
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
        >>> web3.cpc.getTransactionFromBlock('0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd', 0)
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


.. py:method:: Cpc.waitForTransactionReceipt(transaction_hash, timeout=120)

    Waits for the transaction specified by ``transaction_hash`` to be included in a block, then
    returns its transaction receipt.

    Optionally, specify a ``timeout`` in seconds. If timeout elapses before the transaction
    is added to a block, then :meth:`~Cpc.waitForTransactionReceipt` raises a
    :class:`web3.exceptions.TimeExhausted` exception.

    .. code-block:: python

        >>> web3.cpc.waitForTransactionReceipt('0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060')
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


.. py:method:: Cpc.getTransactionReceipt(transaction_hash)

    * Delegates to ``eth_getTransactionReceipt`` RPC Method

    Returns the transaction receipt specified by ``transaction_hash``.  If the transaction has not yet been mined returns ``None``

    .. code-block:: python

        >>> web3.cpc.getTransactionReceipt('0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060')  # not yet mined
        None
        # wait for it to be mined....
        >>> web3.cpc.getTransactionReceipt('0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060')
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


.. py:method:: Cpc.getTransactionCount(account, block_identifier=web3.cpc.defaultBlock)

    * Delegates to ``eth_getTransactionCount`` RPC Method

    Returns the number of transactions that have been sent from ``account`` as
    of the block specified by ``block_identifier``.

    ``account`` may be a hex address or an ENS name

    .. code-block:: python

        >>> web3.cpc.getTransactionCount('0xd3cda913deb6f67967b99d67acdfa1712c293601')
        340


.. py:method:: Cpc.sendTransaction(transaction)

    * Delegates to ``eth_sendTransaction`` RPC Method

    Signs and sends the given ``transaction``

    The ``transaction`` parameter should be a dictionary with the following fields.

    * ``from``: ``bytes or text``, hex address or ENS name - (optional, default:
      ``web3.cpc.defaultAccount``) The address the transaction is send from.
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
    :meth:`~web3.cpc.Cpc.estimateGas()` function with an additional buffer of ``100000``
    gas up to the ``gasLimit`` of the latest block.  In the event that the
    value returned by :meth:`~web3.cpc.Cpc.estimateGas()` method is greater than the
    ``gasLimit`` a ``ValueError`` will be raised.


    .. code-block:: python

        >>> web3.cpc.sendTransaction({'to': '0xd3cda913deb6f67967b99d67acdfa1712c293601', 'from': web3.cpc.coinbase, 'value': 12345})
        '0xe670ec64341771606e55d6b4ca35a1a6b75ee3d5145a99d05921026d1527331'


.. py:method:: Cpc.sendRawTransaction(raw_transaction)

    * Delegates to ``eth_sendRawTransaction`` RPC Method

    Sends a signed and serialized transaction. Returns the transaction hash.

    .. code-block:: python

        >>> signed_txn = w3.cpc.account.signTransaction(dict(
            nonce=w3.cpc.getTransactionCount(w3.cpc.coinbase),
            gasPrice=w3.cpc.gasPrice,
            gas=100000,
            to='0xd3cda913deb6f67967b99d67acdfa1712c293601',
            value=12345,
            data=b'',
          ),
          private_key_for_senders_account,
        )
        >>> w3.cpc.sendRawTransaction(signed_txn.rawTransaction)
        '0xe670ec64341771606e55d6b4ca35a1a6b75ee3d5145a99d05921026d1527331'


.. py:method:: Cpc.replaceTransaction(transaction_hash, new_transaction)

    * Delegates to ``eth_sendTransaction`` RPC Method

    Sends a transaction that replaces the transaction with ``transaction_hash``.

    The ``transaction_hash`` must be the hash of a pending transaction.

    The ``new_transaction`` parameter should be a dictionary with transaction fields
    as required by :meth:`~web3.cpc.Cpc.sendTransaction`. It will be used to entirely
    replace the transaction of ``transaction_hash`` without using any of the pending
    transaction's values.

    If the ``new_transaction`` specifies a ``nonce`` value, it must match the pending
    transaction's nonce.

    If the ``new_transaction`` specifies a ``gasPrice`` value, it must be greater than
    the pending transaction's ``gasPrice``.

    If the ``new_transaction`` does not specify a ``gasPrice`` value, the highest of the
    following 2 values will be used:

    * The pending transaction's ``gasPrice`` * 1.1 - This is typically the minimum
      ``gasPrice`` increase a node requires before it accepts a replacement transaction.
    * The ``gasPrice`` as calculated by the current gas price strategy(See :ref:`Gas_Price`).

    This method returns the transaction hash of the replacement transaction.

    .. code-block:: python

        >>> tx = web3.cpc.sendTransaction({
                'to': '0xd3cda913deb6f67967b99d67acdfa1712c293601',
                'from': web3.cpc.coinbase,
                'value': 1000
            })
        '0xe670ec64341771606e55d6b4ca35a1a6b75ee3d5145a99d05921026d1527331'
        >>> web3.cpc.replaceTransaction('0xe670ec64341771606e55d6b4ca35a1a6b75ee3d5145a99d05921026d1527331', {
                'to': '0xd3cda913deb6f67967b99d67acdfa1712c293601',
                'from': web3.cpc.coinbase,
                'value': 2000
            })


.. py:method:: Cpc.modifyTransaction(transaction_hash, **transaction_params)

    * Delegates to ``eth_sendTransaction`` RPC Method

    Sends a transaction that modifies the transaction with ``transaction_hash``.

    ``transaction_params`` are keyword arguments that correspond to valid transaction
    parameters as required by :meth:`~web3.cpc.Cpc.sendTransaction`. The parameter values
    will override the pending transaction's values to create the replacement transaction
    to send.

    The same validation and defaulting rules of :meth:`~web3.cpc.Cpc.replaceTransaction` apply.

    This method returns the transaction hash of the newly modified transaction.

    .. code-block:: python

        >>> tx = web3.cpc.sendTransaction({
                'to': '0xd3cda913deb6f67967b99d67acdfa1712c293601',
                'from': web3.cpc.coinbase,
                'value': 1000
            })
        '0xe670ec64341771606e55d6b4ca35a1a6b75ee3d5145a99d05921026d1527331'
        >>> web3.cpc.modifyTransaction('0xe670ec64341771606e55d6b4ca35a1a6b75ee3d5145a99d05921026d1527331', value=2000)


.. py:method:: Cpc.sign(account, data=None, hexstr=None, text=None)

    * Delegates to ``eth_sign`` RPC Method

    Caller must specify exactly one of: ``data``, ``hexstr``, or ``text``.

    Signs the given data with the private key of the given ``account``.
    The account must be unlocked.

    ``account`` may be a hex address or an ENS name

    .. code-block:: python

        >>> web3.cpc.sign(
              '0xd3cda913deb6f67967b99d67acdfa1712c293601',
              text='some-text-tö-sign')
        '0x1a8bbe6eab8c72a219385681efefe565afd3accee35f516f8edf5ae82208fbd45a58f9f9116d8d88ba40fcd29076d6eada7027a3b412a9db55a0164547810cc401'

        >>> web3.cpc.sign(
              '0xd3cda913deb6f67967b99d67acdfa1712c293601',
              data=b'some-text-t\xc3\xb6-sign')
        '0x1a8bbe6eab8c72a219385681efefe565afd3accee35f516f8edf5ae82208fbd45a58f9f9116d8d88ba40fcd29076d6eada7027a3b412a9db55a0164547810cc401'

        >>> web3.cpc.sign(
              '0xd3cda913deb6f67967b99d67acdfa1712c293601',
              hexstr='0x736f6d652d746578742d74c3b62d7369676e')
        '0x1a8bbe6eab8c72a219385681efefe565afd3accee35f516f8edf5ae82208fbd45a58f9f9116d8d88ba40fcd29076d6eada7027a3b412a9db55a0164547810cc401'


.. py:method:: Cpc.call(transaction, block_identifier=web3.cpc.defaultBlock)

    * Delegates to ``eth_call`` RPC Method

    Executes the given transaction locally without creating a new transaction
    on the blockchain.  Returns the return value of the executed contract.

    The ``transaction`` parameter is handled in the same manner as the
    :meth:`~web3.cpc.Cpc.sendTransaction()` method.

    .. code-block:: python

        >>> myContract.functions.setVar(1).transact()
        HexBytes('0x79af0c7688afba7588c32a61565fd488c422da7b5773f95b242ea66d3d20afda')
        >>> myContract.functions.getVar().call()
        1
        # The above call equivalent to the raw call:
        >>> we3.cpc.call({'value': 0, 'gas': 21736, 'gasPrice': 1, 'to': '0xc305c901078781C232A2a521C2aF7980f8385ee9', 'data': '0x477a5c98'})
        HexBytes('0x0000000000000000000000000000000000000000000000000000000000000001')

    In most cases it is better to make contract function call through the :py:class:`web3.contract.Contract` interface.


.. py:method:: Cpc.estimateGas(transaction, block_identifier=None)

    * Delegates to ``eth_estimateGas`` RPC Method

    Executes the given transaction locally without creating a new transaction
    on the blockchain.  Returns amount of gas consumed by execution which can
    be used as a gas estimate.

    The ``transaction`` and ``block_identifier`` parameters are handled in the
    same manner as the :meth:`~web3.cpc.call()` method.

    .. code-block:: python

        >>> web3.cpc.estimateGas({'to': '0xd3cda913deb6f67967b99d67acdfa1712c293601', 'from': web3.cpc.coinbase, 'value': 12345})
        21000

    .. note::
        The parameter ``block_identifier`` is not enabled in geth nodes,
        hence passing a value of ``block_identifier`` when connected to a geth
        nodes would result in an error like:  ``ValueError: {'code': -32602, 'message': 'too many arguments, want at most 1'}``


.. py:method:: Cpc.generateGasPrice(transaction_params=None)

    Uses the selected gas price strategy to calculate a gas price. This method
    returns the gas price denominated in wei.

    The `transaction_params` argument is optional however some gas price strategies
    may require it to be able to produce a gas price.

    .. code-block:: python

        >>> Web3.cpc.generateGasPrice()
        20000000000

    .. note::
        For information about how gas price can be customized in web3 see
        :ref:`Gas_Price`.

.. py:method:: Cpc.setGasPriceStrategy(gas_price_strategy)

    Set the selected gas price strategy. It must be a method of the signature
    ``(web3, transaction_params)`` and return a gas price denominated in wei.

Filters
-------

The following methods are available on the ``web3.cpc`` object for interacting
with the filtering API.


.. py:method:: Cpc.filter(filter_params)

    * Delegates to ``eth_newFilter``, ``eth_newBlockFilter``, and
      ``eth_newPendingTransactionFilter`` RPC Methods.

    This method delegates to one of three RPC methods depending on the value of
    ``filter_params``.

    * If ``filter_params`` is the string ``'pending'`` then a new filter is
      registered using the ``eth_newPendingTransactionFilter`` RPC method.
      This will create a new filter that will be called for each new unmined
      transaction that the node receives.
    * If ``filter_params`` is the string ``'latest'`` then a new filter is
      registered using the ``eth_newBlockFilter`` RPC method.  This will create
      a new filter that will be called each time the node receives a new block.
    * If ``filter_params`` is a dictionary then a new filter is registered
      using the ``eth_newFilter`` RPC method.  This will create a new filter
      that will be called for all log entries that match the provided
      ``filter_params``.

    This method returns a ``web3.utils.filters.Filter`` object which can then
    be used to either directly fetch the results of the filter or to register
    callbacks which will be called with each result of the filter.

    When creating a new log filter, the ``filter_params`` should be a
    dictionary with the following keys.

    * ``fromBlock``: ``integer/tag`` - (optional, default: "latest") Integer
      block number, or "latest" for the last mined block or "pending",
      "earliest" for not yet mined transactions.
    * ``toBlock``: ``integer/tag`` - (optional, default: "latest") Integer
      block number, or "latest" for the last mined block or "pending",
      "earliest" for not yet mined transactions.
    * ``address``: ``string`` or list of ``strings``, each 20 Bytes -
      (optional) Contract address or a list of addresses from which logs should
      originate.
    * ``topics``: list of 32 byte ``strings`` or ``null`` - (optional) Array of
      topics that should be used for filtering.  Topics are order-dependent.
      This parameter can also be a list of topic lists in which case filtering
      will match any of the provided topic arrays.


    See :doc:`./filters` for more information about filtering.

    .. code-block:: python

        >>> web3.cpc.filter('latest')
        <BlockFilter at 0x10b72dc28>
        >>> web3.cpc.filter('pending')
        <TransactionFilter at 0x10b780340>
        >>> web3.cpc.filter({'fromBlock': 1000000, 'toBlock': 1000100, 'address': '0x6c8f2a135f6ed072de4503bd7c4999a1a17f824b'})
        <LogFilter at 0x10b7803d8>

.. py:method:: Cpc.getFilterChanges(self, filter_id)

    * Delegates to ``eth_getFilterChanges`` RPC Method.

    Returns all new entries which occurred since the last call to this method
    for the given ``filter_id``

    .. code-block:: python

        >>> filt = web3.cpc.filter()
        >>> web3.cpc.getFilterChanges(filt.filter_id)
        [
            {
                'address': '0xdc3a9db694bcdd55ebae4a89b22ac6d12b3f0c24',
                'blockHash': '0xb72256286ca528e09022ffd408856a73ef90e7216ac560187c6e43b4c4efd2f0',
                'blockNumber': 2217196,
                'data': '0x0000000000000000000000000000000000000000000000000000000000000001',
                'logIndex': 0,
                'topics': ['0xe65b00b698ba37c614af350761c735c5f4a82b4ab365a1f1022d49d9dfc8e930',
                '0x000000000000000000000000754c50465885f1ed1fa1a55b95ee8ecf3f1f4324',
                '0x296c7fb6ccafa3e689950b947c2895b07357c95b066d5cdccd58c301f41359a3'],
                'transactionHash': '0xfe1289fd3915794b99702202f65eea2e424b2f083a12749d29b4dd51f6dce40d',
                'transactionIndex': 1,
            },
            ...
        ]


.. py:method:: Cpc.getFilterLogs(self, filter_id)

    * Delegates to ``eth_getFilterLogs`` RPC Method.

    Returns all entries for the given ``filter_id``

    .. code-block:: python

        >>> filt = web3.cpc.filter()
        >>> web3.cpc.getFilterLogs(filt.filter_id)
        [
            {
                'address': '0xdc3a9db694bcdd55ebae4a89b22ac6d12b3f0c24',
                'blockHash': '0xb72256286ca528e09022ffd408856a73ef90e7216ac560187c6e43b4c4efd2f0',
                'blockNumber': 2217196,
                'data': '0x0000000000000000000000000000000000000000000000000000000000000001',
                'logIndex': 0,
                'topics': ['0xe65b00b698ba37c614af350761c735c5f4a82b4ab365a1f1022d49d9dfc8e930',
                '0x000000000000000000000000754c50465885f1ed1fa1a55b95ee8ecf3f1f4324',
                '0x296c7fb6ccafa3e689950b947c2895b07357c95b066d5cdccd58c301f41359a3'],
                'transactionHash': '0xfe1289fd3915794b99702202f65eea2e424b2f083a12749d29b4dd51f6dce40d',
                'transactionIndex': 1,
            },
            ...
        ]


.. py:method:: Cpc.uninstallFilter(self, filter_id)

    * Delegates to ``eth_uninstallFilter`` RPC Method.

    Uninstalls the filter specified by the given ``filter_id``.  Returns
    boolean as to whether the filter was successfully uninstalled.

    .. code-block:: python

        >>> filt = web3.cpc.filter()
        >>> web3.cpc.uninstallFilter(filt.filter_id)
        True
        >>> web3.cpc.uninstallFilter(filt.filter_id)
        False  # already uninstalled.


.. py:method:: Cpc.getLogs(filter_params)

    This is the equivalent of: creating a new
    filter, running :meth:`~Cpc.getFilterLogs`, and then uninstalling the filter. See
    :meth:`~Cpc.filter` for details on allowed filter parameters.


Contracts
---------

.. py:method:: Cpc.contract(address=None, contract_name=None, ContractFactoryClass=Contract, **contract_factory_kwargs)

    If ``address`` is provided, then this method will return an instance of the
    contract defined by ``abi``. The address may be a hex string,
    or an ENS name like ``'mycontract.cpc'``.

    .. code-block:: python

        from web3 import Web3

        w3 = Web3(...)

        contract = w3.cpc.contract(address='0x000000000000000000000000000000000000dead', abi=...)

        # alternatively:
        contract = w3.cpc.contract(address='mycontract.cpc', abi=...)

    .. note::

        If you use an ENS name to initialize a contract, the contract will be looked up by
        name on each use. If the name could ever change maliciously, first
        :ref:`ens_get_address`, and then create the contract with the hex address.


    If ``address`` is *not* provided, the newly created contract class will be returned. That
    class will then be initialized by supplying the address.

    .. code-block:: python

        from web3 import Web3

        w3 = Web3(...)

        Contract = w3.cpc.contract(abi=...)

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

    Modify the default contract factory from ``Contract`` to ``contractFactoryClass``.
    Future calls to ``Cpc.contract()`` will then default to ``contractFactoryClass``.

    An example of an alternative Contract Factory is ``ConciseContract``.
