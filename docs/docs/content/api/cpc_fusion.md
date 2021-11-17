# Fusion API

## Installation

CPC fusion can be installed by using `pip` as follows:

``` {.shell}
$ pip install cpc-fusion
```

::: tip

If your `pip` is referring to the one in python2, please use the
following command instead.
:::

``` {.shell}
$ pip3 install cpc-fusion
```

Note that CPC fusion is tested on Ubuntu 18.04 and python 3.6.7. A lower
version of Ubuntu and python may incur an error or unsuccessful
installation.

Installation from source can be done from the root of the project with
the following command.

``` {.shell}
$ pip install .
```

## Using Fusion 

To use the cpc fusion library, you are required to initialize the
[CPC](#class-cpc-fusion-cpc-cpc) class.

Before connecting, you must set up a local chain or sync with our
Mainnet.

> 1.  To start a local chain, use the following commands
>
>     > ``` {.shell}
>     > $ cd ./examples/cpchain
>     > $ sudo ./cpchain-all.sh
>     > ```
>     >
>     > Note that starting a local chain may fail. You may try several
>     > times until success.
>
> 2.  To sync with Alpha Mainnet, use the following command
>
>     > ``` {.shell}
>     > $ build/bin/cpchain run --rpcaddr 127.0.0.0:8501 --port 30311
>     > ```

Please check [Quick Start in Detail](../quickstart/quickstart.md#quick-start-in-detail) for more
detailed information.

``` {.python}
>>> from cpc_fusion import Web3
>>> cf = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))
>>> cf.cpc.blockNumber
34341
```

::: tip

If you get the result
`UnhandledRequest: No providers responded to the RPC request`, then you
are not connected to a node.
:::

#### *class* cpc_fusion.cpc.Cpc 

The `cpc_fusion.cpc` object exposes the following properties and methods
to interact with the RPC APIs under the `cpc_` namespace.

Often, when a property or method returns a map from keys to values, it
also returns an `AttributeDict` which acts like a `dict` that you can
access the keys as attributes but cannot modify its fields. For example,
you can find the latest block number in these two ways:

> ``` {.python}
> >>> block = cf.cpc.getBlock('latest')
> AttributeDict({
>   'hash': '0xe8ad537a261e6fff80d551d8d087ee0f2202da9b09b64d172a5f45e818eb472a',
>   'number': 4022281,
>   # ... etc ...
> })
>
> >>> block['number']
> 4022281
> >>> block.number
> 4022281
>
> >>> block.number = 4022282
> Traceback # ... etc ...
> TypeError: This data is immutable -- create a copy instead of modifying
> ```

The following methods are available on the `cpc_fusion.cpc` namespace.

## Transaction API

### Cpc.gasPrice 

#### *class* Cpc.gasPrice 

> -   Delegates to `eth_gasPrice` RPC Method.
>
> Returns the current gas price in Wei.
>
> ``` {.python}
> >>> cf.cpc.gasPrice
> 18000000000
> ```

### Cpc.estimateGas 

#### *class* Cpc.estimateGas(transaction) 

> -   Delegates to `eth_estimateGas` RPC Method

Executes the given transaction locally without creating a new
transaction on the blockchain. Returns amount of gas consumed by
execution which can be used as a gas estimate.

The transaction parameter is handled in the same manner as the
`sendTransaction()` method.

> ::: tip
>
> The addresses in `transaction` should be the returned value of
> `toChecksumAddress(address)`. Non-checksum addresses are considered
> unsafe, and `cpc.estimateGas()` will return an error.
> :::
>
> ``` {.python}
> >>> cf.cpc.estimateGas({'to': cf.toChecksumAddress('0x9e61732d0b1c1674151a01ac0bba824c5b6258fb'), 'from': cf.cpc.coinbase, 'value': 12345})
> 21000
> ```

### Cpc.getBlockTransactionCount 

#### *class* Cpc.getBlockTransactionCount(block_identifier) 

> -   Delegates to `eth_getBlockTransactionCountByNumber` or
>     `eth_getBlockTransactionCountByHash` RPC Methods
>
> Returns the number of transactions in the block specified by
> `block_identifier`. Delegates to
> `eth_getBlockTransactionCountByNumber` if `block_identifier` is an
> integer or one of the predefined block parameters
> `'latest', 'earliest', 'pending'`, otherwise delegates to
> `eth_getBlockTransactionCountByHash`.
>
> ``` {.python}
> >>> cf.cpc.getBlockTransactionCount(46147)
> 1
> >>> cf.cpc.getBlockTransactionCount('0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd')  # block 46147
> 1
> ```

### Cpc.getTransaction 

#### *class* Cpc.getTransaction(transaction_hash) 

> -   Delegates to `eth_getTransactionByHAsh` RPC Method
>
> Returns the transaction specified by `transaction_hash`
>
> ``` {.python}
> >>> cf.cpc.getTransaction('0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060')
> AttributeDict({
>     'blockHash': '0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd',
>     'blockNumber': 46147,
>     'from': '0xa1e4380a3b1f749673e270229993ee55f35663b4',
>     'gas': 21000,
>     'gasPrice': 50000000000000,
>     'hash': '0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060',
>     'input': '0x',
>     'nonce': 0,
>     'to': '0x5df9b87991262f6ba471f09758cde1c0fc1de734',
>     'transactionIndex': 0,
>     'value': 31337,
> })
> ```

### Cpc.getTransactionFromBlock 

#### *class* Cpc.getTransactionFromBlock(block_identifier, transaction_index) 

> ::: tip
>
> This method is obsolete and replaced by `Cpc.getTransactionByBlock`
> :::

### Cpc.getTransactionByBlock 

#### *class* Cpc.getTransactionByBlock(block_identifier, transaction_index) 

> -   Delegates to `eth_getTransactionByBlockNumberAndIndex` or
>     `eth_getTransactionByBlockHashAndIndex` RPC Methods
>
> Returns the transaction at the index specified by `transaction_index`
> from the block specified by `block_identifier`. Delegates to
> `eth_getTransactionByBlockNumberAndIndex` if `block_identifier` is an
> integer or one of the predefined block parameters
> `'latest', 'earliest', 'pending'`, otherwise delegates to
> `eth_getTransactionByBlockHashAndIndex`.
>
> ``` {.python}
> >>> cf.cpc.getTransactionFromBlock(46147, 0)
> AttributeDict({
>     'blockHash': '0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd',
>     'blockNumber': 46147,
>     'from': '0xa1e4380a3b1f749673e270229993ee55f35663b4',
>     'gas': 21000,
>     'gasPrice': 50000000000000,
>     'hash': '0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060',
>     'input': '0x',
>     'nonce': 0,
>     'to': '0x5df9b87991262f6ba471f09758cde1c0fc1de734',
>     'transactionIndex': 0,
>     'value': 31337,
> })
> >>> cf.cpc.getTransactionFromBlock('0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd', 0)
> AttributeDict({
>     'blockHash': '0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd',
>     'blockNumber': 46147,
>     'from': '0xa1e4380a3b1f749673e270229993ee55f35663b4',
>     'gas': 21000,
>     'gasPrice': 50000000000000,
>     'hash': '0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060',
>     'input': '0x',
>     'nonce': 0,
>     'to': '0x5df9b87991262f6ba471f09758cde1c0fc1de734',
>     'transactionIndex': 0,
>     'value': 31337,
> })
> ```

### Cpc.waitForTransactionReceipt 

#### *class* Cpc.waitForTransactionReceipt(transaction_hash, timeout=120) 

> Waits for the transaction specified by `transaction_hash` to be
> included in a block, then returns its transaction receipt.
>
> Optionally, specify a `timeout` in seconds. If timeout elapses before
> the transaction is added to a block, then
> [Cpc.waitForTransactionReceipt](#cpc-waitfortransactionreceipt) raises
> a `cpc_fusion.exceptions.TimeExhausted`{.interpreted-text
> role="class"} exception.
>
> ``` {.python}
> >>> cf.cpc.waitForTransactionReceipt('0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060')
> # If transaction is not yet in a block, time passes, while the thread sleeps...
> # ...
> # Then when the transaction is added to a block, its receipt is returned:
> AttributeDict({
>     'blockHash': '0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd',
>     'blockNumber': 46147,
>     'contractAddress': None,
>     'cumulativeGasUsed': 21000,
>     'from': '0xa1e4380a3b1f749673e270229993ee55f35663b4',
>     'gasUsed': 21000,
>     'logs': [],
>     'root': '96a8e009d2b88b1483e6941e6812e32263b05683fac202abc622a3e31aed1957',
>     'to': '0x5df9b87991262f6ba471f09758cde1c0fc1de734',
>     'transactionHash': '0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060',
>     'transactionIndex': 0,
> })
> ```

### Cpc.getTransactionReceipt 

#### *class* Cpc.getTransactionReceipt(transaction_hash) 

> -   Delegates to `eth_getTransactionReceipt` RPC Method
>
> Returns the transaction receipt specified by `transaction_hash`. If
> the transaction has not yet been mined returns `None`
>
> ``` {.python}
> >>> cf.cpc.getTransactionReceipt('0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060')  # not yet mined
> None
> # wait for it to be mined....
> >>> cf.cpc.getTransactionReceipt('0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060')
> AttributeDict({
>     'blockHash': '0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd',
>     'blockNumber': 46147,
>     'contractAddress': None,
>     'cumulativeGasUsed': 21000,
>     'from': '0xa1e4380a3b1f749673e270229993ee55f35663b4',
>     'gasUsed': 21000,
>     'logs': [],
>     'root': '96a8e009d2b88b1483e6941e6812e32263b05683fac202abc622a3e31aed1957',
>     'to': '0x5df9b87991262f6ba471f09758cde1c0fc1de734',
>     'transactionHash': '0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060',
>     'transactionIndex': 0,
> })
> ```

### Cpc.getTransactionCount 

#### *class* Cpc.getTransactionCount(account, block_identifier=cpc_fusion.cpc.defaultBlock) 

> -   Delegates to `eth_getTransactionCount` RPC Method
>
> Returns the number of transactions that have been sent from `account`
> as of the block specified by `block_identifier`.
>
> `account` may be a hex address or an ENS name
>
> ``` {.python}
> >>> cf.cpc.getTransactionCount('0xd3cda913deb6f67967b99d67acdfa1712c293601')
> 340
> ```

### Cpc.sendTransaction 

#### *class* Cpc.sendTransaction(transaction) 

> -   Delegates to `eth_sendTransaction` RPC Method
>
> Signs and sends the given `transaction`
>
> The `transaction` parameter should be a dictionary with the following
> fields.
>
> -   `type`: `integer`, the type of this transaction which should be
>     set to 0.
> -   `from`: `bytes or text`, hex address or ENS name - (optional,
>     default: `cpc_fusion.cpc.defaultAccount`) The address the
>     transaction is send from.
> -   `to`: `bytes or text`, hex address or ENS name - (optional when
>     creating new contract) The address the transaction is directed to.
> -   `gas`: `integer` - (optional, default: 90000) Integer of the gas
>     provided for the transaction execution. It will return unused gas.
> -   `gasPrice`: `integer` - (optional, default: To-Be-Determined)
>     Integer of the gasPrice used for each paid gas
> -   `value`: `integer` - (optional) Integer of the value send with
>     this transaction
> -   `data`: `bytes or text` - The compiled code of a contract OR the
>     hash of the invoked method signature and encoded parameters. For
>     details see [Ethereum Contract
>     ABI](https://github.com/ethereum/wiki/wiki/Ethereum-Contract-ABI).
> -   `nonce`: `integer` - (optional) Integer of a nonce. This allows to
>     overwrite your own pending transactions that use the same nonce.
>
> If the `transaction` specifies a `data` value but does not specify
> `gas` then the `gas` value will be populated using the
> [Cpc.estimateGas()](#cpc-estimategas)
> function with an additional buffer of `100000` gas up to the
> `gasLimit` of the latest block. In the event that the value returned
> by [Cpc.estimateGas()](#cpc-estimategas)
> method is greater than the `gasLimit` a `ValueError` will be raised.
>
> ``` {.python}
> >>> cf.cpc.sendTransaction({'to': '0xd3cda913deb6f67967b99d67acdfa1712c293601', 'from': cf.cpc.coinbase, 'value': 12345})
> '0xe670ec64341771606e55d6b4ca35a1a6b75ee3d5145a99d05921026d1527331'
> ```

### Cpc.sendRawTransaction 

#### *class* Cpc.sendRawTransaction(raw_transaction) 

> -   Delegates to `eth_sendRawTransaction` RPC Method
>
> Sends a signed and serialized transaction. Returns the transaction
> hash.
>
> ``` {.python}
> >>> signed_txn = cf.cpc.account.signTransaction(dict(
>     type=0,
>     nonce=cf.cpc.getTransactionCount(cf.cpc.coinbase),
>     gasPrice=cf.cpc.gasPrice,
>     gas=100000,
>     to='0xd3cda913deb6f67967b99d67acdfa1712c293601',
>     value=12345,
>     data=b'',
>     chainId=337,
>   ),
>   private_key_for_senders_account,
> )
> >>> cf.cpc.sendRawTransaction(signed_txn.rawTransaction)
> '0xe670ec64341771606e55d6b4ca35a1a6b75ee3d5145a99d05921026d1527331'
> ```

## Block API

### Cpc.blockNumber 

#### *class* Cpc.blockNumber 

> -   Delegates to `eth_blockNumber` RPC Method
>
> Returns the number of the most recent block
>
> ``` {.python}
> >>> cf.cpc.blockNumber
> 2206939
> ```

### Cpc.getBlock 

#### *class* Cpc.getBlock(block_identifier=cpc.defaultBlock, full_transactions=False) 

> -   Delegates to `eth_getBlockByNumber` or `eth_getBlockByHash` RPC
>     Methods
>
> Returns the block specified by `block_identifier`. Delegates to
> `eth_getBlockByNumber` if `block_identifier` is an integer or one of
> the predefined block parameters `'latest', 'earliest', 'pending'`,
> otherwise delegates to `eth_getBlockByHash`.
>
> If `full_transactions` is `True` then the `'transactions'` key will
> contain full transactions objects. Otherwise it will be an array of
> transaction hashes.
>
> ::: tip
>
> The unit of returned `timestamp` is *millisecond*, which is different
> from the unit of *second* of Ethereum counterpart.
> :::
>
> ``` {.python}
> >>> cf.cpc.getBlock(100)
> AttributeDict({'difficulty': 2,
>  'extraData': HexBytes('0xdd85302e302e31876370636861696e88676f312e31302e34856c696e75780000'),
>  'gasLimit': 4712388,
>  'gasUsed': 0,
>  'hash': HexBytes('0xf52f56f96b704e02cf67f797ccbf33a42a095cc00aa9c2be6530ee02b9d34ad7'),
>  'logsBloom': HexBytes('0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'),
>  'miner': '0xc05302AceBd0730E3A18A058d7d1CB1204C4a092',
>  'number': 100,
>  'parentHash': HexBytes('0x7ff55edcbd638510900c0b4a5d5c6cbe66f8f1ff61f66a30f12bd4e1d263d89a'),
>  'receiptsRoot': HexBytes('0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421'),
>  'size': 934,
>  'stateRoot': HexBytes('0x7761096fe7777161e4e66463e17df6a2b555054c369418295703a9ea93008bca'),
>  'timestamp': 1543488712,
>  'totalDifficulty': 201,
>  'transactions': [],
>  'transactionsRoot': HexBytes('0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')})
> ```

### Cpc.getProposerByBlock 

#### *class* Cpc.cf.cpc.getProposerByBlock(block_identifier=cpc.defaultBlock) 

> -   Delegates to `eth_getProposerByBlock` RPC Methods
>
> Returns the proposer address. If the block is impeached, this API also
> works.
>
> ``` {.python}
> >>> cf.cpc.getProposerByBlock(361547)
> Oxce470d57b92248c570faa1caa3444f3da2607f6f
> ```

## Account API

### Cpc.getBalance 

#### *class* Cpc.getBalance(account, block_identifier=cpc.defaultBlock) 

> -   Delegates to `eth_getBalance` RPC Method
>
> Returns the balance of the given `account` at the block specified by
> `block_identifier`.
>
> `account` may be a hex address or an ENS name
>
> ``` {.python}
> >>> cf.cpc.getBalance('0xd3cda913deb6f67967b99d67acdfa1712c293601')
> 77320681768999138915
> ```

## Contract API

### Cpc.contract 

#### *class* Cpc.contract(address=None, contract_name=None, ContractFactoryClass=Contract, \*\*contract_factory_kwargs) 

> If `address` is provided, then this method will return an instance of
> the contract defined by `abi`. The address may be a hex string, or an
> ENS name like `'mycontract.cpc'`.
>
> ``` {.python}
> from cpc_fusion import Web3
>
> cf = Web3(...)
>
> contract = cf.cpc.contract(address='0x000000000000000000000000000000000000dead', abi=...)
>
> # alternatively:
> contract = cf.cpc.contract(address='mycontract.cpc', abi=...)
> ```
>
> If `address` is *not* provided, the newly created contract class will
> be returned. That class will then be initialized by supplying the
> address.
>
> ``` {.python}
> from cpc_fusion import Web3
>
> cf = Web3(...)
>
> Contract = cf.cpc.contract(abi=...)
>
> # later, initialize contracts with the same metadata at different addresses:
> contract1 = Contract(address='0x000000000000000000000000000000000000dead')
> contract2 = Contract(address='mycontract.cpc')
> ```
>
> `contract_name` will be used as the name of the contract class. If it
> is `None` then the name of the `ContractFactoryClass` will be used.
>
> `ContractFactoryClass` will be used as the base Contract class.
>
> The following arguments are accepted for contract class creation.
>
> -   `abi`
> -   `asm`
> -   `ast`
> -   `bytecode`
> -   `bytecode_runtime`
> -   `clone_bin`
> -   `dev_doc`
> -   `interface`
> -   `metadata`
> -   `opcodes`
> -   `src_map`
> -   `src_map_runtime`
> -   `user_doc`

#### *class* Cpc.setContractFactory(contractFactoryClass) 

> Modifies the default contract factory from `Contract` to
> `contractFactoryClass`. Future calls to `Cpc.contract()` will then
> default to `contractFactoryClass`.
>
> An example of an alternative Contract Factory is `ConciseContract`.

## RNode API

### Cpc.getRNodes 

#### *class* Cpc.getRNodes 

> -   Delegates to `eth_getRNodes` RPC Method
>
> Returns the array of address that become `rnode` as of the candidate
> of committee.
>
> ``` {.python}
> >>> cf.cpc.getRNodes
> [{'Address': '0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a','Rpt': 16,'Status': 0},{'Address': '0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a','Rpt': 16,'Status': 1},]
>
> #!/usr/bin/env python
> # -*- coding: utf-8 -*-
> from cpc_fusion import Web3
> from cpc_fusion.middleware import geth_poa_middleware
>
> cf = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))
>
> print("rnode:")
> print(cf.cpc.getRNodes)
> ```

### Cpc.getCurrentTerm 

#### *class* Cpc.getCurrentTerm 

> -   Delegates to `eth_getCurrentTerm` RPC Method
>
> Returns CurrentTerm.
>
> ``` {.python}
> >>> cf.cpc.getCurrentTerm
> 166
> ```

### Cpc.getCurrentView 

#### *class* Cpc.getCurrentView 

> -   Delegates to `eth_getCurrentView` RPC Method
>
> Returns CurrentView.
>
> ``` {.python}
> >>> cf.cpc.getCurrentView
> 1
> ```

### Cpc.getBlockGenerationInfo 

#### *class* Cpc.getBlockGenerationInfo 

> -   Delegates to `eth_getBlockGenerationInfo` RPC Method
>
> Returns Committee Dict.
>
> ``` {.python}
> >>> cf.cpc.getBlockGenerationInfo
> AttributeDict({'BlockNumber': 43073,
>  'Proposer': '0x4d1f1d14f303b746121564e3295e2957e74ea5d2',
>  'ProposerIndex': 4,
>  'Proposers': ['0x50f8c76f6d8442c54905c74245ae163132b9f4ae',
>   '0xfaf2a2cdc4da310b52ad7d8d86e8c1bd5d4c0bd0',
>   '0x8ab63651e6ce7eed40af33276011a5e2e1a533a2',
>   '0x5a55d5ef67c047b5d748724f7401781ed0af65ed',
>   '0x4d1f1d14f303b746121564e3295e2957e74ea5d2',
>   '0x049295e2e925cec28ddeeb63507e654b6d317423',
>   '0x501f6cf7b2437671d770998e3b785474878fef1d',
>   '0x8c65cb8568c4945d4b419af9066874178f19ba43',
>   '0x1f077085dfdfa4a65f8870e50348f277d6fcd97c',
>   '0x9508e430ce672750bcf6bef9c4c0adf303b28c5c',
>   '0xcb6fb6a201d6c126f80053fe17ca45188e24fe2f',
>   '0x73ae2b32ef3fad80707d4da0f49c675d3efc727c'],
>  'Term': 1196,
>  'TermLen': 12,
>  'View': 1})
> ```

#### *class* cpc.version.Version 

The `cpc.version` object exposes methods to interact with the RPC APIs
under the `version_` namespace.

## Personal API

Personal.newAccount +++++++++++++++++

#### *class* newAccount(self, password)

> -   Delegates to `personal_newAccount` RPC Method
>
> Generates a new account in the node's keychain encrypted with the
> given `passphrase`. Returns the address of the created account.
>
> ``` {.python}
> >>> cf.personal.newAccount('1')
> '0x062F4db4DDbE5618412ADffa33b4CbC680634Fc8'
> ```

Personal.lockAccount ++++++++++++++++

#### *class* lockAccount(self, account)

> -   Delegates to `personal_lockAccount` RPC Method
>
> Locks the given `account`.
>
> ``` {.python}
> >>> cf.personal.lockAccount('0xd3cda913deb6f67967b99d67acdfa1712c293601')
> ```

Personal.unlockAccount +++++++++++++++++

#### *class* unlockAccount(self, account, passphrase, duration=None)

> -   Delegates to `personal_unlockAccount` RPC Method
>
> Unlocks the given `account` for `duration` seconds. If `duration` is
> `None` then the account will remain unlocked indefinitely. Returns
> boolean as to whether the account was successfully unlocked.
>
> ``` {.python}
> >>> cf.personal.unlockAccount('0xd3cda913deb6f67967b99d67acdfa1712c293601', 'wrong-passphrase')
> False
> >>> cf.personal.unlockAccount('0xd3cda913deb6f67967b99d67acdfa1712c293601', 'the-passphrase')
> True
> ```

Personal.sendTransaction +++++++++++++++++++++

#### *class* sendTransaction(self, transaction, passphrase)

> -   Delegates to `personal_sendTransaction` RPC Method
>
> Sends the transaction.

## Version API

#### *class* cpc.version.Version 

The `cpc.version` object exposes methods to interact with the RPC APIs
under the `version_` namespace.

The following properties are available on the `cpc_fusion.cpc`
namespace.

### Version.api 

#### *class* Version.api(self) 

> Returns the current Web3 version.
>
> ``` {.python}
> >>> cf.version.api
> "0.0.21"
> ```

### Version.node 

#### *class* Version.node(self) 

> -   Delegates to `web3_clientVersion` RPC Method
>
> Returns the current client version.
>
> ``` {.python}
> >>> cf.version.node
> 'cpchain/v011ef5815d901e17c1b7d747cc2fae3da6b0bf49/linux-amd64/go1.11.1'
> ```

### Version.network 

#### *class* Version.network(self) 

> -   Delegates to `net_version` RPC Method
>
> Returns the current network protocol version.
>
> ``` {.python}
> >>> cf.version.network
> 0
> ```

### Version.cpchain 

#### *class* Version.cpchain(self) 

> -   Delegates to `eth_protocolVersion` RPC Method
>
> Returns the current cpchain protocol version.
>
> ``` {.python}
> >>> cpc.version.cpchain
> 1
> ```
