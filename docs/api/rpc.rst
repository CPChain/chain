.. _rpc-api:

RPC API
=============


JSON RPC API
---------------

`JavaScript Object Notation (JSON) <http://json.org/>`_ is a lightweight data-interchange format.
It consists a collection of a collection of name/value pairs and an ordered list of values.
As a language-independent data format, it represents data objects in a human readable manner.

`JSON-RPC <https://www.jsonrpc.org/specification>`_ is a remote procedure call (RPC) encoded in JSON.
Its main traits are lightweight and stateless, by defining only a few data types and commands.
Primarily this specification defines several data structures and the rules around their processing.
It is transport agnostic in that the concepts can be used within the same process, over sockets, over http, or in many various message passing environments.
It uses JSON `(RFC 4627) <https://www.ietf.org/rfc/rfc4627.txt>`_ as data format.


How Can We Test APIs?
-----------------------------

All JSON-RPC requests are sent via POST method.
You may utilize any tools that supports HTTP POST protocol,
like `curl <https://curl.haxx.se/>`_ and `postman <https://www.getpostman.com/>`_.

Similar to fusion API, the prerequisite of testing API is to start a local chain or connect to Mainnet.
Refer to :ref:`fusion-api-using` to see set up details.

To use curl, you must type four arguments, request method, data, url and header.
Request method is set to -X POST, url is set to --url 'http://127.0.0.1:8501', and header is -H "Content-Type: application/json".
Data for each API is listed on `API Reference`_ below.

To use postman, please choose POST method, type in '127.0.0.1:8501' in to url field.
In Header option, type in 'Content-Type' as KEY, and 'application/json' as VALUE.
Data for each API, should be written in Body option (choose raw format).

In the reference below, we demonstrate CPC APIs in curl.


API Reference
---------------

CPC
########

JSON PRC APIs in this chapter are the counterparts of ones in python class ``fusion_cpc.cpc.CPC``.
CPC APIs are categorized into five types according to their functions which are
*Block*, *Transaction*, *Account*, *RNode* and *Others*.

Block
*********

eth_blockNumber
+++++++++++++++++

It returns the number of most recent block.

**Parameters**

none

**Returns**

``QUANTITY`` - integer of the current block number the client is on.

**Example**

.. code-block:: shell

    // Curl request
    $ curl -X POST --data '{"jsonrpc":"2.0","method":"eth_blockNumber","params":[],"id":1}' --url 'http://127.0.0.1:8501' -H "Content-Type: application/json"

    // Result
    {
        "jsonrpc": "2.0",
        "id": 1,
        "result": "0x724be"  // 468158
    }

eth_getBlockby
++++++++++++++

Returns information about a block by block number.

**Parameters**

``QUANTITY|TAG`` - integer of a block number, or the string "earliest", "latest" or "pending", as in the default block parameter.

``Boolean`` - If true it returns the full transaction objects, if false only the hashes of the transactions.

**Examples**

.. code-block:: shell

    // Curl request
    $ curl -X POST --data '{"jsonrpc":"2.0","method":"eth_getBlockByNumber","params":["0x7EE2A", true],"id":1}' --url 'http://127.0.0.1:8501' -H "Content-Type: application/json"
    // 0x7EE2A is 519722 in decimal

    // Result
    {
        "jsonrpc": "2.0",
        "id": 1,
        "result": {
            "difficulty": "0x1",
            "dpor": {
                "seal": "0x12e0c733a0d6cf7e1a1ed71db183ea47b42d19984f71b7c79b0cb4727fdfea3e61774edfe6181e05c950fe4ce35dd08840e29162c6240ac57c4abf8560a2556700",
                "sigs": [
                    "0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
                    "0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
                    "0x2a385a136ee1a96d8a944fb466cd61c26a10f95cd1119feefa7c753b0e7adfc664801b99e360b6f7d822e7b2e919a44464ddd66930194a987a75aa1ed78a55d401",
                    "0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
                ],
                "proposers": [
                    "0x2a15146f434c0205cfae639de2ac4bb543539b24",
                    "0x7326d5248928b87f63a80e424a1c6d39cb334624",
                    "0xe7a992e4187e95f28f8f69d44487fb16c465071c",
                    "0x2661177788fe63888e93cf18b5e4e31306a01170"
                ],
                "validators": []
            },
            "extraData": "0x0000000000000000000000000000000000000000000000000000000000000000",
            "gasLimit": "0x47e7c4",
            "gasUsed": "0x0",
            "hash": "0x2ae023df10e17f1c0f885d4d42bd976369b1ad22aa80a7df429b4028e3180d4d",
            "logsBloom": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
            "miner": "0x2a15146f434c0205cfae639de2ac4bb543539b24",
            "number": "0x7ee2a",
            "parentHash": "0x81655165cf6ad2b749977c7ecabc2bc576cd58d7dfa838f00340463a865e53cb",
            "receiptsRoot": "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421",
            "size": "0x381",
            "stateRoot": "0x902a8f498dd31d13131b53f84dd918387e002b8acba43432ff9c8ce58bf32c2b",
            "timestamp": "0x168412e5fdb",
            "totalDifficulty": "0x7ee2b",
            "transactions": [],
            "transactionsRoot": "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
        }
    }


Transaction
*************

eth_sendTransaction
++++++++++++++++++++++

Creates new messages call transaction or a contract creation, if the data fields contains code.


**Parameters**

    ``Object`` - The transaction object

    ``from``: ``DATA``, 20 Bytes - The address the transaction is send from.

    ``to``: ``DATA``, 20 Bytes - (optional when creating new contract) The address the transaction is directed to.

    ``gas``: ``QUANTITY`` - (optional, default: 90000) Integer of the gas provided for the transaction execution. It will return unused gas.

    ``gasPrice``: ``QUANTITY`` - (optional, default: To-Be-Determined) Integer of the gasPrice used for each paid gas

    ``value``: ``QUANTITY`` - (optional) Integer of the value sent with this transaction

    ``data``: ``DATA`` - The compiled code of a contract OR the hash of the invoked method signature and encoded parameters.

    ``nonce``: ``QUANTITY`` - (optional) Integer of a nonce. This allows to overwrite your own pending transactions that use the same nonce.


.. code-block:: shell

    "params":[{
      "from": "0xe83a71428655b9f52ff6dc556e2b37043f39f194",
      "to": "0x177b2a835f27a8989dfca814b37d08c54e1de889",
      "gas": "0x76c0", // 30400
      "gasPrice": "0x9184e72a000", // 10000000000000
      "value": "0x9184e72a", // 2441406250
      "data": "0xd46e8dd67c5d32be8d46e8dd67c5d32be8058bb8eb970870f072445675058bb8eb970870f072445675"
    }]



**Returns**

``DATA``, 32 Bytes - the transaction hash, or the zero hash if the transaction is not yet available.

**Example**

.. code-block:: shell

    // Curl request
    curl -X POST --data '{"jsonrpc":"2.0","method":"eth_sendTransaction","params":[{see above}],"id":1}' --url 'http://127.0.0.1:8501' -H "Content-Type: application/json"

    // Result
    {
        "jsonrpc": "2.0",
        "id": 1,
        "result": "0xc38f30dab2b603840682e0f588dbda0a897a73c4409f9c998dd4fdc176784eb2"
    }

eth_getBlockTransactionCountByHash
+++++++++++++++++++++++++++++++++++++

Returns the number of transactions in a block from a block matching the given block hash.

**Parameters**

    ``DATA``, 32 Bytes - hash of a block.

.. code-block:: shell

    params: [
       '0x31b36ef5ec3481f6307170c87b1f21e492a6abf08693622236cb30ce095e1abf'
    ]

**Returns**

    ``QUANTITY`` - integer of the number of transactions in this block.

**Example**


.. code-block:: shell

    // Request
    curl -X POST --data '{"jsonrpc":"2.0","method":"eth_getBlockTransactionCountByHash","params":["0x31b36ef5ec3481f6307170c87b1f21e492a6abf08693622236cb30ce095e1abf"],"id":1}' --url 'http://127.0.0.1:8501' -H "Content-Type: application/json"

    // Result
    {
      "id":1,
      "jsonrpc": "2.0",
      "result": "0x7b" // 123
    }



eth_getBlockTransactionCountByNumber
+++++++++++++++++++++++++++++++++++++

Returns the number of transactions in a block from a block matching the given block number.

**Parameters**


    ``QUANTITY|TAG`` - integer of a block number, or the string "earliest", "latest" or "pending", as in the default block parameter.


.. code-block:: shell

    params: [
       '0x1363eb' //1270763
    ]

**Returns**

    ``QUANTITY`` - integer of the number of transactions in this block.

**Example**


.. code-block:: shell

    // Request
    curl -X POST --data '{"jsonrpc":"2.0","method":"eth_getBlockTransactionCountByNumber","params":["0x1363eb"],"id":1}' --url 'http://127.0.0.1:8501' -H "Content-Type: application/json"

    // Result
    {
      "id":1,
      "jsonrpc": "2.0",
      "result": "0x7b" // 123
    }





eth_gasPrice
+++++++++++++++

It returns the current price per gas in wei.


**Parameters**

none

**Returns**

``QUANTITY`` - integer of the current gas price in wei.

**Example**

.. code-block:: shell

    // Request
    curl -X POST --data '{"jsonrpc":"2.0","method":"eth_gasPrice","params":[],"id":73}' --url 'http://127.0.0.1:8501' -H "Content-Type: application/json"

    // Result
    {
      "id":73,
      "jsonrpc": "2.0",
      "result": "0x430e23400" // 18000000000
    }



eth_estimateGas
++++++++++++++++++

Generates and returns an estimate of how much gas is necessary to allow the transaction to complete.
The transaction will not be added to the blockchain.
Note that the estimate may be significantly more than the amount of gas actually used by the transaction,
for a variety of reasons including EVM mechanics and node performance.

**Parameters**

See `eth_call`_ parameters, expect that all properties are optional.
If no gas limit is specified cpc uses the block gas limit from the pending block as an upper bound.
As a result the returned estimate might not be enough to executed the call/transaction
when the amount of gas is higher than the pending block gas limit.

**Returns**

``QUANTITY`` - the amount of gas used.

**Example**


.. code-block:: shell

    // Request
    curl -X POST --data '{"jsonrpc":"2.0","method":"eth_estimateGas","params":[{see above}],"id":1}' --url 'http://127.0.0.1:8501' -H "Content-Type: application/json"

    // Result
    {
      "id":1,
      "jsonrpc": "2.0",
      "result": "0x430e23400" // 18000000000
    }


eth_call
+++++++++++

Executes a new message call immediately without creating a transaction on the block chain.

**Parameters**

    ``Object`` - The transaction call object

        ``from``: DATA, 20 Bytes - (optional) The address the transaction is sent from.

        ``to``: DATA, 20 Bytes - The address the transaction is directed to.

        ``gas``: QUANTITY - (optional) Integer of the gas provided for the transaction execution. eth_call consumes zero gas, but this parameter may be needed by some executions.

        ``gasPrice``: QUANTITY - (optional) Integer of the gasPrice used for each paid gas

        ``value``: QUANTITY - (optional) Integer of the value sent with this transaction

        ``data``: DATA - (optional) Hash of the method signature and encoded parameters. For details see Ethereum Contract ABI

    ``QUANTITY|TAG`` - integer block number, or the string "latest", "earliest" or "pending", see the default block parameter

.. code-block:: shell

    "params":[{
      "from": "0xe83a71428655b9f52ff6dc556e2b37043f39f194",
      "to": "0x177b2a835f27a8989dfca814b37d08c54e1de889",
      "gas": "0x76c0", // 30400
      "gasPrice": "0x9184e72a000",  // 10000000000000
      "value": "0x9184e72a",  // 2441406250
      "data": "0xd46e8dd67c5d32be8d46e8dd67c5d32be8058bb8eb970870f072445675058bb8eb970870f072445675"
    },"latest"]

**Returns**

``DATA`` - the return value of executed contract.

**Example**

.. code-block:: shell

    // Request
    curl -X POST --data '{"jsonrpc":"2.0","method":"eth_call","params":[{see above}],"id":1}' --url 'http://127.0.0.1:8501' -H "Content-Type: application/json"

    // Result
    {
      "id":1,
      "jsonrpc": "2.0",
      "result": "0x"
    }




eth_getTransactionReceipt
++++++++++++++++++++++++++++

Returns the receipt of a transaction by transaction hash.

Note That the receipt is not available for pending transactions.

**Parameters**

    ``DATA``, 32 Bytes - hash of a transaction

.. code-block:: shell

    params: [
    '0x87afe28c7d60d4e6160ac5f00dce35c1e7b4739e3851412fcd64cc72b800f47b'
    ]

**Returns**

``Object`` - A transaction receipt object, or null when no receipt was found:

    ``transactionHash`` : DATA, 32 Bytes - hash of the transaction.

    ``transactionIndex``: QUANTITY - integer of the transaction's index position in the block.

    ``blockHash``: DATA, 32 Bytes - hash of the block where this transaction was in.

    ``blockNumber``: QUANTITY - block number where this transaction was in.

    ``from``: DATA, 20 Bytes - address of the sender.

    ``to``: DATA, 20 Bytes - address of the receiver. null when it's a contract creation transaction.

    ``cumulativeGasUsed``: QUANTITY - The total amount of gas used when this transaction was executed in the block.

    ``gasUsed``: QUANTITY - The amount of gas used by this specific transaction alone.

    ``contractAddress``: DATA, 20 Bytes - The contract address created, if the transaction was a contract creation, otherwise null.

    ``logs``: Array - Array of log objects, which this transaction generated.

    ``logsBloom``: DATA, 256 Bytes - Bloom filter for light clients to quickly retrieve related logs.

It also returns either :

    ``root``: DATA 32 bytes of post-transaction stateroot (pre Byzantium)

    ``status``: QUANTITY either 1 (success) or 0 (failure)

**Example**


.. code-block:: shell


    // Request
    curl -X POST --data '{"jsonrpc":"2.0","method":"eth_getTransactionReceipt","params":["0xb903239f8543d04b5dc1ba6579132b143087c68db1b2168786408fcbce568238"],"id":1}' --url 'http://127.0.0.1:8501' -H "Content-Type: application/json"

    // Result
    {
        "jsonrpc": "2.0",
        "id": 1,
        "result": {
            "blockHash": "0x44b34580529e172361ff050c53fd948a12def0b002c53f1042c911246d9034d3",
            "blockNumber": "0x152931",
            "contractAddress": null,
            "cumulativeGasUsed": "0x5208",
            "from": "0xe83a71428655b9f52ff6dc556e2b37043f39f194",
            "gasUsed": "0x5208",
            "logs": [],
            "logsBloom": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
            "status": "0x1",
            "to": "0xb436e2feffa76c30beb9d89e825281baa9956d4c",
            "transactionHash": "0x87afe28c7d60d4e6160ac5f00dce35c1e7b4739e3851412fcd64cc72b800f47b",
            "transactionIndex": "0x0"
        }
    }




eth_getTransactionCount
+++++++++++++++++++++++++++++


Returns the number of transactions sent from an address.

**Parameters**

    ``DATA``, 20 Bytes - address.
    ``QUANTITY|TAG`` - integer block number, or the string "latest", "earliest" or "pending", see the default block parameter

**Example Parameters**

.. code-block:: shell

    params: [
       '0xE83a71428655B9F52fF6dc556E2b37043f39F194',
       'latest' // state at the latest block
    ]



**Returns**

``QUANTITY`` - integer of the number of transactions send from this address.

**Example**

.. code-block:: shell

    // Request
    curl -X POST --data '{"jsonrpc":"2.0","method":"eth_getTransactionCount","params":["0xE83a71428655B9F52fF6dc556E2b37043f39F194","latest"],"id":1}'

    // Result
    {
      "id":1,
      "jsonrpc": "2.0",
      "result": "0x1" // 1
    }

eth_sendRawTransaction
+++++++++++++++++++++++++++

Creates new message call transaction or a contract creation for signed transactions.

**Parameters**

    ``DATA``, The signed transaction data.

.. note::

    The input parameter for eth_sendRawTransaction can only be used once,
    computed by various variables like private key, nonce and gas.

**Example Parameters**


.. code-block:: shell

    params: ["0xd46e8dd67c5d32be8d46e8dd67c5d32be8058bb8eb970870f072445675058bb8eb970870f072445675"]

Returns

    ``DATA``, 32 Bytes - the transaction hash, or the zero hash if the transaction is not yet available.

Use `eth_getTransactionReceipt`_ to get the contract address, after the transaction was mined, when you created a contract.


**Example**

.. code-block:: shell

    // Request
    curl -X POST --data '{"jsonrpc":"2.0","method":"eth_sendRawTransaction","params":[{see above}],"id":1}'

    // Result
    {
      "id":1,
      "jsonrpc": "2.0",
      "result": "0xe670ec64341771606e55d6b4ca35a1a6b75ee3d5145a99d05921026d1527331"
    }



Account
***********


eth_getBalance
+++++++++++++++++


It returns the balance according to the wallet address.

**Parameters**

``DATA``, 20 Bytes - address to check for balance.

``QUANTITY|TAG`` - integer block number, or the string "latest", "earliest" or "pending", see the default block parameter

.. code-block:: shell

    "params":[
        "0xa080ea61fa96c092921340e7f6450cc8371e14bc",
        "latest"
    ]

**Returns**

``QUANTITY`` - integer of the current balance.

**Example**

.. code-block:: shell

    // Curl request
    $ curl -X POST --data '{"jsonrpc":"2.0","method":"eth_getBalance","params":["0xa080ea61fa96c092921340e7f6450cc8371e14bc", "latest"],"id":1}' --url 'http://127.0.0.1:8501' -H "Content-Type: application/json"

    // Result
    {
        "jsonrpc": "2.0",
        "id": 1,
        "result": "0x56bc6066367565ff6" // 9999962199999999999
    }





