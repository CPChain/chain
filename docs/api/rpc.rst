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


How can we test API?
----------------

All JSON-RPC requests are sent via POST method.
You may utilize any tools that supports HTTP POST protocol,
like `curl <https://curl.haxx.se/>`_ and `postman <https://www.getpostman.com/>`_.

Similar to fusion API, the prerequisite of testing API is to start a local chain or connect to Mainnet.
Refer to :ref:`fusion-api` to see set up details.

To use curl, you must type four arguments, request method, data, url and header.
Request method is set to -X POST, url is set to --url 'http://127.0.0.1:8501', and header is -H "Content-Type: application/json".
Data for each API is listed on `API Reference`_ below.

To use postman, please choose POST method, type in '127.0.0.1:8501' in to url field.
In Header option, type in 'Content-Type' as KEY, and 'application/json' as VALUE.
Data for each API, should be written in Body option (choose raw format).

In the reference below, we demonstrate CPC APIs in curl.


API Reference
---------------

eth_blockNumber
*******************

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


eth_getBalance
*******************

It returns the balance according to the wallet address.

**Parameters**

1. ``DATA``, 20 Bytes - address to check for balance.

#. ``QUANTITY|TAG`` - integer block number, or the string "latest", "earliest" or "pending", see the default block parameter

.. code-block:: shell

    "params":[
        "0xa080ea61fa96c092921340e7f6450cc8371e14bc",
        "latest"
    ]

Returns

QUANTITY - integer of the current balance.

Example

.. code-block:: shell

    // Curl request
    $ curl -X POST --data '{"jsonrpc":"2.0","method":"eth_getBalance","params":["0xa080ea61fa96c092921340e7f6450cc8371e14bc", "latest"],"id":1}' --url 'http://127.0.0.1:8501' -H "Content-Type: application/json"

    // Result
    {
        "jsonrpc": "2.0",
        "id": 1,
        "result": "0x56bc6066367565ff6" // 9999962199999999999e-18 CPC
    }

