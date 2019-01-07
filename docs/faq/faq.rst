FAQ
~~~~~~~~~~~

- **How to interact with CPChain?**

You can utilize ``cpc_fusion`` to interact with CPChain in a python interpreter.

.. code-block:: python

    >>> from cpc_fusion import Web3
    >>> cf = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))
    >>> cf.cpc.blockNumber
    34341


- **Why does my ``Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))`` return an error (Errno 111) that connection is refused?**

Before connecting http://127.0.0.1:8501, you should either set up a local chain or sync with our Mainnet.
Refer to :ref:`fusion-api-using` to detailed explanations.
