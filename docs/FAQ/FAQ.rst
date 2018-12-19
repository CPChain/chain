FAQ
~~~~~~~~~

- How to interact with CPChain

You can ``cpc_fusion`` to interact with CPChain in a python interpreter.

.. code-block:: python

    >>> from cpc_fusion import Web3
    >>> cf = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))
    >>> cf.cpc.blockNumber
    34341