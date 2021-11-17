Configuration
~~~~~~~~~~~~~~~~


MainnetChainId and MainnetNetworkId
------------------------------------------

All general configuration have been curated in ``configs/general.go``.
Two notable parameters are ``MainnetChainId`` and ``MainnetNetworkId``.

The code below are cited from general.go.
As we can see MainnetChainId is set to 337.

.. code-block:: go

    const (
	DevChainId         = 41
	MainnetChainId     = 337
	TestMainnetChainId = 42
	TestnetChainId     = 43
    )

    const (
        TestMainnetNetworkId = 0
        DevNetworkId         = 1
        TestnetNetworkId     = 2
    )

These two parameters are the marks of Mainnet.
If either of them is not as default setting,
the chain does not sync with Mainnet.
Any message from a node with different setting is regarded as useless information.


In addition, it is possible to start a private chain with its own network ID and chain ID.
But it requires more settings like IP addresses for validators.





Configure a Private Network
----------------------------------

To customize your own private chain, please modify the file ``core/genesis.go``.

.. code::

    $ ./cpchain-init.sh dev
    $ ./cpchain-all.sh







