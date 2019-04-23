Configuration
~~~~~~~~~~~~~~~~


MainnetChainId and MainnetNetworkId
------------------------------------------

All general configuration have been curated in ``configs/general.go``.
Two notable parameters are ``MainnetChainId`` and ``MainnetNetworkId``.

The code below are cited from general.go.
As we can see MainnetChainId is set to 42,
while MainnetNetworkId is 0.

.. code-block:: go

    const (
	DevChainId     = 41
	MainnetChainId = 42
	TestnetChainId = 43
    )

    const (
        MainnetNetworkId = 0
        DevNetworkId     = 1
        TestnetNetworkId = 2
    )

These two parameters are the marks of Mainnet.
If either of them is not as default setting,
the chain does not sync with Mainnet.
Any message from a node with different setting is regarded as useless information.


In addition, it is possible to start a private chain with its own network ID and chain ID.
But it requires more settings like IP addresses for validators.





Configure a Private Network
----------------------------------

Modify ``genesis.toml`` in the directory examples/cpchain/conf-dev to configure your own private network.

.. code::

	timestamp = 1492009146
	#extraData = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
	gasLimit = 47000000
	difficulty = 1
	coinbase = "0x0000000000000000000000000000000000000000"
	number = 0
	gasUsed = 0
	parentHash = "0x0000000000000000000000000000000000000000000000000000000000000000"

	[config]
	chainId = 41

	[config.dpor]
	period = 200_000_000
	#period = 500_000_000
	#period = 1_000_000_000
	termLen = 4
	viewLen = 3
	validatorsLen = 4
	maxInitBlockNumber = 120
	proxyContractRegister = "0x1a9fae75908752d0abf4dca45ebcac311c376290"
	impeachTimeout = 2000000000

	[config.dpor.contracts]
	campaign = "0x0ddf4057eedfb80d58029be49bab09bbc45bc500"
	pdash = "0xaaae743244a7a5116470df8bd398e7d562ae8881"
	proposer = "0x310236762f36bf0f69f792bd9fb08b5c679aa3f1"
	register = "0x019cc04ff9d88529b9e58ff26bfc53bce060e915"
	rpt = "0x82104907aa699b2982fc46f38fd8c915d03cdb8d"

	[alloc.0x0000000000000000000000000000000000000000]
	balance = "0x0"

	[alloc.0x0000000000000000000000000000000000000001]
	balance = "0x0"

	[alloc.0x0000000000000000000000000000000000000002]
	balance = "0x0"

	[alloc.0x00000000000000000000000000000000000000ff]
	balance = "0x0"

	[alloc.0x22a672eab2b1a3ff3ed91563205a56ca5a560e08]
	balance = "0x7fffffffffffffff"

	[alloc.0x3a18598184ef84198db90c28fdfdfdf56544f747]
	balance = "0x7fffffffffffffff"

	[alloc.0x6e31e5b68a98dcd17264bd1ba547d0b3e874da1e]
	balance = "0x7fffffffffffffff"

	[alloc.0xc05302acebd0730e3a18a058d7d1cb1204c4a092]
	balance = "0x7fffffffffffffff"

	[alloc.0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a]
	balance = "0x7fffffffffffffff"

	[alloc.0xef3dd127de235f15ffb4fc0d71469d1339df6465]
	balance = "0x7fffffffffffffff"

	[dpor]
	#seal = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
	#sigs = [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
	proposers = ["0xc05302acebd0730e3a18a058d7d1cb1204c4a092", "0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a", "0xef3dd127de235f15ffb4fc0d71469d1339df6465", "0x6e31e5b68a98dcd17264bd1ba547d0b3e874da1e"]
	validators = ["0x7b2f052a372951d02798853e39ee56c895109992", "0x2f0176cc3a8617b6ddea6a501028fa4c6fc25ca1", "0xe4d51117832e84f1d082e9fc12439b771a57e7b2", "0x32bd7c33bb5060a85f361caf20c0bda9075c5d51"]

Initialize CPChain after modifying the configuration file, then run a private chain.

.. code::

    $ ./cpchain-init.sh
    $ ./cpchain-all.sh







