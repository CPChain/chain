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

## Using Fusion {#fusion-api-using}

To use the cpc fusion library, you are required to initialize the
`~cpc_fusion.cpc`{.interpreted-text role="class"} class.

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

Please check `quick-start`{.interpreted-text role="ref"} for more
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

::: {#first_w3_use}
:::

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

### Cpc.estimateGas

Executes the given transaction locally without creating a new
transaction on the blockchain. Returns amount of gas consumed by
execution which can be used as a gas estimate.

The transaction parameter is handled in the same manner as the
`sendTransaction()` method.

> ::: {.note}
> ::: {.title}
> Note
> :::
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

### Cpc.getTransaction

### Cpc.getTransactionFromBlock

### Cpc.getTransactionByBlock

### Cpc.waitForTransactionReceipt

### Cpc.getTransactionReceipt

### Cpc.getTransactionCount

### Cpc.sendTransaction

### Cpc.sendRawTransaction

## Block API

### Cpc.blockNumber

### Cpc.getBlock

### Cpc.getProposerByBlock

## Account API

### Cpc.getBalance

## Contract API

### Cpc.contract

## RNode API

### Cpc.getRNodes {#cpc-getrnodes}

### Cpc.getCurrentTerm

### Cpc.getCurrentView

### Cpc.getBlockGenerationInfo

The `cpc.version` object exposes methods to interact with the RPC APIs
under the `version_` namespace.

## Personal API

Personal.newAccount +++++++++++++++++

Personal.lockAccount ++++++++++++++++

Personal.unlockAccount +++++++++++++++++

Personal.sendTransaction +++++++++++++++++++++

## Version API

The `cpc.version` object exposes methods to interact with the RPC APIs
under the `version_` namespace.

The following properties are available on the `cpc_fusion.cpc`
namespace.

### Version.api

### Version.node

### Version.network

### Version.cpchain
