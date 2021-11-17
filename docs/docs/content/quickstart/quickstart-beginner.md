# Quick Start for Beginner 

Refer to [Download page](https://github.com/CPChain/chain/releases) for
binary releases of `cpchain`.

For ease of reading, we use `cpchain` to represent all available cpchain
versions. The instructions below are demonstrated on Linux.

If you are using Windows platform, all commands below are also viable.
Just replace `cpchain` with `cpchain-windows-4.0-386.exe` or
`cpchain-windows-4.0-amd64.exe`.

For 32-bit PC user, please select `386` version. And 64-bit PC users
should download `amd64` version.

For Mac user, please download `darwin` version. (Darwin forms the core
of macOS)

::: tip

All code starting with a `$` is meant to run in your terminal or cmd. Do
not copy `$`, as it is not a part of a command.
:::

## Apply for a Wallet

Use the `cd` command to enter the directory containing `cpchain` binary
file.

For Windows users, use the commands below in cmd.

``` {.shell}
$ cpchain-windows-4.0-amd64.exe account new
```

::: tip

Change `cpchain-windows-4.0-amd64.exe` to `cpchain-windows-4.0-386.exe`
if you are using on 32 bit operation system.
:::

For Linux and Mac users, use the commands below in terminal:

``` {.shell}
$ ./cpchain account new
```

Your account will be generated in default directory. Use the help
command below to check the manuel which includes the path of default
directory for your environment.

For Windows users:

``` {.shell}
$ cpchain-windows-4.0-amd64.exe account new -h
```

For Linux and Mac users:

``` {.shell}
$ ./cpchain account new -h
```

::: tip

You may use `--datadir` option to specify the keystore directory.
:::

## Connect to Mainnet

::: tip

The capitalized VARIABLES requires your modification according to your
own settings.
:::

Refer to [FAQ](../misc/faq.md#faq) if you encounter any
problem.

### Get Block Mined

This section is for users that are willing to propose new blocks.

::: tip

Before mining a block, make sure that you the balance in your account is
large enough (at least 200,000 cpc).
:::

Windows user the command below. (Here we use `amd64` version as
demonstration.)

``` {.shell}
$ cpchain-windows-4.0-amd64.exe run --unlock WALLET_ADDRESS --mine
```

Linux and Mac users please use the following command:

``` {.shell}
$ ./cpchain run --unlock WALLET_ADDRESS --mine
```

::: tip

The default port 30310 (or the port you specified using `--port`) should
be opened. Otherwise, other nodes cannot connect you in the P2P network.
:::

::: tip

If you use `--datadir` option, the account file is read from your
specified path.
:::

::: tip

A flag `--account WALLET_ADDRESS` is required in case your keystore
directory contains more than one account file.
:::

If you also willing to utilize API, please check
[Run a Node as Proposer](./quickstart.md#run-a-node-as-proposer).

### Get Chain Synced

This section is for users that only want to sync with the Mainnet,
review or sending transactions.

Windows users can utilize the command below:

``` {.shell}
$ cpchain-windows-4.0-amd64.exe run
```

Linux and Mac users please try this command:

``` {.shell}
$ ./cpchain run
```

If you are willing to use API, please check
[Run a Node as Civilian](./quickstart.md#run-a-node-as-civilian).

### Check Your Status

After you use `./cpchain run` command, you have connected to Mainnet.
Use the commands below to check your status.

For Linux and Mac users:

``` {.shell}
$ ./cpchain campaign status --keystore ./datadir/keystore/YOUR_ACCOUNT
```

For Windows users:

``` {.shell}
$ cpchain-windows-4.0-amd64.exe campaign status --keystore ./datadir/keystore/YOUR_ACCOUNT
```

This command is to check your account status given the `keystore` file.

### Stop Your Node from Mining

Generally, it is safe to quit the node use `ctrl+c`. Using commands like
`kill -9` or `killall` may incur impeached blocks. Refer to
[Why ``Control+C`` cannot abort the program](../misc/faq.md#why-``control+c``-cannot-abort-the-program) for detailed explanation.

To stop mining without quitting the node, use the command below.

Windows users:

``` {.shell}
$ cpchain-windows-4.0-amd64.exe campaign stop --keystore ./datadir/keystore/YOUR_ACCOUNT
```

Linux and Mac users:

``` {.shell}
$ ./cpchain campaign stop --keystore ./datadir/keystore/YOUR_ACCOUNT
```

## Upgrade

If you receive any error message under good network condition, the first
thing you need to do is to check if your node version is out-dated.

The upgrade is simple. All you need is to download the latest version
from [Download page](https://github.com/CPChain/chain/releases), and
stop your currently running node, and replace the old version with the
latest one.

::: tip

Please check [Why ``Control+C`` cannot abort the program](../misc/faq.md#why-``control+c``-cannot-abort-the-program), if you cannot
stop the node properly.
:::

You can always use `--version` flag to check the version.

For Linux and Mac users, use the command as below:

``` {.shell}
$ ./cpchain --version
```

Windows users use the following command.

``` {.shell}
$ cpchain.exe --version
```

After you upgrade, your node can continue syncing with the chain.
