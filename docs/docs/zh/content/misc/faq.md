# FAQ 

## Issue Page

If you find any questions unlisted here, please raise an issue on our
[Issue Page](https://github.com/CPChain/chain/issues).

## How to stop mining and get my CPC back?

1.  Start CPChain program with command if you don't have a running
    cpchain node.

``` {.bash}
./cpchain run \
--unlock WALLET_ADDRESS \
--rpcaddr 127.0.0.1:8501 --mine \
--rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner"

# `--rpcaddr` and `--rpcapi` must be made available.
# your default datadir is `$HOME/.cpchain` and you can add `--datadir` to specify your datadir
```

2.  Wait for data synchronization to complete.
3.  open another console and type command

``` {.bash}
./cpchain campaign stop --keystore YOUR_KEYSTORE_DIR --rpc 127.0.0.1:8501
```

`YOUR_KEYSTORE_DIR` must add `/`，e.g.: `./datadir/keystore/`

## How to interact with CPChain?

You can utilize `cpc_fusion` to interact with CPChain in a python
interpreter.

``` {.python}
>>> from cpc_fusion import Web3
>>> cf = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))
>>> cf.cpc.blockNumber
34341
```

## Why does fusion return an error (Errno 111) indicating connection is refused?

The Errno 111 can be returned when you call
`Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))` in fusion.

Before connecting <http://127.0.0.1:8501>, you should either set up a
local chain or sync with our Mainnet. Refer to
[Using Fusion](../api/cpc_fusion.md#using-fusion) to detailed
explanations.

## Why `./cpchain run` command cannot be executed successfully? 

Several reasons can account for this problem. You may try the following
means to solve the problem.

1.  Confirm that you are connecting to the network and the ports you
    nominated are available.

If you use the command in [Quick Start in Detail](../quickstart/quickstart.md#quick-start-in-detail) as

``` {.shell}
$ ./cpchain run
```

, make sure the default port `30310` (or the port you specified using
`--port`) has not be occupied yet.

If you add the flag `--rpcaddr 127.0.0.1:8501`, you should also open
port `8501`. You may also use other ports as you wish.

2.  Remove temporary user files.

The existence of some temporary files get `cpchain` skip some
initialization processes, which may result in an unsuccessful execution.

Type in the following to remove temporary files.

``` {.shell}
$ ./cpchain chain cleandb
```

3.  Manually kill all `cpchain` processes.

An incomplete abort of `cpchain` can incur a failure in starting a new
process. If you receive an error message indicating your port or datadir
being occupied, it is highly possible that there are some `cpchain`
processes still running in background.

You can may either use `ps` command paired with `kill` to terminate
`cpchain` processes, or choose to kill all cpchain processes by

``` {.shell}
$ killall -9 cpchain
```

## Message `The file "./cpchain" is not executable by this user` pops when running `cpchain` 

This problem is due to a wrong access permission of the binary file. You
can fix this problem by using the command below:

``` {.shell}
$ chmod +x cpchain
```

## Message `Fatal: Failed to unlock account` pops when running `cpchain`

One possible reason is that the account file is not in the right
directory.

In the command

``` {.shell}
$ ./cpchain run --datadir ./datadir \
    --unlock WALLET_ADDRESS \
    --rpcaddr 127.0.0.1:8501 --port 30311 --mine \
    --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner --linenumber
```

`--datadir ./datadir` means the account file (keystore) in under
`./datadir` directory. If you create an account without specify a
directory, like using the command `./cpchain account new account`
instead of `./cpchain account new account --datadir ./datadir`, the
account file is created under a default directory, which is not
`./datadir`.

In this case, you can either

-   Specify YOUR_ACCOUNT_DIRECOTRY after `--datadir`, or
-   Move your account file to `./datadir`.

## Message `error  while  loading  shared  libraries:  libz3.so.4` pops when running `solc` 

It can be resolved by running the command below:

``` {.shell}
$ sudo  apt-get  install  libz3-dev
```

## The default `solc` is not a compatible version

To check the version of solidity, you may utilize the following command:

``` {.shell}
$ solc --version
```

And by using `$ which solc` command, you can locate the path for default
`solc`, and replace it with a 0.4.25 version.

``` {.shell}
$ which solc
/usr/bin/solc
$ rm -f /usr/bin/solc
// copy solc 0.4.25 to /user/bin
$ cp solc /usr/bin
```

## Why `Control+C` cannot abort the program 

`Ctrl+C` cannot abort `cpchain` if either of the following condition is
satisfied:

1.  You are one of the proposers committee in the current term;
2.  You are elected to seal blocks in a future term.

To sustain the throughput of the chain, we disable the functionality of
aborting the program via `Ctrl+C` for all current and future proposers.

To quit `cpchain`, your node should meet neither of the conditions
above. The safest way is to stop mining and wait all elected terms end.
Launch another `cpchain` program and utilize the command below to stop
mining.

``` {.shell}
$ ./cpchain campaign stop --keystore ./datadir/keystore/YOUR_ACCOUNT
```

You can also utilize the command below to check your status.

``` {.shell}
$ ./cpchain campaign status --keystore ./datadir/keystore/YOUR_ACCOUNT
```

::: tip

You can use the flag `--password ./datadir/password` to input the
password, similar to other `./cpchain campaign` commands.
:::

## How can I address `system clock` error? 

For users finding error message
`system clock need to be synchronized.there is more than 10 seconds gap between ntp and this server`,
they need to adjust their servers' local clock. One of the prerequisites
to run the node is that the time gas between local time and NTP (network
time protocol) must be less than 10 seconds.

To address the issue, please toggle *automatic time & date* in your
server such that the local time keeps correct.

## What could I handle a large amount of impeached blocks?

For proposer finding that it has a large amount of impeached blocks,
please check if your version is the latest one. You can use the command

``` {.shell}
$ ./cpchain --version
```

to check the version number.

If your node still encounter a high frequency of getting impeached,
please raise an issue on our GitHub [Issue
Page](https://github.com/CPChain/chain/issues).

## Why are the wallet addresses mixed case?

Some addresses (like ones in [Explorer](https://cpchain.io/explorer/))
are expressed in mixed cases, e.g.,
0xC8d95F1b3179c30fB067243ce68F5eA20E750351.

These addresses with uppercase letters are **checksummed**, and the ones
with only lowercase are **non-checksummed**.

-   Non-checksummed version: 0xc8d95f1b3179c30fb067243ce68f5ea20e750351
-   checksummed version: 0xC8d95F1b3179c30fB067243ce68F5eA20E750351

The checksum is a kind of validation. It can tell if the address is
valid and do not contain typos.

## What is checksum used for in [Download Page](https://github.com/CPChain/chain/releases)?

We provide a checksum value for each release after version 0.4.7. It is
used for validating if the downloaded file is correct. You can use the
[Checksum
Page](https://emn178.github.io/online-tools/sha256_checksum.html)
(SHA256) to obtain a checksum result for a file you download, and
compare the value with the one on [Download
Page](https://github.com/CPChain/chain/releases).

## How to reduce the disk usage of `cpchain`?

From version 0.4.8, two commands are provided to delete useless files in
`cpchain` folder. Please type the following two commands in order.

``` {.shell}
./cpchain chain delete dpor-
./cpchain chain compact
```

::: tip

i\) You can use the flag `--datadir` to indicate your `cpchain` folder
if your node is not stored in the default directory.

ii\) The `chain delete dpor-` command does not shrink disk usage
directly. It traverses all cpchain files and labels redundant and
obsolete files.

iii\) The `chain compact` command then compacts files following the
labels done by `chain delete dpor-` command.

iv\) Both commands can be rather time consuming. The process time is
estimated to around 20 minutes for each command.

v\) Note that there is a **hyphen** following `dpor` in
`chain delete dpor-` command. The argument `dpor-` indicates the prefix
of file names. Other arguments rather than `dpor-` may lead to
**unexpected results**.

vi\) Also note that both commands **can only** be executed when the
chain is stopped. An error will be raised if you execute either command
for a running node.
:::

## Is `sudo` needed to run `cpchain`?

In principle, `sudo` (or administrator privileges) is not required to
run `cpchain`. However, some users may encounter error message
indicating a denied permission. Here we list some possible reasons
accounting for this problem:

**1. The root user and normal user have different default folders of**
`cpchain` **.**

Thus, if you run `cpchain` as root for the first time (e.g., using
`sudo`), you have to use `--datadir` to refer to the `cpchain` folder as
a normal user.

**2. Write into a log file that requires root privilege.**

Some users (e.g., ones using `nohup`) utilize `>` to redirect the output
of `cpchain` to a log file. If the log file can only be written as root
(e.g., in a root-privileged folder), this redirection will lead to a
failure in launching `cpchain`.

You can either use the `chmod` command to change the permissions of the
log file, or redirect the output to other log file that you can access.

## Which version is compatible with the latest one?

**We strongly encourage the users to adopt the latest version!**

In principle version 0.a.b is compatible with version 0.a.c, where a, b,
c, are natural numbers. For example 0.4.8 is compatible with 0.4.6.

The word **"compatible"** here means no conflicts in the level of
consensus, but older versions certainly contain more bugs and lack new
features. Thus, we highly recommend the user to keep the `cpchain` file
updated to the latest version.

Nevertheless, it is feasible to downgrade to a previous compatible
version to circumvent certain bugs in the newer ones. Downgrading should
be only considered as an expedient. And please update `cpchain` if the
bug is solved.

## 如何指定 RPC 服务的域名

在 `datadir` 中创建文件 `config.toml`，文件内容如下：

```toml

[node]
HTTPVirtualHosts=["server01"]

```

其中，`server01` 即所需域名，表示节点只接受通过此域名来访问的请求。若指定为 `*`，则表示所有域名的请求都可接受。
