# Installation

In this section, you are going to learn how to download our code, build
the project and run it on you own system.

::: tip

All code starting with a `$` is meant to run in your terminal. All code
starting with a `>>>` is meant to run in a python interpreter, like
[ipython](https://pypi.org/project/ipython/).
:::

First, make sure you have installed [go](https://golang.org/), and
configured the \$GOPATH.

## Getting Repository

You can click [here](https://github.com/CPChain/chain) to access source
code, or execute the following commands to clone code on github.

``` {.}
# open a $GOPATH
$ cd $GOPATH/src

$ mkdir -p bitbucket.org/cpchain/

$ cd bitbucket/cpchain

# TODO: chain url
$ git clone https://github.com/CPChain/chain
```

## Building

Run the command to compile and generate binary file in the `chain`
directory.

``` {.}
$ cd chain
$ make clean
$ make all
```

## Executables

You can find several executables in `build/bin` directory after building
the project.

``` {.}
$ cd build/bin
$ ls
```

<table cellspacing="0" cellpadding="5">
	<tr>
		<th colspan="1">Command           </th>
		<th colspan="1"> Description                        </th>
	</tr>
	<tr>
		<td  rowspan="1">cpchain </td>
		<td  rowspan="1"> Executable for the cpchain blockchain networks. </td>
	</tr>
	<tr>
		<td  rowspan="1">abigen </td>
		<td  rowspan="1"> Source code generator to convert CPChain contract definitions into easy to use, compile-time type-safe Go packages. </td>
	</tr>
	<tr>
		<td  rowspan="1">bootnode </td>
		<td  rowspan="1"> A lightweight bootstrap node to aid in finding peers in private networks. </td>
	</tr>
	<tr>
		<td  rowspan="1">contract-admin </td>
		<td  rowspan="1"> Executable for the cpchain official contract admin. </td>
	</tr>
	<tr>
		<td  rowspan="1">testtool </td>
		<td  rowspan="1"> Executable command tool for easy test. </td>
	</tr>
	<tr>
		<td  rowspan="1">transfer </td>
		<td  rowspan="1"> Executable for CPC transfer. </td>
	</tr>
	<tr>
		<td  rowspan="1">ecpubkey </td>
		<td  rowspan="1"> Return the public key given a keystore file and its password. </td>
	</tr>
	<tr>
		<td  rowspan="1">findimpeach </td>
		<td  rowspan="1"> Only for test purpose. </td>
	</tr>
	<tr>
		<td  rowspan="1">smartcontract </td>
		<td  rowspan="1"> For deploying smart contract. </td>
	</tr>
</table>
