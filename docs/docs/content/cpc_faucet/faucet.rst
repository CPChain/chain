CPC Faucet
=============



Preliminaries
--------------

CPC faucet is an application that you can collect CPC test coins for free.
The test coins can be used in newly-published CPChain Alpha Mainnet.
Refer to https://cpchain.io/faucet/ to try it now.


Apply for a Wallet Address
----------------------------

To apply for test coins, a wallet address is required.
CPC fusion provides APIs for interested users to create a wallet address.

1. Refer to :ref:`fusion-api`, if you have yet installed CPC fusion.

#. You can choose either start a local chain, or sync with Alpha Mainnet (Rhea).

    1. To start a local chain, use the following commands:

        .. code-block:: shell

            $ cd ./examples/cpchain
            $ sudo ./cpchain-all.sh

        Note that starting a local chain may fails. You may try several times until success.

    #. To sync with Alpha Mainnet, use the following command:

        .. code-block:: shell

            $ ./cpchain run --rpcapi personal,eth,cpc,admission,net,web3,db,txpool,miner --rpcaddr 0.0.0.0:8501 --runmode=testnet


        Then use the commands above to connect to Alpha Mainnet.

#. Apply a wallet address in the chain.

    1. Enter python3 interpreter, type in:

        .. code-block:: python

            >>> from cpc_fusion import Web3
            >>> cf = Web3(Web3.HTTPProvider('http://127.0.0.1:8501'))
            >>> cf.personal.newAccount(pwd)

        The port here can be varying from 8501 to 8512.
        And ``pwd`` refers to the a string of password you prefer.

    #. Once succeeds, it a hexadecimal number, which is the wallet address.

Claim Test Coins
-----------------------------

1. Copy the wallet address and paste it in https://cpchain.io/faucet/. Now you can claim test coins.
#. The password it requires is 'cpchain2019'
#. Following a successful claim, this transaction is inserted into the test chain. In this site https://cpchain.io/explorer/, the transaction details can be searched.



