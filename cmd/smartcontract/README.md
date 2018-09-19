# smart contract deploy

## Usage
deploy init smart contract for chain.
get contract address after deploy success, config address in params/config.go#CpchainChainConfig


## Deploy Smart Contract

deploy init smart contract

```shell
export GOPATH=${gopath}
cd ../../
go run ${gopath}/src/github.com/ethereum/go-ethereum/cmd/smartcontract/main.go
```

replace ${gopath} with real env path. ex:/home/${user}/workspace/chain_dev