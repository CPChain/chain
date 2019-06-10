# This Makefile is meant to be used by people that do not usually work
# with Go source code. If you know what GOPATH is then you probably
# don't need to bother with make.

.PHONY: cpchain cpchain-cross all test clean
.PHONY: cpchain-linux cpchain-linux-386 cpchain-linux-amd64 cpchain-linux-mips64 cpchain-linux-mips64le
.PHONY: cpchain-linux-arm cpchain-linux-arm-5 cpchain-linux-arm-6 cpchain-linux-arm-7 cpchain-linux-arm64
.PHONY: cpchain-darwin cpchain-darwin-386 cpchain-darwin-amd64
.PHONY: cpchain-windows cpchain-windows-386 cpchain-windows-amd64
.PHONY: dev-init dev-tools
.PHONY: docs docs-serve docs-serve-clean docs-clean
.PHONY: docs-mv-solidity docs-cp-solidity docs-solidity

SHELL := $(shell which bash)

GOBIN = $(shell pwd)/build/bin
GO ?= latest

# NOTE: SUPPORT PRIVATE TRANSACTION
# To support private transaction functionality, set ENV variable 'PRIVATE_TX' to be true
# Example: env PRIVATE_TX=true make all

all: cpchain bootnode abigen smartcontract ecpubkey testtool findimpeach

#console

cpchain:
	build/env.sh go run build/ci.go install ./cmd/cpchain
	@echo "Done building."
	@echo "Run \"$(GOBIN)/cpchain\" to launch cpchain."

cpchain-race:
	build/env.sh go run build/ci.go raceInstall ./cmd/cpchain
	@echo "Done building."
	@echo "Run \"$(GOBIN)/cpchain\" to launch cpchain."

bootnode:
	build/env.sh go run build/ci.go install ./tools/bootnode
	@echo "Done building."
	@echo "Run \"$(GOBIN)/bootnode\" to launch bootnode."

abigen:
	build/env.sh go run build/ci.go install ./tools/abigen
	@echo "Done building."
	@echo "Run \"$(GOBIN)/abigen\" to launch abigen."

smartcontract:
	build/env.sh go run build/ci.go install ./tools/smartcontract
	@echo "Done building."
	@echo "Run \"$(GOBIN)/smartcontracts\" to launch smartcontract."

ecpubkey:
	build/env.sh go run build/ci.go install ./tools/ecpubkey
	@echo "Done building."
	@echo "Run \"$(GOBIN)/ecpubkey\" to launch ecpubkey."

updateproxycontract:
	build/env.sh go run build/ci.go install ./tools/smartcontract/updateproxycontract
	@echo "Done building."
	@echo "Run \"$(GOBIN)/updateproxycontract\" to launch updateproxycontract."

findimpeach:
	build/env.sh go run build/ci.go install ./tools/findimpeach
	@echo "Done building."
	@echo "Run \"$(GOBIN)/findimpeach\" to lanch findimpeach."

console:
	build/env.sh go run build/ci.go install ./tools/console
	@echo "Done building."
	@echo "Run \"$(GOBIN)/console\" to manage cpchain node."

testtool:
	build/env.sh go run build/ci.go install ./tools/smartcontract/testtool
	@echo "Done building."
	@echo "Run \"$(GOBIN)/testtool\" to launch testtool."

test: all
	env IGNORE_NTP_CHECK=true build/env.sh go run build/ci.go test

test-nocache: all
	env IGNORE_NTP_CHECK=true build/env.sh go run build/ci.go noCacheTest

test-coverage: all
	env IGNORE_NTP_CHECK=true build/env.sh go run build/ci.go test -coverage
	#go tool cover -html=build/_workspace/coverage.out -o build/_workspace/coverage.html
	#go tool cover -func=build/_workspace/coverage.out -o build/_workspace/coverage.txt
	#go get github.com/t-yuki/gocover-cobertura
	#gocover-cobertura < build/_workspace/coverage.out >  build/_workspace/cobertura.xml

test-race: all
	env IGNORE_NTP_CHECK=true build/env.sh go run build/ci.go raceTest

test-race-nocache: all
	env IGNORE_NTP_CHECK=true build/env.sh go run build/ci.go noCacheRaceTest

lint: ## Run linters.
	build/env.sh go run build/ci.go lint

clean:
	rm -fr build/_workspace/pkg/ $(GOBIN)/*

# The devtools target installs tools required for 'go generate'.
# You need to put $GOBIN (or $GOPATH/bin) in your PATH to use 'go generate'.

devtools:
	env GOBIN= go get -u golang.org/x/tools/cmd/stringer
	env GOBIN= go get -u github.com/kevinburke/go-bindata/go-bindata
	env GOBIN= go get -u github.com/fjl/gencodec
	env GOBIN= go get -u github.com/golang/protobuf/protoc-gen-go
	env GOBIN= go install ./cmd/abigen
	@type "npm" 2> /dev/null || echo 'Please install node.js and npm'
	@type "solc" 2> /dev/null || echo 'Please install solc'
	@type "protoc" 2> /dev/null || echo 'Please install protoc'

# Cross Compilation Targets (xgo)

cpchain-cross: cpchain-linux cpchain-darwin cpchain-windows
	@echo "Full cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-*

#cpchain-linux: cpchain-linux-386 cpchain-linux-amd64 cpchain-linux-arm cpchain-linux-mips64 cpchain-linux-mips64le
cpchain-linux: cpchain-linux-386 cpchain-linux-amd64 console-linux-386 console-linux-amd64
	@echo "Linux cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-linux-*

cpchain-linux-386:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=linux/386 -v ./cmd/cpchain
	@echo "Linux 386 cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-linux-* | grep 386

cpchain-linux-amd64:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=linux/amd64 -v ./cmd/cpchain
	@echo "Linux amd64 cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-linux-* | grep amd64

console-linux-386:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=linux/386 -v ./tools/console
	@echo "Linux 386 cross compilation done:"
	@ls -ld $(GOBIN)/console-linux-* | grep 386

console-linux-amd64:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=linux/amd64 -v ./tools/console
	@echo "Linux amd64 cross compilation done:"
	@ls -ld $(GOBIN)/console-linux-* | grep amd64

cpchain-linux-arm: cpchain-linux-arm-5 cpchain-linux-arm-6 cpchain-linux-arm-7 cpchain-linux-arm64
	@echo "Linux ARM cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-linux-* | grep arm

cpchain-linux-arm-5:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=linux/arm-5 -v ./cmd/cpchain
	@echo "Linux ARMv5 cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-linux-* | grep arm-5

cpchain-linux-arm-6:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=linux/arm-6 -v ./cmd/cpchain
	@echo "Linux ARMv6 cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-linux-* | grep arm-6

cpchain-linux-arm-7:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=linux/arm-7 -v ./cmd/cpchain
	@echo "Linux ARMv7 cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-linux-* | grep arm-7

cpchain-linux-arm64:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=linux/arm64 -v ./cmd/cpchain
	@echo "Linux ARM64 cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-linux-* | grep arm64

cpchain-linux-mips:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=linux/mips --ldflags '-extldflags "-static"' -v ./cmd/cpchain
	@echo "Linux MIPS cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-linux-* | grep mips

cpchain-linux-mipsle:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=linux/mipsle --ldflags '-extldflags "-static"' -v ./cmd/cpchain
	@echo "Linux MIPSle cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-linux-* | grep mipsle

cpchain-linux-mips64:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=linux/mips64 --ldflags '-extldflags "-static"' -v ./cmd/cpchain
	@echo "Linux MIPS64 cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-linux-* | grep mips64

cpchain-linux-mips64le:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=linux/mips64le --ldflags '-extldflags "-static"' -v ./cmd/cpchain
	@echo "Linux MIPS64le cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-linux-* | grep mips64le

cpchain-darwin: cpchain-darwin-386 cpchain-darwin-amd64 console-darwin-386 console-darwin-amd64
	@echo "Darwin cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-darwin-*

cpchain-darwin-386:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=darwin/386 -v ./cmd/cpchain
	@echo "Darwin 386 cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-darwin-* | grep 386

cpchain-darwin-amd64:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=darwin/amd64 -v ./cmd/cpchain
	@echo "Darwin amd64 cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-darwin-* | grep amd64

console-darwin-386:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=darwin/386 -v ./tools/console
	@echo "Darwin 386 cross compilation done:"
	@ls -ld $(GOBIN)/console-darwin-* | grep 386

console-darwin-amd64:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=darwin/amd64 -v ./tools/console
	@echo "Darwin amd64 cross compilation done:"
	@ls -ld $(GOBIN)/console-darwin-* | grep amd64

cpchain-windows: cpchain-windows-386 cpchain-windows-amd64 console-windows-386 console-windows-amd64
	@echo "Windows cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-windows-*

cpchain-windows-386:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=windows/386 -v ./cmd/cpchain
	@echo "Windows 386 cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-windows-* | grep 386

cpchain-windows-amd64:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=windows/amd64 -v ./cmd/cpchain
	@echo "Windows amd64 cross compilation done:"
	@ls -ld $(GOBIN)/cpchain-windows-* | grep amd64

console-windows-386:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=windows/386 -v ./tools/console
	@echo "Windows 386 cross compilation done:"
	@ls -ld $(GOBIN)/console-windows-* | grep 386

console-windows-amd64:
	build/env.sh go run build/ci.go xgo -- --go=$(GO) --targets=windows/amd64 -v ./tools/console
	@echo "Windows amd64 cross compilation done:"
	@ls -ld $(GOBIN)/console-windows-* | grep amd64

# invoke make test inside docker
dev-test:
	docker build -f Dockerfile.dev .
	@echo "chain test in docker done"


dev-init:
	@cp  dev/git-pre-commit-hook  .git/hooks/pre-commit
	@echo "move pre-commit-hook to .git/hooks/pre-commit"

dev-tools:
	go get -u github.com/fjl/gencodec

docs:
	@env UID=$$(id -u) GID=$$(id -g) docker-compose -f docs/docker/docker-compose.yml run --rm docs sphinx-build -b html ./ _build

docs-serve:
	@env UID=$$(id -u) GID=$$(id -g) docker-compose -f docs/docker/docker-compose.yml run --name cpchain_docs -d --service-ports --rm serve python3 docker/app.py

docs-serve-clean:
	docker rm -f cpchain_docs

docs-clean:
	rm -fr docs/_build

docs-mv-solidity:
	rm -rf docs/_build/solidity
	mkdir docs/_build/solidity

docs-cp-solidity:
	cp -rf docs/solidity/docs/_build/* docs/_build/solidity/

docs-solidity: docs-mv-solidity docs-cp-solidity
