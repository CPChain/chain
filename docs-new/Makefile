export version="0.0.1"

all: build-image run-image

prod:
	@yarn run docs:build

build-image: prod
	@docker build -t cpchain-chain-docs:$(version) .

run-image:
	@echo "Preview on http://127.0.0.1:8090/"
	@docker run -it --rm -p 8090:80 cpchain-chain-docs:$(version)
