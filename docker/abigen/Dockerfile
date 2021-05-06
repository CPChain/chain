FROM ethereum/solc:0.4.25

RUN sed -i 's/dl-cdn.alpinelinux.org/mirrors.aliyun.com/g' /etc/apk/repositories && apk update

RUN apk add --no-cache libc6-compat

RUN apk add go --no-cache

ENV GOPATH="/go"

ADD build/bin/abigen /usr/bin/abigen

RUN chmod +x /usr/bin/abigen

ADD . /go/src/bitbucket.org/cpchain/chain

WORKDIR /go/src/bitbucket.org/cpchain/chain

ENTRYPOINT []
