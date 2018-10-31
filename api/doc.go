package api

// for Ubuntu: Download protoc compile from here
// unzip it, and then add the binary file to system path;
// mkdir protoc && cd protoc
// download https://github.com/protocolbuffers/protobuf/releases/download/v3.6.1/protoc-3.6.1-linux-x86_64.zip
// unzip protoc-3.6.1-linux-x86_64.zip -d protoc
// sudo mv protoc /usr/local/protoc
// add `export PATH=$PATH:/usr/local/protoc/bin` to your bashrc or zshrc file
// then go get -u github.com/golang/protobuf/protoc-gen-go

// go get -u github.com/grpc-ecosystem/grpc-gateway/protoc-gen-grpc-gateway
// go get -u github.com/grpc-ecosystem/grpc-gateway/protoc-gen-swagger
// go get -u github.com/golang/protobuf/protoc-gen-go

//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --go_out=plugins=grpc,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/common/common.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --grpc-gateway_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/common/common.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --swagger_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/common/common.proto

//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --go_out=plugins=grpc,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/admin/admin.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --grpc-gateway_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/admin/admin.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --swagger_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/admin/admin.proto

//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --go_out=plugins=grpc,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/cpc/cpc.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --grpc-gateway_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/cpc/cpc.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --swagger_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/cpc/cpc.proto

//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --go_out=plugins=grpc,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/debug/debug.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --grpc-gateway_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/debug/debug.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --swagger_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/debug/debug.proto

//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --go_out=plugins=grpc,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/miner/miner.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --grpc-gateway_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/miner/miner.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --swagger_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/miner/miner.proto

//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --go_out=plugins=grpc,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/net/net.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --grpc-gateway_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/net/net.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --swagger_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/net/net.proto

//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --go_out=plugins=grpc,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/personal/personal.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --grpc-gateway_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/personal/personal.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --swagger_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/personal/personal.proto

//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --go_out=plugins=grpc,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/txpool/txpool.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --grpc-gateway_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/txpool/txpool.proto
//go:generate protoc -I. -Iv1/ -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --swagger_out=logtostderr=true,Mcommon/common.proto=bitbucket.org/cpchain/chain/api/v1/common:. ./v1/txpool/txpool.proto
