// Package apis provides ...
package apis

// Generate gRPC stub
// ####example go:generate protoc -I/usr/local/include -I. -I$GOPATH/src -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --go_out=plugins=grpc:. *.proto
// go:generate protoc -I/usr/local/include -I. -I$GOPATH/src -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --go_out=plugins=grpc:. pb/chain/*.proto

// Generate reverse-proxy
// go:generate protoc -I/usr/local/include -I. -I$GOPATH/src -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --grpc-gateway_out=logtostderr=true:. pb/chain/*.proto

// Generate swagger definitions
// go:generate protoc -I/usr/local/include -I.  -I$GOPATH/src -I$GOPATH/src/github.com/grpc-ecosystem/grpc-gateway/third_party/googleapis --swagger_out=logtostderr=true:. pb/chain/*.proto

// go:generate protoc --go_out=import_prefix=bitbucket.org/cpchain/chain/apis:. pb/chain/PublicEthereumAPI.proto
