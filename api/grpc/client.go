// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package grpc

import (
	"context"
	"math/big"

	pb "bitbucket.org/cpchain/chain/api/grpc/v1/common"
	"bitbucket.org/cpchain/chain/api/grpc/v1/cpc"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"google.golang.org/grpc"
)

type Client struct {
	c *grpc.ClientConn
}

// Dial listens the url and returns grpc client
func Dial(rawurl string) (*Client, error) {
	return DialContext(context.Background(), rawurl)
}

// DialContext returns a Clients with given rul
func DialContext(ctx context.Context, rawurl string) (*Client, error) {
	c, err := grpc.DialContext(ctx, rawurl)
	if err != nil {
		return nil, err
	}
	return New(c), nil
}

// New returns a Client
func New(conn *grpc.ClientConn) *Client {
	return &Client{c: conn}
}

// Close close the connections
func (c *Client) Close() {
	c.c.Close()
}

// Blockchain Access

// BlockByHash returns the given full block.
//
// Note that loading full blocks requires two requests. Use HeaderByHash
// if you don't need all transactions or uncle headers.

func (c *Client) BlockByHash(ctx context.Context, hash common.Hash) (*pb.Block, error) {
	args := &cpc.ChainReaderRequest{
		IsFull:    true,
		BlockHash: hash.Hex(),
	}
	return c.getBlock(ctx, "/protos_chain.PublicBlockChainAPI/GetBlockByHash", args)
	// err := c.cc.Invoke(ctx, "/cpc.ChainReader/GetBlockByHash", in, out, opts...)
}

// BlockByNumber returns a block from the current canonical chain. If number is nil, the
// latest known block is returned.
//
// Note that loading full blocks requires two requests. Use HeaderByNumber
// if you don't need all transactions or uncle headers.
func (c *Client) BlockByNumber(ctx context.Context, number *big.Int) (*pb.Block, error) {
	args := &cpc.ChainReaderRequest{
		IsFull:      true,
		BlockNumber: number.Int64(),
	}
	return c.getBlock(ctx, "/protos_chain.PublicBlockChainAPI/GetBlockByNumber", args)
	// err := c.cc.Invoke(ctx, "/cpc.ChainReader/GetBlockByNumber", in, out, opts...)
}

func (c *Client) getBlock(ctx context.Context, method string, in *cpc.ChainReaderRequest) (*pb.Block, error) {
	out := new(pb.Block)
	err := c.c.Invoke(ctx, method, in, out)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func GRPCUnMarshalHeader(b *pb.Block) *types.Header {
	header := new(types.Header)
	header.Nonce = types.EncodeNonce(b.Nonce)
	header.LogsBloom = types.BytesToBloom(b.LogsBloom)
	header.Number = new(big.Int).SetUint64(b.Number)
	header.GasUsed = b.GasUsed
	header.ParentHash = common.HexToHash(b.ParentHash)
	header.ReceiptsRoot = common.HexToHash(b.ReceiptsRoot)
	header.TxsRoot = common.HexToHash(b.TransactionsRoot)
	header.Time, _ = new(big.Int).SetString(b.Timestamp, 10)
	header.Extra = make([]byte, len(b.ExtraData))
	copy(header.Extra, b.ExtraData)
	header.Difficulty = new(big.Int).SetUint64(b.Difficulty)
	header.GasLimit = b.GasLimit
	header.StateRoot = common.HexToHash(b.StateRoot)
	header.MixHash = common.HexToHash(b.MixHash)
	return header
}

func GRPCUnMarshalBlock(b *pb.Block, inclTx bool, fullTx bool) (*types.Block, error) {
	header := GRPCUnMarshalHeader(b)
	return types.NewBlockWithHeader(header), nil
}

// HeaderByHash returns the block header with the given hash.
func (c *Client) HeaderByHash(ctx context.Context, hash common.Hash) (*types.Header, error) {
	block, err := c.BlockByHash(ctx, hash)
	if err != nil {
		return nil, err
	}
	return GRPCUnMarshalHeader(block), nil
}

// HeaderByNumber returns a block header from the current canonical chain. If number is
// nil, the latest known header is returned.
func (c *Client) HeaderByNumber(ctx context.Context, number *big.Int) (*types.Header, error) {
	block, err := c.BlockByNumber(ctx, number)
	if err != nil {
		return nil, err
	}
	return GRPCUnMarshalHeader(block), nil
}

// TransactionCount returns the total number of transactions in the given block.
func (c *Client) TransactionCount(ctx context.Context, blockHash common.Hash) (uint, error) {
	in := &pb.BlockHash{BlockHash: blockHash.Hex()}
	out := new(cpc.TransactionCount)
	err := c.c.Invoke(ctx, "/cpc.TransactionPoolReader/GetTransactionCountByBlockHash", in, out)
	if err != nil {
		return 0, nil
	}
	return uint(out.TransactionCount), nil
}
