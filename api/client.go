package api

import (
	"context"
	"math/big"

	pb "bitbucket.org/cpchain/chain/api/v1/common"
	"bitbucket.org/cpchain/chain/api/v1/cpc"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"google.golang.org/grpc"
)

type Client struct {
	c *grpc.ClientConn
}

func Dial(rawurl string) (*Client, error) {
	return DialContext(context.Background(), rawurl)
}

func DialContext(ctx context.Context, rawurl string) (*Client, error) {
	c, err := grpc.DialContext(ctx, rawurl)
	if err != nil {
		return nil, err
	}
	return New(c), nil
}

func New(conn *grpc.ClientConn) *Client {
	return &Client{c: conn}
}

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

// HeaderByHash returns the block header with the given hash.
func (c *Client) HeaderByHash(ctx context.Context, hash common.Hash) (*types.Header, error) {
	// block, err := c.BlockByHash(ctx, hash)
	// if err != nil {
	// 	return nil, err
	// }
	// return ethapi.GRPCUnMarshalHeader(block), nil
	return nil, nil
}

// HeaderByNumber returns a block header from the current canonical chain. If number is
// nil, the latest known header is returned.
func (c *Client) HeaderByNumber(ctx context.Context, number *big.Int) (*types.Header, error) {
	// block, err := c.BlockByNumber(ctx, number)
	// if err != nil {
	// 	return nil, err
	// }
	// return ethapi.GRPCUnMarshalHeader(block), nil
	return nil, nil
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
