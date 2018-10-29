package cpc

import (
	"bitbucket.org/cpchain/chain/api/v1/admin"
	"bitbucket.org/cpchain/chain/api/v1/common"
	"bitbucket.org/cpchain/chain/types"
	"compress/gzip"
	"fmt"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/grpc-ecosystem/grpc-gateway/runtime"
	"golang.org/x/net/context"
	"google.golang.org/grpc"
	"io"
	"os"
	"strings"
)

// ChainManager is the collection of Ethereum full node-related APIs
// exposed over the private admin endpoint.
type ChainManager struct {
	c *CpchainService
}

// NewAdminManager creates a new API definition for the full node private
// admin methods of the Ethereum service.
func NewAdminManager(c *CpchainService) *ChainManager {
	return &ChainManager{c: c}
}

// IsPublic if public default
func (c *ChainManager) IsPublic() bool {
	return false
}

// Namespace namespace
func (c *ChainManager) Namespace() string {
	return "admin"
}

// RegisterServer register api to grpc
func (c *ChainManager) RegisterServer(s *grpc.Server) {
	admin.RegisterAdminManagerServer(s, c)
}

// RegisterGateway register api to restfull json
func (c *ChainManager) RegisterGateway(ctx context.Context, mux *runtime.ServeMux, endpoint string, opts []grpc.DialOption) {
	admin.RegisterAdminManagerHandlerFromEndpoint(ctx, mux, endpoint, opts)
}

// ExportChain exports the current blockchain into a local file.
func (api *ChainManager) ExportChain(ctx context.Context, file *admin.File) (*common.IsOk, error) {
	// Make sure we can create the file to export into
	out, err := os.OpenFile(file.File, os.O_CREATE|os.O_WRONLY|os.O_TRUNC, os.ModePerm)
	if err != nil {
		return &common.IsOk{IsOk: false}, err
	}
	defer out.Close()

	var writer io.Writer = out
	if strings.HasSuffix(file.File, ".gz") {
		writer = gzip.NewWriter(writer)
		defer writer.(*gzip.Writer).Close()
	}

	// Export the blockchain
	if err := api.c.BlockChain().Export(writer); err != nil {
		return &common.IsOk{IsOk: false}, err
	}
	return &common.IsOk{IsOk: true}, nil
}

// ImportChain imports a blockchain from a local file.
func (api *ChainManager) ImportChain(ctx context.Context, file *admin.File) (*common.IsOk, error) {
	// Make sure the can access the file to import
	in, err := os.Open(file.File)
	if err != nil {
		return &common.IsOk{IsOk: false}, err
	}
	defer in.Close()

	var reader io.Reader = in
	if strings.HasSuffix(file.File, ".gz") {
		if reader, err = gzip.NewReader(reader); err != nil {
			return &common.IsOk{IsOk: false}, err
		}
	}

	// Run actual the import in pre-configured batches
	stream := rlp.NewStream(reader, 0)

	blocks, index := make([]*types.Block, 0, 2500), 0
	for batch := 0; ; batch++ {
		// Load a batch of blocks from the input file
		for len(blocks) < cap(blocks) {
			block := new(types.Block)
			if err := stream.Decode(block); err == io.EOF {
				break
			} else if err != nil {
				return &common.IsOk{IsOk: false}, fmt.Errorf("block %d: failed to parse: %v", index, err)
			}
			blocks = append(blocks, block)
			index++
		}
		if len(blocks) == 0 {
			break
		}

		if hasAllBlocks(api.c.BlockChain(), blocks) {
			blocks = blocks[:0]
			continue
		}
		// Import the batch and reset the buffer
		if _, err := api.c.BlockChain().InsertChain(blocks); err != nil {
			return &common.IsOk{IsOk: false}, fmt.Errorf("batch %d: failed to insert: %v", batch, err)
		}
		blocks = blocks[:0]
	}
	return &common.IsOk{IsOk: true}, nil
}
