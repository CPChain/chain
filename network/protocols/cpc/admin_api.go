package cpc

import (
    "bitbucket.org/cpchain/chain/api/v1"
    "bitbucket.org/cpchain/chain/core"
    "bitbucket.org/cpchain/chain/types"
    "compress/gzip"
    "fmt"
    "github.com/ethereum/go-ethereum/rlp"
    "golang.org/x/net/context"
    "io"
    "os"
    "strings"
)

// ChainManager is the collection of Ethereum full node-related APIs
// exposed over the private admin endpoint.
type ChainManager struct {
    eth *CpchainService
}

// NewChainManager creates a new API definition for the full node private
// admin methods of the Ethereum service.
func NewChainManager(eth *CpchainService) *ChainManager {
    return &ChainManager{eth: eth}
}

// ExportChain exports the current blockchain into a local file.
func (api *ChainManager) ExportChain(ctx context.Context, file *protos.File) (*protos.IsOk, error) {
    // Make sure we can create the file to export into
    out, err := os.OpenFile(file.File, os.O_CREATE|os.O_WRONLY|os.O_TRUNC, os.ModePerm)
    if err != nil {
        return &protos.IsOk{IsOk:false}, err
    }
    defer out.Close()

    var writer io.Writer = out
    if strings.HasSuffix(file.File, ".gz") {
        writer = gzip.NewWriter(writer)
        defer writer.(*gzip.Writer).Close()
    }

    // Export the blockchain
    if err := api.eth.BlockChain().Export(writer); err != nil {
        return &protos.IsOk{IsOk:false}, err
    }
    return &protos.IsOk{IsOk:true}, nil
}

func hasAllBlocks(chain *core.BlockChain, bs []*types.Block) bool {
    for _, b := range bs {
        if !chain.HasBlock(b.Hash(), b.NumberU64()) {
            return false
        }
    }

    return true
}

// ImportChain imports a blockchain from a local file.
func (api *ChainManager) ImportChain(ctx context.Context, file *protos.File) (*protos.IsOk, error) {
    // Make sure the can access the file to import
    in, err := os.Open(file.File)
    if err != nil {
        return &protos.IsOk{IsOk:false}, err
    }
    defer in.Close()

    var reader io.Reader = in
    if strings.HasSuffix(file.File, ".gz") {
        if reader, err = gzip.NewReader(reader); err != nil {
            return &protos.IsOk{IsOk:false}, err
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
                return &protos.IsOk{IsOk:false}, fmt.Errorf("block %d: failed to parse: %v", index, err)
            }
            blocks = append(blocks, block)
            index++
        }
        if len(blocks) == 0 {
            break
        }

        if hasAllBlocks(api.eth.BlockChain(), blocks) {
            blocks = blocks[:0]
            continue
        }
        // Import the batch and reset the buffer
        if _, err := api.eth.BlockChain().InsertChain(blocks); err != nil {
            return &protos.IsOk{IsOk:false}, fmt.Errorf("batch %d: failed to insert: %v", batch, err)
        }
        blocks = blocks[:0]
    }
    return &protos.IsOk{IsOk:true}, nil
}
