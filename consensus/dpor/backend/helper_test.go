package backend

import (
	"math/big"
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

func newRecentBlocks() *RecentBlocks {
	db := database.NewMemDatabase()
	rb := NewRecentBlocks(db)
	return rb
}

func TestHandlerHelper_AddBlock(t *testing.T) {
	rb := newRecentBlocks()
	unknownBlock := types.NewBlock(&types.Header{GasLimit: configs.DefaultGasLimitPerBlock}, nil, nil)
	err := rb.AddBlock(unknownBlock)
	if err != nil {
		t.Error("Handler add block failed...")
	}
}

func TestHandlerHelper_RemoveBlock(t *testing.T) {
	rb := newRecentBlocks()
	unknownBlock := types.NewBlock(&types.Header{GasLimit: configs.DefaultGasLimitPerBlock}, nil, nil)
	bi := NewBlockIdentifier(unknownBlock.Number().Uint64(), unknownBlock.Hash())
	err := rb.RemoveBlock(bi)
	if err != nil {
		t.Error("Handler remove block failed...")
	}
}

func TestHandlerHelper_GetBlock(t *testing.T) {
	rb := newRecentBlocks()
	unknownBlock := types.NewBlock(&types.Header{GasLimit: configs.DefaultGasLimitPerBlock}, nil, nil)

	bi := NewBlockIdentifier(unknownBlock.Number().Uint64(), unknownBlock.Hash())
	err := rb.AddBlock(unknownBlock)
	if err != nil {
		t.Error("Handler add block failed...")
	}
	c, _ := rb.GetBlock(bi)
	equalSigner := reflect.DeepEqual(c, unknownBlock)
	if !equalSigner {
		t.Error("Get Block failed...")
	}

}

func TestHandlerHelper_GetBlockIdentifiers(t *testing.T) {
	rb := newRecentBlocks()
	unknownBlock := types.NewBlock(&types.Header{GasLimit: configs.DefaultGasLimitPerBlock}, nil, nil)
	bid := NewBlockIdentifier(unknownBlock.Number().Uint64(), unknownBlock.Hash())
	err := rb.AddBlock(unknownBlock)
	if err != nil {
		t.Error("Handler add block failed...")
	}
	wantResult := contains(rb.GetBlockIdentifiers(), bid)
	if !wantResult {
		t.Error("Call GetBlockIdentifiers failed..")
	}
}

func contains(bs []BlockIdentifier, b BlockIdentifier) bool {
	for _, bi := range bs {
		if b.number == bi.number && b.hash == bi.hash {
			return true
		}
	}
	return false
}

func newHeader() *types.Header {
	return &types.Header{
		ParentHash:   common.HexToHash("0x83cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55"),
		Coinbase:     common.HexToAddress("0x8888f1F195AFa192CfeE860698584c030f4c9dB1"),
		StateRoot:    common.HexToHash("0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"),
		TxsRoot:      common.HexToHash("0x5fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptsRoot: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Number:       big.NewInt(888),
		GasLimit:     uint64(3141592),
		GasUsed:      uint64(21000),
		Time:         big.NewInt(1426516743),
		Extra:        []byte("0x0000000000000000000000000000000000000000000000000000000000000000095e7baea6a6c7c4c2dfeb977efac326af552d87e94b7b6c5a0e526a4d97f9768ad6097bde25c62ac05302acebd0730e3a18a058d7d1cb1204c4a092ef3dd127de235f15ffb4fc0d71469d1339df64650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"),
	}
}

func TestHandlerHelper_IsHeader(t *testing.T) {
	header := newHeader()
	bh := NewBOHFromHeader(header)
	wantResult := bh.IsHeader()
	if !wantResult {
		t.Error("Test isHeader failed...")
	}
}

func TestHandlerHelper_IsBlock(t *testing.T) {
	unknownBlock := types.NewBlock(&types.Header{GasLimit: configs.DefaultGasLimitPerBlock, Number: big.NewInt(886)}, nil, nil)
	bh := NewBOHFromBlock(unknownBlock)
	wantResult := bh.IsBlock()
	if !wantResult {
		t.Error("Test isBlock failed...")
	}
	equalSigner := reflect.DeepEqual(bh.IsBlock(), bh.IsHeader())
	if equalSigner {
		t.Error("Test Isblock or block failed...")
	}

}

func TestHandlerHelper_Number(t *testing.T) {
	unknownBlock := types.NewBlock(&types.Header{GasLimit: configs.DefaultGasLimitPerBlock, Number: big.NewInt(886)}, nil, nil)
	num := unknownBlock.Number()
	bh := NewBOHFromBlock(unknownBlock)
	bnum := bh.Number()
	equalSigner := reflect.DeepEqual(num.Uint64(), bnum)
	if !equalSigner {
		t.Error("Call BlockIdentifier number failed...")
	}

}

func TestHandlerHelper_Hash(t *testing.T) {
	header := newHeader()
	bh := NewBOHFromHeader(header)
	hash1 := header.Hash()
	hash2 := bh.Hash()
	equalSigner := reflect.DeepEqual(hash1, hash2)
	if !equalSigner {
		t.Error("Call BlockIdentifier hash failed...")
	}
}
