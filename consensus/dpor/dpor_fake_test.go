package dpor

import (
	"errors"
	"math/big"
	"time"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

type FakeReader struct {
	consensus.ChainReader
}

func (*FakeReader) Config() *configs.ChainConfig {
	// TODO @hmw populate this config
	return &configs.ChainConfig{}
}

func (*FakeReader) GetHeaderByNumber(number uint64) *types.Header {
	return &types.Header{Number: big.NewInt(0), Time: big.NewInt(0).Sub(big.NewInt(time.Now().Unix()), big.NewInt(100))}
}

type fakeDporUtil struct {
	dporUtil
	success bool
}

func (f *fakeDporUtil) calcDifficulty(snap *DporSnapshot, signer common.Address) *big.Int {
	if f.success {
		return big.NewInt(10)
	} else {
		return nil
	}
}

type fakeDporHelper struct {
	dporUtil
	verifySuccess   bool
	snapshotSuccess bool
}

func (f *fakeDporHelper) verifyHeader(c *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error {
	if f.verifySuccess {
		return nil
	} else {
		return errors.New("verify Header")
	}
}

func (*fakeDporHelper) verifyCascadingFields(c *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error {
	panic("implement me")
}

func (f *fakeDporHelper) snapshot(c *Dpor, chain consensus.ChainReader, number uint64, hash common.Hash, parents []*types.Header) (*DporSnapshot, error) {
	if f.snapshotSuccess {
		return &DporSnapshot{}, nil
	} else {
		return nil, errors.New("err")
	}

}

func (*fakeDporHelper) verifySeal(c *Dpor, chain consensus.ChainReader, header *types.Header, parents []*types.Header, refHeader *types.Header) error {
	panic("implement me")
}

type fakeSnapshot struct {
	Snapshot
}
