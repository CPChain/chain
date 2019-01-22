package backend

import (
	"fmt"
	"math/big"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
)

func TestImpeachment_restart(t *testing.T) {

	dpor := &FakeDpor{}
	returnCh := make(chan *types.Block)
	returnFn := func(block *types.Block) error {
		returnCh <- block
		return nil
	}
	im := NewImpeachment(dpor, returnFn)

	go im.Restart(4)
	<-time.After(1 * time.Millisecond)

	go im.Restart(5)
	<-time.After(1 * time.Millisecond)

	go im.Restart(6)
	<-time.After(1 * time.Millisecond)

	go im.Restart(7)

	select {
	case block := <-returnCh:
		fmt.Println(block)
	}

}

type FakeDpor struct {
}

func (fd *FakeDpor) TermOf(number uint64) uint64 {
	panic("not implemented")
}

func (fd *FakeDpor) FutureTermOf(number uint64) uint64 {
	panic("not implemented")
}

func (fd *FakeDpor) VerifyProposerOf(signer common.Address, term uint64) (bool, error) {
	panic("not implemented")
}

func (fd *FakeDpor) VerifyValidatorOf(signer common.Address, term uint64) (bool, error) {
	panic("not implemented")
}

func (fd *FakeDpor) ValidatorsOf(number uint64) ([]common.Address, error) {
	panic("not implemented")
}

func (fd *FakeDpor) ProposersOf(number uint64) ([]common.Address, error) {
	panic("not implemented")
}

func (fd *FakeDpor) ValidatorsOfTerm(term uint64) ([]common.Address, error) {
	panic("not implemented")
}

func (fd *FakeDpor) ProposersOfTerm(term uint64) ([]common.Address, error) {
	panic("not implemented")
}

func (fd *FakeDpor) VerifyHeaderWithState(header *types.Header, state consensus.State) error {
	panic("not implemented")
}

func (fd *FakeDpor) ValidateBlock(block *types.Block, verifySigs bool, verifyProposers bool) error {
	panic("not implemented")
}

func (fd *FakeDpor) SignHeader(header *types.Header, state consensus.State) error {
	panic("not implemented")
}

func (fd *FakeDpor) BroadcastBlock(block *types.Block, prop bool) {
	panic("not implemented")
}

func (fd *FakeDpor) InsertChain(block *types.Block) error {
	panic("not implemented")
}

func (fd *FakeDpor) Status() *consensus.PbftStatus {
	header := &types.Header{Number: big.NewInt(3)}
	return &consensus.PbftStatus{
		Head: header,
	}
}

func (fd *FakeDpor) StatusUpdate() error {
	panic("not implemented")
}

func (fd *FakeDpor) CreateImpeachBlock() (*types.Block, error) {

	return &types.Block{}, nil
}

func (fd *FakeDpor) GetCurrentBlock() *types.Block {
	panic("not implemented")
}

func (fd *FakeDpor) HasBlockInChain(hash common.Hash, number uint64) bool {
	panic("not implemented")
}

func (fd *FakeDpor) ImpeachTimeout() time.Duration {
	return time.Second * 3
}

func (fd *FakeDpor) ECRecoverSigs(header *types.Header, state consensus.State) ([]common.Address, []types.DporSignature, error) {
	panic("not implemented")
}

func (fd *FakeDpor) UpdatePrepareSigsCache(validator common.Address, hash common.Hash, sig types.DporSignature) {
	panic("not implemented")
}

func (fd *FakeDpor) UpdateFinalSigsCache(validator common.Address, hash common.Hash, sig types.DporSignature) {
	panic("not implemented")
}

func (fd *FakeDpor) GetMac() (string, []byte, error) {
	panic("not implemented")
}
