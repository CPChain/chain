package backend_test

import (
	"fmt"
	"io"
	"log"
	"math/big"
	"math/rand"
	"reflect"
	"sync/atomic"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/core/vm"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/p2p"
	"github.com/ethereum/go-ethereum/p2p/discover"
)

const (
	DefaultMaxInitBlockNumber           = 180
	NormalMode                dpor.Mode = iota
)

var (
	testBankKey, _  = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	testBank        = crypto.PubkeyToAddress(testBankKey.PublicKey)
	testBankBalance = new(big.Int).Mul(big.NewInt(10000000), big.NewInt(configs.Cpc))
)

// MsgPipeRW is an endpoint of a MsgReadWriter pipe.
type MsgPipeRW struct {
	w       chan<- p2p.Msg
	r       <-chan p2p.Msg
	closing chan struct{}
	closed  *int32
}

// MsgPipe creates a message pipe. Reads on one end are matched
// with writes on the other. The pipe is full-duplex, both ends
// implement MsgReadWriter.
func MsgPipe() (*MsgPipeRW, *MsgPipeRW) {
	var (
		c1, c2  = make(chan p2p.Msg), make(chan p2p.Msg)
		closing = make(chan struct{})
		closed  = new(int32)
		rw1     = &MsgPipeRW{c1, c2, closing, closed}
		rw2     = &MsgPipeRW{c2, c1, closing, closed}
	)
	return rw1, rw2
}

// eofSignal wraps a reader with eof signaling. the eof channel is
// closed when the wrapped reader returns an error or when count bytes
// have been read.
type eof struct {
	wrapped io.Reader
	count   uint32 // number of bytes left
	eof     chan<- struct{}
}

// note: when using eofSignal to detect whether a message payload
// has been read, Read might not be called for zero sized messages.
func (r *eof) Read(buf []byte) (int, error) {
	if r.count == 0 {
		if r.eof != nil {
			r.eof <- struct{}{}
			r.eof = nil
		}
		return 0, io.EOF
	}

	max := len(buf)
	if int(r.count) < len(buf) {
		max = int(r.count)
	}
	n, err := r.wrapped.Read(buf[:max])
	r.count -= uint32(n)
	if (err != nil || r.count == 0) && r.eof != nil {
		r.eof <- struct{}{} // tell Peer that msg has been consumed
		r.eof = nil
	}
	return n, err
}

// WriteMsg sends a messsage on the pipe.
// It blocks until the receiver has consumed the message payload.
func (p *MsgPipeRW) WriteMsg(msg p2p.Msg) error {
	if atomic.LoadInt32(p.closed) == 0 {
		consumed := make(chan struct{}, 1)
		msg.Payload = &eof{msg.Payload, msg.Size, consumed}
		select {
		case p.w <- msg:
			if msg.Size > 0 {
				// wait for payload read or discard
				select {
				case <-consumed:
				case <-p.closing:
				}
			}
			return nil
		case <-p.closing:
		}
	}
	return p2p.ErrPipeClosed
}

// ReadMsg returns a message sent on the other end of the pipe.
func (p *MsgPipeRW) ReadMsg() (p2p.Msg, error) {
	if atomic.LoadInt32(p.closed) == 0 {
		select {
		case msg := <-p.r:
			return msg, nil
		case <-p.closing:
		}
	}
	return p2p.Msg{}, p2p.ErrPipeClosed
}

func NewPeerForTest() *p2p.Peer {
	var id discover.NodeID
	rand.Read(id[:])
	peer := p2p.NewPeer(id, "peer", nil)
	return peer
}

func generateABatchAccounts(n int) []common.Address {
	var addresses []common.Address
	for i := 1; i < n; i++ {
		addresses = append(addresses, common.HexToAddress("0x"+fmt.Sprintf("%040x", i)))
	}
	return addresses
}

func NewDpor() *dpor.Dpor {
	proposers := generateABatchAccounts(5)
	validaters := generateABatchAccounts(5)
	snapshot := dpor.NewSnapshot(&configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3, MaxInitBlockNumber: DefaultMaxInitBlockNumber}, 827, common.Hash{}, proposers, validaters, NormalMode)
	d := &dpor.Dpor{}
	d.SetCurrentSnap(snapshot)

	return d
}

func TestDialer_AddPeer(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	_, p, _, _ := dialer.AddPeer(11, peer, conn, "ss", nil, 33, 34)
	equalSigner := reflect.DeepEqual(p, nil)
	if equalSigner {
		t.Error("Add peer failed...")
	}

}

func TestDialer_isCurrentOrFutureProposer(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	proposer := common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")

	term := d.TermOf(d.CurrentSnap().Number)
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	dialer.AddRemoteProposer(11, 33, peer, conn, proposer)
	wantResult := dialer.IsCurrentOrFutureProposer(proposer, term, term+1)
	if wantResult {
		t.Error("Call function IsCurrentOrFutureProposer failed...")
	}
}

func TestDialer_isCurrentOrFutureValidater(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	validater := common.HexToAddress("0x" + fmt.Sprintf("%040x", 3))
	term := d.TermOf(d.CurrentSnap().Number)

	wantResult := dialer.IsCurrentOrFutureValidator(validater, term, term+1)
	if !wantResult {
		t.Error("Call function IsCurrentOrFutureProposer failed...")
	}
}

func TestDialer_Proposers(t *testing.T) {
	dialer := backend.NewDialer()
	addr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 67))
	addr1 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 518))
	rs := backend.NewRemoteProposer(addr)
	dialer.SetProposer(addr1.Hex(), rs)
	_, wantResult := dialer.GetProposer(addr1.Hex())
	if !wantResult {
		t.Error("SetDialer proposer failed")
	}
}

func TestDialer_Validators(t *testing.T) {
	dialer := backend.NewDialer()
	addr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 67))
	addr1 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 518))
	rs := backend.NewRemoteValidator(addr)
	dialer.SetValidator(addr1.Hex(), rs)
	_, wantResult := dialer.GetValidator(addr1.Hex())
	if !wantResult {
		t.Error("SetDialer proposer failed")
	}
}

func TestDialer_AddRemoteProposer(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	addr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 666))
	dialer.AddRemoteProposer(11, 33, peer, conn, addr)
	_, wantResult := dialer.GetProposer(addr.Hex())
	if !wantResult {
		t.Error("AddRemote proposer failed")
	}

}

func TestDialer_AddRemoteValidater(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	addr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 666))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr)
	_, wantResult := dialer.GetValidator(addr.Hex())
	if !wantResult {
		t.Error("AddRemote validater failed")
	}

}

func TestDialer_RemoveRemoteProposers(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	addr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 666))
	dialer.AddRemoteProposer(11, 33, peer, conn, addr)
	dialer.RemoveRemoteProposers(addr.Hex())
	_, wantResult := dialer.GetProposer(addr.Hex())
	if wantResult {
		t.Error("Remove remoteproposer failed")
	}
}

func TestDialer_RemoveRemoteValidater(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	addr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 42114))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr)
	dialer.RemoveRemoteValidators(addr.Hex())
	_, wantResult := dialer.GetValidator(addr.Hex())
	if wantResult {
		t.Error("Remove remoteproposer failed")
	}
}

func TestDialer_UpdateRemoteProposers(t *testing.T) {
	proposers := generateABatchAccounts(6)
	dialer := backend.NewDialer()
	d := NewDpor()
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	term := d.TermOf(d.CurrentSnap().Number)
	proposer := common.HexToAddress("0x" + fmt.Sprintf("%040x", 5))
	_, beforeResult := dialer.GetProposer(proposer.Hex())
	err := dialer.UpdateRemoteProposers(term, proposers)
	if err != nil {
		log.Fatal(err.Error())
	}
	_, afterResult := dialer.GetProposer(proposer.Hex())
	equalSigner := reflect.DeepEqual(beforeResult, afterResult)
	if equalSigner {
		t.Error("Update remote proposers failed...")
	}

}

func TestDialer_AllUselessProposers(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	chain := newBlockchain_contractAddr(22)
	d.SetChainConfig(chain)
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	term := d.TermOf(d.CurrentSnap().Number)
	proposers := generateABatchAccounts(6)
	err := dialer.UpdateRemoteProposers(term, proposers)
	if err != nil {
		log.Fatal(err.Error())
	}
	equalSigner := reflect.DeepEqual(nil, dialer.AllUselessProposers())
	if equalSigner {
		t.Error("Get AllUselessProposers failed...")
	}

}

func newBlockchain_contractAddr(n int) *core.BlockChain {
	db := database.NewMemDatabase()
	remoteDB := database.NewIpfsDbWithAdapter(database.NewFakeIpfsAdapter())
	gspec := core.DefaultGenesisBlock()
	gspec.GasLimit = 100000000
	gspec.Alloc = core.GenesisAlloc{testBank: {Balance: testBankBalance}}
	genesis := gspec.MustCommit(db)
	config := gspec.Config
	dporConfig := config.Dpor
	dporFakeEngine := dpor.NewFaker(dporConfig, db)
	//Define three accounts to simulate transactions with
	acc1Key, _ := crypto.HexToECDSA("8a1f9a8f95be41cd7ccb6168179afb4504aefe388d1e14474d32c45c72ce7b7a")
	acc2Key, _ := crypto.HexToECDSA("49a7b37aa6f6645917e7b807e9d1c00d4fa71f18343b0d4122a4d2df64dd6fee")
	acc1Addr := crypto.PubkeyToAddress(acc1Key.PublicKey)
	acc2Addr := crypto.PubkeyToAddress(acc2Key.PublicKey)
	generator := func(i int, block *core.BlockGen) {
		switch i {
		case 0:
			// In block 1, the test bank sends account #1 some ether.
			tx, _ := types.SignTx(types.NewTransaction(block.TxNonce(testBank), acc1Addr, big.NewInt(100000), configs.TxGas, nil, nil), types.HomesteadSigner{}, testBankKey)
			block.AddTx(tx)
		case 1:
			// In block 2, the test bank sends some more ether to account #1.
			// acc1Addr passes it on to account #2.
			tx1, _ := types.SignTx(types.NewTransaction(block.TxNonce(testBank), acc1Addr, big.NewInt(1000), configs.TxGas, nil, nil), types.HomesteadSigner{}, testBankKey)
			tx2, _ := types.SignTx(types.NewTransaction(block.TxNonce(acc1Addr), acc2Addr, big.NewInt(1000), configs.TxGas, nil, nil), types.HomesteadSigner{}, acc1Key)
			block.AddTx(tx1)
			block.AddTx(tx2)

		}
	}

	blocks, _ := core.GenerateChain(config, genesis, dporFakeEngine, db, remoteDB, n, generator)
	blockchain, _ := core.NewBlockChain(db, nil, gspec.Config, dporFakeEngine, vm.Config{}, remoteDB, nil)
	_, _ = blockchain.InsertChain(blocks)
	backend := backends.NewDporSimulatedBackendWithExistsBlockchain(db, blockchain, config)
	backend.Commit()
	return blockchain
}

func Test_ProposersOfTerm(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	term := d.TermOf(d.CurrentSnap().Number)
	proposers := generateABatchAccounts(6)
	err := dialer.UpdateRemoteProposers(term, proposers)
	if err != nil {
		log.Fatal(err.Error())
	}
	if wantResult := dialer.ProposersOfTerm(term); reflect.DeepEqual(wantResult, nil) {
		t.Error("Get proposers of term failed...")
	}

}

func Test_ValidatersOfTerm(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	term := d.TermOf(d.CurrentSnap().Number)
	addr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 666))
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	dialer.AddRemoteValidator(11, 33, peer, conn, addr)
	fmt.Println(dialer.ValidatorsOfTerm(term))
	if wantResult := dialer.ValidatorsOfTerm(term); reflect.DeepEqual(wantResult, nil) {
		t.Error("Get proposers of term failed...")
	}

}

func TestDialer_EnoughValidatorsOfTerm(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	conf := &configs.DporConfig{}
	conf.FaultyNumber = 2
	d.SetConfig(conf)
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	term := d.TermOf(d.CurrentSnap().Number)
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	addr1 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 3))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr1)
	addr2 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 4))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr2)
	addr3 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 5))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr3)
	addr4 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 1))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr4)
	addr5 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 2))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr5)
	_, ok := dialer.EnoughValidatorsOfTerm(term)
	if !ok {
		t.Error("Enough Validators Of Term test failed...")
	}
}

func TestDialer_EnoughImpeachValidatorsOfTerm(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	conf := &configs.DporConfig{}
	conf.FaultyNumber = 1
	d.SetConfig(conf)
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	term := d.TermOf(d.CurrentSnap().Number)
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	addr1 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 3))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr1)
	addr2 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 4))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr2)
	addr3 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 5))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr3)
	_, ok := dialer.EnoughImpeachValidatorsOfTerm(term)
	if !ok {
		t.Error("Enough Validators Of Term test failed...")
	}
}

func TestDialer_PeerInfos(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	addr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 666))
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	dialer.AddRemoteValidator(11, 33, peer, conn, addr)
	peers, _ := dialer.PeerInfos()
	equalSigner := reflect.DeepEqual(nil, peers)
	if equalSigner {
		t.Error("Get peerInfos failed...")
	}
}
