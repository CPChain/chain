package dpor

import (
	"encoding/json"
	"fmt"
	"math/big"
	"math/rand"
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	lru "github.com/hashicorp/golang-lru"
)

var (
	testBankKey, _  = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	testBank        = crypto.PubkeyToAddress(testBankKey.PublicKey)
	testBankBalance = new(big.Int).Mul(big.NewInt(10000), big.NewInt(configs.Cpc))
	rptAddr         common.Address
)

type fakeDb struct {
	dbType uint64
}

func (*fakeDb) Put(key []byte, value []byte) error {
	fmt.Println("executing db put")
	return nil
}

func (*fakeDb) Delete(key []byte) error {
	panic("implement me 1")
}

func (f *fakeDb) Get(key []byte) ([]byte, error) {
	fmt.Println("executing db put")
	if f.dbType == 1 {
		snap := new(DporSnapshot)
		blob, err := json.Marshal(snap)
		return blob, err
	}
	return []byte("dpor-ssss"), nil

}

func (*fakeDb) Has(key []byte) (bool, error) {
	panic("implement me3")
}

func (*fakeDb) Close() {
	panic("implement me4")
}

func (*fakeDb) NewBatch() database.Batch {
	panic("implement me5")
}

func Test_newSnapshot(t *testing.T) {
	snap := newSnapshot(&configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}, 1, common.Hash{}, getProposerAddress(), getValidatorAddress(), FakeMode)
	equal := reflect.DeepEqual(snap.ProposersOf(1), getProposerAddress())
	if !equal {
		t.Errorf("expect %v,get %v", true, equal)
	}
	candidates := snap.candidates()
	if len(candidates) != 0 {
		t.Errorf("expect 0 candidates,get %v", len(candidates))
	}
}

func bench_newSnapshot(b *testing.B) {
	b.ReportAllocs()
	b.ResetTimer()
	snap := newSnapshot(&configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}, 1, common.Hash{}, getProposerAddress(), getValidatorAddress(), FakeMode)
	b.Log("creates a new Snapshot with the specified startup parameters...Mode is :", snap.Mode)

}
func BenchmarkCreateSnapsshot(b *testing.B) {
	bench_newSnapshot(b)
}

func TestSnapshot_copy(t *testing.T) {
	snap := newSnapshot(&configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}, 1, common.Hash{}, getProposerAddress(), getValidatorAddress(), FakeMode)
	snap.Candidates = getCandidates()

	cpySnap := snap.copy()

	equal := reflect.DeepEqual(cpySnap.ProposersOf(1), getProposerAddress())
	if !equal {
		t.Errorf("expect %v,get %v", true, equal)
	}

	candidates := cpySnap.candidates()
	if len(candidates) != 3 {
		t.Errorf("expect 3 candidates,get %v", len(candidates))
	}
}

func TestSnapshot_setRecentProposers(t *testing.T) {
	snap := newSnapshot(&configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}, 1, common.Hash{}, getProposerAddress(), getValidatorAddress(), FakeMode)
	proposers := getCandidates()
	randterm := rand.Uint64()
	snap.setRecentProposers(randterm, proposers)

	ss := snap.RecentProposers[randterm]

	equal := reflect.DeepEqual(ss, proposers)
	if !equal {
		t.Errorf("setRecentProposers fail...")
	}

}

func TestSnapshot_setCandidates(t *testing.T) {
	snap := newSnapshot(&configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}, 1, common.Hash{}, getProposerAddress(), getValidatorAddress(), FakeMode)
	candidates := getCandidates()
	snap.setCandidates(candidates)
	sc := snap.Candidates
	equal := reflect.DeepEqual(sc, candidates)
	if !equal {
		t.Errorf("setCandidates fail...")
	}
}

func TestSnapshot_apply(t *testing.T) {
	type fields struct {
		config     *configs.DporConfig
		sigcache   *lru.ARCCache
		Number     uint64
		Hash       common.Hash
		Candidates []common.Address
	}
	type args struct {
		headers []*types.Header
	}
	testConfig := configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}
	testCache, _ := lru.NewARC(inMemorySnapshots)
	expectedResult := new(DporSnapshot)
	expectedResult.Number = 1
	expectedResult.config = &testConfig
	expectedResult.Candidates = getProposerAddress()
	//testHeader := make([]*types.Header, 0)
	tests := []struct {
		name    string
		fields  fields
		args    args
		want    *DporSnapshot
		wantErr bool
	}{
		{"empty header",
			fields{&testConfig,
				testCache,
				1,
				common.Hash{},
				getProposerAddress(),
			},
			args{
				nil,
			},
			expectedResult,
			false,
		},
		//TODO: Add a non-empty header
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := &DporSnapshot{
				config:     tt.fields.config,
				Number:     tt.fields.Number,
				Hash:       tt.fields.Hash,
				Candidates: tt.fields.Candidates,
			}
			got, err := s.apply(tt.args.headers, true, nil, nil)
			if (err != nil) != tt.wantErr {
				t.Errorf("DporSnapshot.apply(%v) error = %v, wantErr %v", tt.args.headers, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("DporSnapshot.apply(%v) = \n%v, want \n%v", tt.args.headers, got, tt.want)
			}
		})
	}
}

func TestSnapshot_updateRpts(t *testing.T) {
	type fields struct {
		config        *configs.DporConfig
		sigcache      *lru.ARCCache
		Number        uint64
		Hash          common.Hash
		Candidates    []common.Address
		RecentSigners map[uint64][]common.Address
	}
	type args struct {
		header *types.Header
	}
	tests := []struct {
		name    string
		fields  fields
		args    args
		want    rpt.RptList
		wantErr bool
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := &DporSnapshot{
				config: tt.fields.config,
				// sigcache:      tt.fields.sigcache,
				Number:     tt.fields.Number,
				Hash:       tt.fields.Hash,
				Candidates: tt.fields.Candidates,
				// RecentSigners: tt.fields.RecentSigners,
			}
			got, err := s.updateRpts(nil)
			if (err != nil) != tt.wantErr {
				t.Errorf("DporSnapshot.updateRpts(%v) error = %v, wantErr %v", tt.args.header, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("DporSnapshot.updateRpts(%v) = %v, want %v", tt.args.header, got, tt.want)
			}
		})
	}
}

func TestSnapshot_signers(t *testing.T) {
	snap := createSnapshot()
	proposers := snap.ProposersOf(snap.Number)
	equalSigner := reflect.DeepEqual(proposers, getProposerAddress())
	if !equalSigner {
		t.Errorf("expected isEqualSigner is %v,get %v", true, equalSigner)
	}
}

func TestSnapshot_isSigner(t *testing.T) {
	snap := newSnapshot(&configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}, 1, common.Hash{}, getProposerAddress()[1:2], getValidatorAddress(), FakeMode)
	isSinger, _ := snap.IsProposerOf(addr1, 1)
	if isSinger {
		t.Errorf("expected isSinger %v,get %v", false, isSinger)
	}
	isSinger, _ = snap.IsProposerOf(addr2, 1)
	if !isSinger {
		t.Errorf("expected isSinger %v,get %v", true, isSinger)
	}
}

func TestSnapshot_isLeaderErrorWhenBlockNumberIsZero(t *testing.T) {
	snap := createSnapshot()
	isLeader, err := snap.IsProposerOf(addr1, 0)
	if err == nil {
		t.Errorf("expect isLeader Error, get %v", isLeader)
	}
}

func TestSnapshot_isLeader(t *testing.T) {
	snap := createSnapshot()
	isLeader, err := snap.IsProposerOf(addr1, 1)
	if !isLeader || err != nil {
		t.Errorf("expect isLeader true, get %v", isLeader)
	}
	isLeader, err = snap.IsProposerOf(addr2, 2)
	if !isLeader || err != nil {
		t.Errorf("expect isLeader true, get %v", isLeader)
	}
	isLeader, err = snap.IsProposerOf(addr3, 3)
	if !isLeader || err != nil {
		t.Errorf("expect isLeader true, get %v", isLeader)
	}
}

func TestSnapshot_isNotLeader(t *testing.T) {
	snap := createSnapshot()
	isLeader, _ := snap.IsProposerOf(addr2, 1)
	if isLeader {
		t.Errorf("expect isLeader false get %v", isLeader)
	}
	isLeader, _ = snap.IsProposerOf(addr3, 1)
	if isLeader {
		t.Errorf("expect isLeader false get %v", isLeader)
	}
}

func createSnapshot() *DporSnapshot {
	proposers := getProposerAddress()
	validators := getValidatorAddress()
	config := &configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}
	// cache, _ := lru.NewARC(inmemorySnapshots)
	snap := newSnapshot(config, 1, common.Hash{}, proposers, validators, FakeMode)
	return snap
}

func TestSnapshot_candidates(t *testing.T) {
	type fields struct {
		config        *configs.DporConfig
		sigcache      *lru.ARCCache
		Number        uint64
		Hash          common.Hash
		Candidates    []common.Address
		RecentSigners map[uint64][]common.Address
	}
	tests := []struct {
		name   string
		fields fields
		want   []common.Address
	}{
		// TODO: Add test cases.
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := &DporSnapshot{
				config: tt.fields.config,
				// sigcache:      tt.fields.sigcache,
				Number:     tt.fields.Number,
				Hash:       tt.fields.Hash,
				Candidates: tt.fields.Candidates,
				// RecentSigners: tt.fields.RecentSigners,
			}
			if got := s.candidates(); !reflect.DeepEqual(got, tt.want) {
				t.Errorf("DporSnapshot.candidates() = %v, want %v", got, tt.want)
			}
		})
	}
}

func TestSnapshot_inturn(t *testing.T) {
	proposers := getProposerAddress()
	config := &configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}
	// cache, _ := lru.NewARC(inmemorySnapshots)
	snap := newSnapshot(config, 1, common.Hash{}, proposers, getValidatorAddress(), FakeMode)

	tests := []struct {
		number         uint64
		addr           common.Address
		expectedResult bool
	}{
		{1, addr1, true},
		{1, addr2, false},
		{1, addr3, false},
		{2, addr1, false},
		{2, addr2, true},
		{2, addr3, false},
		{3, addr1, false},
		{3, addr2, false},
		{3, addr3, true},
	}

	for _, tt := range tests {
		inturn := snap.InturnOf(tt.number, tt.addr)
		if inturn != tt.expectedResult {
			t.Errorf("expected result is %v,get %v,number:%v,addr:%v", tt.expectedResult, inturn, tt.number, tt.addr.Hex())
		}
	}
}

func Test_choseSomeProposers(t *testing.T) {
	type args struct {
		proposers []common.Address
		seed      int64
		wantLen   int
	}
	tests := []struct {
		name                 string
		args                 args
		wantDefaultProposers []common.Address
	}{
		// TODO: Add test cases.
		{
			name: "1",
			args: args{
				proposers: []common.Address{
					common.HexToAddress("0x0000000000000000000000000000000000000001"),
					common.HexToAddress("0x0000000000000000000000000000000000000002"),
				},
				seed:    0,
				wantLen: 1,
			},
			wantDefaultProposers: []common.Address{
				common.HexToAddress("0x0000000000000000000000000000000000000001"),
			},
		},
		{
			name: "2",
			args: args{
				proposers: []common.Address{
					common.HexToAddress("0x0000000000000000000000000000000000000001"),
					common.HexToAddress("0x0000000000000000000000000000000000000002"),
				},
				seed:    0,
				wantLen: 2,
			},
			wantDefaultProposers: []common.Address{
				common.HexToAddress("0x0000000000000000000000000000000000000001"),
				common.HexToAddress("0x0000000000000000000000000000000000000002"),
			},
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if gotDefaultProposers := choseSomeAddresses(tt.args.proposers, tt.args.seed, tt.args.wantLen); !reflect.DeepEqual(gotDefaultProposers, tt.wantDefaultProposers) {
				t.Errorf("choseSomeProposers() = %v, want %v", gotDefaultProposers, tt.wantDefaultProposers)
			}
		})
	}
}

func Test_choseSomeProposers2(t *testing.T) {
	proposers := []common.Address{
		common.HexToAddress("0x0000000000000000000000000000000000000001"),
		common.HexToAddress("0x0000000000000000000000000000000000000002"),
	}

	seed := int64(0)
	wantLen := 1

	chosenProposers := choseSomeAddresses(proposers, seed, wantLen)

	fmt.Println("---------------------------")
	fmt.Println("all proposers")
	for i, ep := range proposers {
		fmt.Println("proposer", "idx", i, "addr", ep.Hex())
	}
	fmt.Println("---------------------------")

	fmt.Println("---------------------------")
	fmt.Println("chosen  proposers")
	for i, ep := range chosenProposers {
		fmt.Println("proposer", "idx", i, "addr", ep.Hex())
	}
	fmt.Println("---------------------------")

}

func Test_evenlyInsertDefaultProposers(t *testing.T) {
	type args struct {
		electedProposers       []common.Address
		chosenDefaultProposers []common.Address
		seed                   int64
		wantLen                int
	}
	tests := []struct {
		name          string
		args          args
		wantProposers []common.Address
	}{
		// TODO: Add test cases.

		{
			name: "1",
			args: args{
				electedProposers: []common.Address{
					common.HexToAddress("0x0000000000000000000000000000000000000001"),
					common.HexToAddress("0x0000000000000000000000000000000000000002"),
					common.HexToAddress("0x0000000000000000000000000000000000000003"),
					common.HexToAddress("0x0000000000000000000000000000000000000004"),
					common.HexToAddress("0x0000000000000000000000000000000000000005"),
					common.HexToAddress("0x0000000000000000000000000000000000000006"),
					common.HexToAddress("0x0000000000000000000000000000000000000007"),
					common.HexToAddress("0x0000000000000000000000000000000000000008"),
				},
				chosenDefaultProposers: []common.Address{
					common.HexToAddress("0x0000000000000000000000000000000000000009"),
					common.HexToAddress("0x0000000000000000000000000000000000000010"),
					common.HexToAddress("0x0000000000000000000000000000000000000011"),
					common.HexToAddress("0x0000000000000000000000000000000000000012"),
				},
				seed:    0,
				wantLen: 12,
			},
			wantProposers: []common.Address{
				common.HexToAddress("0x0000000000000000000000000000000000000009"),
				common.HexToAddress("0x0000000000000000000000000000000000000001"),
				common.HexToAddress("0x0000000000000000000000000000000000000002"),

				common.HexToAddress("0x0000000000000000000000000000000000000010"),
				common.HexToAddress("0x0000000000000000000000000000000000000003"),
				common.HexToAddress("0x0000000000000000000000000000000000000004"),

				common.HexToAddress("0x0000000000000000000000000000000000000005"),
				common.HexToAddress("0x0000000000000000000000000000000000000011"),
				common.HexToAddress("0x0000000000000000000000000000000000000006"),

				common.HexToAddress("0x0000000000000000000000000000000000000007"),
				common.HexToAddress("0x0000000000000000000000000000000000000012"),
				common.HexToAddress("0x0000000000000000000000000000000000000008"),
			},
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if gotProposers := evenlyInsertDefaultProposers(tt.args.electedProposers, tt.args.chosenDefaultProposers, tt.args.seed, tt.args.wantLen); !reflect.DeepEqual(gotProposers, tt.wantProposers) {
				t.Errorf("evenlyInsertDefaultProposers() = %v, want %v", gotProposers, tt.wantProposers)
			}
		})
	}
}

func Test_addressExcept(t *testing.T) {
	type args struct {
		all    []common.Address
		except []common.Address
	}
	tests := []struct {
		name       string
		args       args
		wantResult []common.Address
	}{
		// TODO: Add test cases.
		{

			name: "1",
			args: args{
				all: []common.Address{
					common.BigToAddress(big.NewInt(1)),
					common.BigToAddress(big.NewInt(2)),
				},
				except: []common.Address{
					common.BigToAddress(big.NewInt(2)),
					common.BigToAddress(big.NewInt(3)),
					common.BigToAddress(big.NewInt(4)),
				},
			},
			wantResult: []common.Address{
				common.BigToAddress(big.NewInt(1)),
			},
		},

		{

			name: "2",
			args: args{
				all: []common.Address{
					common.BigToAddress(big.NewInt(1)),
					common.BigToAddress(big.NewInt(2)),
					common.BigToAddress(big.NewInt(3)),
				},
				except: []common.Address{
					common.BigToAddress(big.NewInt(4)),
				},
			},
			wantResult: []common.Address{
				common.BigToAddress(big.NewInt(1)),
				common.BigToAddress(big.NewInt(2)),
				common.BigToAddress(big.NewInt(3)),
			},
		},

		{

			name: "3",
			args: args{
				all: []common.Address{
					common.BigToAddress(big.NewInt(1)),
					common.BigToAddress(big.NewInt(2)),
					common.BigToAddress(big.NewInt(3)),
				},
				except: []common.Address{},
			},
			wantResult: []common.Address{
				common.BigToAddress(big.NewInt(1)),
				common.BigToAddress(big.NewInt(2)),
				common.BigToAddress(big.NewInt(3)),
			},
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if gotResult := addressExcept(tt.args.all, tt.args.except); !reflect.DeepEqual(gotResult, tt.wantResult) {
				t.Errorf("addressExcept() = %v, want %v", gotResult, tt.wantResult)
			}
		})
	}
}

func generateABatchAccounts(n int) []common.Address {
	var addresses []common.Address
	for i := 1; i < n; i++ {
		addresses = append(addresses, common.HexToAddress("0x"+fmt.Sprintf("%040x", i)))
	}
	return addresses
}

func TestTermof(t *testing.T) {
	cfg := &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 3}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	recentP := make(map[uint64][]common.Address)
	recentP[1] = proposers
	snapshot := &DporSnapshot{config: cfg, RecentProposers: recentP, Number: 8888}
	calcTerm := (snapshot.Number - 1) / ((snapshot.config.TermLen) * (snapshot.config.ViewLen))
	t.Log("blockNumber is 0:", snapshot.TermOf(0))
	wantResult := snapshot.TermOf(snapshot.Number)
	if !reflect.DeepEqual(calcTerm, wantResult) {
		t.Error("termCalculateExceptresult is wrong...")
	}
}
func TestStartBlockNumberOfTerm(t *testing.T) {
	cfg := &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 3}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	recentP := make(map[uint64][]common.Address)
	recentP[1] = proposers
	snapshot := &DporSnapshot{config: cfg, RecentProposers: recentP, Number: 888}
	wantResult := snapshot.config.ViewLen * snapshot.config.TermLen * (snapshot.TermOf(snapshot.Number) + 1)
	startBlock := snapshot.StartBlockNumberOfTerm(snapshot.TermOf(snapshot.Number) + 1)
	if !reflect.DeepEqual(startBlock, wantResult) {
		t.Error("termStartBlock calculate is  not right...")
	}
}

//caculate the number of this term's validator??
func TestValidatorViewOf(t *testing.T) {
	cfg := &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 3}
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	recentA := generateABatchAccounts(5)
	recentV := make(map[uint64][]common.Address)
	recentP := make(map[uint64][]common.Address)
	snapshot := &DporSnapshot{config: cfg, RecentProposers: recentP, RecentValidators: recentV, Number: 888, Mode: FakeMode}
	term := snapshot.TermOf(snapshot.Number)
	recentV[term] = recentA
	recentP[term] = proposers
	testAddr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 4))
	wantNumber, _ := snapshot.ValidatorViewOf(testAddr, snapshot.Number)
	equalSigner := reflect.DeepEqual(intToBool(wantNumber), addressContains(recentV[snapshot.TermOf(snapshot.Number)], testAddr))
	if !equalSigner {
		t.Error("ValidatorView test fail...")
	}

}

func TestFutureValidatorViewOf(t *testing.T) {
	cfg := &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 3}
	recentAddr := generateABatchAccounts(5)
	recentP := make(map[uint64][]common.Address)
	snapshot := &DporSnapshot{config: cfg, RecentProposers: recentP, Number: 888}
	currentTerm := snapshot.TermOf(snapshot.Number)
	pastTerm := snapshot.TermOf(snapshot.Number) - TermDistBetweenElectionAndMining - 1
	recentP[currentTerm] = recentAddr
	testAddr := common.HexToAddress("0x" + fmt.Sprintf("%040x", 4))
	wantNumber, _ := snapshot.FutureProposerViewOf(testAddr, snapshot.Number)
	equalSigner := reflect.DeepEqual(intToBool(wantNumber), addressContains(recentP[pastTerm], testAddr))
	if !equalSigner {
		t.Error("ValidatorView test fail...")

	}
}

func TestIsProposerOf(t *testing.T) {
	cfg := &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 3}
	recentAddr := generateABatchAccounts(10)
	recentP := make(map[uint64][]common.Address)
	snapshot := &DporSnapshot{config: cfg, RecentProposers: recentP, Number: 888}
	term := snapshot.TermOf(snapshot.Number)
	recentP[term] = recentAddr

	var i int
	var testResult int
H:
	for i = 1; i < (len(recentAddr) + 1); i++ {
		generateAddr := common.HexToAddress("0x" + fmt.Sprintf("%040x", i))
		wantResult, _ := snapshot.IsProposerOf(generateAddr, snapshot.Number)
		if wantResult {
			testResult++
			break H
		}
	}
	equalSigner := reflect.DeepEqual(0, testResult)
	if equalSigner {
		t.Error("The mining proposer is not be selected... ")
	}

}

func TestFutureProposersOf(t *testing.T) {
	cfg := &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 3}
	recentAddr := generateABatchAccounts(5)
	recentP := make(map[uint64][]common.Address)
	snapshot := &DporSnapshot{config: cfg, RecentProposers: recentP, Number: 888}
	futureTerm := snapshot.TermOf(snapshot.Number) + TermDistBetweenElectionAndMining + 1
	recentP[futureTerm] = recentAddr
	equalSigner := reflect.DeepEqual(snapshot.FutureProposersOf(snapshot.Number), recentAddr)
	if !equalSigner {
		t.Error("Proposers of future term calculate is wrong... ")
	}

}

func addressContains(addresses []common.Address, address common.Address) bool {
	for _, addr := range addresses {
		if addr == address {
			return true
		}

	}
	return false
}

func intToBool(num int) bool {
	if num == -1 {
		return false
	}
	return true
}

func TestInturnOf(t *testing.T) {
	cfg := &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 3}
	recentAddr := generateABatchAccounts(5)
	recentP := make(map[uint64][]common.Address)
	snapshot := &DporSnapshot{config: cfg, RecentProposers: recentP, Number: 888}
	term := snapshot.TermOf(snapshot.Number)
	recentP[term] = recentAddr
	testAddr1 := common.HexToAddress("0x" + fmt.Sprintf("%040x", len(recentAddr)-1))
	testAddr2 := common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")

	flag1 := snapshot.InturnOf(snapshot.Number, testAddr1)
	equalSigner1 := reflect.DeepEqual(flag1, addressContains(recentAddr, testAddr1))
	if !equalSigner1 {
		t.Error("Inturn function error...")
	}
	// test an inexistent account...
	equalSigner2 := reflect.DeepEqual(flag1, addressContains(recentAddr, testAddr2))
	if equalSigner2 {
		t.Error("inexitent account should not inturn")
	}
	// test another term
	flag2 := snapshot.InturnOf(732, testAddr1)
	equalSigner3 := reflect.DeepEqual(flag2, addressContains(recentAddr, testAddr1))

	if equalSigner3 {
		t.Error("Given another term should fail")
	}
}

func TestSnapshot_updateCandidates(t *testing.T) {
	//t.Skip("Snapshot_updateCandiates have not complete yet")
	type fields struct {
		config     *configs.DporConfig
		sigcache   *lru.ARCCache
		Number     uint64
		Hash       common.Hash
		Candidates []common.Address
		//RecentSigners map[uint64][]common.Address
	}
	type args struct {
		header *types.Header
	}
	testConfig := configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}
	testCache, _ := lru.NewARC(inMemorySnapshots)
	expectedResult := new(DporSnapshot)
	expectedResult.Number = 1
	expectedResult.config = &testConfig
	expectedResult.Candidates = getProposerAddress()
	tests := []struct {
		name    string
		fields  fields
		args    args
		wantErr bool
	}{
		{"empty header",
			fields{&testConfig,
				testCache,
				1,
				common.Hash{},
				getProposerAddress(),
			},
			args{
				nil,
				//TODO: this header should not be nil, otherwise it causes a panic on invalid memory address
			},
			false,
		},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			s := &DporSnapshot{
				config: tt.fields.config,
				// sigcache:      tt.fields.sigcache,
				Number:     tt.fields.Number,
				Hash:       tt.fields.Hash,
				Candidates: tt.fields.Candidates,
				// RecentSigners: tt.fields.RecentSigners,
			}
			if err := s.updateCandidates(nil, 0); (err != nil) != tt.wantErr {
				t.Errorf("DporSnapshot.updateCandidates(%v) error = %v, wantErr %v", tt.args.header, err, tt.wantErr)
			}
		})
	}
}

func TestSnapshot_setRecentValidaters(t *testing.T) {
	snap := newSnapshot(&configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}, 7989, common.Hash{}, getProposerAddress(), getValidatorAddress(), FakeMode)
	vterm := snap.TermOf(snap.Number)

	ss := snap.RecentValidators[vterm]
	getValidaters := snap.getRecentValidators(vterm)
	snap.setRecentValidators(snap.TermOf(snap.Number), getValidaters)

	equal := reflect.DeepEqual(ss, getValidaters)
	if !equal {
		t.Errorf("setRecentValidaters fail...")
	}
}
