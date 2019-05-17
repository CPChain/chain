package dpor

import (
	"encoding/json"
	"fmt"
	"reflect"
	"testing"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor/rpt"
	"bitbucket.org/cpchain/chain/database"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	lru "github.com/hashicorp/golang-lru"
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

func Test_loadSnapshot(t *testing.T) {
	type args struct {
		config   *configs.DporConfig
		sigcache *lru.ARCCache
		db       database.Database
		hash     common.Hash
	}
	testConfig := configs.DporConfig{Period: 3, TermLen: 3, ViewLen: 3}
	cache, _ := lru.NewARC(inMemorySnapshots)
	expectedDporSnapshot := new(DporSnapshot)
	expectedDporSnapshot.config = &testConfig
	tests := []struct {
		name    string
		args    args
		want    *DporSnapshot
		wantErr bool
	}{
		{"test_loadSnapshot1",
			args{&testConfig, cache, &fakeDb{dbType: 1}, common.Hash{}},
			expectedDporSnapshot,
			false},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := loadSnapshot(tt.args.config, tt.args.db, tt.args.hash)
			if (err != nil) != tt.wantErr {
				t.Errorf("loadSnapshot(%v, %v, %v, %v) error = %v, wantErr %v", tt.args.config, tt.args.sigcache, tt.args.db, tt.args.hash, err, tt.wantErr)
				return
			}
			if !reflect.DeepEqual(got, tt.want) {
				t.Errorf("loadSnapshot(%v, %v, %v, %v) = \n %v, want \n %v\n", tt.args.config, tt.args.sigcache, tt.args.db, tt.args.hash, got, tt.want)
			}
		})
	}
}

func TestSnapshot_store(t *testing.T) {

	type fields struct {
		config     *configs.DporConfig
		sigcache   *lru.ARCCache
		Number     uint64
		Hash       common.Hash
		Candidates []common.Address
		// RecentSigners map[uint64][]common.Address
	}
	type args struct {
		db database.Database
	}

	cache, _ := lru.NewARC(inMemorySnapshots)
	config := &configs.DporConfig{Period: 3, TermLen: 3}

	tests := []struct {
		name    string
		fields  fields
		args    args
		wantErr bool
	}{
		{"store ok",
			fields{
				config,
				cache,
				1,
				common.Hash{},
				getProposerAddress(),
				// map[uint64][]common.Address{0: getSignerAddress()},
			},
			args{&fakeDb{}},
			false},
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
			if err := s.store(tt.args.db); (err != nil) != tt.wantErr {
				t.Errorf("DporSnapshot.store(%v) error = %v, wantErr %v", tt.args.db, err, tt.wantErr)
			}
		})
	}
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

func TestSnapshot_apply(t *testing.T) {
	type fields struct {
		config     *configs.DporConfig
		sigcache   *lru.ARCCache
		Number     uint64
		Hash       common.Hash
		Candidates []common.Address
		//RecentSigners map[uint64][]common.Address
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
				config: tt.fields.config,
				// sigcache:      tt.fields.sigcache,
				Number:     tt.fields.Number,
				Hash:       tt.fields.Hash,
				Candidates: tt.fields.Candidates,
				// RecentSigners: tt.fields.RecentSigners,
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

func TestSnapshot_applyHeader(t *testing.T) {
	t.Skip("temporally skip for further considerations in header construction")
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
			if err := s.applyHeader(tt.args.header, true, nil, nil); (err != nil) != tt.wantErr {
				t.Errorf("DporSnapshot.applyHeader(%v) error = %v, wantErr %v", tt.args.header, err, tt.wantErr)
			}
		})
	}
}

func TestSnapshot_updateCandidates(t *testing.T) {
	t.Skip("Snapshot_updateCandiates have not complete yet")
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
			if err := s.updateCandidates(nil); (err != nil) != tt.wantErr {
				t.Errorf("DporSnapshot.updateCandidates(%v) error = %v, wantErr %v", tt.args.header, err, tt.wantErr)
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
	isLeader, err = snap.IsProposerOf(addr1, 2)
	if !isLeader || err != nil {
		t.Errorf("expect isLeader true, get %v", isLeader)
	}
	isLeader, err = snap.IsProposerOf(addr1, 3)
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
		{2, addr1, true},
		{2, addr2, false},
		{2, addr3, false},
		{3, addr1, true},
		{3, addr2, false},
		{3, addr3, false},
	}

	for _, tt := range tests {
		inturn := snap.InturnOf(tt.number, tt.addr)
		if inturn != tt.expectedResult {
			t.Errorf("expected result is %v,get %v,number:%v,addr:%v", tt.expectedResult, inturn, tt.number, tt.addr.Hex())
		}
	}
}

func Test_loadSnapshot_marshal(t *testing.T) {
	cfg := &configs.DporConfig{Period: 3, ViewLen: 3, TermLen: 3}
	db := database.NewMemDatabase()
	proposers := []common.Address{common.HexToAddress("0xe94b7b6c5a0e526a4d97f9768ad6097bde25c62a")}
	recentP := make(map[uint64][]common.Address)
	recentP[1] = proposers
	snapshot := &DporSnapshot{config: cfg, RecentProposers: recentP}

	hash := common.Hash{}
	snapshot.setHash(hash)
	snapshot.store(db)
	got, err := loadSnapshot(cfg, db, hash)
	_ = got
	if err != nil {
		t.Error("should not fail", err)
	}

	if !reflect.DeepEqual(snapshot, got) {
		t.Error("loaded snapshot does not equal to original one")
	}

	t.Log("snapshot loaded", got)
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

		// this will panic, it's correct
		// {
		// 	name: "1",
		// 	args: args{
		// 		proposers: []common.Address{
		// 			common.HexToAddress("0x0000000000000000000000000000000000000001"),
		// 			common.HexToAddress("0x0000000000000000000000000000000000000002"),
		// 		},
		// 		seed:    0,
		// 		wantLen: 3,
		// 	},
		// 	wantDefaultProposers: nil,
		// },
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if gotDefaultProposers := choseSomeProposers(tt.args.proposers, tt.args.seed, tt.args.wantLen); !reflect.DeepEqual(gotDefaultProposers, tt.wantDefaultProposers) {
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

	chosenProposers := choseSomeProposers(proposers, seed, wantLen)

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

func TestDporSnapshot_updateProposers(t *testing.T) {

}
