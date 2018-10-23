package rpt

import (
	//	"bitbucket.org/cpchain/chain/contracts/dpor/contract/campaign"
	"context"
	"crypto/ecdsa"
	"errors"
	"fmt"
	"github.com/hashicorp/golang-lru"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/configs"
	pdash "bitbucket.org/cpchain/chain/contracts/dpor/contract/Pdash"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/crypto"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/stretchr/testify/assert"
)

var (
	errUnknownBlock = errors.New("unknown block")
)

var (
	endpoint = "http://localhost:8501"
	//endpoint = "https://rinkeby.infura.io"
	blockNum      = uint64(0)
	hex           = "0x96216849c49358B10257cb55b28eA603c874b05E"
	address       = common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87")
	leaderAddress = common.HexToAddress("0x3030303030303030303030303030303030303030")
)

var cache *lru.ARCCache

var (
	raddress1 = []common.Address{
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d86"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d85"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d84"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d83"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d82"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d81"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d80"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d88"),
	}
	committeaddress2 = []common.Address{
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d86"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d85"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d84"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d83"),
		common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d82"),
		common.HexToAddress("0x3030303030303030303030303030303030303030"),
	}
)

var (
	key, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	addr   = crypto.PubkeyToAddress(key.PublicKey)
)

func deploy(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	deployTransactor.Value = amount
	addr, _, _, err := pdash.DeployPdash(deployTransactor, backend)
	if err != nil {
		return common.Address{}, err
	}
	backend.Commit()
	return addr, nil
}

func newHeader() *types.Header {
	return &types.Header{
		ParentHash:   common.HexToHash("0x83cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55"),
		Coinbase:     common.HexToAddress("0x8888f1F195AFa192CfeE860698584c030f4c9dB1"),
		Root:    common.HexToHash("0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"),
		TxHash:      common.HexToHash("0x5fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptHash: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Difficulty:   big.NewInt(131072),
		Number:       big.NewInt(1),
		GasLimit:     uint64(3141592),
		GasUsed:      uint64(21000),
		Time:         big.NewInt(1426516743),
		Extra:        []byte("0x0000000000000000000000000000000000000000000000000000000000000000095e7baea6a6c7c4c2dfeb977efac326af552d87e94b7b6c5a0e526a4d97f9768ad6097bde25c62ac05302acebd0730e3a18a058d7d1cb1204c4a092ef3dd127de235f15ffb4fc0d71469d1339df64650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"),
		//Extra2:      []byte("ext2"),
		MixDigest: common.HexToHash("bd4472abb6659ebe3ee06ee4d7b72a00a9f4d001caca51342001075469aff498"),
		Nonce:   types.EncodeNonce(uint64(0xa13a5a8c8f2bb1c4)),
	}
}

type fakeClientBackend struct {
}

func (b *fakeClientBackend) BalanceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (*big.Int, error) {
	return big.NewInt(100), nil
}

func (b *fakeClientBackend) BlockByNumber(ctx context.Context, number *big.Int) (*types.Block, error) {

	tx1 := types.NewTransaction(0, address, big.NewInt(10), 50000, big.NewInt(10), nil)
	tx1, _ = tx1.WithSignature(types.HomesteadSigner{}, common.Hex2Bytes("9bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094f8a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b100"))

	var trans []*types.Transaction = make([]*types.Transaction, 1)
	trans[0] = tx1
	newBlock := types.NewBlock(newHeader(), trans, nil)
	return newBlock, nil
}

func (b *fakeClientBackend) HeaderByNumber(ctx context.Context, number *big.Int) (*types.Header, error) {
	return newHeader(), nil
}

type fakeErrorClientBackend struct {
	errorType uint64
}

func (b *fakeErrorClientBackend) BalanceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (*big.Int, error) {
	if b.errorType == 1 {
		return big.NewInt(110), errUnknownBlock
	}
	return big.NewInt(110), nil
}

func (b *fakeErrorClientBackend) BlockByNumber(ctx context.Context, number *big.Int) (*types.Block, error) {
	if b.errorType == 2 {
		return nil, errUnknownBlock
	}

	tx1 := types.NewTransaction(0, address, big.NewInt(10), 50000, big.NewInt(10), nil)
	tx1, _ = tx1.WithSignature(types.HomesteadSigner{}, common.Hex2Bytes("9bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094f8a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b100"))

	var trans []*types.Transaction = make([]*types.Transaction, 1)
	trans[0] = tx1
	newBlock := types.NewBlock(newHeader(), trans, nil)
	return newBlock, nil
}

func (b *fakeErrorClientBackend) HeaderByNumber(ctx context.Context, number *big.Int) (*types.Header, error) {
	if b.errorType == 3 {
		return nil, errUnknownBlock
	}
	return newHeader(), nil
}

func TestNewEthClient(t *testing.T) {
	client, err := NewEthClient(endpoint)
	fmt.Println(client)
	assert.Nil(t, err)
	assert.NotNil(t, client)
}

func getClientBackend() (ClientBackend, error) {
	return &fakeClientBackend{}, nil
	//return NewEthClient(endpoint)
}

func getErrorClientBackend(errorType uint64) (ClientBackend, error) {
	return &fakeErrorClientBackend{errorType}, nil
}

func TestNewBasicCollector(t *testing.T) {
	bc := createBasicCollector(t, 4)
	address := common.HexToAddress(hex)
	balance, err := bc.BalanceAt(context.Background(), address, big.NewInt(int64(blockNum)))
	fmt.Println(balance, err)
	assert.Equal(t, big.NewInt(100), balance, "balance value error")
}

func TestBasicCollector_GetRpts(t *testing.T) {
	cache, _ := lru.NewARC(20)
	bc := createBasicCollector(t, 4)
	var addresses []common.Address
	for i := 0; i < 3; i++ {
		addresses = append(
			addresses,
			common.HexToAddress("0x"+fmt.Sprintf("%040x", i)),
		)
	}

	assert.Equal(t, "0x0000000000000000000000000000000000000000", addresses[0].Hex())
	assert.Equal(t, float64(50), bc.GetRpts(addresses, blockNum, cache)[0].Rpt)
}

func TestCache(t *testing.T) {
	cache, _ := lru.NewARC(20)
	bc := createBasicCollector(t, 4)
	var num uint64
	num = 0
	for i, address := range raddress1 {
		hash := sigHash(Rptitems{nodeaddress: address, key: num})
		cache.Add(hash, RPT{Address: address, Rpt: 0 + float64(i)})
		num++
	}
	assert.Equal(t, float64(55), bc.GetRpts(raddress1, 6, cache)[5].Rpt)
}
func TestBasicCollector_GetRptInfos(t *testing.T) {
	bc := createBasicCollector(t, 4)
	var addresses []common.Address

	for i := 0; i < 6; i++ {
		addresses = append(
			addresses,
			common.HexToAddress("0x"+fmt.Sprintf("%040x", i)),
		)
	}

	fmt.Printf("rpt info of %s is\n", addresses[0].Hex())
	fmt.Println(bc.GetRptInfos(addresses, blockNum)[addresses[0]])
	assert.Equal(t, "0x0000000000000000000000000000000000000000", addresses[0].Hex())
}

func createErrorBasicCollector(t *testing.T, chainId int64, errorType uint64) *BasicCollector {
	config := getCollectorConfig(chainId)
	ethClient, _ := getErrorClientBackend(errorType)
	bc, err := NewBasicCollector(ethClient, config)
	assert.Nil(t, err)
	return bc
}

func createBasicCollector(t *testing.T, chainId int64) *BasicCollector {
	config := getCollectorConfig(chainId)
	ethClient, _ := getClientBackend()
	bc, err := NewBasicCollector(ethClient, config)
	assert.Nil(t, err)
	return bc
}

func TestBasicCollector_GetRptInfosNew(t *testing.T) {
	bc := createBasicCollector(t, 4)
	var addresses []common.Address

	for i := 0; i < 3; i++ {
		addresses = append(
			addresses,
			common.HexToAddress("0x"+fmt.Sprintf("%040x", i)),
		)
	}

	fmt.Printf("rpt info of %s is\n", addresses[0].Hex())
	fmt.Println(bc.GetRptInfos(addresses, blockNum)[addresses[0]])
	assert.Equal(t, "0x0000000000000000000000000000000000000000", addresses[0].Hex())
	length := len(bc.GetRptInfos(addresses, blockNum))
	assert.Equal(t, 3, length)
	assert.NotNil(t, bc.GetRptInfos(addresses, blockNum)[addresses[0]])
}

func getCollectorConfig(chainId int64) *CollectorConfig {
	client,_:=NewEthClient(endpoint)
	config := &CollectorConfig{
		LeaderReward:   80,
		ProxyReward:    0,
		UploadReward:   0,
		CommitteReward: 60,
		Alpha:          0.5,
		Beta:           0.15,
		Gamma:          0.1,
		Phi:            0.15,
		Omega:          0.1,
		WindowSize:     5,
		ChainConfig: &configs.ChainConfig{
			ChainID: big.NewInt(chainId),
		},
		DporConfig: &configs.DporConfig{
			Epoch:  3,
			Period: 1,
		},
		committeenamber: 20,
		client:client,
		proxycontractaddress:common.HexToAddress(""),
		uploadcontractAddress:common.HexToAddress(""),
	}
	return config
}

func TestGetCoinAge(t *testing.T) {
	bc := createBasicCollector(t, 4)
	balance, _ := bc.getCoinAge(address, raddress1, 10)
	assert.Equal(t, float64(100), balance)
}

func TestGetTxVolume(t *testing.T) {
	bc := createBasicCollector(t, 4)
	balance, _ := bc.getTxVolume(address, 10)
	assert.Equal(t, float64(0), balance)
}

func TestGetMaintenance(t *testing.T) {
	bc := createBasicCollector(t, 5)
	Maintenance, _ := bc.getMaintenance(leaderAddress, 10)
	assert.Equal(t, float64(80), Maintenance)
}

func TestGetIfLeaderNotLeader(t *testing.T) {
	bc := createBasicCollector(t, 4)
	leaderReward, _ := bc.getIfLeader(address, 10)
	assert.Equal(t, float64(0), leaderReward)
}

func TestGetIfLeaderIsLeader(t *testing.T) {
	bc := createBasicCollector(t, 5)
	LeaderReward, _ := bc.getIfLeader(leaderAddress, 10)
	assert.Equal(t, float64(80), LeaderReward)
}

func TestGetUploadReward(t *testing.T) {
	bc := createBasicCollector(t, 5)
	LeaderReward := bc.getUploadReward(address,raddress1,10)
	assert.Equal(t, float64(0), LeaderReward)
}

func TestGetProxyReward(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	contractAddr, _ := deploy(key, big.NewInt(0), contractBackend)
	bc := createBasicCollector(t, 5)
	bc.Config.proxycontractaddress=contractAddr
	ProxyReward := bc.getProxyReward(address, 10)
	assert.Equal(t, float64(0), ProxyReward)
}

func TestGetContractRptInfo4(t *testing.T) {
	SetFakeOderInfo()
	bc := createBasicCollector(t, 5)
	contractRptInfo := bc.getContractRptInfo(leaderAddress,raddress1, 4)
	assert.NotNil(t, contractRptInfo)
	assert.Equal(t, float64(0), contractRptInfo.ProxyReward)
	assert.Equal(t, float64(0), contractRptInfo.UploadReward)
}

func TestGetContractRptInfo5(t *testing.T) {
	SetFakeOderInfo()
	bc := createBasicCollector(t, 5)
	contractRptInfo := bc.getContractRptInfo(address, raddress1,5)
	assert.NotNil(t, contractRptInfo)
	assert.Equal(t, float64(0), contractRptInfo.ProxyReward)
	assert.Equal(t, float64(0), contractRptInfo.UploadReward)
}

func TestGetContractRptInfo6(t *testing.T) {
	SetFakeOderInfo()
	bc := createBasicCollector(t, 5)
	contractRptInfo := bc.getContractRptInfo(address, raddress1,6)
	assert.NotNil(t, contractRptInfo)
	assert.Equal(t, float64(0), contractRptInfo.ProxyReward)
	assert.Equal(t, float64(0), contractRptInfo.UploadReward)
}

func TestGetContractRptInfo10(t *testing.T) {
	SetFakeOderInfo()
	bc := createBasicCollector(t, 5)
	contractRptInfo := bc.getContractRptInfo(address, raddress1,10)
	assert.NotNil(t, contractRptInfo)
	assert.Equal(t, float64(0), contractRptInfo.ProxyReward)
	assert.Equal(t, float64(0), contractRptInfo.UploadReward)
}

func TestGetChainRptInfo(t *testing.T) {
	bc := createBasicCollector(t, 5)
	chainRptInfo := bc.getChainRptInfo(leaderAddress, raddress1, 10)
	assert.NotNil(t, chainRptInfo)
	assert.Equal(t, float64(100), chainRptInfo.CoinAge)
	assert.Equal(t, float64(80), chainRptInfo.IfLeader)
	assert.Equal(t, float64(0), chainRptInfo.TxVolume)
}

func TestGetChainRptInfoError1(t *testing.T) {
	bc := createErrorBasicCollector(t, 5, 1)
	chainRptInfo := bc.getChainRptInfo(leaderAddress, raddress1, 10)
	assert.NotNil(t, chainRptInfo)
	assert.Equal(t, float64(0), chainRptInfo.CoinAge)
	assert.Equal(t, float64(0), chainRptInfo.IfLeader)
	assert.Equal(t, float64(0), chainRptInfo.TxVolume)
}

func TestGetChainRptInfoError2(t *testing.T) {
	bc := createErrorBasicCollector(t, 5, 2)
	chainRptInfo := bc.getChainRptInfo(leaderAddress, raddress1, 10)
	assert.NotNil(t, chainRptInfo)
	assert.Equal(t, float64(0), chainRptInfo.CoinAge)
	assert.Equal(t, float64(0), chainRptInfo.IfLeader)
	assert.Equal(t, float64(0), chainRptInfo.TxVolume)
}

func TestGetChainRptInfoError3(t *testing.T) {
	bc := createErrorBasicCollector(t, 5, 3)
	chainRptInfo := bc.getChainRptInfo(leaderAddress, raddress1, 10)
	assert.NotNil(t, chainRptInfo)
	assert.Equal(t, float64(0), chainRptInfo.CoinAge)
	assert.Equal(t, float64(0), chainRptInfo.IfLeader)
	assert.Equal(t, float64(0), chainRptInfo.TxVolume)
}
