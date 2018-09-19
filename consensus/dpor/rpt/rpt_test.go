package rpt

import (
	"context"
	"errors"
	"fmt"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/params"

	"bitbucket.org/cpchain/chain/common"
	"bitbucket.org/cpchain/chain/core/types"
	"bitbucket.org/cpchain/chain/rlp"
	"github.com/stretchr/testify/assert"
)

var (
	endpoint = "http://localhost:8501"
	//endpoint = "https://rinkeby.infura.io"
	blockNum      = uint64(0)
	hex           = "0x96216849c49358B10257cb55b28eA603c874b05E"
	address       = common.HexToAddress("095e7baea6a6c7c4c2dfeb977efac326af552d87")
	leaderAddress = common.HexToAddress("0x3030303030303030303030303030303030303030")
)

func newHeader() *types.Header {
	return &types.Header{
		ParentHash:  common.HexToHash("0x83cafc574e1f51ba9dc0568fc617a08ea2429fb384059c972f13b19fa1c8dd55"),
		UncleHash:   common.HexToHash("0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"),
		Coinbase:    common.HexToAddress("0x8888f1F195AFa192CfeE860698584c030f4c9dB1"),
		Root:        common.HexToHash("0xef1552a40b7165c3cd773806b9e0c165b75356e0314bf0706f279c729f51e017"),
		TxHash:      common.HexToHash("0x5fe50b260da6308036625b850b5d6ced6d0a9f814c0688bc91ffb7b7a3a54b67"),
		ReceiptHash: common.HexToHash("0xbc37d79753ad738a6dac4921e57392f145d8887476de3f783dfa7edae9283e52"),
		Difficulty:  big.NewInt(131072),
		Number:      big.NewInt(1),
		GasLimit:    uint64(3141592),
		GasUsed:     uint64(21000),
		Time:        big.NewInt(1426516743),
		Extra:       []byte("0x0000000000000000000000000000000000000000000000000000000000000000095e7baea6a6c7c4c2dfeb977efac326af552d87e94b7b6c5a0e526a4d97f9768ad6097bde25c62ac05302acebd0730e3a18a058d7d1cb1204c4a092ef3dd127de235f15ffb4fc0d71469d1339df64650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"),
		//Extra2:      []byte("ext2"),
		MixDigest: common.HexToHash("bd4472abb6659ebe3ee06ee4d7b72a00a9f4d001caca51342001075469aff498"),
		Nonce:     types.EncodeNonce(uint64(0xa13a5a8c8f2bb1c4)),
	}
}

type fakeClientBackend struct {
}

func (b *fakeClientBackend) BalanceAt(ctx context.Context, account common.Address, blockNumber *big.Int) (*big.Int, error) {
	return big.NewInt(110), nil
}

func (b *fakeClientBackend) BlockByNumber(ctx context.Context, number *big.Int) (*types.Block, error) {

	tx1 := types.NewTransaction(0, address, big.NewInt(10), 50000, big.NewInt(10), nil)
	tx1, _ = tx1.WithSignature(types.HomesteadSigner{}, common.Hex2Bytes("9bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094f8a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b100"))

	var trans []*types.Transaction = make([]*types.Transaction, 1)
	trans[0] = tx1
	var uncls []*types.Header
	rlp.DecodeBytes(common.Hex2Bytes("c0"), uncls)
	newBlock := types.NewBlock(newHeader(), trans, uncls, nil)
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
		return big.NewInt(110), errors.New("unknown block")
	}
	return big.NewInt(110), nil
}

func (b *fakeErrorClientBackend) BlockByNumber(ctx context.Context, number *big.Int) (*types.Block, error) {
	if b.errorType == 2 {
		return nil, errors.New("unknown block")
	}

	tx1 := types.NewTransaction(0, address, big.NewInt(10), 50000, big.NewInt(10), nil)
	tx1, _ = tx1.WithSignature(types.HomesteadSigner{}, common.Hex2Bytes("9bea4c4daac7c7c52e093e6a4c35dbbcf8856f1af7b059ba20253e70848d094f8a8fae537ce25ed8cb5af9adac3f141af69bd515bd2ba031522df09b97dd72b100"))

	var trans []*types.Transaction = make([]*types.Transaction, 1)
	trans[0] = tx1
	var uncls []*types.Header
	rlp.DecodeBytes(common.Hex2Bytes("c0"), uncls)
	newBlock := types.NewBlock(newHeader(), trans, uncls, nil)
	return newBlock, nil
}

func (b *fakeErrorClientBackend) HeaderByNumber(ctx context.Context, number *big.Int) (*types.Header, error) {
	if b.errorType == 3 {
		return nil, errors.New("unknown block")
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

func TestGetRptError1(t *testing.T) {
	address := common.HexToAddress(hex)
	bc := createErrorBasicCollector(t, 4, 1)
	rpt := bc.GetRpt(address, blockNum)
	fmt.Println("address:", rpt.Address.Hex(), "rpt:", rpt.Rpt)
	assert.Equal(t, hex, rpt.Address.Hex(), "rpt address error")
	assert.Equal(t, float64(20), rpt.Rpt, "rpt value error")
}

func TestGetRptError2(t *testing.T) {
	address := common.HexToAddress(hex)
	bc := createErrorBasicCollector(t, 4, 2)
	rpt := bc.GetRpt(address, blockNum)
	fmt.Println("address:", rpt.Address.Hex(), "rpt:", rpt.Rpt)
	assert.Equal(t, hex, rpt.Address.Hex(), "rpt address error")
	assert.Equal(t, float64(20), rpt.Rpt, "rpt value error")
}

func TestGetRptError3(t *testing.T) {
	address := common.HexToAddress(hex)
	bc := createErrorBasicCollector(t, 4, 3)
	rpt := bc.GetRpt(address, blockNum)
	fmt.Println("address:", rpt.Address.Hex(), "rpt:", rpt.Rpt)
	assert.Equal(t, hex, rpt.Address.Hex(), "rpt address error")
	assert.Equal(t, float64(20), rpt.Rpt, "rpt value error")
}

func TestBasicCollector_GetRpt(t *testing.T) {
	address := common.HexToAddress(hex)
	bc := createBasicCollector(t, 4)
	rpt := bc.GetRpt(address, blockNum)
	fmt.Println("address:", rpt.Address.Hex(), "rpt:", rpt.Rpt)
	assert.Equal(t, hex, rpt.Address.Hex(), "rpt address error")
	assert.Equal(t, float64(20), rpt.Rpt, "rpt value error")
}

func TestNewBasicCollector(t *testing.T) {
	bc := createBasicCollector(t, 4)
	address := common.HexToAddress(hex)
	balance, err := bc.BalanceAt(context.Background(), address, big.NewInt(int64(blockNum)))

	fmt.Println(balance, err)
	assert.Equal(t, big.NewInt(110), balance, "balance value error")
}

func TestBasicCollector_GetRpts(t *testing.T) {
	bc := createBasicCollector(t, 4)
	var addresses []common.Address

	for i := 0; i < 3; i++ {
		addresses = append(
			addresses,
			common.HexToAddress("0x"+fmt.Sprintf("%040x", i)),
		)
	}

	assert.Equal(t, "0x0000000000000000000000000000000000000000", addresses[0].Hex())
	assert.Equal(t, float64(20), bc.GetRpts(&addresses, blockNum)[0].Rpt)
}

func TestBasicCollector_GetRptInfos(t *testing.T) {
	bc := createBasicCollector(t, 4)
	var addresses []common.Address

	for i := 0; i < 3; i++ {
		addresses = append(
			addresses,
			common.HexToAddress("0x"+fmt.Sprintf("%040x", i)),
		)
	}

	fmt.Printf("rpt info of %s is\n", addresses[0].Hex())
	fmt.Println(bc.GetRptInfos(&addresses, blockNum)[addresses[0]])
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
	fmt.Println(bc.GetRptInfos(&addresses, blockNum)[addresses[0]])
	assert.Equal(t, "0x0000000000000000000000000000000000000000", addresses[0].Hex())
	length := len(bc.GetRptInfos(&addresses, blockNum))
	assert.Equal(t, 3, length)
	assert.NotNil(t, bc.GetRptInfos(&addresses, blockNum)[addresses[0]])
}

func getCollectorConfig(chainId int64) *CollectorConfig {
	config := &CollectorConfig{
		LeaderReward: 50,
		ProxyReward:  50,
		UploadReward: 50,
		Alpha:        0.2,
		Beta:         0.2,
		Gamma:        0.2,
		Phi:          0.2,
		Omega:        0.2,
		WindowSize:   5,
		ChainConfig: &params.ChainConfig{
			ChainID: big.NewInt(chainId),
		},
		DporConfig: &params.DporConfig{
			Epoch:  3,
			Period: 1,
		},
	}
	return config
}

func TestGetCoinAge(t *testing.T) {
	bc := createBasicCollector(t, 4)
	balance, _ := bc.getCoinAge(address, 10)
	assert.Equal(t, float64(110), balance)
}

func TestGetTxVolume(t *testing.T) {
	bc := createBasicCollector(t, 4)
	balance, _ := bc.getTxVolume(address, 10)
	assert.Equal(t, float64(0), balance)
}

func TestGetIfLeaderNotLeader(t *testing.T) {
	bc := createBasicCollector(t, 4)
	leaderReward, _ := bc.getIfLeader(address, 10)
	assert.Equal(t, float64(0), leaderReward)
}

func TestGetIfLeaderIsLeader(t *testing.T) {
	bc := createBasicCollector(t, 5)
	LeaderReward, _ := bc.getIfLeader(leaderAddress, 10)
	assert.Equal(t, float64(50), LeaderReward)
}

func TestGetUploadReward(t *testing.T) {
	bc := createBasicCollector(t, 5)
	LeaderReward := bc.getUploadReward(leaderAddress, 10)
	assert.Equal(t, float64(50), LeaderReward)
}

func TestGetProxyReward(t *testing.T) {
	bc := createBasicCollector(t, 5)
	leaderReward := bc.getProxyReward(leaderAddress, 10)
	assert.Equal(t, float64(50), leaderReward)
}

func TestGetContractRptInfo4(t *testing.T) {
	bc := createBasicCollector(t, 5)
	contractRptInfo := bc.getContractRptInfo(leaderAddress, 4)
	assert.NotNil(t, contractRptInfo)
	assert.Equal(t, float64(0), contractRptInfo.ProxyReward)
	assert.Equal(t, float64(0), contractRptInfo.UploadReward)
}

func TestGetContractRptInfo5(t *testing.T) {
	bc := createBasicCollector(t, 5)
	contractRptInfo := bc.getContractRptInfo(leaderAddress, 5)
	assert.NotNil(t, contractRptInfo)
	assert.Equal(t, float64(250), contractRptInfo.ProxyReward)
	assert.Equal(t, float64(250), contractRptInfo.UploadReward)
}

func TestGetContractRptInfo6(t *testing.T) {
	bc := createBasicCollector(t, 5)
	contractRptInfo := bc.getContractRptInfo(leaderAddress, 6)
	assert.NotNil(t, contractRptInfo)
	assert.Equal(t, float64(300), contractRptInfo.ProxyReward)
	assert.Equal(t, float64(300), contractRptInfo.UploadReward)
}

func TestGetContractRptInfo10(t *testing.T) {
	bc := createBasicCollector(t, 5)
	contractRptInfo := bc.getContractRptInfo(leaderAddress, 10)
	assert.NotNil(t, contractRptInfo)
	assert.Equal(t, float64(300), contractRptInfo.ProxyReward)
	assert.Equal(t, float64(300), contractRptInfo.UploadReward)
}

func TestGetChainRptInfo(t *testing.T) {
	bc := createBasicCollector(t, 5)
	chainRptInfo := bc.getChainRptInfo(leaderAddress, 10)
	assert.NotNil(t, chainRptInfo)
	assert.Equal(t, float64(660), chainRptInfo.CoinAge)
	assert.Equal(t, float64(200), chainRptInfo.IfLeader)
	assert.Equal(t, float64(0), chainRptInfo.TxVolume)
}

func TestGetChainRptInfoError1(t *testing.T) {
	bc := createErrorBasicCollector(t, 5, 1)
	chainRptInfo := bc.getChainRptInfo(leaderAddress, 10)
	assert.NotNil(t, chainRptInfo)
	assert.Equal(t, float64(0), chainRptInfo.CoinAge)
	assert.Equal(t, float64(0), chainRptInfo.IfLeader)
	assert.Equal(t, float64(0), chainRptInfo.TxVolume)
}

func TestGetChainRptInfoError2(t *testing.T) {
	bc := createErrorBasicCollector(t, 5, 2)
	chainRptInfo := bc.getChainRptInfo(leaderAddress, 10)
	assert.NotNil(t, chainRptInfo)
	assert.Equal(t, float64(0), chainRptInfo.CoinAge)
	assert.Equal(t, float64(0), chainRptInfo.IfLeader)
	assert.Equal(t, float64(0), chainRptInfo.TxVolume)
}

func TestGetChainRptInfoError3(t *testing.T) {
	bc := createErrorBasicCollector(t, 5, 3)
	chainRptInfo := bc.getChainRptInfo(leaderAddress, 10)
	assert.NotNil(t, chainRptInfo)
	assert.Equal(t, float64(0), chainRptInfo.CoinAge)
	assert.Equal(t, float64(0), chainRptInfo.IfLeader)
	assert.Equal(t, float64(0), chainRptInfo.TxVolume)
}
