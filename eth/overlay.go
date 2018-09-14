package eth

import (
	"context"
	"math/big"
	"reflect"

	"github.com/ethereum/go-ethereum/accounts/abi/bind"
	"github.com/ethereum/go-ethereum/accounts/keystore"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/ethclient"
)

// ContractCaller is used to call the contract with given key and client.
type ContractCaller struct {
	key    *keystore.Key
	client *ethclient.Client
}

// NewContractCaller returns a ContractCaller.
func NewContractCaller(key *keystore.Key, ethClient *ethclient.Client) (*ContractCaller, error) {
	return &ContractCaller{
		key:    key,
		client: ethClient,
	}, nil
}

// CheckBalance returns balance of the account.
func (cc *ContractCaller) CheckBalance(number int64) (uint64, error) {
	address := cc.key.Address
	balance, err := cc.client.BalanceAt(context.Background(), address, big.NewInt(number))
	return balance.Uint64(), err
}

// NewContract makes a new contract with given newContractFunc.
func (cc *ContractCaller) NewContract(contract interface{}, newContractFuncName string, contractAddress common.Address) (contractInstance interface{}) {
	m := reflect.ValueOf(contract).MethodByName(newContractFuncName)
	in := []reflect.Value{
		reflect.ValueOf(contractAddress),
		reflect.ValueOf(cc.client),
	}
	contractInstance = m.Call(in)
	return contractInstance
}

func (cc *ContractCaller) NewAuth(value uint64, gasLimit uint64) (opts *bind.TransactOpts, err error) {
	gasPrice, err := cc.client.SuggestGasPrice(context.Background())
	if err != nil {
		return nil, err
	}

	auth := bind.NewKeyedTransactor(cc.key.PrivateKey)
	auth.Value = big.NewInt(int64(value))
	auth.GasLimit = gasLimit
	auth.GasPrice = gasPrice

	return auth, nil
}

func (cc *ContractCaller) CallContractFunc(contractInstance interface{}, contractFuncName string, parameters ...interface{}) (callResult interface{}) {

	m := reflect.ValueOf(contractInstance).MethodByName(contractFuncName)
	in := []reflect.Value{}
	for _, p := range parameters {
		in = append(in, reflect.ValueOf(p))
	}
	callResult = m.CallSlice(in)

	return callResult
}

type NodeID string
type Pubkey []byte

type RemoteSigner struct {
	pubkey  Pubkey
	nodeID  NodeID
	address common.Address
}

// fetchPubkey fetches the public key of the remote signer from the contract.
func (rs *RemoteSigner) fetchPubkey(ethClient *ethclient.Client) (Pubkey, error) {
	panic("not implemented")
}

// fetchNodeID fetches the node id of the remote signer encrypted with my public key, and decrypts it with my private key.
func (rs *RemoteSigner) fetchNodeID() (NodeID, error) {
	panic("not implemented")
}

// updateNodeID encrypts my node id with this remote signer's public key and update to the contract.
func (rs *RemoteSigner) updateNodeID(nodeID NodeID) error {
	panic("not implemented")
}

// BasicOverlayCallback implements OverlayCallback
type BasicOverlayCallback struct {
	*peerSet

	ownNodeID  NodeID
	ownPubkey  Pubkey
	ownAddress common.Address

	remoteSigners []*RemoteSigner
}

func NewBasicOverlayCallback(peers *peerSet, ownNodeID NodeID, ownPubkey Pubkey, ownAddress common.Address)

// Callback implements OverlayCallback.Callback
func (oc *BasicOverlayCallback) Callback(ethClient *ethclient.Client) (err error) {

	// fetchpubkey
	// oc.FetchPubKey()

	// updatenodeid
	// oc.UpdateNodeID()

	// fetchnodeid
	// oc.FetchNodeID()

	// dialremote
	// oc.DialRemote()

	panic("not implemented")
}

// FetchPubKey implements OverlayCallback.FetchPubKey
func (oc *BasicOverlayCallback) FetchPubKey(remoteAddress common.Address) (pubkey []byte, err error) {
	panic("not implemented")
}

// UpdateNodeID implements OverlayCallback.UpdateNodeID
func (oc *BasicOverlayCallback) UpdateNodeID(ownNodeID string) error {
	panic("not implemented")
}

// FetchNodeID implements OverlayCallback.FetchNodeID
func (oc *BasicOverlayCallback) FetchNodeID() (remoteNodeID string, err error) {
	panic("not implemented")
}

// DialRemote implements OverlayCallback.DialRemote
func (oc *BasicOverlayCallback) DialRemote(remoteNodeID string, ownAddress common.Address) (err error) {
	panic("not implemented")
}
