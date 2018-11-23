package backend

import (
	"context"
	"sync"

	"math/big"

	"encoding/hex"

	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/signer_register"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
)

type Proposer struct {
	nodeId  string
	termIdx uint64
	address common.Address
	pubkey  []byte

	nodeIdUpdated bool //A bool variable indicating if its encrypted nodeId is sent to contract
	server        *p2p.Server
	rsaKey        *rsakey.RsaKey

	//Proposer register contract related fields
	contractAddress    common.Address
	contractCaller     *ContractCaller
	contractInstance   *contract.SignerConnectionRegister
	contractTransactor *bind.TransactOpts

	lock sync.RWMutex
}

// SetServer sets Proposer.server
func (p *Proposer) SetServer(server *p2p.Server) error {
	p.lock.Lock()
	defer p.lock.Unlock()

	p.server = server
	p.nodeId = server.Self().String()

	return nil
}

// SetRsaKey sets Proposer.rsaKey
func (p *Proposer) SetRsaKey(rsaReader RsaReader) error {
	p.lock.Lock()
	defer p.lock.Unlock()

	var err error
	p.rsaKey, err = rsaReader()

	return err
}

// SetContractCaller sets Proposer.contractcaller.
func (p *Proposer) SetContractCaller(contractCaller *ContractCaller) error {

	// creates an contract instance
	contractInstance, err := contract.NewSignerConnectionRegister(p.contractAddress, contractCaller.Client)
	if err != nil {
		return err
	}

	// creates a keyed transactor
	auth := bind.NewKeyedTransactor(contractCaller.Key.PrivateKey)

	gasPrice, err := contractCaller.Client.SuggestGasPrice(context.Background())
	if err != nil {
		return err
	}

	auth.Value = big.NewInt(0)
	auth.GasLimit = contractCaller.GasLimit
	auth.GasPrice = gasPrice

	rsaReader := func() (*rsakey.RsaKey, error) {
		return contractCaller.Key.RsaKey, nil
	}
	err = p.SetRsaKey(rsaReader)
	if err != nil {
		return err
	}

	p.lock.Lock()

	// assign
	p.contractCaller = contractCaller
	p.contractInstance = contractInstance
	p.contractTransactor = auth

	p.lock.Unlock()

	return nil
}

// updateNodeID encrypts nodeId with this remote validator's public key and update to the contract.
// It is invoked for each validator in validators committee
func (p *Proposer) updateNodeId(nodeId string, auth *bind.TransactOpts, contractInstance *contract.SignerConnectionRegister, client ClientBackend) error {
	termIdx, address := p.termIdx, p.address

	log.Debug("fetched rsa pubkey")
	log.Debug(hex.Dump(p.pubkey))

	pubkey, err := rsakey.NewRsaPublicKey(p.pubkey)

	log.Debug("updating self nodeId with remote validator's public key")
	log.Debug("term", "idx", termIdx)
	log.Debug("signer", "addr", address.Hex())
	log.Debug("nodeID", "nodeID", nodeId)
	log.Debug("pubkey", "pubkey", pubkey)

	if err != nil {
		log.Error(err.Error())
		return err
	}

	encryptedNodeId, err := pubkey.RsaEncrypt([]byte(nodeId))

	log.Debug("encryptedNodeId")
	log.Debug(hex.Dump(encryptedNodeId))

	transaction, err := contractInstance.AddNodeInfo(auth, big.NewInt(int64(termIdx)), address, encryptedNodeId)
	if err != nil {
		log.Error(err.Error())
		return err
	}

	ctx := context.Background()
	_, err = bind.WaitMined(ctx, client, transaction)
	if err != nil {
		log.Error(err.Error())
		return err
	}

	p.nodeIdUpdated = true

	log.Debug("updated self nodeId")

	return nil
}

// PVHandshake is to handshake between proposer and a validator from validators commmittee
func PVHandshake(p *p2p.Peer, rw p2p.MsgReadWriter, proposerAddress common.Address, signerValidator ValidateSignerFn) (isSigner bool, address common.Address, err error) {
	// Send out own handshake in a new thread
	errs := make(chan error, 2)
	var proposerStatus signerStatusData // safe to read after two values have been received from errs

	go func() {
		err := p2p.Send(rw, NewSignerMsg, &signerStatusData{
			ProtocolVersion: uint32(ProtocolVersion),
			Address:         proposerAddress,
		})
		errs <- err
	}()
	go func() {
		isSigner, address, err = ReadValidatorStatus(p, rw, &proposerStatus, signerValidator)
		errs <- err
	}()
	timeout := time.NewTimer(handshakeTimeout)
	defer timeout.Stop()
	for i := 0; i < 2; i++ {
		select {
		case err := <-errs:
			if err != nil {
				return false, common.Address{}, err
			}
		case <-timeout.C:
			return false, common.Address{}, p2p.DiscReadTimeout
		}
	}
	return isSigner, address, nil
}

// ReadSignerStatus reads status of remote signer
func ReadValidatorStatus(p *p2p.Peer, rw p2p.MsgReadWriter, signerStatus *signerStatusData, signerValidator ValidateSignerFn) (isSigner bool, address common.Address, err error) {
	msg, err := rw.ReadMsg()
	if err != nil {
		return false, common.Address{}, err
	}
	if msg.Code != NewSignerMsg {
		return false, common.Address{}, errResp(ErrNoStatusMsg, "first msg has code %x (!= %x)", msg.Code, NewSignerMsg)
	}
	if msg.Size > ProtocolMaxMsgSize {
		return false, common.Address{}, errResp(ErrMsgTooLarge, "%v > %v", msg.Size, ProtocolMaxMsgSize)
	}
	// Decode the handshake and make sure everything matches
	if err := msg.Decode(&signerStatus); err != nil {
		return false, common.Address{}, errResp(ErrDecode, "msg %v: %v", msg, err)
	}
	if int(signerStatus.ProtocolVersion) != ProtocolVersion {
		return false, common.Address{}, errResp(ErrProtocolVersionMismatch, "%d (!= %d)", signerStatus.ProtocolVersion, ProtocolVersion)
	}

	// TODO: this (addr, ...) pair should be signed with its private key.
	// @liuq

	isSigner, err = signerValidator(signerStatus.Address)
	return isSigner, signerStatus.Address, err
}
