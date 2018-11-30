package backend_test

import (
	"context"
	"crypto/ecdsa"
	"encoding/hex"
	"fmt"
	"math/big"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"bitbucket.org/cpchain/chain/contracts/dpor/contracts"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

func init() {
	log.SetLevel(log.DebugLevel)
}

func loadDefaultAccount(idx int) (common.Address, *keystore.Key) {
	filename := "../../../examples/cpchain/conf/keys/"
	kst := keystore.NewKeyStore(filename, 2, 1)
	account := kst.Accounts()[idx]
	account, key, err := kst.GetDecryptedKey(account, "password")
	privateKey := key.PrivateKey
	if err != nil {
		log.Fatal(err.Error())
	}
	publicKey := privateKey.Public()
	publicKeyECDSA, ok := publicKey.(*ecdsa.PublicKey)
	if !ok {
		log.Fatal("error casting public key to ECDSA")
	}
	fromAddress := crypto.PubkeyToAddress(*publicKeyECDSA)

	return fromAddress, key
}

func createSimulatedBackend(alloc core.GenesisAlloc) *backends.SimulatedBackend {
	contractBackend := backends.NewDporSimulatedBackend(alloc)
	return contractBackend
}

func deployRegister(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, *types.Transaction, *dpor.ProposerRegister, error) {

	deployTransactor := bind.NewKeyedTransactor(prvKey)
	addr, tx, instance, err := dpor.DeployProposerRegister(deployTransactor, backend)

	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
		return common.Address{}, nil, nil, err
	}
	backend.Commit()
	return addr, tx, instance, nil
}

func createTransactor(key *ecdsa.PrivateKey) *bind.TransactOpts {
	transactOpts := bind.NewKeyedTransactor(key)
	transactOpts.GasLimit = 3000000
	transactOpts.GasPrice = big.NewInt(0)
	transactOpts.Value = big.NewInt(1000)
	return transactOpts
}

func TestBasicLogic(t *testing.T) {

	// create parameters

	// create two accounts, one as validator, one as proposer
	vAddr, vKey := loadDefaultAccount(1)
	pAddr, pKey := loadDefaultAccount(2)

	fmt.Println("validator address", vAddr.Hex())
	fmt.Println("proposer address", pAddr.Hex())

	term := uint64(1)

	fmt.Println("term", term)

	pID := "enode://helloworld@1.2.3.4:8888"
	_ = pID

	// create a server

	// new a simulated backend
	alloc := core.GenesisAlloc{
		vAddr: {Balance: big.NewInt(1000000000000)},
		pAddr: {Balance: big.NewInt(1000000000000)},
	}
	backend := createSimulatedBackend(alloc)

	// create transactors
	vTransactor := createTransactor(vKey.PrivateKey)
	pTransactor := createTransactor(pKey.PrivateKey)

	_, _ = vTransactor, pTransactor

	// deploy the contract
	contractAddr, tx, register, err := deployRegister(vKey.PrivateKey, big.NewInt(0), backend)
	_, _, _, _ = contractAddr, tx, register, err
	backend.Commit()

	fmt.Println("contract addr", contractAddr.Hex())

	// register validator's public key
	tx, err = register.RegisterPublicKey(vTransactor, vKey.RsaKey.PublicKey.RsaPublicKeyBytes)
	_, _ = tx, err
	backend.Commit()

	// proposer fetches validator's public key
	vPubBytes, err := register.GetPublicKey(nil, vAddr)
	vPubkey, err := rsakey.NewRsaPublicKey(vPubBytes)
	_, _ = vPubkey, err

	fmt.Println("validator's pubkey from contract \n", hex.Dump(vPubBytes))

	// proposer encrypts his nodeID with the pubkey
	encryptedNodeID, err := vPubkey.RsaEncrypt([]byte(pID))
	fmt.Println("encrypted proposer's nodeID \n", hex.Dump(encryptedNodeID), "err", err)

	// proposer uploads this encrypted nodeID to the contract
	termB := big.NewInt(int64(term))
	tx, err = register.AddNodeInfo(pTransactor, termB, vAddr, encryptedNodeID)
	fmt.Println("tx", tx.Hash().Hex(), "err", err)

	backend.Commit()

	// validator fetches the encrypted nodeID from the contract
	vCallOpts := &bind.CallOpts{
		From: vAddr,
	}
	eNodeIDBytes, err := register.GetNodeInfo(vCallOpts, termB, pAddr)
	fmt.Println("fetched encrypted nodeID from contract \n", hex.Dump(eNodeIDBytes), "err", err)

	nodeID, err := vKey.RsaKey.RsaDecrypt(eNodeIDBytes)
	fmt.Println("decrypted nodeID", string(nodeID), "err", err)

}

func TestRemoteSigner(T *testing.T) {

	// prepare accouts
	v1Addr, v1Key := loadDefaultAccount(1)
	v2Addr, v2Key := loadDefaultAccount(2)
	v3Addr, v3Key := loadDefaultAccount(5)
	v4Addr, v4Key := loadDefaultAccount(6)

	p1Addr, p1Key := loadDefaultAccount(7)

	// setup backend

	// new a simulated backend
	alloc := core.GenesisAlloc{
		v1Addr: {Balance: big.NewInt(1000000000000)},
		v2Addr: {Balance: big.NewInt(1000000000000)},
		v3Addr: {Balance: big.NewInt(1000000000000)},
		v4Addr: {Balance: big.NewInt(1000000000000)},

		p1Addr: {Balance: big.NewInt(1000000000000)},
	}
	simulatedBackend := createSimulatedBackend(alloc)

	// create validator transactors
	v1Transactor := createTransactor(v1Key.PrivateKey)
	v2Transactor := createTransactor(v2Key.PrivateKey)
	v3Transactor := createTransactor(v3Key.PrivateKey)
	v4Transactor := createTransactor(v4Key.PrivateKey)

	// deploy the contract
	contractAddr, tx, register, err := deployRegister(v1Key.PrivateKey, big.NewInt(0), simulatedBackend)
	_, _, _, _ = contractAddr, tx, register, err
	simulatedBackend.Commit()

	fmt.Println("contract addr", contractAddr.Hex())

	// register validator's public key
	tx, err = register.RegisterPublicKey(v1Transactor, v1Key.RsaKey.PublicKey.RsaPublicKeyBytes)
	simulatedBackend.Commit()
	tx, err = register.RegisterPublicKey(v2Transactor, v2Key.RsaKey.PublicKey.RsaPublicKeyBytes)
	simulatedBackend.Commit()
	tx, err = register.RegisterPublicKey(v3Transactor, v3Key.RsaKey.PublicKey.RsaPublicKeyBytes)
	simulatedBackend.Commit()
	tx, err = register.RegisterPublicKey(v4Transactor, v4Key.RsaKey.PublicKey.RsaPublicKeyBytes)
	simulatedBackend.Commit()

	//
	term := uint64(4)
	gasLimit := uint64(1000000)

	// as a proposer
	nodeID := "hello world"

	// contractCaller
	contractCaller, err := backend.NewContractCaller(p1Key, simulatedBackend, gasLimit)

	// creates an contract instance
	contractInstance, err := dpor.NewProposerRegister(contractAddr, contractCaller.Client)

	// creates a keyed transactor
	auth := bind.NewKeyedTransactor(contractCaller.Key.PrivateKey)
	gasPrice, err := contractCaller.Client.SuggestGasPrice(context.Background())
	auth.Value = big.NewInt(0)
	auth.GasLimit = contractCaller.GasLimit
	auth.GasPrice = gasPrice

	// create remote validator
	remoteV := backend.NewRemoteValidator(term, v1Addr)

	// upload all
	go func() {
		succeed, err := remoteV.UploadNodeInfo(nodeID, auth, contractInstance, simulatedBackend)
		fmt.Println("succeed", succeed, "err", err)
	}()

	done := make(chan struct{})
	go func() {
		time.Sleep(1 * time.Second)
		simulatedBackend.Commit()
		close(done)
	}()

	<-done

	// fetch it

	remoteP := backend.NewRemoteProposer(term, p1Addr)
	succeed, err := remoteP.FetchNodeInfoAndDial(v1Addr, nil, v1Key.RsaKey, contractInstance)
	fmt.Println("succeed", succeed, "err", err)

}

// //
// gasLimit := uint64(100000)

// // create a dialer as proposer 1
// dialer := backend.NewDialer(p1Addr, contractAddr)
// dialer.SetNodeID("Hello World")
// contractCaller, err := backend.NewContractCaller(p1Key, simulatedBackend, gasLimit)
// dialer.SetContractCaller(contractCaller)

// // set term and remote proposers
// term := uint64(4)
// validators := []common.Address{
// 	v1Addr,
// 	v2Addr,
// 	v3Addr,
// 	v4Addr,
// }

// err = dialer.UpdateRemoteValidators(term, validators)
// fmt.Println("err when update remote validators", err)

// // upload encrypted keys
// go func() {
// 	err = dialer.UploadEncryptedNodeInfo(term)
// 	fmt.Println("err when upload encrypted node info", err)
// }()

// done := make(chan struct{})

// go func() {
// 	i := 0
// 	for i < 5 {
// 		i++
// 		time.Sleep(1 * time.Second)
// 		simulatedBackend.Commit()
// 	}
// 	close(done)
// }()

// <-done

// // create a dialer as validator 1
// dialer = backend.NewDialer(v1Addr, contractAddr)
// contractCaller, err = backend.NewContractCaller(v1Key, simulatedBackend, gasLimit)
// dialer.SetContractCaller(contractCaller)

// proposers := []common.Address{
// 	p1Addr,
// }

// err = dialer.UpdateRemoteProposers(term, proposers)
// fmt.Println("err when update proposers", err)

// err = dialer.DialAllRemoteProposers(term)
// fmt.Println("err when fetch and dial", err)

// callOpts := &bind.CallOpts{
// 	From: v1Addr,
// }

// eNodeIDBytes, err := register.GetNodeInfo(callOpts, big.NewInt(int64(term)), p1Addr)
// fmt.Println("fetched encrypted nodeID from contract \n", hex.Dump(eNodeIDBytes), "err", err)

// nodeID, err := v1Key.RsaKey.RsaDecrypt(eNodeIDBytes)
// fmt.Println("decrypted nodeID", string(nodeID), "err", err)
