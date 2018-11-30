package backend_test

import (
	"crypto/ecdsa"
	"encoding/hex"
	"fmt"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/proposer_register"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

func init() {
	log.SetLevel(log.FatalLevel)
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

func deployRegister(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, *types.Transaction, *contract.ProposerRegister, error) {

	deployTransactor := bind.NewKeyedTransactor(prvKey)
	addr, tx, instance, err := contract.DeployProposerRegister(deployTransactor, backend)

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

func TestDial(t *testing.T) {

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
