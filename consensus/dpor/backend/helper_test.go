package backend_test

import (
	"crypto/ecdsa"
	"fmt"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/commons/crypto/rsakey"
	"bitbucket.org/cpchain/chain/commons/log"
	contract "bitbucket.org/cpchain/chain/contracts/dpor/contracts/signer_register"
	"bitbucket.org/cpchain/chain/core"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
)

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

func deployRegister(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, *types.Transaction, *contract.SignerConnectionRegister, error) {

	deployTransactor := bind.NewKeyedTransactor(prvKey)
	addr, tx, instance, err := contract.DeploySignerConnectionRegister(deployTransactor, backend)

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

	// create two accounts, one as local peer, one as remote signer
	addr1, key1 := loadDefaultAccount(1)
	addr2, key2 := loadDefaultAccount(2)

	fmt.Println("addr1", addr1, "key1", key1)
	fmt.Println("addr2", addr2, "key2", key2)

	epochIdx := uint64(1)
	ownAddr := addr1

	fmt.Println("epoch", epochIdx)
	fmt.Println("own address", ownAddr)

	id1, id2 := "ID1", "ID2"

	_, _ = id1, id2

	// create a server

	// new a simulated backend
	alloc := core.GenesisAlloc{
		addr1: {Balance: big.NewInt(1000000000000)},
		addr2: {Balance: big.NewInt(1000000000000)},
	}

	backend := createSimulatedBackend(alloc)

	// create transactors
	transactor1 := createTransactor(key1.PrivateKey)
	transactor2 := createTransactor(key2.PrivateKey)

	_, _ = transactor1, transactor2

	// deploy the contract
	contractAddr, tx, register, err := deployRegister(key1.PrivateKey, big.NewInt(0), backend)
	_, _, _, _ = contractAddr, tx, register, err

	backend.Commit()

	fmt.Println("contract addr", contractAddr.Hex())

	fmt.Println("RegisterPublicKey tx:", tx.Hash().Hex())

	tx, err = register.RegisterPublicKey(transactor1, key1.RsaKey.PublicKey.RsaPublicKeyBytes)
	_, _ = tx, err

	tx, err = register.RegisterPublicKey(transactor2, key2.RsaKey.PublicKey.RsaPublicKeyBytes)
	_, _ = tx, err

	pub1bytes, err := register.GetPublicKey(nil, addr1)
	pub2bytes, err := register.GetPublicKey(nil, addr2)

	pub1, err := rsakey.NewRsaPublicKey(pub1bytes)

	_, _ = pub1, err

	fmt.Println("pubkey from contract 1", pub1bytes)
	fmt.Println("pubkey from contract 2", pub2bytes)

	// create a RemoteSigner
	// rs := NewRemoteSigner(epochIdx, addr2)
	// _ = rs

	// // set fields

	// transactor2 = createTransactor(key2.PrivateKey)
	// // upload id2
	// encryptedid2, err := pub1.RsaEncrypt([]byte(id2))
	// tx, err = register.AddNodeInfo(transactor2, big.NewInt(1), addr1, encryptedid2)
	// fmt.Println("err when update node id 2", err)

	// backend.Commit()

	// ctx := context.Background()
	// receipt, err := backend.TransactionReceipt(ctx, tx.Hash())
	// fmt.Println("status", receipt.Status)

	// callopts1 := &bind.CallOpts{
	// 	From:    addr1,
	// 	Pending: true,
	// 	Context: ctx,
	// }
	// x, err := register.GetNodeInfo(callopts1, big.NewInt(1), addr2)
	// fmt.Println(x, err)

	// callopts2 := &bind.CallOpts{
	// 	From:    addr2,
	// 	Pending: true,
	// 	Context: ctx,
	// }

	// x, err = register.GetNodeInfo(callopts2, big.NewInt(1), addr1)
	// fmt.Println(x, err)

	// // // fetch pub2
	// nodeid, err := rs.fetchPubkey(register)
	// fmt.Println(nodeid, err)

	// // fetch id1
	// nodeid, err = fetchNodeID(rs.epochIdx, addr1, addr1, register)
	// fmt.Println("fetched id of node1", nodeid, "err", err)

	// nodeid, err = register.GetNodeInfo(nil, big.NewInt(int64(rs.epochIdx)), addr1)
	// fmt.Println("fetched id of node1", nodeid, "err", err)

	// transactor1 = createTransactor(key1.PrivateKey)
	// err = rs.updateNodeID(id1, transactor1, register, backend)
	// fmt.Println("err when update node id 1", err)

	// backend.Commit()

	// // fetch id2
	// id, err := rs.fetchNodeID(addr1, register, key1.RsaKey)
	// fmt.Println(id)
	// fmt.Println("fetched id of node2", rs.nodeID, "err", err)

}
