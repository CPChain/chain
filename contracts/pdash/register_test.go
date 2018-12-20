// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package pdash

import (
	"crypto/ecdsa"
	"fmt"
	"math/big"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/accounts/abi/bind/backends"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/core"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto/sha3"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/stretchr/testify/assert"
)

type file struct {
	fileName string
	fileHash [32]byte
	fileSize *big.Int
}

func sigHash(testfile file) (hash common.Hash) {
	hasher := sha3.NewKeccak256()

	rlp.Encode(hasher, []interface{}{
		testfile.fileName,
		testfile.fileSize,
	})
	hasher.Sum(hash[:0])
	return hash
}

func deployTestRegister(prvKey *ecdsa.PrivateKey, amount *big.Int, backend *backends.SimulatedBackend) (common.Address, *RegisterWrapper, error) {
	deployTransactor := bind.NewKeyedTransactor(prvKey)
	addr, instance, err := DeployRegisterAndReturnWrapper(deployTransactor, backend)
	fmt.Println("contract address :", addr.Hex())

	if err != nil {
		log.Fatalf("failed to deploy contact when mining :%v", err)
		return common.Address{}, nil, err
	}
	backend.Commit()
	return addr, instance, nil
}

func TestRegister(t *testing.T) {
	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
	_, register, err := deployTestRegister(key, big.NewInt(0), contractBackend)
	checkError(t, "can't deploy root registry: %v", err)
	contractBackend.Commit()

	fakefile := file{
		fileName: ",cpchian,cpchian,cpchian",
		fileSize: big.NewInt(88),
	}
	copy(fakefile.fileHash[:], sigHash(fakefile).Bytes())

	transactOpts := bind.NewKeyedTransactor(key)
	_, err = register.ClaimRegister(transactOpts, fakefile.fileName, fakefile.fileHash, fakefile.fileSize)
	if err != nil {
		fmt.Println("ClainRegister error :", err)
		log.Warn("ClaimRegister error", err)
	}
	contractBackend.Commit()

	filenumber, err := register.GetUploadCount(nil, addr)
	if err != nil {
		log.Warn("GetUploadCount err", addr, err)
	}
	fmt.Println(err)
	assert.Equal(t, float64(1), float64(filenumber.Int64()))

	file, err := register.UploadHistory(addr, big.NewInt(int64(0)))
	if err != nil {
		log.Warn("GetUploadCount err", addr, err)
	}
	assert.Equal(t, fakefile.fileName, file.FileName)
}

func checkError(t *testing.T, msg string, err error) {
	if err != nil {
		t.Fatalf(msg, err)
	}
}
