package pdash

import (
	"github.com/ethereum/go-ethereum/crypto"
)

var (
	key, _ = crypto.HexToECDSA("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
	addr   = crypto.PubkeyToAddress(key.PublicKey)
)

// TODO: @AC the unittest is duplicated with register_test.go, should add real unittest for pdash.sol.
// func TestRegister(t *testing.T) {
// 	contractBackend := backends.NewDporSimulatedBackend(core.GenesisAlloc{addr: {Balance: big.NewInt(1000000000000)}})
// 	_, _, _ = deployTestRegister(key, big.NewInt(0), contractBackend)
// 	contractBackend.Commit()
// }
