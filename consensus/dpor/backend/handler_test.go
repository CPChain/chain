package backend

import (
	"fmt"
	"os"
	"path/filepath"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/keystore"
)

// launch the chain
// new a committee_network_handler
// build the network.

// func TestNewHandler(t *testing.T) {
// 	type args struct {
// 		config    *configs.DporConfig
// 		etherbase common.Address
// 	}

// 	//define the parameter "config" of NewHandler()
// 	var testConfig *configs.DporConfig
// 	testConfig = configs.MainnetChainConfig.Dpor
// 	//define the parameter "etherbase" for NewHandler()
// 	testEtherbase := common.HexToAddress("0x4CE687F9dDd42F26ad580f435acD0dE39e8f0000")

// 	//Assign an expected handler
// 	var expectedResult Handler
// 	expectedResult.mode = LBFTMode
// 	expectedResult.coinbase = testEtherbase
// 	expectedResult.knownBlocks = newKnownBlocks()
// 	expectedResult.pendingBlockCh = make(chan *types.Block)
// 	expectedResult.quitSync = make(chan struct{})
// 	expectedResult.available = false

// 	tests := []struct {
// 		name string
// 		args args
// 		want *Handler
// 	}{
// 		{"testHandler1", args{testConfig, testEtherbase}, &expectedResult},
// 	}
// 	for _, tt := range tests {
// 		t.Run(tt.name, func(t *testing.T) {
// 			got := NewHandler(tt.args.config, tt.args.etherbase)
// 			//pendingBlockCh and quitSync are expected to be different
// 			//Thus, before reflect.DeepEqual(), we set both variables equalling to the expected value
// 			got.pendingBlockCh = expectedResult.pendingBlockCh
// 			got.quitSync = expectedResult.quitSync
// 			if !reflect.DeepEqual(got, tt.want) {
// 				t.Errorf("NewHandler() = %v, \n want %v\n", got, tt.want)
// 			}
// 		})
// 	}
// }
func TestHandler_IsAvailable(t *testing.T) {
	var testHandler Handler
	testHandler.available = false
	//Test IsAvailable()
	if testHandler.IsAvailable() != false {
		t.Errorf("IsAvailable() = %v, want %v\n", testHandler.IsAvailable(), false)
	}
	//Test SetAvailable()
	testHandler.SetAvailable()
	if testHandler.IsAvailable() != true {
		t.Errorf("SetAvailale() does not work\n")
	}
}

// Load account. Used for create ContractCaller
func getAccount(keyStoreFilePath string, passphrase string, t *testing.T) keystore.Key {
	ff, err := filepath.Abs("../../../")
	file, err := os.Open(ff + "/examples/cpchain/data/" + keyStoreFilePath)
	if err != nil {
		t.Fatalf("KeyStoreFilePath error, got %v\n", err)
	}

	keyPath, err := filepath.Abs(filepath.Dir(file.Name()))
	if err != nil {
		t.Fatalf("KeyStoreFilePath error, got %v\n", err)
	}

	kst := keystore.NewKeyStore(keyPath, 2, 1)

	// Get account.
	account := kst.Accounts()[0]
	account, key, err := kst.GetDecryptedKey(account, passphrase)
	if err != nil {
		t.Fatalf("Get account failed, got %v", err)
	}

	return *key

}

func TestHandler_SetContractCaller(t *testing.T) {
	t.Skip("skip testing this function")
	var key keystore.Key
	key = getAccount("dd1/keystore/", "password", t)
	fmt.Println("sucessfully print")
	fmt.Println(key)
}
