package backend

import (
	"fmt"
	"os"
	"path/filepath"
	"testing"

	"bitbucket.org/cpchain/chain/accounts/keystore"
)

func TestHandler_Available(t *testing.T) {
	var testHandler Handler
	testHandler.available = false
	//Test IsAvailable()
	if testHandler.Available() != false {
		t.Errorf("IsAvailable() = %v, want %v\n", testHandler.Available(), false)
	}
	//Test SetAvailable()
	testHandler.SetAvailable()
	if testHandler.Available() != true {
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
