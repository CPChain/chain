package private

import (
	"testing"

	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/rlp"
)

// TestSealPrivatePayload test seal and encrypt private tx's payload.
func TestSealPrivatePayload(t *testing.T) {
	payload := []byte("This is a payload plaintext.")
	txNonce := uint64(10000)

	parties := []string{"0x3082010a0282010100d065e5942da25a81fc431f46788281a19d2b961ca14cddc09376c7d63d949ae581735cbee1ff96d60b6410a4501d2c9df01ec6152e39600a80f0af1446c5f4ec275a292c5d9d1ef70a07c04c4f0dd1c8e586059002c16e9c4189c47c848adbd06f256a05da7557f3a4d781e7f185a47045eb4926c6db5c45f639091c7c3e1b29c9869f293b97963cdb83f586bf7e35d2ae1745c79baaa9912f2acd46b1fe35112c50eff32d356e6c2edc27dfa5564ad2ce04e8f39de86ddf5eb76e5958b23da580c242653463eec95ca186f916d5709ccae8ede25c1ad4b19cd62b1e1cfe7e6ea53f8fcd3c7812d2ceb89b5cd3e0d7d4926c9627ddd531fc59010b95a30de8a70203010001",
		"0x3082010a0282010100bc84262a13ceff4b5d3bfb296d594658ce52b2853d88df4393f96644cdb0c5ab8bf72d529422d955e046c225cf67cf311c3c32ca02abf9f0e3cf669dc702ae07fd234a953113c9744ef11bf33c9794e4b57742bcb2139edfdcc1fbc6258414ca4d9872ee59769aa8caecaa5495c891c168963fd6793e19a42e630f9265abaaf8374911c5ac5dc3170f122c5697fabc72fc4604523a4dd629a34510ade89a0eb26e9ad1ba56f0dfcc83294bcbda9b7d97b2e41d6ea2ad84957e4353207ac51753b801206b4ff99df96bcaec37728956b41ebe892eed87543cf41fba2b02401f15d6daa335baecd30f1622f8bf1bfd39ac638eee957dc3c30ed3b6d823708cd0470203010001"}

	fakeIpfsAdapter := ethdb.NewFakeIpfsAdapter()
	replacement, err := SealPrivatePayload(payload, txNonce, parties, ethdb.NewIpfsDbWithAdapter(fakeIpfsAdapter))
	if err != nil {
		t.Fatal("It should return expected IPFS address without any error.")
	}
	if len(replacement.Participants) == 0 {
		t.Fatal("It should return non-empty participants.")
	}

	ipfsDb := ethdb.NewIpfsDb("localhost:5001")
	content, err := ipfsDb.Get(replacement.Address)
	if err != nil {
		t.Fatal("It should return expected content from IPFS.")
	}

	sealedPayload := SealedPrivatePayload{}
	err = rlp.DecodeBytes(content, &sealedPayload)
	if err != nil {
		t.Fatal("The content retrieved from IPFS should be decoded into a SealedPrivatePayload object.")
	}
	if len(sealedPayload.Participants) == 0 {
		t.Fatal("The retrieved sealed payload should hava more than zero participants.")
	}
	if len(sealedPayload.SymmetricKeys) != len(sealedPayload.Participants) {
		t.Fatal("The number of participants should be equal to encrypted keys.")
	}
	if len(sealedPayload.Payload) == 0 {
		t.Fatal("The payload should not be empty.")
	}
}

// TestGetPrivateKeyForAccount tests getting private key for given account.
func TestGetPrivateKeyForAccount(t *testing.T) {
	account1 := "e94b7b6c5a0e526a4d97f9768ad6097bde25c62a"
	prv1 := GetPrivateKeyForAccount(account1)
	if prv1 == nil {
		t.Fatalf("The private key for %s should be retrieved.", account1)
	}
}
