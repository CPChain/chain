package private

import (
	"testing"

	"bytes"

	"encoding/binary"

	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/rlp"
)

func TestSealPrivatePayload(t *testing.T) {
	payload := []byte("This is a payload plaintext.")
	txNonce := uint64(10000)

	ipfsAddr, err := SealPrivatePayload(payload, txNonce)
	if err != nil {
		t.Fatal("It should return expected IPFS address without any error.")
	}

	ipfsDb := ethdb.NewIpfsDb("localhost:5001")
	content, err := ipfsDb.Get(ipfsAddr)
	if err != nil {
		t.Fatal("It should return expected content from IPFS.")
	}

	sealedPayload := SealedPrivatePayload{}
	err = rlp.DecodeBytes(content, &sealedPayload)
	if err != nil {
		t.Fatal("The content retrieved from IPFS should be decoded into a SealedPrivatePayload object.")
	}

	// use tx's nonce as gcm nonce
	nonce := make([]byte, 12)
	binary.BigEndian.PutUint64(nonce, txNonce)
	binary.BigEndian.PutUint32(nonce[8:], uint32(txNonce))
	recoveredPayload, err := decrypt(sealedPayload.Payload, sealedPayload.SymmetricKey, nonce)
	if err != nil {
		t.Fatal("The decryption should succeedd.")
	}

	if !bytes.Equal(payload, recoveredPayload) {
		t.Fatal("The recovered payload should be equal to origin one.")
	}
}
