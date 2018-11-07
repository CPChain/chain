package private

import (
	"crypto/aes"
	"crypto/cipher"
	"encoding/binary"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/database"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/rlp"
)

// Read tx's payload replacement, retrieve encrypted payload from IPFS and decrypt it.
// Return decrypted payload, a flag indicating if the node has enough permission and error if there is.
func RetrieveAndDecryptPayload(data []byte, txNonce uint64, remoteDB database.RemoteDatabase, accm *accounts.Manager) (payload []byte, hasPermission bool, error error) {
	replacement := PayloadReplacement{}
	err := rlp.DecodeBytes(data, &replacement)
	if err != nil {
		return []byte{}, false, err
	}

	accLookup := make(map[string]*accounts.Account) // <public key encoded string> -> Account
	walLookup := make(map[string]accounts.Wallet)   // <public key encoded string> -> Wallet
	for _, wallet := range accm.Wallets() {
		for _, account := range wallet.Accounts() {
			rsaKey, error := wallet.GetRsaPublicKey(account)
			if error == nil {
				pubKeyEncoded := hexutil.Encode(rsaKey.RsaPublicKeyBytes)
				accLookup[pubKeyEncoded] = &account
				walLookup[pubKeyEncoded] = wallet
			}
		}
	}

	// Check if the current node is in the participant group by comparing is public key and decrypt with its private
	// key and return result.
	sealed, err := getDataFromRemote(replacement.TxPayloadUri, remoteDB)
	if err != nil {
		return []byte{}, false, err
	}

	sp := SealedPrivatePayload{}
	err = rlp.DecodeBytes(sealed, &sp)
	if err != nil {
		return []byte{}, false, err
	}
	for i, k := range replacement.Participants {
		acc, exists := accLookup[k]
		if exists {
			wallet, _ := walLookup[k]

			encryptedKey := sp.SymmetricKeys[i]
			symKey := decryptSymKey(encryptedKey, wallet, acc)
			decrypted, _ := decryptPayload(sp.Payload, symKey, txNonce)
			return decrypted, true, nil
		}
	}

	return []byte{}, false, nil
}

func getDataFromRemote(ipfsAddress []byte, remoteDB database.RemoteDatabase) ([]byte, error) {
	content, err := remoteDB.Get(ipfsAddress)
	if err != nil {
		return []byte{}, err
	}
	return content, nil
}

func decryptSymKey(data []byte, wallet accounts.Wallet, account *accounts.Account) []byte {
	decrypted, _ := wallet.DecryptWithRsa(*account, data)
	return decrypted
}

// Decrypt payload with the given symmetric key.
// Returns decrypted payload and error if exists.
func decryptPayload(cipherdata []byte, skey []byte, txNonce uint64) ([]byte, error) {
	// use tx's nonce as gcm nonce
	nonce := make([]byte, 12)
	binary.BigEndian.PutUint64(nonce, txNonce)
	binary.BigEndian.PutUint32(nonce[8:], uint32(txNonce))

	block, err := aes.NewCipher(skey)
	if err != nil {
		return []byte{}, err
	}

	aesgcm, err := cipher.NewGCM(block)
	data, err := aesgcm.Open(nil, nonce, cipherdata, nil)
	if err != nil {
		return []byte{}, err
	}
	return data, nil
}
