package rsa1

import (
	"io/ioutil"

	"github.com/ethereum/go-ethereum/log"
)

func LoadFile(path string) ([]byte, error) {
	b, err := ioutil.ReadFile(path)
	if err != nil {
		log.Info("file ", path, " not found.")
		return nil, err
	}
	return b, nil
}
