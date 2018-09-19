package rsa_

import (
	"io/ioutil"

	"bitbucket.org/cpchain/chain/log"
)

func LoadFile(path string) ([]byte, error) {
	b, err := ioutil.ReadFile(path)
	if err != nil {
		log.Info("file ", path, " not found.")
		return nil, err
	}
	return b, nil
}
