package ethdb

import (
	"bytes"

	"github.com/ipfs/go-ipfs-api"
)

type IpfsDatabase struct {
	url   string
	shell *shell.Shell
}

func NewIpfsDb(url string) *IpfsDatabase {
	s := shell.NewShell(url)
	return NewIpfsDbWithShell(url, s)
}

func NewIpfsDbWithShell(url string, s *shell.Shell) *IpfsDatabase {
	return &IpfsDatabase{
		url:   url,
		shell: s,
	}
}

func (db *IpfsDatabase) Get(key []byte) ([]byte, error) {
	k := string(key[:])
	reader, err := db.shell.Cat(k)
	if err != nil {
		return nil, err
	}

	const bufsize = 1000
	buf := make([]byte, bufsize)
	var ret []byte
	for {
		n, _ := reader.Read(buf)
		if n == 0 {
			break
		}

		ret = append(ret, buf[:n]...)
	}
	return ret, nil
}

func (db *IpfsDatabase) Put(value []byte) ([]byte, error) {
	reader := bytes.NewBuffer(value)
	hash, err := db.shell.Add(reader)

	if err != nil {
		return nil, err
	} else {
		return []byte(hash), nil
	}
}

func (db *IpfsDatabase) Delete(key []byte) error {
	// TODO: implement it
	return nil
}

func (db *IpfsDatabase) Has(key []byte) (bool, error) {
	// TODO: implement it
	return false, nil
}
