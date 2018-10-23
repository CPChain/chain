package gapis

import (
	"crypto/x509"
	"errors"
	"io/ioutil"
)

// Create a certificate pool from the certificate authority
func createCertPool() (*x509.CertPool, error) {
	certPool := x509.NewCertPool()
	ca, err := ioutil.ReadFile(ca)
	if err != nil {
		return nil, err
	}

	if ok := certPool.AppendCertsFromPEM(ca); !ok {
		return nil, errors.New("failed to append client certs")
	}

	return certPool, nil
}
