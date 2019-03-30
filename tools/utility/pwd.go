package utility

import (
	"io/ioutil"
	"strings"
)

// ReadPasswordByFile read password
func ReadPasswordByFile(file string) (*string, error) {
	b, err := ioutil.ReadFile(file)
	if err != nil {
		return nil, err
	}
	pwd := string(b)
	pwd = strings.Trim(pwd, "\n")
	pwd = strings.Trim(pwd, " ")
	return &pwd, nil
}
