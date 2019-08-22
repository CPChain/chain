package utility

import (
	"fmt"
	"io/ioutil"
	"strings"

	"bitbucket.org/cpchain/chain/cmd/cpchain/commons"
)

// ReadPasswordByFile read password
func ReadPasswordByFile(file string) (*string, error) {
	if file == "" {
		prompt := fmt.Sprintf("Input password:")
		password, _ := commons.ReadPassword(prompt, false)
		return &password, nil
	}

	b, err := ioutil.ReadFile(file)
	if err != nil {
		return nil, err
	}
	pwd := string(b)
	pwd = strings.Trim(pwd, "\n")
	pwd = strings.Trim(pwd, " ")
	return &pwd, nil
}
