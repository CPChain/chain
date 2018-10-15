package main

import (
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/node"
	"bytes"
	"fmt"
	"github.com/urfave/cli"
	"golang.org/x/crypto/ssh/terminal"
	"syscall"
)

// readPassword retrieves the password associated with an account, either fetched
// from a list of preloaded passphrases, or requested interactively from the user.
func readPassword(prompt string, needConfirm bool, i int, passwords []string) string {
	if len(passwords) > 0 {
		if i < len(passwords) {
			return passwords[i]
		}
		return passwords[len(passwords)-1]
	}
	// be cautious about whitespace
	if prompt != "" {
		fmt.Println("If your password contains whitespaces, please be careful enough to avoid later confusion.")
		fmt.Println(prompt)
	}
	password, err := terminal.ReadPassword(syscall.Stdin)
	fmt.Println()
	if err != nil {
		log.Fatalf("Failed to read password: %v", err)
	}
	if needConfirm {
		fmt.Print("Please repeat:")
		p, err := terminal.ReadPassword(syscall.Stdin)
		fmt.Println()
		if err != nil {
			log.Fatalf("Failed to read password: %v", err)
		}
		if !bytes.Equal(password, p) {
			log.Fatalf("Password doesn't match")
		}
	}
	// trailing newline is by default ignored
	return string(password)
}

func registerService() {

}

func createNode(ctx *cli.Context) *node.Node {
	cfg := getConfig(ctx)

	n, err := node.New(&cfg.Node)
	if err != nil {
		log.Fatalf("Node creation failed: %v", err)
	}
	// TODO
	// registerService()
	return n
}
