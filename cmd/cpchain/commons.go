package main

import (
	"bytes"
	"fmt"
	"syscall"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/node"
	"github.com/urfave/cli"
	"golang.org/x/crypto/ssh/terminal"
)

func readPassword(prompt string, needConfirm bool) string {
	// be cautious about whitespace
	fmt.Println("If your password contains whitespaces, please be careful enough to avoid later confusion.")
	fmt.Print(prompt)
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
