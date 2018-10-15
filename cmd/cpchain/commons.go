package main

import (
	"bytes"
	"fmt"
	"syscall"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/eth"
	"bitbucket.org/cpchain/chain/node"

	"golang.org/x/crypto/ssh/terminal"
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

// Register chain services for a *full* node.
func registerChainService(cfg *eth.Config, n *node.Node) {
	// TODO adjust to the sync mode
	// if cfg.SyncMode != downloader.FullSync {
	// 	log.Fatalf("We only support full sync currently.")
	// }

	err := n.Register(func(ctx *node.ServiceContext) (node.Service, error) {
		fullNode, err := eth.New(ctx, cfg)
		// no plan for les server.
		// if fullNode != nil && cfg.LightServ > 0 {
		// 	ls, _ := les.NewLesServer(fullNode, cfg)
		// 	fullNode.AddLesServer(ls)
		// }
		return fullNode, err
	})
	if err != nil {
		log.Fatalf("Failed to register the chain service: %v", err)
	}
}
