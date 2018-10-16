package main

import (
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/eth"
	"bitbucket.org/cpchain/chain/node"
	"bufio"
	"fmt"
	"os"
)

// readPassword retrieves the password associated with an account, either fetched
// from a list of preloaded passphrases, or requested interactively from the user.
func readPassword(prompt string, createPassword bool) string {
	// be cautious about whitespace when creating new password
	if createPassword {
		// fmt.Println("If your password contains whitespaces, please be careful enough to avoid later confusion.")
	}
	password, _ := ReadPassword(prompt)
	// password, err := terminal.ReadPassword(syscall.Stdin)
	// fmt.Println()
	// if err != nil {
	// 	log.Fatalf("Failed to read password: %v", err)
	// }
	if createPassword {
		// fmt.Print("Please repeat:")
		// p, err := terminal.ReadPassword(syscall.Stdin)
		p, err := ReadPassword("Please repeat:")
		fmt.Println()
		if err != nil {
			log.Fatalf("Failed to read password: %v", err)
		}

		// fmt.Println("password:", password)
		// fmt.Println("p:", p)
		if password != p {
			fmt.Println("Fatal: Password do not match")
			// log.Fatalf("Password doesn't match")
		}
	}
	// trailing newline is by default ignored
	return string(password)
}

func readPassword_(prompt string, createPassword bool) string {
	if prompt != "" {
		fmt.Println(prompt)
	}

	fmt.Print("Please input your password:")
	reader := bufio.NewReader(os.Stdin)
	password, err := reader.ReadString('\n')
	fmt.Println(password)

	if err != nil {
		log.Fatalf("Failed to read passphrase: %v", err)
	}
	if createPassword {
		// confirm, err := console.Stdin.PromptPassword("Repeat passphrase: ")
		reader := bufio.NewReader(os.Stdin)
		fmt.Print("Please repeat:")
		confirm, err := reader.ReadString('\n')
		fmt.Println(confirm)

		if err != nil {
			log.Fatalf("Failed to read passphrase confirmation: %v", err)
		}
		if password != confirm {
			log.Fatalf("Passphrases do not match")
		}
	}
	return password
}

func ReadPassword(prompt string) (string, error) {
	fmt.Print(prompt)
	// password, _ := terminal.ReadPassword(syscall.Stdin)
	// fmt.Print("SSS:", password)
	// return string(password), nil

	// reader := bufio.NewReader(os.Stdin)
	// password, err := reader.ReadString('\n')
	// if err != nil {
	// 	log.Fatalf("Failed to read password: %v", err)
	// 	return "", err
	// }
	// fmt.Print("SSS:", password)
	// return password, nil
	var input string
	fmt.Scanf("%s", &input)
	fmt.Println("*************88input:", input)
	return input, nil
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
