package main

import (
	"bitbucket.org/cpchain/chain/commons/inpututil"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/eth"
	"bitbucket.org/cpchain/chain/node"
	"fmt"
	"io"
	"os"
	"runtime"
)

// Fatalf formats a message to standard error and exits the program.
// The message is also printed to standard output if standard error
// is redirected to a different file.
func Fatalf(format string, args ...interface{}) {
	w := io.MultiWriter(os.Stdout, os.Stderr)
	if runtime.GOOS == "windows" {
		// The SameFile check below doesn't work on Windows.
		// stdout is unlikely to get redirected though, so just print there.
		w = os.Stdout
	} else {
		outf, _ := os.Stdout.Stat()
		errf, _ := os.Stderr.Stat()
		if outf != nil && errf != nil && os.SameFile(outf, errf) {
			w = os.Stderr
		}
	}
	fmt.Fprintf(w, "Fatal: "+format+"\n", args...)
	os.Exit(1)
}

func readPassword(prompt string, needConfirm bool) (string, error) {
	// prompt the user for the password
	if prompt != "" {
		fmt.Println(prompt)
	}
	password, err := inpututil.Stdin.PromptPassword("Password: ")
	if err != nil {
		Fatalf("Failed to read password: %v", err)
	}
	if needConfirm {
		confirm, err := inpututil.Stdin.PromptPassword("Repeat password: ")
		if err != nil {
			Fatalf("Failed to read password confirmation: %v", err)
		}
		if password != confirm {
			Fatalf("Password do not match")
		}
	}
	return password, nil
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
