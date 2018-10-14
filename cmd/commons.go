package main

import (
	"bytes"
	"fmt"
	"io"
	"os"
	"runtime"
	"syscall"

	"bitbucket.org/cpchain/chain/node"
	"github.com/urfave/cli"
	"golang.org/x/crypto/ssh/terminal"
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

func readPassword(prompt string, needConfirm bool) string {
	// be cautious about whitespace
	fmt.Println("If your password contains whitespaces, please be careful enough to avoid later confusion.")
	fmt.Print(prompt)
	password, err := terminal.ReadPassword(syscall.Stdin)
	fmt.Println()
	if err != nil {
		Fatalf("Failed to read password: %v", err)
	}
	if needConfirm {
		fmt.Print("Please repeat:")
		p, err := terminal.ReadPassword(syscall.Stdin)
		fmt.Println()
		if err != nil {
			Fatalf("Failed to read password: %v", err)
		}

		if !bytes.Equal(password, p) {
			Fatalf("Password doesn't match")
		}
	}
	// trailing newline is ignored
	return string(password)
}

func registerService() {

}

func createNode(ctx *cli.Context) *node.Node {
	cfg := getConfig(ctx)

	n, err := node.New(&cfg.Node)
	if err != nil {
		Fatalf("Node creation failed: %v", err)
	}
	// TODO
	// registerService()
	return n
}
