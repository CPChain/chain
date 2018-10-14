package main

import (
	"fmt"

	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/cmd/flags"
	"github.com/urfave/cli"
)

var (
	accountCommand = cli.Command{
		Name:  "account",
		Usage: "Manage accounts",
		Description: `Manage accounts, list all existing accounts,
import a private key into a new account, create a new account or update an existing account.
Make sure you remember the password you gave when creating a new account (with
either new or import). Without it you are not able to unlock your account.

Keys are stored under <DATADIR>/keystore.`,
		Subcommands: []cli.Command{
			{
				Name:   "new",
				Usage:  "Create a new account",
				Action: createAccount,
				Flags: []cli.Flag{
					flags.GetByName("datadir"),
				},
				Description: `Creates a new account and prints the address.
The account is saved in encrypted format, you are prompted for a passphrase.
You must remember this passphrase to unlock your account in the future.`,
			},
		},
	}
)

// accountCreate creates a new account into the keystore defined by the CLI flags
func createAccount(ctx *cli.Context) error {
	cfg := getConfig(ctx)
	scryptN, scryptP, keydir, err := cfg.Node.AccountConfig()
	if err != nil {
		Fatalf("Failed to read configuration: %v", err)
	}
	password := readPassword("Please input your password:", true)
	address, err := keystore.StoreKey(keydir, password, scryptN, scryptP)
	if err != nil {
		Fatalf("Failed to create account: %v", err)
	}
	fmt.Printf("Address: {%x}\n", address)
	return nil
}
