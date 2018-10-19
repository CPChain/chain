package main

import (
	"fmt"

	"bitbucket.org/cpchain/chain/accounts"
	"bitbucket.org/cpchain/chain/accounts/keystore"
	"bitbucket.org/cpchain/chain/cmd/cpchain/flags"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/crypto"
	"github.com/ethereum/go-ethereum/common"
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

Keys are stored under <datadir>/keystore.`,
		Subcommands: []cli.Command{
			{
				Name:   "list",
				Usage:  "Print summary of existing accounts",
				Action: accountList,
				Flags: []cli.Flag{
					flags.GetByName("datadir"),
				},
				Description: `Print a short summary of all accounts`,
			},
			{
				Name:   "new",
				Usage:  "Create a new account",
				Action: createAccount,
				Flags: []cli.Flag{
					flags.GetByName("datadir"),
					flags.GetByName("password"),
					flags.GetByName("lightkdf"),
				},
				Description: `Creates a new account and prints the address.
The account is saved in encrypted format, you are prompted for a password.
You must remember this password to unlock your account in the future.`,
			},
			{
				Name:      "update",
				Usage:     "Update an existing account",
				Action:    accountUpdate,
				ArgsUsage: "<address>",
				Flags: []cli.Flag{
					flags.GetByName("datadir"),
					flags.GetByName("lightkdf"),
				},
				Description: `cpchain account update <address>

Update an existing account.

The account is saved in the newest version in encrypted format, you are prompted
for a password to unlock the account and another to save the updated file.
This same command can therefore be used to migrate an account of a deprecated
format to the newest format or change the password for an account.
For non-interactive use the password can be specified with the --password flag:
    cpchain account update [options] <address>
Since only one password can be given, only format update can be performed,
changing your password is only possible interactively.`,
			},
			{
				Name:   "import",
				Usage:  "Import a private key into a new account",
				Action: accountImport,
				Flags: []cli.Flag{
					flags.GetByName("datadir"),
					flags.GetByName("password"),
					flags.GetByName("lightkdf"),
				},
				ArgsUsage: "<keyFile>",
				Description: `cpchain account import <keyfile>

Imports an unencrypted private key from <keyfile> and creates a new account.
Prints the address.
The keyfile is assumed to contain an unencrypted private key in hexadecimal format.
The account is saved in encrypted format, you are prompted for a password.
You must remember this password to unlock your account in the future.
For non-interactive use the password can be specified with the --password flag:
    cpchain account import [options] <keyfile>`,
			},
		},
	}
)

func accountList(ctx *cli.Context) error {
	_, n := newConfigNode(ctx)
	var index int
	for _, wallet := range n.AccountManager().Wallets() {
		for _, account := range wallet.Accounts() {
			fmt.Printf("Account #%d: {%x} %s\n", index, account.Address, &account.URL)
			index++
		}
	}
	return nil
}

// accountCreate creates a new account into the keystore defined by the CLI flags
func createAccount(ctx *cli.Context) error {
	cfg, _ := newConfigNode(ctx)
	scryptN, scryptP, keydir, err := cfg.Node.AccountConfig()
	if err != nil {
		Fatalf("Failed to read configuration: %v", err)
	}
	password, _ := readPassword("If your password contains whitespaces, please be careful enough to avoid later confusion.\nPlease give a password.", true)
	address, err := keystore.StoreKey(keydir, password, scryptN, scryptP)
	if err != nil {
		Fatalf("Failed to create account: %v", err)
	}
	fmt.Printf("Address: {%x}\n", address)
	return nil
}

// accountUpdate transitions an account from a previous format to the current
// one, also providing the possibility to change the password.
func accountUpdate(ctx *cli.Context) error {
	if len(ctx.Args()) == 0 {
		log.Fatalf("No accounts specified to update")
	}
	_, n := newConfigNode(ctx)
	ks := n.AccountManager().Backends(keystore.KeyStoreType)[0].(*keystore.KeyStore)

	for _, addr := range ctx.Args() {
		account, oldPassword := unlockAccountWithPrompt(ks, addr)
		newPassword, _ := readPassword("If your password contains whitespaces, please be careful enough to avoid later confusion.\nPlease give a new password.", true)
		if err := ks.Update(account, oldPassword, newPassword); err != nil {
			Fatalf("Could not update the account: %v", err)
		}
	}
	return nil
}

// MakeAddress converts an account specified directly as a hex encoded string
func makeAddress(ks *keystore.KeyStore, account string) (accounts.Account, error) {
	// If the specified account is a valid address, return it
	if common.IsHexAddress(account) {
		return accounts.Account{Address: common.HexToAddress(account)}, nil
	}
	return accounts.Account{}, fmt.Errorf("invalid account address %q", account)
}

func ambiguousAddrRecovery(ks *keystore.KeyStore, err *keystore.AmbiguousAddrError, auth string) accounts.Account {
	fmt.Printf("Multiple key files exist for address %x:\n", err.Addr)
	for _, a := range err.Matches {
		fmt.Println("  ", a.URL)
	}
	fmt.Println("Testing your password against all of them...")
	var match *accounts.Account
	for _, a := range err.Matches {
		if err := ks.Unlock(a, auth); err == nil {
			match = &a
			break
		}
	}
	if match == nil {
		Fatalf("None of the listed files could be unlocked.")
	}
	fmt.Printf("Your password unlocked %s\n", match.URL)
	fmt.Println("In order to avoid this warning, you need to remove the following duplicate key files:")
	for _, a := range err.Matches {
		if a != *match {
			fmt.Println("  ", a.URL)
		}
	}
	return *match
}

// tries unlocking the specified account a few times.
func unlockAccountWithPrompt(ks *keystore.KeyStore, address string) (accounts.Account, string) {
	account, err := makeAddress(ks, address)
	if err != nil {
		Fatalf("Could not list accounts: %v", err)
	}
	for trials := 0; trials < 3; trials++ {
		prompt := fmt.Sprintf("Unlocking account %s | Attempt %d/%d", address, trials+1, 3)

		password, _ := readPassword(prompt, false)
		err = ks.Unlock(account, password)
		if err == nil {
			log.Info("Unlocked account", "address", account.Address.Hex())
			return account, password
		}
		if err, ok := err.(*keystore.AmbiguousAddrError); ok {
			log.Info("Unlocked account", "address", account.Address.Hex())
			return ambiguousAddrRecovery(ks, err, password), password
		}
		if err != keystore.ErrDecrypt {
			// No need to prompt again if the error is not decryption-related.
			break
		}
	}
	// All trials expended to unlock account, bail out
	Fatalf("Failed to unlock account %s (%v)", address, err)
	return accounts.Account{}, ""
}

// tries unlocking the specified account a few times.
func unlockAccountWithPassword(ks *keystore.KeyStore, address string, password string) accounts.Account {
	account, err := makeAddress(ks, address)
	if err != nil {
		Fatalf("Could not list accounts: %v", err)
	}
	err = ks.Unlock(account, password)
	if err == nil {
		log.Info("Unlocked account", "address", account.Address.Hex())
		return account
	} else if err, ok := err.(*keystore.AmbiguousAddrError); ok {
		log.Info("Unlocked account", "address", account.Address.Hex())
		return ambiguousAddrRecovery(ks, err, password)
	}
	// All trials expended to unlock account, bail out
	log.Warnf("Failed to unlock account %s (%v)", address, err)
	return accounts.Account{}
}

func accountImport(ctx *cli.Context) error {
	keyfile := ctx.Args().First()
	if len(keyfile) == 0 {
		log.Fatalf("keyfile must be given as argument")
	}
	key, err := crypto.LoadECDSA(keyfile)
	if err != nil {
		log.Fatalf("Failed to load the private key: %v", err)
	}

	_, n := newConfigNode(ctx)
	password, err := readPassword("Your new account is locked with a password. Please give a password. Do not forget this password.\nPassword:", true)
	if err != nil {
		log.Fatalf("Failed to readPassword: %v", err)
	}
	ks := n.AccountManager().Backends(keystore.KeyStoreType)[0].(*keystore.KeyStore)
	acct, err := ks.ImportECDSA(key, password)
	if err != nil {
		log.Fatalf("Could not create the account: %v", err)
	}
	fmt.Printf("Address: {%x}\n", acct.Address)
	return nil
}
