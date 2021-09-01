package tools

import (
	"fmt"

	"bitbucket.org/cpchain/chain/tools/contract-admin/flags"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/urfave/cli"
)

var GeneralFlags = []cli.Flag{
	cli.StringFlag{
		Name:  "owner",
		Usage: "owner of the contract",
	},
	cli.Int64Flag{
		Name:  "nonce",
		Usage: "Specify nonce",
	},
}

var (
	ToolsCommand = cli.Command{
		Name:  "tools",
		Usage: "Tools",
		Description: `
		Tools
		`,
		Flags: flags.GeneralFlags,
		Subcommands: []cli.Command{
			{
				Name:        "gen-address",
				Usage:       "gen-address --owner <address> --nonce 0",
				Action:      genAddress,
				Flags:       GeneralFlags,
				Description: `generate the address of contract when specify the owner`,
			},
		},
	}
)

func genAddress(ctx *cli.Context) error {
	owner := ctx.String("owner")
	nonce := ctx.Int64("nonce")

	admin := common.HexToAddress(owner)
	c := crypto.CreateAddress(admin, uint64(nonce))
	fmt.Println(c.Hex())
	return nil
}
