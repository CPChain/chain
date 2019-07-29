package campaign

import (
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/campaign"
	"bitbucket.org/cpchain/chain/tools/contract-admin/flags"
	"bitbucket.org/cpchain/chain/tools/contract-admin/utils"
	"github.com/ethereum/go-ethereum/common"
	"github.com/urfave/cli"
)

var (
	CampaignCommand = cli.Command{
		Name:  "campaign",
		Usage: "Manage Campaign Contract",
		Description: `
		Manage Campaign Contract
		`,
		Flags: flags.GeneralFlags,
		Subcommands: []cli.Command{
			{
				Name:        "setadmissionaddr",
				Usage:       "set admission contract address, <address in string>",
				Action:      setAdmissionAddress,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "address",
				Description: `set admission contract address`,
			},
			{
				Name:        "setrnodeaddr",
				Usage:       "set rnode contract address, <address in string>",
				Action:      setRnodeAddress,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "address",
				Description: `set rnode contract address`,
			},
			{
				Name:        "setminnoc",
				Usage:       "set min noc",
				Action:      setMinNoc,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set rnode contract address`,
			},
			{
				Name:        "setmaxnoc",
				Usage:       "set max noc",
				Action:      setMaxNoc,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set rnode contract address`,
			},
			{
				Name:        "setblocks",
				Usage:       "set acceptable blocks",
				Action:      setAcceptableBlocks,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set acceptable blocks`,
			},
			{
				Name:        "setversion",
				Usage:       "set supported version",
				Action:      setVersion,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "int",
				Description: `set supported version`,
			},
			{
				Name:        "showconfigs",
				Usage:       "show configs in contract",
				Action:      showConfigs,
				Flags:       flags.GeneralFlags,
				Description: `show configs in contract`,
			},
			{
				Name:        "showcandidates",
				Usage:       "show candidates in contract in given term range, [start, end]",
				Action:      showCandidates,
				Flags:       flags.GeneralFlags,
				ArgsUsage:   "start, end",
				Description: `show candidates in contract in given term range in contract`,
			},
		},
	}
)

func setAdmissionAddress(ctx *cli.Context) error {
	cmp, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {

		return err
	}
	addr := utils.GetFirstStringArgument(ctx)
	tx, err := cmp.SetAdmissionAddr(opts, common.HexToAddress(addr))
	if err != nil {
		log.Info("Failed to SetAdmissionAddr", "err", err)
		return err
	}
	return utils.WaitMined(client, tx)
}

func setRnodeAddress(ctx *cli.Context) error {
	cmp, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {

		return err
	}
	addr := utils.GetFirstStringArgument(ctx)
	tx, err := cmp.SetRnodeInterface(opts, common.HexToAddress(addr))
	if err != nil {
		log.Info("Failed to SetRnodeInterface", "err", err)
		return err
	}
	return utils.WaitMined(client, tx)
}

func setMinNoc(ctx *cli.Context) error {
	cmp, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {
		return err
	}
	value := utils.GetFirstIntArgument(ctx)
	tx, err := cmp.UpdateMinNoc(opts, big.NewInt(value))
	if err != nil {
		log.Info("Failed to UpdateMinNoc", "err", err)
		return err
	}
	return utils.WaitMined(client, tx)
}

func setMaxNoc(ctx *cli.Context) error {
	cmp, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {

		return err
	}
	value := utils.GetFirstIntArgument(ctx)
	tx, err := cmp.UpdateMaxNoc(opts, big.NewInt(value))
	if err != nil {
		log.Info("Failed to UpdateMaxNoc", "err", err)
		return err
	}
	return utils.WaitMined(client, tx)
}

func setAcceptableBlocks(ctx *cli.Context) error {
	cmp, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {

		return err
	}
	value := utils.GetFirstIntArgument(ctx)
	tx, err := cmp.UpdateAcceptableBlocks(opts, big.NewInt(value))
	if err != nil {
		log.Info("Failed to UpdateAcceptableBlocks", "err", err)
		return err
	}
	return utils.WaitMined(client, tx)
}

func setVersion(ctx *cli.Context) error {
	cmp, opts, client, err := createContractInstanceAndTransactor(ctx, true)
	if err != nil {

		return err
	}
	value := utils.GetFirstIntArgument(ctx)
	tx, err := cmp.UpdateSupportedVersion(opts, big.NewInt(value))
	if err != nil {
		log.Info("Failed to UpdateSupportedVersion", "err", err)
		return err
	}
	return utils.WaitMined(client, tx)
}

func showConfigs(ctx *cli.Context) error {
	cmp, _, _, err := createContractInstanceAndTransactor(ctx, false)
	if err != nil {

		return err
	}
	termIdx, err := cmp.TermIdx(nil)
	if err != nil {
		log.Fatal("Failed to get term index", "err", err)
	}
	log.Info("term index", "value", termIdx.Int64())

	termLen, err := cmp.TermLen(nil)
	if err != nil {
		log.Fatal("Failed to get term len", "err", err)
	}
	log.Info("term len", "value", termLen.Int64())

	viewLen, err := cmp.ViewLen(nil)
	if err != nil {
		log.Fatal("Failed to get view len", "err", err)
	}
	log.Info("view len", "value", viewLen.Int64())

	npm, err := cmp.NumPerRound(nil)
	if err != nil {
		log.Fatal("Failed to get num per round", "err", err)
	}
	log.Info("num per round", "value", npm.Int64())

	minNoc, err := cmp.MinNoc(nil)
	if err != nil {
		log.Fatal("Failed to get min noc", "err", err)
	}
	log.Info("min noc", "value", minNoc.Int64())

	maxNoc, err := cmp.MaxNoc(nil)
	if err != nil {
		log.Fatal("Failed to get max noc", "err", err)
	}
	log.Info("max noc", "value", maxNoc.Int64())

	acceptableBlocks, err := cmp.AcceptableBlocks(nil)
	if err != nil {
		log.Fatal("Failed to get acceptable blocks", "err", err)
	}
	log.Info("acceptable blocks", "value", acceptableBlocks.Int64())

	supportedVersion, err := cmp.SupportedVersion(nil)
	if err != nil {
		log.Fatal("Failed to get supported version", "err", err)
	}
	log.Info("supported version", "value", supportedVersion.Int64())

	return nil
}

func showCandidates(ctx *cli.Context) error {
	cmp, _, _, err := createContractInstanceAndTransactor(ctx, false)
	if err != nil {

		return err
	}
	startTerm, endTerm := utils.GetFirstTwoIntArgument(ctx)

	for i := startTerm; i <= endTerm; i++ {
		candidates, err := cmp.CandidatesOf(nil, big.NewInt(i))

		log.Info("Candidates number of term", "term", i, "len", len(candidates))

		if err != nil {
			log.Info("Failed to get candidates for term", "term", i, "err", err)
			return err
		}

		for _, candidate := range candidates {
			log.Info("Candidate in term", "term", i, "candidate", candidate.Hex())
		}
	}

	return nil
}

func createContractInstanceAndTransactor(ctx *cli.Context, withTransactor bool) (contract *campaign.Campaign, opts *bind.TransactOpts, client *cpclient.Client, err error) {
	contractAddr, client, key, err := utils.PrepareAll(ctx, withTransactor)
	if err != nil {
		return &campaign.Campaign{}, &bind.TransactOpts{}, &cpclient.Client{}, err
	}
	if withTransactor {
		opts = bind.NewKeyedTransactor(key.PrivateKey)
	}
	contract, err = campaign.NewCampaign(contractAddr, client)
	if err != nil {
		log.Info("Failed to create new contract instance", "err", err)
		return &campaign.Campaign{}, &bind.TransactOpts{}, &cpclient.Client{}, err
	}

	return contract, opts, client, nil
}
