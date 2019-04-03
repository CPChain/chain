package backend

import (
	"hash/fnv"

	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/consensus"
	"bitbucket.org/cpchain/chain/types"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/p2p"
	lru "github.com/hashicorp/golang-lru"
)

// handleLBFTMsg handles given msg with lbft (lightweighted bft) mode
func (vh *Handler) handleLBFTMsg(msg p2p.Msg, p *RemoteSigner) error {
	if vh.lbft == nil {
		vh.lbft = NewLBFT(vh)
	}

	return vh.lbft.Handle(msg, p)
}

func logMsgReceived(number uint64, hash common.Hash, msgCode MsgCode, p *RemoteSigner) {
	log.Debug("received msg", "number", number, "hash", hash.Hex(), "msg code", msgCode.String(), "remote peer", func() string {
		if p != nil {
			return p.Coinbase().Hex()
		}
		return "nil peer"
	}())
}

func (vh *Handler) handleSignerConnectionMsg(version int, p *p2p.Peer, rw p2p.MsgReadWriter, msg p2p.Msg) (string, error) {
	switch msg.Code {
	case NewSignerMsg:

		log.Debug("received new signer msg from", "peer.RemoteAddress", p.RemoteAddr().String())

		var signerStatus SignerStatusData
		address, err := ReadSignerStatus(msg, &signerStatus)
		if err != nil {
			return common.Address{}.Hex(), err
		}

		blk := vh.dpor.GetCurrentBlock()
		if blk == nil {
			return "", errNilBlock
		}

		var (
			currectNumber = blk.NumberU64()
			term          = vh.dpor.TermOf(currectNumber)
			futureTerm    = vh.dpor.FutureTermOf(currectNumber)
		)

		// if current or future proposer, add to local peer set
		if vh.dialer.isCurrentOrFutureProposer(address, term, futureTerm) {
			vh.dialer.addRemoteProposer(version, p, rw, address)
			log.Debug("added the signer as a proposer", "address", address.Hex(), "peer.RemoteAddress", p.RemoteAddr().String())
		}

		// if current or future validator, add to local peer set
		if vh.dialer.isCurrentOrFutureValidator(address, term, futureTerm) {
			vh.dialer.addRemoteValidator(version, p, rw, address)
			log.Debug("added the signer as a validator", "address", address.Hex(), "peer.RemoteAddress", p.RemoteAddr().String())
		}

		return address.Hex(), nil

	default:
		log.Warn("unknown msg code when handling signer connection msg", "msg", msg.Code)
	}
	return common.Address{}.Hex(), nil
}

func (vh *Handler) handleLBFT2Msg(msg p2p.Msg, p *RemoteSigner) error {

	var (
		input         = &BlockOrHeader{}
		inputMsgCode  = NoMsgCode
		currentNumber = uint64(0)
	)

	currentBlock := vh.dpor.GetCurrentBlock()
	if currentBlock == nil {
		log.Warn("current block is nil")
		return nil
	}
	currentNumber = currentBlock.NumberU64()

	switch msg.Code {
	case PreprepareBlockMsg:
		// recover the block from msg
		block, err := RecoverBlockFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input = &BlockOrHeader{
			block: block,
		}
		inputMsgCode = PreprepareMsgCode

	case PrepareHeaderMsg:
		// recover the header from msg
		header, err := RecoverHeaderFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input = &BlockOrHeader{
			header: header,
		}
		inputMsgCode = PrepareMsgCode

	case CommitHeaderMsg:
		// recover the header from msg
		header, err := RecoverHeaderFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input = &BlockOrHeader{
			header: header,
		}
		inputMsgCode = CommitMsgCode

	case ValidateBlockMsg:
		// recover the block from msg
		block, err := RecoverBlockFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input = &BlockOrHeader{
			block: block,
		}
		inputMsgCode = ValidateMsgCode

	case PreprepareImpeachBlockMsg:
		// recover the block from msg
		block, err := RecoverBlockFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input = &BlockOrHeader{
			block: block,
		}
		inputMsgCode = ImpeachPreprepareMsgCode

	case PrepareImpeachHeaderMsg:
		// recover the header from msg
		header, err := RecoverHeaderFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input = &BlockOrHeader{
			header: header,
		}
		inputMsgCode = ImpeachPrepareMsgCode

	case CommitImpeachHeaderMsg:
		// recover the header from msg
		header, err := RecoverHeaderFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input = &BlockOrHeader{
			header: header,
		}
		inputMsgCode = ImpeachCommitMsgCode

	case ValidateImpeachBlockMsg:
		// recover the block from msg
		block, err := RecoverBlockFromMsg(msg, p)
		if err != nil {
			return err
		}

		// prepare input and msg code for the fsm
		input = &BlockOrHeader{
			block: block,
		}
		inputMsgCode = ImpeachValidateMsgCode

	default:
		log.Warn("unknown msg code", "msg", msg.Code)
	}

	// log output received msg
	logMsgReceived(input.Number(), input.Hash(), inputMsgCode, p)

	// if number is larger than local current number, sync from remote peer
	if input.Number() > currentNumber+1 && p != nil {
		go vh.dpor.SyncFrom(p.Peer)
		log.Debug("I am slow, syncing with peer", "peer", p.address.Hex())
	}

	// if number is equal or less than current number, drop the msg
	if input.Number() < currentNumber {
		log.Debug("received outdated msg, discarding...")
		return nil
	}

	// this is just for debug
	switch inputMsgCode {
	// if received a impeach validate msg, log out some debug infos
	case ImpeachValidateMsgCode:

		log.Debug("-----------------------------")
		log.Debug("now received an ImpeachValidateMsg", "number", input.Number(), "hash", input.Hash().Hex())

		correctProposer, err := vh.dpor.ProposerOf(input.Number())
		if err != nil {
			log.Debug("err when get proposer of number", "err", err, "number", input.Number())
		}

		correctProposerPeer, exist := vh.dialer.getProposer(correctProposer.Hex())
		if !exist || correctProposerPeer == nil {
			log.Debug("proposer for the block is not in local proposer peer set")
			log.Debug("for this block number, the correct proposer should be", "addr", correctProposer.Hex())
		} else {
			log.Debug("for this block number, the correct proposer should be", "addr", correctProposer.Hex(), "ip:port", correctProposerPeer.Peer.RemoteAddr())
		}

		log.Debug("-----------------------------")
	}

	// if the msg is PreprepareImpeachBlockMsg, or msg code is ImpeachPreprepareMsgCode, the sender must be nil(self)
	switch inputMsgCode {
	case ImpeachPreprepareMsgCode:
		if p != nil {
			// invalid impeach preprepare msg sender!
			return nil
		}
	}

	// call fsm
	output, action, outputMsgCode, err := vh.fsm.FSM(input, inputMsgCode)
	switch err {
	case nil:
		// rebroadcast the preprepare msg
		switch inputMsgCode {
		case PreprepareMsgCode:
			go vh.reBroadcast(input, outputMsgCode)
		}

	case consensus.ErrUnknownAncestor:
		log.Debug("added block to unknown ancestor cache", "number", input.Number(), "hash", input.Hash().Hex())

		vh.unknownAncestorBlocks.AddBlock(input.block)
		return nil

	default:
		log.Error("received an error when run fsm", "err", err)

		return nil
	}

	// handle fsm result
	switch output {
	case nil:
		// nil output, do nothing

	default:
		switch action {
		case BroadcastMsgAction:

			switch outputMsgCode {
			case PrepareMsgCode:
				go vh.BroadcastPrepareHeader(output[0].header)

			case CommitMsgCode:
				go vh.BroadcastCommitHeader(output[0].header)

			case PrepareAndCommitMsgCode:
				go vh.BroadcastPrepareHeader(output[0].header)
				go vh.BroadcastCommitHeader(output[1].header)

			case ValidateMsgCode:
				go vh.BroadcastValidateBlock(output[0].block)

			case ImpeachPrepareMsgCode:
				go vh.BroadcastPrepareImpeachHeader(output[0].header)

			case ImpeachCommitMsgCode:
				go vh.BroadcastCommitImpeachHeader(output[0].header)

			case ImpeachPrepareAndCommitMsgCode:
				go vh.BroadcastPrepareImpeachHeader(output[0].header)
				go vh.BroadcastCommitImpeachHeader(output[1].header)

			case ImpeachValidateMsgCode:
				go vh.BroadcastValidateImpeachBlock(output[0].block)

			// unknown msg code
			default:
				log.Debug("unknown msg code for fsm output", "msgCode", outputMsgCode)
			}

		// other actions
		default:
			log.Debug("unknown action code for fsm output", "action", action)
		}

	}

	return nil
}

// ReceiveImpeachPendingBlock receives a block to add to pending block channel
func (vh *Handler) ReceiveImpeachPendingBlock(block *types.Block) error {
	select {
	case vh.pendingImpeachBlockCh <- block:
		err := vh.knownBlocks.AddBlock(block)
		if err != nil {
			return err
		}

		return nil
	}
}

type msgID struct {
	blockID BlockIdentifier
	msgCode MsgCode
	msgHash common.Hash
}

func newMsgID(number uint64, hash common.Hash, msgCode MsgCode, signatures []types.DporSignature) msgID {

	var payload []byte
	for _, s := range signatures {
		payload = append(payload, s[:]...)
	}

	msgHash := fnv.New32a()
	msgHash.Write(payload)

	return msgID{
		blockID: BlockIdentifier{number: number, hash: hash},
		msgCode: msgCode,
		msgHash: common.BytesToHash(msgHash.Sum(nil)),
	}
}

type broadcastRecord struct {
	record *lru.ARCCache
}

func newBroadcastRecord() *broadcastRecord {
	record, _ := lru.NewARC(1000)
	return &broadcastRecord{
		record: record,
	}
}

func (br *broadcastRecord) markAsBroadcasted(number uint64, hash common.Hash, msgCode MsgCode, signatures []types.DporSignature) {
	msgID := newMsgID(number, hash, msgCode, signatures)
	br.record.Add(msgID, true)
}

func (br *broadcastRecord) ifBroadcasted(number uint64, hash common.Hash, msgCode MsgCode, signatures []types.DporSignature) bool {
	msgID := newMsgID(number, hash, msgCode, signatures)
	broadcasted, exists := br.record.Get(msgID)
	return exists && broadcasted.(bool) == true
}

type impeachmentRecord struct {
	record *lru.ARCCache
}

func newImpeachmentRecord() *impeachmentRecord {
	record, _ := lru.NewARC(1000)
	return &impeachmentRecord{
		record: record,
	}
}

func (ir *impeachmentRecord) markAsImpeached(number uint64, hash common.Hash) {
	bi := NewBlockIdentifier(number, hash)
	ir.record.Add(bi, true)
}

func (ir *impeachmentRecord) ifImpeached(number uint64, hash common.Hash) bool {
	bi := NewBlockIdentifier(number, hash)
	impeached, exists := ir.record.Get(bi)
	return exists && impeached.(bool) == true
}

func (vh *Handler) reBroadcast(input *BlockOrHeader, msgCode MsgCode) {
	var signatures []types.DporSignature

	if input.IsBlock() {
		signatures = input.block.Dpor().Sigs
	} else if input.IsHeader() {
		signatures = input.header.Dpor.Sigs
	} else {
		return
	}

	if !vh.broadcastRecord.ifBroadcasted(input.Number(), input.Hash(), msgCode, signatures) {
		switch msgCode {
		case PreprepareMsgCode:
			vh.BroadcastPreprepareBlock(input.block)
		case PrepareMsgCode:
			vh.BroadcastPrepareHeader(input.header)
		case CommitMsgCode:
			vh.BroadcastCommitHeader(input.header)
		case ValidateMsgCode:
			vh.BroadcastValidateBlock(input.block)
		case ImpeachPreprepareMsgCode:
			vh.BroadcastPreprepareImpeachBlock(input.block)
		case ImpeachPrepareMsgCode:
			vh.BroadcastPrepareImpeachHeader(input.header)
		case ImpeachCommitMsgCode:
			vh.BroadcastCommitImpeachHeader(input.header)
		case ImpeachValidateMsgCode:
			vh.BroadcastValidateImpeachBlock(input.block)
		default:
		}
		vh.broadcastRecord.markAsBroadcasted(input.Number(), input.Hash(), msgCode, signatures)
	}
}
