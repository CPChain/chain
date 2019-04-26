// Copyright 2017 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package consensus

import (
	"errors"
)

var (
	// ErrUnknownAncestor is returned when validating a block requires an ancestor
	// that is unknown.
	ErrUnknownAncestor = errors.New("unknown ancestor")

	// ErrPrunedAncestor is returned when validating a block requires an ancestor
	// that is known, but the state of which is not available.
	ErrPrunedAncestor = errors.New("pruned ancestor")

	// ErrFutureBlock is returned when a block's timestamp is in the future according
	// to the current node.
	ErrFutureBlock = errors.New("block in the future")

	// ErrInvalidTimestamp is returned when a block's timestamp is larger than parent's
	// timestamp + period + timeout.
	ErrInvalidTimestamp = errors.New("invalid timestamp")

	// ErrInvalidNumber is returned if a block's number doesn't equal it's parent's
	// plus one.
	ErrInvalidNumber = errors.New("invalid block number")

	// ErrNotEnoughSigs is returned if there is not enough signatures for a block.
	ErrNotEnoughSigs = errors.New("not enough signatures in block")

	// ErrUnauthorized is returned if a header is signed by a non-authorized entity.
	ErrUnauthorized = errors.New("unauthorized leader")

	// ErrNotInProposerCommittee is returned  if the account is not in proposer committee.
	ErrNotInProposerCommittee = errors.New("not in proposer committee")

	// ErrUnknownLbftState is returned if committee handler's state is unknown
	ErrUnknownLbftState = errors.New("unknown lbft state")

	// ErrInvalidSigners is returned if a block contains an invalid extra sigers bytes.
	ErrInvalidSigners = errors.New("invalid signer list on checkpoint block")

	// ErrInvalidImpeachCoinbase is returned if an impeach block's coinbase is not 0x00.
	ErrInvalidImpeachCoinbase = errors.New("invalid impeach coinbase")

	// ErrInvalidImpeachTxs is returned if an impeach block contrains txs
	ErrInvalidImpeachTxs = errors.New("invalid impeach txs")

	// ErrorInvalidValidatorsList is returned if the validators list is invalid
	ErrorInvalidValidatorsList = errors.New("invalid validators list")
)
