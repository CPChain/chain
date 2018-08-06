// Copyright 2014 The go-ethereum Authors
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

package dpor

import (
	"io"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rlp"
)

type BlockSignature struct {
	Address   common.Address
	Signature string
}

// BlockSignatureInfo blocknumber -> []BlockSignature, store map[signerAddress][signature]
type BlockSignatureInfo struct {
	BlockNumber     uint64
	BlockSignatures []BlockSignature
}

// DporContext is Dpor context info
type DporContext struct {
	Name          string
	Committees    []common.Address
	SignatureInfo BlockSignatureInfo
	CandidateList []common.Address
}

type dporStorageContext struct {
	Name          string
	Committees    []common.Address
	SignatureInfo BlockSignatureInfo
	CandidateList []common.Address
}

// EncodeRLP writes x as RLP list [a, b] that omits the Name field.
func (c *DporContext) EncodeRLP(w io.Writer) (err error) {
	// Note: the receiver can be a nil pointer. This allows you to
	// control the encoding of nil, but it also means that you have to
	// check for a nil receiver.
	if c == nil {
		return rlp.Encode(w, dporStorageContext{})
	} else {
		return rlp.Encode(
			w, dporStorageContext{
				Name:          c.Name,
				Committees:    c.Committees,
				SignatureInfo: c.SignatureInfo,
				CandidateList: c.CandidateList,
			})
	}
}

// DecodeRLP implements Decoder.
func (c *DporContext) DecodeRLP(s *rlp.Stream) error {
	var context dporStorageContext
	err := s.Decode(&context)
	if err == nil {
		// read CandidateList from globalContext
		//cl := []common.Address{}
		*c = DporContext(context)
	}
	return err
}
