// Copyright 2018 The cpchain authors
// This file is part of the cpchain library.
//
// The cpchain library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The cpchain library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the cpchain library. If not, see <http://www.gnu.org/licenses/>.

package campaign

import (
	"math/big"

	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
	"github.com/ethereum/go-ethereum/common"

	// TODO: fix this @liuq
	campaignContract "bitbucket.org/cpchain/chain/contracts/dpor/campaign4"
)

// CandidateService provides methods to obtain all candidates from campaign contract
type CandidateService interface {
	CandidatesOf(term uint64) ([]common.Address, error)
}

// CandidateServiceImpl is the default candidate list collector
type CandidateServiceImpl struct {
	client bind.ContractBackend
}

// NewCandidateService creates a concrete candidate service instance.
func NewCandidateService(backend bind.ContractBackend) (CandidateService, error) {

	rs := &CandidateServiceImpl{
		client: backend,
	}
	return rs, nil
}

// CandidatesOf implements CandidateService
func (rs *CandidateServiceImpl) CandidatesOf(term uint64) ([]common.Address, error) {

	// new campaign contract address
	// TODO: fix this @liuq
	campaignAddr := configs.ChainConfigInfo().Dpor.Contracts[configs.ContractCampaign4]

	// new campaign contract instance
	contractInstance, err := campaignContract.NewCampaign(campaignAddr, rs.client)
	if err != nil {
		log.Debug("error when create campaign 4 instance", "err", err)
		return nil, err
	}

	// candidates from new campaign contract
	cds, err := contractInstance.CandidatesOf(nil, new(big.Int).SetUint64(term))
	if err != nil {
		log.Debug("error when read candidates from campaign 4", "err", err)
		return nil, err
	}

	log.Debug("now read candidates from campaign contract 4", "len", len(cds), "contract addr", campaignAddr.Hex())
	return cds, nil
}
