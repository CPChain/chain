package rnode

import (
	"bitbucket.org/cpchain/chain/accounts/abi/bind"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/contracts/dpor/rnode"
	"github.com/ethereum/go-ethereum/common"
)

type RNodeService interface {
	GetRNodes() ([]common.Address, error)
}

type RNodeServiceImpl struct {
	client   bind.ContractBackend
	contract common.Address
}

// NewRNodeService creates an instance to read rNodes from contract
func NewRNodeService(rNodeContract common.Address, backend bind.ContractBackend) (RNodeService, error) {

	rs := &RNodeServiceImpl{
		contract: rNodeContract,
		client:   backend,
	}
	return rs, nil
}

// GetRNodes implements RNodeService.GetRNodes
func (rs *RNodeServiceImpl) GetRNodes() ([]common.Address, error) {

	instance, err := rnode.NewRnode(rs.contract, rs.client)
	if err != nil {
		log.Debug("error when create rNode instance", "err", err)
		return []common.Address{}, err
	}

	rNodes, err := instance.GetRnodes(nil)
	if err != nil {
		log.Debug("error when read rNodes from rNode contract", "err", err)
		return []common.Address{}, err
	}

	log.Debug("now read rNodes from rNode contract", "len", len(rNodes), "contract addr", rs.contract.Hex())
	return rNodes, nil
}
