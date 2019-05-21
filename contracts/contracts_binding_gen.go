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

package contracts

//go:generate abigen --sol ./dpor/contracts/admission/admission.sol --pkg admission --out ./dpor/contracts/admission/admission.go

//go:generate abigen --sol ./dpor/contracts/campaign/campaign.sol --pkg campaign --out ./dpor/contracts/campaign/campaign.go

//go:generate abigen --sol ./dpor/contracts/primitives/primitive_contracts.sol --pkg primitives --out ./dpor/contracts/primitives/primitive_contracts.go

//go:generate abigen --sol ./dpor/contracts/primitives/primitive_contracts_test.sol --pkg primitives_test --out ./dpor/contracts/primitives/primitive_contracts_test.go

//go:generate abigen --sol ./dpor/contracts/proposer_register/proposer_register.sol --pkg proposer_register --out ./dpor/contracts/proposer_register/proposer_register.go

//go:generate abigen --sol ./dpor/contracts/rpt/rpt.sol --pkg contracts --out ./dpor/contracts/rpt/rpt.go

//go:generate abigen --sol ./dpor/contracts/reward/reward.sol --pkg reward --out ./dpor/contracts/reward/reward.go

//go:generate abigen --sol ./pdash/pdash_contract/pdash.sol --pkg pdash_contract --out ./pdash/pdash_contract/pdash.go

//go:generate abigen --sol ./pdash/pdash_contract/pdash_proxy.sol --pkg pdash_contract --out ./pdash/pdash_contract/pdash_proxy.go

//go:generate abigen --sol ./pdash/pdash_contract/register.sol --pkg pdash_contract --out ./pdash/pdash_contract/register.go

//go:generate abigen --sol ./proxy/proxy_contract/proxy.sol --pkg contract --out ./proxy/proxy_contract/proxy.go

//go:generate abigen --sol ./proxy/proxy_contract/proxy_contract_register.sol --pkg contract --out ./proxy/proxy_contract/proxy_contract_register.go

//go:generate abigen --sol ./dpor/contracts/campaign2/campaign2.sol --pkg campaign --out ./dpor/contracts/campaign2/campaign2.go

//go:generate abigen --sol ./dpor/contracts/rnode/rnode.sol --pkg rnode --out ./dpor/contracts/rnode/rnode.go

//go:generate abigen --sol ./dpor/contracts/campaign3/campaign3.sol --pkg campaign --out ./dpor/contracts/campaign3/campaign3.go


