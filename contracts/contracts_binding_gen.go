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

//go:generate abigen --sol ./dpor/admission/admission.sol --pkg admission --out ./dpor/admission/admission.go

//go:generate abigen --sol ./dpor/campaign/campaign.sol --pkg campaign --out ./dpor/campaign/campaign.go

//go:generate abigen --sol ./dpor/primitives/primitive_contracts.sol --pkg primitives --out ./dpor/primitives/primitive_contracts.go

//go:generate abigen --sol ./dpor/primitives/primitive_contracts_test.sol --pkg primitives_test --out ./dpor/primitives/primitive_contracts_test.go

//go:generate abigen --sol ./dpor/rpt/rpt.sol --pkg contracts --out ./dpor/rpt/rpt.go

//go:generate abigen --sol ./dpor/campaign2/campaign2.sol --pkg campaign --out ./dpor/campaign2/campaign2.go

//go:generate abigen --sol ./dpor/rnode/rnode.sol --pkg rnode --out ./dpor/rnode/rnode.go

//go:generate abigen --sol ./dpor/rnode2/rnode.sol --pkg rnode --out ./dpor/rnode2/rnode.go

//go:generate abigen --sol ./dpor/campaign3/campaign3.sol --pkg campaign --out ./dpor/campaign3/campaign3.go

//go:generate abigen --sol ./pdash/pdash_contract/pdash.sol --pkg pdash_contract --out ./pdash/pdash_contract/pdash.go

//go:generate abigen --sol ./pdash/pdash_contract/pdash_proxy.sol --pkg pdash_contract --out ./pdash/pdash_contract/pdash_proxy.go

//go:generate abigen --sol ./pdash/pdash_contract/register.sol --pkg pdash_contract --out ./pdash/pdash_contract/register.go

//go:generate abigen --sol ./proxy/proxy_contract/proxy.sol --pkg contract --out ./proxy/proxy_contract/proxy.go

//go:generate abigen --sol ./proxy/proxy_contract/proxy_contract_register.sol --pkg contract --out ./proxy/proxy_contract/proxy_contract_register.go

//go:generate abigen --sol ./reward/reward.sol --pkg reward --out ./reward/reward.go

//go:generate abigen --sol ./reward2/reward.sol --pkg reward --out ./reward2/reward.go



