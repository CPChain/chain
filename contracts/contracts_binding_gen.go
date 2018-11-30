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

//go:generate abigen --sol ./dpor/contracts/proposer_register.sol --pkg dpor --out ./dpor/contracts/proposer_register.go

//go:generate abigen --sol ./dpor/contracts/rpt.sol --pkg dpor --out ./dpor/contracts/rpt.go

//go:generate abigen --sol ./pdash/sol/pdash.sol --pkg pdash --out ./pdash/sol/pdash.go

//go:generate abigen --sol ./pdash/sol/register.sol --pkg sol --out ./pdash/sol/register.go

//go:generate abigen --sol ./proxy/proxy_contract/proxy.sol --pkg contract --out ./proxy/proxy_contract/proxy.go
