package contracts

//go:generate abigen --sol ./dpor/contracts/admission/admission.sol --pkg admission --out ./dpor/contracts/admission/admission.go

//go:generate abigen --sol ./dpor/contracts/campaign/campaign.sol --pkg campaign --out ./dpor/contracts/campaign/campaign.go

//go:generate abigen --sol ./dpor/contracts/primitives/primitive_contracts.sol --pkg primitives --out ./dpor/contracts/primitives/primitive_contracts.go

//go:generate abigen --sol ./dpor/contracts/signer_register/signer_register.sol --pkg signerRegister --out ./dpor/contracts/signer_register/signer_register.go

//go:generate abigen --sol ./dpor/contracts/rpt.sol --pkg dpor --out ./dpor/contracts/rpt.go

//go:generate abigen --sol ./pdash/sol/pdash.sol --pkg pdash --out ./pdash/sol/pdash.go

//go:generate abigen --sol ./pdash/sol/register.sol --pkg sol --out ./pdash/sol/register.go

//go:generate abigen --sol ./proxy/proxy_contract/proxy.sol --pkg contract --out ./proxy/proxy_contract/proxy.go
