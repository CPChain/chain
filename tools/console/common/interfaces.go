package common

// Output data
type Output interface {
	Status(status *Status)
	Balance(balance Balance)
	Info(info string)
	Error(err string)
	Fatal(fatal string)
	Warn(warn string)
}

// Manager manage the cpchain node
type Manager interface {
	GetStatus() (*Status, error)
	StartMining() error
	StopMining() error
	Balance() (Balance, error)
	BalanceOnReward() (RewardBalance, error)
	Withdraw() error
	SubmitDeposit() error
	WantRenew() error
	QuitRenew() error
}

// Balance of the cpchain node
type Balance struct {
}

// Status is the status of cpchain ndoe
type Status struct {
	Mining     bool
	RNode      bool
	ENode      bool
	Proposer   bool
	NextNumber bool
}

// RewardBalance is balance of contract namded reward
type RewardBalance struct {
}
