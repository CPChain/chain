package common

// Output data
type Output interface {
	Status(status *Status)
	Info(msg string, params ...interface{})
	Error(msg string, params ...interface{})
	Fatal(msg string, params ...interface{})
	Warn(msg string, params ...interface{})
}

// Manager manage the cpchain node
type Manager interface {
	GetStatus() (*Status, error)
	StartMining() error
	StopMining() error
	QuitRnode() error
	JoinRnode() error
}

// Status is the status of cpchain node
type Status struct {
	Mining   bool
	RNode    bool
	Proposer bool
	Locked   bool
}
