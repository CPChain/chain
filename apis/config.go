package gapis

type ServerConfig struct {
	endpoint         string
	useTLS           bool
	RequireandVerify bool
}

type ClientConfig struct {
	endpoint string
	useTLS   bool
}

var DefaultClientConfig = &ClientConfig{
	endpoint: "localhost:8080",
}

var DefaultServerConfig = &ServerConfig{
	endpoint: "localhost:8080",
}
