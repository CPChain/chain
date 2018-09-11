package private

const DefaultIpfsUrl = "localhost:5001"

type Config struct {
	IpfsURL string
}

func DefaultConfig() Config {
	return Config{
		IpfsURL: DefaultIpfsUrl,
	}
}
