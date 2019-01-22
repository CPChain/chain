package chainmetrics

import (
	"net"

	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/prometheus/client_golang/prometheus"
	"github.com/prometheus/client_golang/prometheus/push"
)

var (
	// gauge items
	blockNumberCounter = prometheus.NewGauge(prometheus.GaugeOpts{Name: "cpchain_block_number",
		Help: "current blockNumber."})
)

// configuration items
var (
	chainId        = ""
	gatewayAddress = ""
)

func InitMetrics(port, gatewayURL string) {
	ips := getIP()
	log.Debug("InitMetrics", "ips", ips)
	if len(ips) > 0 {
		chainId = ips[0] + ":" + port
	}
	gatewayAddress = gatewayURL
	log.Debug("InitMetrics", "chainId", chainId, "gatewayAddress", gatewayAddress)
}

func NeedMetrics() bool {
	return gatewayAddress != ""
}
func ReportBlockNumberGauge(exportedJob string, blockNumber float64) {
	log.Debug("currentBlockNumber", blockNumber)
	blockNumberCounter.Set(blockNumber)
	reportGauge(gatewayAddress, exportedJob, chainId, blockNumberCounter)
}

func reportGauge(monitorURL, exportedJob, host string, gauge prometheus.Gauge) {
	if err := push.New(monitorURL, exportedJob).
		Collector(gauge).
		Grouping("host", host).
		Push(); err != nil {
		log.Error("Could not push blockNumber to Pushgateway.", "error", err)
	}
}

func getIP() []string {
	ips := []string{}
	addresses, err := net.InterfaceAddrs()
	if err != nil {
		log.Error(err.Error())
	}
	for _, address := range addresses {
		if ip, ok := address.(*net.IPNet); ok && !ip.IP.IsLoopback() {
			if ip.IP.To4() != nil {
				ips = append(ips, ip.IP.String())
			}
		}
	}
	return ips
}
