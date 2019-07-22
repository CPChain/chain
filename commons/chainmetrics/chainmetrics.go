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

	txsNumberCounter = prometheus.NewGauge(prometheus.GaugeOpts{Name: "cpchain_txs_number",
		Help: "current txsNumber."})

	insertionElapsedTime = prometheus.NewGauge(prometheus.GaugeOpts{Name: "cpchain_insertion_elapsed_time",
		Help: "current insertion elapsed time."})
)

// configuration items
var (
	host           = ""
	gatewayAddress = ""
)

func InitPushMetrics(port, gatewayURL string) {
	ips := getIP()
	log.Debug("InitPushMetrics", "ips", ips)
	if len(ips) > 0 {
		host = ips[0] + ":" + port
	}
	gatewayAddress = gatewayURL
	log.Debug("InitPushMetrics", "host", host, "gatewayAddress", gatewayAddress)
}

func NeedPushMetrics() bool {
	return gatewayAddress != ""
}

func UpdateBlockNumberGauge(blockNumber float64) {
	blockNumberCounter.Set(blockNumber)
}

func UpdateTxsNumberGauge(txsNumber float64) {
	txsNumberCounter.Set(txsNumber)
}

func UpdateInsertionElapsedTime(elapsed float64) {
	insertionElapsedTime.Set(elapsed)
}

func ReportBlockNumberGauge(exportedJob string) {
	reportGauge(gatewayAddress, exportedJob, host, blockNumberCounter)
}

func ReportTxsNumberGauge(exportedJob string) {
	reportGauge(gatewayAddress, exportedJob, host, txsNumberCounter)
}

func ReportInsertionElapsedTime(exportedJob string) {
	reportGauge(gatewayAddress, exportedJob, host, insertionElapsedTime)
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
