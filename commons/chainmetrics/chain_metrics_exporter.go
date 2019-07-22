package chainmetrics

import (
	"flag"
	"net/http"

	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/prometheus/client_golang/prometheus"
	"github.com/prometheus/client_golang/prometheus/promhttp"
)

var (
	_exposeMetricsAddress = ""
)

func InitExposeMetrics(exposeMetricsAddress string) {
	log.Debug("exposeMetricsAddress", "exposeMetricsAddress", exposeMetricsAddress)
	_exposeMetricsAddress = exposeMetricsAddress
}

func init() {
	prometheus.MustRegister(blockNumberCounter)
}

func NeedExposeMetrics() bool {
	return _exposeMetricsAddress != ""
}

func StartExposeMetrics() {
	flag.Parse()
	log.Info("StartExposeMetrics", "addr", _exposeMetricsAddress)
	// Expose the registered metrics via HTTP.
	http.Handle("/metrics", promhttp.Handler())
	if err := http.ListenAndServe(_exposeMetricsAddress, nil); err != nil {
		log.Fatal("StartExposeMetrics service failed", "err", err)
	}
}
