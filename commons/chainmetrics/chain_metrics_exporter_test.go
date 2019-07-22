package chainmetrics

import (
	"testing"
)

func TestMetrics(t *testing.T) {
	t.Skip("skip http service")
	InitExposeMetrics(":9100")
	StartExposeMetrics()
}
