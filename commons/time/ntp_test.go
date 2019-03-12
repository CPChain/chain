package times

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestNetworkTime1(t *testing.T) {
	networkTime, err := NetworkTime([]string{
		"3.pool.ntp.org",
	})
	fmt.Println(networkTime)
	assert.Nil(t, err)
	assert.NotNil(t, networkTime)
}

func TestNetworkTime2(t *testing.T) {
	networkTime, err := NetworkTime(ntpServerList)
	fmt.Println(networkTime)
	assert.Nil(t, err)
	assert.NotNil(t, networkTime)
}

func TestInvalidSystemClock(t *testing.T) {
	err := InvalidSystemClock()
	assert.Nil(t, err)
}
