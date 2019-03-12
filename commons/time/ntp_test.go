package times

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestNetworkTime(t *testing.T) {
	networkTime, err := NetworkTime(ntpServerList)
	fmt.Println(networkTime)
	assert.Nil(t, err)
	assert.NotNil(t, networkTime)
}

func TestInvalidSystemClock(t *testing.T) {
	err := InvalidSystemClock()
	assert.Nil(t, err)
}
