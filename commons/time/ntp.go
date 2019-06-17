package times

import (
	"errors"
	"math"
	"os"
	"time"

	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/beevik/ntp"
)

var (
	InvalidSystemClockErr    = errors.New("invalid system clock,exceed max gap")
	NtpServerNotAvailableErr = errors.New("ntp server not available")
	MaxGapDuration           = 10.0 // seconds

	ntpServerList = []string{
		"time.windows.com",
		"0.pool.ntp.org",
		"1.pool.ntp.org",
		"2.pool.ntp.org",
		"3.pool.ntp.org",
	}
)

func NetworkTime(ntpServer []string) (time.Time, error) {
	for _, ntpServer := range ntpServer {
		time, err := ntp.Time(ntpServer)
		if err == nil {
			return time, err
		}
	}
	return time.Now(), NtpServerNotAvailableErr
}

func InvalidSystemClock() error {
	if os.Getenv("IGNORE_NTP_CHECK") != "" {
		log.Debug("IGNORE NTP CHECK")
		return nil
	}

	networkTime, err := NetworkTime(ntpServerList)
	if err != nil {
		// if ntp server not available,do nothing just print warning message.
		log.Warn("ntp server not available, check your network please.", "err", err)
		return err
	}

	now := time.Now()
	dur := now.Sub(networkTime)
	log.Debug("InvalidSystemClock", "now", now, "networkTime", networkTime, "duration(s)", dur.Seconds())

	if math.Abs(dur.Seconds()) > MaxGapDuration {
		log.Debug("duration exceed max gap", "seconds", dur.Seconds())
		return InvalidSystemClockErr
	}
	return nil
}
