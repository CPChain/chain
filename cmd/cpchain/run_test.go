package main

import (
	"fmt"
	"io/ioutil"
	"os"
	"testing"

	"bitbucket.org/cpchain/chain/internal/cmdtest"
	"github.com/docker/docker/pkg/reexec"
	"github.com/urfave/cli"
)

func tmpdir(t *testing.T) string {
	dir, err := ioutil.TempDir("", "cpchain-test")
	if err != nil {
		t.Fatal(err)
	}
	return dir
}

type testcpchain struct {
	*cmdtest.TestCmd

	// template variables for expect
	Datadir   string
	Etherbase string
}

func init() {
	app := cli.NewApp()
	// Run the app if we've been exec'd as "cpchain-test" in runCpchain.
	reexec.Register("cpchain-test", func() {
		if err := app.Run(os.Args); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		os.Exit(0)
	})
}

func TestMain(m *testing.M) {
	// check if we have been reexec'd
	if reexec.Init() {
		return
	}
	os.Exit(m.Run())
}

// spawns cpchain with the given command line args. If the args don't set --datadir, the
// child g gets a temporary data directory.
func runCpchain(t *testing.T, args ...string) *testcpchain {
	tt := &testcpchain{}
	tt.TestCmd = cmdtest.NewTestCmd(t, tt)
	for i, arg := range args {
		switch {
		case arg == "-datadir" || arg == "--datadir":
			if i < len(args)-1 {
				tt.Datadir = args[i+1]
			}
		case arg == "-etherbase" || arg == "--etherbase":
			if i < len(args)-1 {
				tt.Etherbase = args[i+1]
			}
		}
	}
	if tt.Datadir == "" {
		tt.Datadir = tmpdir(t)
		tt.Cleanup = func() { os.RemoveAll(tt.Datadir) }
		args = append([]string{"-datadir", tt.Datadir}, args...)
		// Remove the temporary datadir if something fails below.
		defer func() {
			if t.Failed() {
				tt.Cleanup()
			}
		}()
	}

	// Boot "cpchain". This actually runs the test binary but the TestMain
	// function will prevent any tests from running.
	tt.Log("args:", args[0])
	tt.Run("cpchain-test", args...)

	return tt
}
