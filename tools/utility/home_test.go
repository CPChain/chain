package utility

import "testing"

func TestHome(t *testing.T) {
	home, err := Home()
	if err != nil {
		t.Error(err)
	}
	t.Log(home)
}
