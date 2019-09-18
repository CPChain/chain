package backend_test

import (
	"fmt"
	"reflect"
	"testing"
	"time"

	"bitbucket.org/cpchain/chain/configs"
	"bitbucket.org/cpchain/chain/consensus/dpor/backend"
	"github.com/ethereum/go-ethereum/common"
)

func TestBroadcast_WaitForEnoughValidators(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	conf := &configs.DporConfig{}
	conf.FaultyNumber = 2
	d.SetConfig(conf)
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	term := d.TermOf(d.CurrentSnap().Number)
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	addr1 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 3))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr1)
	addr2 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 4))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr2)
	addr3 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 5))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr3)
	addr4 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 1))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr4)
	addr5 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 2))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr5)
	vali, _ := dialer.EnoughValidatorsOfTerm(term)
	handler := NewHandler()
	handler.SetDporService(d)
	handler.SetDialer(dialer)
	validaters := backend.WaitForEnoughValidators(handler, term, nil)
	equalSigner := reflect.DeepEqual(validaters, vali)
	if !equalSigner {
		t.Error("Call WaitForEnoughValidators failed...")
	}

}

func TestBroadcast_WaitForEnoughPreprepareValidators(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	conf := &configs.DporConfig{}
	conf.FaultyNumber = 1
	d.SetConfig(conf)
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	term := d.TermOf(d.CurrentSnap().Number)
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	addr1 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 3))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr1)
	addr2 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 4))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr2)
	addr3 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 5))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr3)
	vi, _ := dialer.EnoughImpeachValidatorsOfTerm(term)
	handler := NewHandler()
	handler.SetDporService(d)
	handler.SetDialer(dialer)
	validaters := backend.WaitForEnoughPreprepareValidators(handler, term, nil, time.Now())
	equalSigner := reflect.DeepEqual(validaters, vi)
	if !equalSigner {
		t.Error("Call WaitForEnoughImpeachValidators failed...")
	}
}

func TestBroadcast_WaitForEnoughImpeachValidators(t *testing.T) {
	dialer := backend.NewDialer()
	d := NewDpor()
	conf := &configs.DporConfig{}
	conf.FaultyNumber = 1
	d.SetConfig(conf)
	ds := backend.DporService(d)
	dialer.SetDporService(ds)
	term := d.TermOf(d.CurrentSnap().Number)
	peer := NewPeerForTest()
	conn, _ := MsgPipe()
	addr1 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 3))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr1)
	addr2 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 4))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr2)
	addr3 := common.HexToAddress("0x" + fmt.Sprintf("%040x", 5))
	dialer.AddRemoteValidator(11, 33, peer, conn, addr3)
	vim, _ := dialer.EnoughImpeachValidatorsOfTerm(term)
	handler := NewHandler()
	handler.SetDporService(d)
	handler.SetDialer(dialer)
	validaters := backend.WaitForEnoughImpeachValidators(handler, term, nil)
	equalSigner := reflect.DeepEqual(validaters, vim)
	if !equalSigner {
		t.Error("Call WaitForEnoughImpeachValidators failed...")
	}
}
