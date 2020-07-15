package main_test

import (
	"bytes"
	"crypto/ecdsa"
	"crypto/rand"
	"fmt"
	"net"
	"net/http"
	"os"
	"testing"
	"time"

	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/p2p/discover"
	"github.com/ethereum/go-ethereum/p2p/nat"
	"github.com/ethereum/go-ethereum/rlp"
)

const (
	macSize  = 256 / 8
	sigSize  = 520 / 8
	headSize = macSize + sigSize // space of packet frame data
)

var (
	headSpace        = make([]byte, headSize)
	DiscoveryVersion = uint(9527)
)

// RPC packet types
const (
	pingPacket = iota + 1 // zero is 'reserved'
	pongPacket
	findnodePacket
	neighborsPacket
)

type (
	rpcEndpoint struct {
		IP  net.IP // len 4 for IPv4 or 16 for IPv6
		UDP uint16 // for discovery protocol
		TCP uint16 // for RLPx protocol
	}
	ping struct {
		Version    uint
		From, To   rpcEndpoint
		Expiration uint64
		// Ignore additional fields (for forward compatibility).
		Rest []rlp.RawValue `rlp:"tail"`
	}
)

func (req *ping) name() string { return "PING/v4" }

func makeEndpoint(addr *net.UDPAddr, tcpPort uint16) rpcEndpoint {
	ip := addr.IP.To4()
	if ip == nil {
		ip = addr.IP.To16()
	}
	return rpcEndpoint{IP: ip, UDP: uint16(addr.Port), TCP: tcpPort}
}

func encodePacket(priv *ecdsa.PrivateKey, ptype byte, req interface{}) (packet, hash []byte, err error) {
	b := new(bytes.Buffer)
	b.Write(headSpace)
	b.WriteByte(ptype)
	if err := rlp.Encode(b, req); err != nil {
		log.Error("Can't encode discv4 packet", "err", err)
		return nil, nil, err
	}
	packet = b.Bytes()
	sig, err := crypto.Sign(crypto.Keccak256(packet[headSize:]), priv)
	if err != nil {
		log.Error("Can't sign discv4 packet", "err", err)
		return nil, nil, err
	}
	copy(packet[macSize:], sig)
	// add the hash to the front. Note: this doesn't protect the
	// packet in any way. Our public key will be part of this hash in
	// The future.
	hash = crypto.Keccak256(packet[macSize:])
	copy(packet, hash)
	return packet, hash, nil
}

func TestBootnode(t *testing.T) {
	// set log level
	glogger := log.NewGlogHandler(log.StreamHandler(os.Stdout, log.TerminalFormat(false)))
	glogger.Verbosity(log.Lvl(log.LvlTrace))
	glogger.Vmodule("")
	log.Root().SetHandler(glogger)

	// start
	var address = "127.0.0.1:45678"
	addr, err := net.ResolveUDPAddr("udp", address)
	if err != nil {
		t.Fatalf("-ResolveUDPAddr: %v", err)
	}
	conn, err := net.ListenUDP("udp", addr)
	if err != nil {
		t.Fatalf("-ListenUDP: %v", err)
	}
	natm, err := nat.Parse("none")
	if err != nil {
		t.Fatalf("-nat: %v", err)
	}
	realaddr := conn.LocalAddr().(*net.UDPAddr)
	if natm != nil {
		if !realaddr.IP.IsLoopback() {
			go nat.Map(natm, nil, "udp", realaddr.Port, realaddr.Port, "ethereum discovery")
		}
		// TODO: react to external IP changes over time.
		if ext, err := natm.ExternalIP(); err == nil {
			realaddr = &net.UDPAddr{IP: ext, Port: realaddr.Port}
		}
	}
	nodeKey, err := crypto.GenerateKey()
	if err != nil {
		t.Fatalf("could not generate key: %v", err)
	}
	cfg := discover.Config{
		PrivateKey:   nodeKey,
		AnnounceAddr: realaddr,
		NetRestrict:  nil,
	}
	// add hook
	discover.AddIPHook(func(ip net.IP) {
		t.Log(ip)
	})

	// add hook
	discover.AddIPHook(func(ip net.IP) {
		// push to ip-server
		var ipServer = "http://127.0.0.1:8010/nodes/ip/"
		jsonStr := []byte(fmt.Sprintf(`{ "ip": "%s"}`, ip))
		url := ipServer
		req, err := http.NewRequest("POST", url, bytes.NewBuffer(jsonStr))
		if err != nil {
			log.Error("create req for pushing ip info", "err", err)
			return
		}
		req.Header.Set("Content-Type", "application/json")
		client := &http.Client{}
		_, err = client.Do(req)
		if err != nil {
			log.Error("when push ip info to the gateway", "err", err)
			return
		}
	})

	// start udp server
	go func() {
		if _, err := discover.ListenUDP(conn, cfg); err != nil {
			t.Errorf("%v", err)
		}
	}()

	<-time.After(1 * time.Second)

	// start a client to connect
	go func() {
		var id discover.NodeID
		rand.Read(id[:])
		client, err := net.Dial("udp", address)
		if err != nil {
			t.Error(err)
			return
		}
		_ = client

		ourEndpointAddr, _ := net.ResolveUDPAddr("udp", "192.168.0.1:45679")
		ourEndpoint := makeEndpoint(ourEndpointAddr, 0)
		expiration := 5 * time.Second

		req := &ping{
			Version:    DiscoveryVersion,
			From:       ourEndpoint,
			To:         makeEndpoint(addr, 0), // TODO: maybe use known TCP port from DB
			Expiration: uint64(time.Now().Add(expiration).Unix()),
		}
		priv, _ := crypto.GenerateKey()
		packet, hash, err := encodePacket(priv, pingPacket, req)
		_ = hash
		if _, err := client.Write(packet); err != nil {
			t.Error(err)
		}
	}()
	<-time.After(3 * time.Second)
}
