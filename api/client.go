package api

import (
	"google.golang.org/grpc"
)

type Client struct {
	c *grpc.ClientConn
}

func NewClient(conn *grpc.ClientConn) *Client {
	return &Client{c: conn}
}

