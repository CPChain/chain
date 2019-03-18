// Copyright 2018 The cpchain authors

package main

import (
	"context"
	"math/big"
	"os"

	"bitbucket.org/cpchain/chain/api/cpclient"
	"bitbucket.org/cpchain/chain/commons/log"
	"bitbucket.org/cpchain/chain/configs"
)

func main() {
	// find impeach block
	log.Info("find impeach block")
	endPoint := "http://localhost:8501"
	if len(os.Args) > 1 {
		endPoint = os.Args[1]
	}
	log.Infof("endPoint:%s", endPoint)
	ep, err := configs.ResolveUrl(endPoint)
	if err != nil {
		log.Fatal("unknown endpoint", "endpoint", endPoint, "err", err)
	}
	// Create client.
	client, err := cpclient.Dial(ep)
	if err != nil {
		log.Fatal(err.Error())
	}
	number := client.GetBlockNumber()
	log.Infof("latest number:%v", number)

	impeachCounter := 0
	for i := 0; i < int(number.Int64()); i++ {
		block, err := client.BlockByNumber(context.Background(), big.NewInt(int64(i)))
		if err != nil {
			log.Infof("BlockByNumber Error:%v", i)
			break
		}

		miner := block.Coinbase()
		// fmt.Println(miner.Hex())
		if miner.Hex() == "0x0000000000000000000000000000000000000000" {
			log.Info("impeach block", "number", i)
			impeachCounter++
		}
	}

	log.Info("--------------------------------------")
	log.Infof("impeachCounter is %d", impeachCounter)

}
