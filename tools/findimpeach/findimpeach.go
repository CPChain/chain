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

// print impeach block and validators for debug
// usage:
// 1.print proposer and validators : ./findimpeach http://localhost:8501 true
// 2.print proposer : ./findimpeach http://localhost:8501

func main() {
	// find impeach block
	log.Info("find impeach block")
	endPoint := "http://localhost:8501"
	showValidator := false
	if len(os.Args) > 1 {
		endPoint = os.Args[1]
	}
	if len(os.Args) > 2 {
		showValidator = "true" == os.Args[2]
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
		blockNr := big.NewInt(int64(i))
		block, err := client.BlockByNumber(context.Background(), blockNr)
		if err != nil {
			log.Infof("BlockByNumber Error:%v", i)
			break
		}

		if block.Impeachment() {
			log.Info("=======================================================")
			proposer, err := client.GetProposerByBlock(context.Background(), blockNr)
			if err != nil {
				log.Errorf("get proposer for block %v error", i)
			} else {
				log.Infof("timestamp=%v,number=%v,proposer=%x", block.Timestamp(), i, proposer)
			}

			if showValidator {
				validators, err := client.GetValidatorsByBlockNumber(context.Background(), blockNr)
				if err != nil {
					log.Errorf("get validators for block %v error", i)
				} else {
					log.Infof("validators=%x", validators)
				}
			}
			impeachCounter++
		}
	}
	log.Info("--------------------------------------")
	log.Infof("impeachCounter is %d", impeachCounter)
}
