// Copyright 2018 The cpchain authors
// Copyright 2016 The go-ethereum Authors

/*
Package miner mints blocks.

Currently, there is a single miner. It is created by CpchainService.

A miner contains an engine.
The job of the engine is to dispatch un-sealed blocks to several workers and seal the returned block.
*/
package miner
