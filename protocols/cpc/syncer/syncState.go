package syncer

import (
	"bytes"
	"errors"
	"time"

	state_object "bitbucket.org/cpchain/chain/core/state"

	"bitbucket.org/cpchain/chain/commons/log"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/ethereum/go-ethereum/trie"
)

// sync state data
func (s *Synchronizer) processFastSyncContent(hash common.Hash) error {
	var (
		batch = MaxStateFetch
		sched *trie.Sync
		stats = struct {
			start time.Time
		}{}
	)
	callback := func(leaf []byte, parent common.Hash) error {
		var obj state_object.Account
		if err := rlp.Decode(bytes.NewReader(leaf), &obj); err != nil {
			return err
		}
		sched.AddSubTrie(obj.Root, 64, parent, nil)
		sched.AddRawEntry(common.BytesToHash(obj.CodeHash), 64, parent)
		return nil
	}
	_ = callback
	sched = trie.NewSync(hash, s.blockchain.Database(), callback)
	queue := append([]common.Hash{}, sched.Missing(batch)...)

	// fetch data

	for len(queue) > 0 {
		log.Debug("Queue", "len", len(queue))
		var results []trie.SyncResult
		stats.start = time.Now()

		s.syncRequestStateDataCh <- queue
		timer := time.NewTimer(SyncStateTimeout)

		select {
		case data := <-s.syncStateDataCh:
			// wait state data
			log.Debug("received state data", "len", len(data))
			results = make([]trie.SyncResult, len(data))
			if len(queue) < len(data) {
				log.Error("len(queue) != len(data)", "queue", len(queue), "data", len(data))
				return errors.New("sync state error")
			}
			for i, item := range data {
				results[i] = trie.SyncResult{Hash: queue[i], Data: item}
			}
		case <-timer.C:
			s.stateSyncErrCh <- ErrTimeout
			log.Error("state sync timeout error")
			return ErrTimeout
		case <-s.cancelCh:
			s.processFastSyncContentCh <- struct{}{}
			return errCanceled
		case <-s.quitCh:
			return errQuitSync
		}

		// push the results to sched
		if _, _, err := sched.Process(results); err != nil {
			s.stateSyncErrCh <- err
			return err
		}

		if _, err := sched.Commit(s.blockchain.Database()); err != nil {
			s.stateSyncErrCh <- err
			return err
		}

		// next batch
		queue = append(queue[len(results):], sched.Missing(batch)...)
		elapsed := common.PrettyDuration(time.Since(stats.start))
		log.Info("fetch state trie", "elapsed", elapsed, "results", len(results))
	}
	return nil
}
