.. _testcase:

Chain Test Cases
==================


This page curates test cases for the chain.

Abnormal Test Cases
-----------------------

This category lists all abnormal cases scenarios.

Verification of All Attributes
++++++++++++++++++++++++++++++++++

All attributes of a block is shown below:

.. code-block:: go

    type Block struct {
    header       *Header
    transactions Transactions

    // caches  Insert
    hash atomic.Value
    size atomic.Value

    // Td is used by package core to store the total difficulty
    // of the chain up to and including the block.
    td *big.Int

    // These fields are used to track inter-peer block relay.
    ReceivedAt   time.Time
    ReceivedFrom interface{}
    }

    type Header struct {
        ParentHash   common.Hash
        Coinbase     common.Address
        StateRoot    common.Hash
        TxsRoot      common.Hash
        ReceiptsRoot common.Hash
        LogsBloom    Bloom
        Number       *big.Int
        GasLimit     uint64
        GasUsed      uint64
        Time         *big.Int
        Extra        []byte
        Dpor         DporSnap
    }

    type DporSnap struct {
        // the signature of the block's proposer
        Seal       DporSignature
        // the signatures of validators to endorse the block
        Sigs       []DporSignature
        // current proposers committee
        Proposers  []common.Address
        // updated validator committee in next epoch if it is not nil.
        // keep the same to current if it is nil.
        Validators []common.Address
    }



Double Spend Attack
+++++++++++++++++++++

Unknown Ancestor
++++++++++++++++++

Future Block
++++++++++++++

Delayed Block
+++++++++++++++

Unrecognized Node
+++++++++++++++++++++

Fake Impeach
+++++++++++++++++

Time Consuming TX List
+++++++++++++++++++++++


System Stability Test Cases
-------------------------------

Mining Test Cases
--------------------


