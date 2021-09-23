------------------------------- MODULE lbft4 -------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC


(*
--algorithm lbft4
variables
    \* set of proposers
\*    proposers = {"p1", "p2"},
\*    predeterminedBlockHeight = [p1 |-> 1, p2 |-> 2],
    proposers = {"p1"},
    predeterminedBlockHeight = [p1 |-> 1],
    \* set of validators
    validators = {"v1", "v2", "v3", "v4"},
    \* possible block heights
    \*    highestHeight = 2,
\*    highestHeight = 1,
    \* possibleHeights = 1..highestHeight,
\*    possibleHeights = {1},
\*    validatorTimesHeight = validators \X possibleHeights,
    \* signature for each validators
    sig = [v1 |-> 1, v2 |-> 2, v3 |-> 3, v4 |-> 4],
    \* a function to represent state for each validator
    \* 0,1,2 represent idle, prepare, commit
    \* 3,4 represent impeach prepare and impeach commit state
    \* 9 represents a consensus of normal case
    state = [va \in validators |-> 0],
    \* two sigs refers to signatures for different messages
    prepareSig = [va \in validators |-> {}],
    commitSig = [va \in validators |-> {}],
    \* a cache store received block
    blockCache = [va \in validators |-> ""],
    \* the receiver is set to the block when the proposer mines a block
    \* blockReceiver = [va \in validatorTimesHeight |-> ""],
    blockReceiver = [va \in validators |-> ""],
    \* a counter to record block heights for validators and proposers
    validatorBlockHeight = [va \in validators |-> 1],
    proposerBlockHeight = [pr \in proposers |-> 1],
    \* the local chain for each validator/proposer
    validatorChain = [va \in validators |-> <<>>],
    proposerChain = [pr \in proposers |-> <<>>],


define
    \* return true if suffice a certificate
    prepareCertificate(v) ==
        Cardinality(prepareSig[v]) >= 3

    commitCertificate(v) ==
        Cardinality(commitSig[v]) >= 3

    ifConsensus(v) ==
        validatorBlockHeight[v] > 1

    \* testing variables to check if sig has been added
    \* if these variables violates invariant properties,
    \* the validator successfully transit to next state.
    validatorPrepareSig1 == 1 \notin prepareSig["v1"]
    validatorCommitSig1 == 1 \notin commitSig["v1"]
    validatorPrepareCertificate1 == ~prepareCertificate("v1")
    validatorPrepareCertificate4 == ~prepareCertificate("v4")
    validatorState1 == state["v1"] /= 9
    validatorState4 == state["v4"] /= 2
    \* GoToNextHeight is violated when all validators have advanced to next block height
    getToNextHeight ==
        state["v1"] /=9 \/
        state["v2"] /=9 \/
        state["v3"] /=9 \/
        state["v4"] /=9
    \* all validators hold same block height, should have same local chain.
    uniqueValidation ==
        \A va \in validators:
        validatorBlockHeight[va] /= validatorBlockHeight["v1"] \/
        validatorChain[va] = validatorChain["v1"]





end define;

\* the receiver add signatures according received message
procedure addSig(receiver, inputType, sender) begin
PrepareMsg:
    if inputType = "prepareMsg"
    \* accumulate prepare signatures
    then
        prepareSig[receiver] := prepareSig[receiver] \union prepareSig[sender];
    end if;

CommitMsg:
    if inputType = "commitMsg"
    \* accumulate commit and prepare signatures
    then
        prepareSig[receiver] := prepareSig[receiver] \union prepareSig[sender];
        commitSig[receiver] := commitSig[receiver] \union commitSig[sender];
    end if;

ValidateMsg:
    if inputType = "validateMsg"
    \* accumulate commit and prepare signatures
    then
        prepareSig[receiver] := prepareSig[receiver] \union prepareSig[sender];
        commitSig[receiver] := commitSig[receiver] \union commitSig[sender];
    end if;
    return;
end procedure;

\* broadcast the message to all validators
procedure broadcast(sender, inputType) begin
Broadcast1:
        call addSig("v1", inputType,sender);
Broadcast2:
        call addSig("v2", inputType,sender);
Broadcast3:
        call addSig("v3", inputType,sender);
Broadcast4:
        call addSig("v4", inputType,sender);
    return;
end procedure;

\* broadcast blockInsertMsg to all proposers
procedure broadcastAll(sender, inputType, block, height) begin
broadcastAll:
    if inputType = "blockInsertMsg" then
        with proposer \in proposers do
            if proposerBlockHeight[proposer] = height
            then
                \* proposer add one on its block height
                \* and insert the block in its local chain
                proposerChain[proposer] := Append(proposerChain[proposer], block);
                proposerBlockHeight[proposer] := proposerBlockHeight[proposer] + 1;
            elsif proposerBlockHeight[proposer] = height + 1
            then
                \* assert an error if the received block is not indentical
                \* to the counterpart of the same height in its local chain
                assert proposerChain[proposer][height] = block;
            end if;
        end with;
    end if;
    return;
end procedure;

\* launch a process for each validator to process a block
process validator \in validators
\* consensus is set to TRUE when it collect a commit certificate
variables consensus = FALSE;
begin
Fsm:
    while ~consensus do
        either \* idle state
            \* transfer to prepare state given a block
            \* requirement of idle state
            await state[self] = 0;
            \* requirement of receiving a block of correct block height
            await blockReceiver[self] \in DOMAIN predeterminedBlockHeight;
            \* requirement of the block height of the validator
            await predeterminedBlockHeight[blockReceiver[self]] = validatorBlockHeight[self];
            blockCache[self] := blockReceiver[self];
            prepareSig[self] := prepareSig[self] \union {sig[self]};
            state[self] := 1;
            \* print prepareSig;
            call broadcast(self, "prepareMsg");

        or  \* prepare state
            \* state of v should be prepare state
            await state[self] = 1;
            await prepareCertificate(self);
            \* transfer to commit state if collect a certificate
            commitSig[self] := commitSig[self] \union {sig[self]};
            state[self] := 2;
            \* print commitSig;
            call broadcast(self, "commitMsg");

        or  \* commit state
            \* state of both v should be commit state
            await state[self] = 2;
            await commitCertificate(self);
            \* transfer to idle state in next height given the certificate
            state[self] := 9;
            \* broadcast validateMsg to all validators
            call broadcast(self, "validateMsg");
        or \* validate state
            await state[self] = 9;
            BroadcastAll:
            call broadcastAll(sender, "blockInsertMsg", blockCache[self], validatorBlockHeight[self]);
            HeightAugmentation:
            \* add one upon its block height
            \* append the block in the local chain
            validatorBlockHeight[self] := validatorBlockHeight[self] + 1;
            validatorChain[self] := Append(validatorChain[self], blockCache[self]);
            \* print result
\*            print self;
\*            print validatorChain[self];
\*            print validatorBlockHeight[self];
\*            print ifConsensus(self);
\*            print validatorBlockHeight[self] > 1;
            \* clean prepare and commit sigs
            CleanTemps:
            prepareSig[self] := {};
            commitSig[self] := {};
            \* clean blockCache and blockReceiver
            blockCache[self] := "";
            blockReceiver[self] := "";
            \* set state = 0
            state[self] := 0;
\*            consensus := TRUE;
            consensus := validatorBlockHeight[self] > 1;
\*            print consensus
\*        or
\*            skip;
        end either;
    end while;
end process;

\* launch a process for each proposer
process proposer \in proposers
\*variable
\*temp;
\*isBroadcast = [va \in validators |-> FALSE]
begin
Proposer:
    \* the proposer wait until its block height to send out block
    await proposerBlockHeight[self] = predeterminedBlockHeight[self];
    \* broadcast its block to all validators
\*BroadcastBlock:
\*    while \E va \in validators: isBroadcast[va] = FALSE do
\*        temp := CHOOSE va \in validators: isBroadcast[va] = FALSE;
\*        blockReceiver[temp] := self;
\*        isBroadcast[temp] := TRUE;
\*    end while;

SendBlock1:
    blockReceiver["v1"] := self;
SendBlock2:
    blockReceiver["v2"] := self;
SendBlock3:
    blockReceiver["v3"] := self;
SendBlock4:
    blockReceiver["v4"] := self;

end process;



end algorithm;*)
\* BEGIN TRANSLATION
\* Label broadcastAll of procedure broadcastAll at line 126 col 5 changed to broadcastAll_
\* Parameter inputType of procedure addSig at line 84 col 28 changed to inputType_
\* Parameter sender of procedure addSig at line 84 col 39 changed to sender_
\* Parameter sender of procedure broadcast at line 111 col 21 changed to sender_b
\* Parameter inputType of procedure broadcast at line 111 col 29 changed to inputType_b
CONSTANT defaultInitValue
VARIABLES proposers, predeterminedBlockHeight, validators, sig, state,
          prepareSig, commitSig, blockCache, blockReceiver,
          validatorBlockHeight, proposerBlockHeight, validatorChain,
          proposerChain, pc, stack

(* define statement *)
prepareCertificate(v) ==
    Cardinality(prepareSig[v]) >= 3

commitCertificate(v) ==
    Cardinality(commitSig[v]) >= 3

ifConsensus(v) ==
    validatorBlockHeight[v] > 1




validatorPrepareSig1 == 1 \notin prepareSig["v1"]
validatorCommitSig1 == 1 \notin commitSig["v1"]
validatorPrepareCertificate1 == ~prepareCertificate("v1")
validatorPrepareCertificate4 == ~prepareCertificate("v4")
validatorState1 == state["v1"] /= 9
validatorState4 == state["v4"] /= 2

getToNextHeight ==
    state["v1"] /=9 \/
    state["v2"] /=9 \/
    state["v3"] /=9 \/
    state["v4"] /=9

uniqueValidation ==
    \A va \in validators:
    validatorBlockHeight[va] /= validatorBlockHeight["v1"] \/
    validatorChain[va] = validatorChain["v1"]

VARIABLES receiver, inputType_, sender_, sender_b, inputType_b, sender,
          inputType, block, height, consensus

vars == << proposers, predeterminedBlockHeight, validators, sig, state,
           prepareSig, commitSig, blockCache, blockReceiver,
           validatorBlockHeight, proposerBlockHeight, validatorChain,
           proposerChain, pc, stack, receiver, inputType_, sender_, sender_b,
           inputType_b, sender, inputType, block, height, consensus >>

ProcSet == (validators) \cup (proposers)

Init == (* Global variables *)
        /\ proposers = {"p1"}
        /\ predeterminedBlockHeight = [p1 |-> 1]
        /\ validators = {"v1", "v2", "v3", "v4"}
        /\ sig = [v1 |-> 1, v2 |-> 2, v3 |-> 3, v4 |-> 4]
        /\ state = [va \in validators |-> 0]
        /\ prepareSig = [va \in validators |-> {}]
        /\ commitSig = [va \in validators |-> {}]
        /\ blockCache = [va \in validators |-> ""]
        /\ blockReceiver = [va \in validators |-> ""]
        /\ validatorBlockHeight = [va \in validators |-> 1]
        /\ proposerBlockHeight = [pr \in proposers |-> 1]
        /\ validatorChain = [va \in validators |-> <<>>]
        /\ proposerChain = [pr \in proposers |-> <<>>]
        (* Procedure addSig *)
        /\ receiver = [ self \in ProcSet |-> defaultInitValue]
        /\ inputType_ = [ self \in ProcSet |-> defaultInitValue]
        /\ sender_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure broadcast *)
        /\ sender_b = [ self \in ProcSet |-> defaultInitValue]
        /\ inputType_b = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure broadcastAll *)
        /\ sender = [ self \in ProcSet |-> defaultInitValue]
        /\ inputType = [ self \in ProcSet |-> defaultInitValue]
        /\ block = [ self \in ProcSet |-> defaultInitValue]
        /\ height = [ self \in ProcSet |-> defaultInitValue]
        (* Process validator *)
        /\ consensus = [self \in validators |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in validators -> "Fsm"
                                        [] self \in proposers -> "Proposer"]

PrepareMsg(self) == /\ pc[self] = "PrepareMsg"
                    /\ IF inputType_[self] = "prepareMsg"
                          THEN /\ prepareSig' = [prepareSig EXCEPT ![receiver[self]] = prepareSig[receiver[self]] \union prepareSig[sender_[self]]]
                          ELSE /\ TRUE
                               /\ UNCHANGED prepareSig
                    /\ pc' = [pc EXCEPT ![self] = "CommitMsg"]
                    /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                    validators, sig, state, commitSig,
                                    blockCache, blockReceiver,
                                    validatorBlockHeight, proposerBlockHeight,
                                    validatorChain, proposerChain, stack,
                                    receiver, inputType_, sender_, sender_b,
                                    inputType_b, sender, inputType, block,
                                    height, consensus >>

CommitMsg(self) == /\ pc[self] = "CommitMsg"
                   /\ IF inputType_[self] = "commitMsg"
                         THEN /\ prepareSig' = [prepareSig EXCEPT ![receiver[self]] = prepareSig[receiver[self]] \union prepareSig[sender_[self]]]
                              /\ commitSig' = [commitSig EXCEPT ![receiver[self]] = commitSig[receiver[self]] \union commitSig[sender_[self]]]
                         ELSE /\ TRUE
                              /\ UNCHANGED << prepareSig, commitSig >>
                   /\ pc' = [pc EXCEPT ![self] = "ValidateMsg"]
                   /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                   validators, sig, state, blockCache,
                                   blockReceiver, validatorBlockHeight,
                                   proposerBlockHeight, validatorChain,
                                   proposerChain, stack, receiver, inputType_,
                                   sender_, sender_b, inputType_b, sender,
                                   inputType, block, height, consensus >>

ValidateMsg(self) == /\ pc[self] = "ValidateMsg"
                     /\ IF inputType_[self] = "validateMsg"
                           THEN /\ prepareSig' = [prepareSig EXCEPT ![receiver[self]] = prepareSig[receiver[self]] \union prepareSig[sender_[self]]]
                                /\ commitSig' = [commitSig EXCEPT ![receiver[self]] = commitSig[receiver[self]] \union commitSig[sender_[self]]]
                           ELSE /\ TRUE
                                /\ UNCHANGED << prepareSig, commitSig >>
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ receiver' = [receiver EXCEPT ![self] = Head(stack[self]).receiver]
                     /\ inputType_' = [inputType_ EXCEPT ![self] = Head(stack[self]).inputType_]
                     /\ sender_' = [sender_ EXCEPT ![self] = Head(stack[self]).sender_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                     validators, sig, state, blockCache,
                                     blockReceiver, validatorBlockHeight,
                                     proposerBlockHeight, validatorChain,
                                     proposerChain, sender_b, inputType_b,
                                     sender, inputType, block, height,
                                     consensus >>

addSig(self) == PrepareMsg(self) \/ CommitMsg(self) \/ ValidateMsg(self)

Broadcast1(self) == /\ pc[self] = "Broadcast1"
                    /\ /\ inputType_' = [inputType_ EXCEPT ![self] = inputType_b[self]]
                       /\ receiver' = [receiver EXCEPT ![self] = "v1"]
                       /\ sender_' = [sender_ EXCEPT ![self] = sender_b[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "addSig",
                                                                pc        |->  "Broadcast2",
                                                                receiver  |->  receiver[self],
                                                                inputType_ |->  inputType_[self],
                                                                sender_   |->  sender_[self] ] >>
                                                            \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "PrepareMsg"]
                    /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                    validators, sig, state, prepareSig,
                                    commitSig, blockCache, blockReceiver,
                                    validatorBlockHeight, proposerBlockHeight,
                                    validatorChain, proposerChain, sender_b,
                                    inputType_b, sender, inputType, block,
                                    height, consensus >>

Broadcast2(self) == /\ pc[self] = "Broadcast2"
                    /\ /\ inputType_' = [inputType_ EXCEPT ![self] = inputType_b[self]]
                       /\ receiver' = [receiver EXCEPT ![self] = "v2"]
                       /\ sender_' = [sender_ EXCEPT ![self] = sender_b[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "addSig",
                                                                pc        |->  "Broadcast3",
                                                                receiver  |->  receiver[self],
                                                                inputType_ |->  inputType_[self],
                                                                sender_   |->  sender_[self] ] >>
                                                            \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "PrepareMsg"]
                    /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                    validators, sig, state, prepareSig,
                                    commitSig, blockCache, blockReceiver,
                                    validatorBlockHeight, proposerBlockHeight,
                                    validatorChain, proposerChain, sender_b,
                                    inputType_b, sender, inputType, block,
                                    height, consensus >>

Broadcast3(self) == /\ pc[self] = "Broadcast3"
                    /\ /\ inputType_' = [inputType_ EXCEPT ![self] = inputType_b[self]]
                       /\ receiver' = [receiver EXCEPT ![self] = "v3"]
                       /\ sender_' = [sender_ EXCEPT ![self] = sender_b[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "addSig",
                                                                pc        |->  "Broadcast4",
                                                                receiver  |->  receiver[self],
                                                                inputType_ |->  inputType_[self],
                                                                sender_   |->  sender_[self] ] >>
                                                            \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "PrepareMsg"]
                    /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                    validators, sig, state, prepareSig,
                                    commitSig, blockCache, blockReceiver,
                                    validatorBlockHeight, proposerBlockHeight,
                                    validatorChain, proposerChain, sender_b,
                                    inputType_b, sender, inputType, block,
                                    height, consensus >>

Broadcast4(self) == /\ pc[self] = "Broadcast4"
                    /\ /\ inputType_' = [inputType_ EXCEPT ![self] = inputType_b[self]]
                       /\ receiver' = [receiver EXCEPT ![self] = "v4"]
                       /\ sender_' = [sender_ EXCEPT ![self] = sender_b[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "addSig",
                                                                pc        |->  Head(stack[self]).pc,
                                                                receiver  |->  receiver[self],
                                                                inputType_ |->  inputType_[self],
                                                                sender_   |->  sender_[self] ] >>
                                                            \o Tail(stack[self])]
                    /\ pc' = [pc EXCEPT ![self] = "PrepareMsg"]
                    /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                    validators, sig, state, prepareSig,
                                    commitSig, blockCache, blockReceiver,
                                    validatorBlockHeight, proposerBlockHeight,
                                    validatorChain, proposerChain, sender_b,
                                    inputType_b, sender, inputType, block,
                                    height, consensus >>

broadcast(self) == Broadcast1(self) \/ Broadcast2(self) \/ Broadcast3(self)
                      \/ Broadcast4(self)

broadcastAll_(self) == /\ pc[self] = "broadcastAll_"
                       /\ IF inputType[self] = "blockInsertMsg"
                             THEN /\ \E proposer \in proposers:
                                       IF proposerBlockHeight[proposer] = height[self]
                                          THEN /\ proposerChain' = [proposerChain EXCEPT ![proposer] = Append(proposerChain[proposer], block[self])]
                                               /\ proposerBlockHeight' = [proposerBlockHeight EXCEPT ![proposer] = proposerBlockHeight[proposer] + 1]
                                          ELSE /\ IF proposerBlockHeight[proposer] = height[self] + 1
                                                     THEN /\ Assert(proposerChain[proposer][height[self]] = block[self],
                                                                    "Failure of assertion at line 138, column 17.")
                                                     ELSE /\ TRUE
                                               /\ UNCHANGED << proposerBlockHeight,
                                                               proposerChain >>
                             ELSE /\ TRUE
                                  /\ UNCHANGED << proposerBlockHeight,
                                                  proposerChain >>
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ sender' = [sender EXCEPT ![self] = Head(stack[self]).sender]
                       /\ inputType' = [inputType EXCEPT ![self] = Head(stack[self]).inputType]
                       /\ block' = [block EXCEPT ![self] = Head(stack[self]).block]
                       /\ height' = [height EXCEPT ![self] = Head(stack[self]).height]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                       validators, sig, state, prepareSig,
                                       commitSig, blockCache, blockReceiver,
                                       validatorBlockHeight, validatorChain,
                                       receiver, inputType_, sender_, sender_b,
                                       inputType_b, consensus >>

broadcastAll(self) == broadcastAll_(self)

Fsm(self) == /\ pc[self] = "Fsm"
             /\ IF ~consensus[self]
                   THEN /\ \/ /\ state[self] = 0
                              /\ blockReceiver[self] \in DOMAIN predeterminedBlockHeight
                              /\ predeterminedBlockHeight[blockReceiver[self]] = validatorBlockHeight[self]
                              /\ blockCache' = [blockCache EXCEPT ![self] = blockReceiver[self]]
                              /\ prepareSig' = [prepareSig EXCEPT ![self] = prepareSig[self] \union {sig[self]}]
                              /\ state' = [state EXCEPT ![self] = 1]
                              /\ /\ inputType_b' = [inputType_b EXCEPT ![self] = "prepareMsg"]
                                 /\ sender_b' = [sender_b EXCEPT ![self] = self]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcast",
                                                                          pc        |->  "Fsm",
                                                                          sender_b  |->  sender_b[self],
                                                                          inputType_b |->  inputType_b[self] ] >>
                                                                      \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "Broadcast1"]
                              /\ UNCHANGED commitSig
                           \/ /\ state[self] = 1
                              /\ prepareCertificate(self)
                              /\ commitSig' = [commitSig EXCEPT ![self] = commitSig[self] \union {sig[self]}]
                              /\ state' = [state EXCEPT ![self] = 2]
                              /\ /\ inputType_b' = [inputType_b EXCEPT ![self] = "commitMsg"]
                                 /\ sender_b' = [sender_b EXCEPT ![self] = self]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcast",
                                                                          pc        |->  "Fsm",
                                                                          sender_b  |->  sender_b[self],
                                                                          inputType_b |->  inputType_b[self] ] >>
                                                                      \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "Broadcast1"]
                              /\ UNCHANGED <<prepareSig, blockCache>>
                           \/ /\ state[self] = 2
                              /\ commitCertificate(self)
                              /\ state' = [state EXCEPT ![self] = 9]
                              /\ /\ inputType_b' = [inputType_b EXCEPT ![self] = "validateMsg"]
                                 /\ sender_b' = [sender_b EXCEPT ![self] = self]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcast",
                                                                          pc        |->  "Fsm",
                                                                          sender_b  |->  sender_b[self],
                                                                          inputType_b |->  inputType_b[self] ] >>
                                                                      \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "Broadcast1"]
                              /\ UNCHANGED <<prepareSig, commitSig, blockCache>>
                           \/ /\ state[self] = 9
                              /\ pc' = [pc EXCEPT ![self] = "BroadcastAll"]
                              /\ UNCHANGED <<state, prepareSig, commitSig, blockCache, stack, sender_b, inputType_b>>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << state, prepareSig, commitSig,
                                        blockCache, stack, sender_b,
                                        inputType_b >>
             /\ UNCHANGED << proposers, predeterminedBlockHeight, validators,
                             sig, blockReceiver, validatorBlockHeight,
                             proposerBlockHeight, validatorChain,
                             proposerChain, receiver, inputType_, sender_,
                             sender, inputType, block, height, consensus >>

BroadcastAll(self) == /\ pc[self] = "BroadcastAll"
                      /\ /\ block' = [block EXCEPT ![self] = blockCache[self]]
                         /\ height' = [height EXCEPT ![self] = validatorBlockHeight[self]]
                         /\ inputType' = [inputType EXCEPT ![self] = "blockInsertMsg"]
                         /\ sender' = [sender EXCEPT ![self] = sender[self]]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcastAll",
                                                                  pc        |->  "HeightAugmentation",
                                                                  sender    |->  sender[self],
                                                                  inputType |->  inputType[self],
                                                                  block     |->  block[self],
                                                                  height    |->  height[self] ] >>
                                                              \o stack[self]]
                      /\ pc' = [pc EXCEPT ![self] = "broadcastAll_"]
                      /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                      validators, sig, state, prepareSig,
                                      commitSig, blockCache, blockReceiver,
                                      validatorBlockHeight,
                                      proposerBlockHeight, validatorChain,
                                      proposerChain, receiver, inputType_,
                                      sender_, sender_b, inputType_b,
                                      consensus >>

HeightAugmentation(self) == /\ pc[self] = "HeightAugmentation"
                            /\ validatorBlockHeight' = [validatorBlockHeight EXCEPT ![self] = validatorBlockHeight[self] + 1]
                            /\ validatorChain' = [validatorChain EXCEPT ![self] = Append(validatorChain[self], blockCache[self])]
                            /\ pc' = [pc EXCEPT ![self] = "CleanTemps"]
                            /\ UNCHANGED << proposers,
                                            predeterminedBlockHeight,
                                            validators, sig, state, prepareSig,
                                            commitSig, blockCache,
                                            blockReceiver, proposerBlockHeight,
                                            proposerChain, stack, receiver,
                                            inputType_, sender_, sender_b,
                                            inputType_b, sender, inputType,
                                            block, height, consensus >>

CleanTemps(self) == /\ pc[self] = "CleanTemps"
                    /\ prepareSig' = [prepareSig EXCEPT ![self] = {}]
                    /\ commitSig' = [commitSig EXCEPT ![self] = {}]
                    /\ blockCache' = [blockCache EXCEPT ![self] = ""]
                    /\ blockReceiver' = [blockReceiver EXCEPT ![self] = ""]
                    /\ state' = [state EXCEPT ![self] = 0]
                    /\ consensus' = [consensus EXCEPT ![self] = validatorBlockHeight[self] > 1]
                    /\ pc' = [pc EXCEPT ![self] = "Fsm"]
                    /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                    validators, sig, validatorBlockHeight,
                                    proposerBlockHeight, validatorChain,
                                    proposerChain, stack, receiver, inputType_,
                                    sender_, sender_b, inputType_b, sender,
                                    inputType, block, height >>

validator(self) == Fsm(self) \/ BroadcastAll(self)
                      \/ HeightAugmentation(self) \/ CleanTemps(self)

Proposer(self) == /\ pc[self] = "Proposer"
                  /\ proposerBlockHeight[self] = predeterminedBlockHeight[self]
                  /\ pc' = [pc EXCEPT ![self] = "SendBlock1"]
                  /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                  validators, sig, state, prepareSig,
                                  commitSig, blockCache, blockReceiver,
                                  validatorBlockHeight, proposerBlockHeight,
                                  validatorChain, proposerChain, stack,
                                  receiver, inputType_, sender_, sender_b,
                                  inputType_b, sender, inputType, block,
                                  height, consensus >>

SendBlock1(self) == /\ pc[self] = "SendBlock1"
                    /\ blockReceiver' = [blockReceiver EXCEPT !["v1"] = self]
                    /\ pc' = [pc EXCEPT ![self] = "SendBlock2"]
                    /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                    validators, sig, state, prepareSig,
                                    commitSig, blockCache,
                                    validatorBlockHeight, proposerBlockHeight,
                                    validatorChain, proposerChain, stack,
                                    receiver, inputType_, sender_, sender_b,
                                    inputType_b, sender, inputType, block,
                                    height, consensus >>

SendBlock2(self) == /\ pc[self] = "SendBlock2"
                    /\ blockReceiver' = [blockReceiver EXCEPT !["v2"] = self]
                    /\ pc' = [pc EXCEPT ![self] = "SendBlock3"]
                    /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                    validators, sig, state, prepareSig,
                                    commitSig, blockCache,
                                    validatorBlockHeight, proposerBlockHeight,
                                    validatorChain, proposerChain, stack,
                                    receiver, inputType_, sender_, sender_b,
                                    inputType_b, sender, inputType, block,
                                    height, consensus >>

SendBlock3(self) == /\ pc[self] = "SendBlock3"
                    /\ blockReceiver' = [blockReceiver EXCEPT !["v3"] = self]
                    /\ pc' = [pc EXCEPT ![self] = "SendBlock4"]
                    /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                    validators, sig, state, prepareSig,
                                    commitSig, blockCache,
                                    validatorBlockHeight, proposerBlockHeight,
                                    validatorChain, proposerChain, stack,
                                    receiver, inputType_, sender_, sender_b,
                                    inputType_b, sender, inputType, block,
                                    height, consensus >>

SendBlock4(self) == /\ pc[self] = "SendBlock4"
                    /\ blockReceiver' = [blockReceiver EXCEPT !["v4"] = self]
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << proposers, predeterminedBlockHeight,
                                    validators, sig, state, prepareSig,
                                    commitSig, blockCache,
                                    validatorBlockHeight, proposerBlockHeight,
                                    validatorChain, proposerChain, stack,
                                    receiver, inputType_, sender_, sender_b,
                                    inputType_b, sender, inputType, block,
                                    height, consensus >>

proposer(self) == Proposer(self) \/ SendBlock1(self) \/ SendBlock2(self)
                     \/ SendBlock3(self) \/ SendBlock4(self)

Next == (\E self \in ProcSet:  \/ addSig(self) \/ broadcast(self)
                               \/ broadcastAll(self))
           \/ (\E self \in validators: validator(self))
           \/ (\E self \in proposers: proposer(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
