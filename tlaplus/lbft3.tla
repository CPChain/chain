------------------------------- MODULE lbft3 -------------------------------


EXTENDS Integers, Sequences, FiniteSets, TLC


(*
--algorithm lbft3
variables
    proposers = {"p1"},
    \* set of proposers
    validators = {"v1","v2","v3","v4"},
    possibleHeights = {1},
    sig = [v1|->1,v2|->2,v3|->3,v4|->4],
    predeterminedBlockHeight = [p1|->1],
    state = [va \in validators |-> 0],
    prepareSig = [va \in validators |->{}],
    commitSig = [va \in validators |->{}],
    impeachPrepareSig = [va \in validators |->{}],
    impeachCommitSig = [va \in validators |->{}],
    blockCache = [va \in validators|->""],
    blockReceiver = [va \in validators |->""],
    validatorBlockHeight = [va \in validators |-> 1],
    proposerBlockHeight = [pr \in proposers |-> 1],
    validatorChain = [va \in validators |-> <<>>],
    proposerChain = [pr \in proposers |-> <<>>],
    \* sequence of validators
    \* 0,1,2 represent idle, prepare, commit
    \* 3,4 represent impeach prepare and impeach commit state
    \* 9 represents a consensus of normal case
    \* four sigs refers to signatures for different messages

define
    \* return true if suffice a certificate
    prepareCertificate(v) ==
        Cardinality(prepareSig[v]) >= 3

    commitCertificate(v) ==
        Cardinality(commitSig[v]) >= 3

    impeachPrepareCertificate(v) ==
        Cardinality(impeachPrepareSig[v]) >= 2

    impeachCommitCertificate(v) ==
        Cardinality(impeachCommitSig[v]) >= 2


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
    GetToNextHeight ==
        state["v1"] /=9 \/
        state["v2"] /=9 \/
        state["v3"] /=9 \/
        state["v4"] /=9





end define;

procedure addSig(receiver, inputType, sender) begin

PrepareMsg:
    if inputType = "prepareMsg"
    \* accumulate prepare signatures
    then
        prepareSig[receiver] := prepareSig[receiver] \union prepareSig[sender];
    end if;

CommitMsg:
    if inputType = "commitMsg"
    then
        prepareSig[receiver] := prepareSig[receiver] \union prepareSig[sender];
        commitSig[receiver] := commitSig[receiver] \union commitSig[sender];
    end if;

ValidateMsg:
    if inputType = "validateMsg"
    then
        prepareSig[receiver] := prepareSig[receiver] \union prepareSig[sender];
        commitSig[receiver] := commitSig[receiver] \union commitSig[sender];
    end if;
    return;
end procedure;

procedure foreverLoop() begin
Forever:
    await state["v1"] = 9;
end procedure;

procedure broadcast(sender, inputType) begin
Broadcast1:
        call addSig("v1",inputType,sender);
Broadcast2:
        call addSig("v2",inputType,sender);
Broadcast3:
        call addSig("v3",inputType,sender);
Broadcast4:
        call addSig("v4",inputType,sender);
    return;
end procedure;

procedure broadcastAll(sender, inputType, block, height) begin
broadcastAll:
    if inputType = "blockInsertMsg" then
        with proposer \in proposers do
            if proposerBlockHeight[proposer] = height then
                proposerChain[proposer] := Append(proposerChain[proposer],block);
                proposerBlockHeight[proposer] := proposerBlockHeight[proposer]+1;
            end if;
        end with;
    end if;
    return;
end procedure;

process validator \in validators
variables consensus = FALSE;
begin
Fsm:
    while ~consensus do
        either \* idle state
            \* transfer to prepare state given a block
            await state[self] = 0;
            await predeterminedBlockHeight[blockReceiver[self]] = validatorBlockHeight[self];
            blockCache[self] := blockReceiver[self];
            prepareSig[self] := prepareSig[self] \union {sig[self]};
            state[self] := 1;
            print prepareSig;
            call broadcast(self, "prepareMsg");

        or  \* prepare state
            \* states of both v and input should be prepare state
            await state[self] = 1;
            await prepareCertificate(self);
            \* transfer to commit state if collect a certificate
            commitSig[self] := commitSig[self] \union {sig[self]};
            state[self] := 2;
            \* print commitSig;
            call broadcast(self,"commitMsg");

        or  \* commit state
            \* states of both v and input should be commit state
            await state[self] = 2;
            await commitCertificate(self);
            \* transfer to idle state in next height given the certificate
            state[self] := 9;
            consensus := TRUE;
            validatorChain[self] := Append(validatorChain[self], blockCache[self]);
            call broadcast(self,"validateMsg");
            BroadcastAll:
            call broadcastAll(sender, "blockInsertMsg", blockCache[self], validatorBlockHeight[self]);
            HeightAugmentation:
            validatorBlockHeight[self] := validatorBlockHeight[self]+1;
\*        or
\*            skip;
        end either;
    end while;
end process;

process proposer \in proposers
begin
Proposer:
    await proposerBlockHeight[self] = predeterminedBlockHeight[self];
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
\* Label broadcastAll of procedure broadcastAll at line 114 col 5 changed to broadcastAll_
\* Parameter inputType of procedure addSig at line 70 col 28 changed to inputType_
\* Parameter sender of procedure addSig at line 70 col 39 changed to sender_
\* Parameter sender of procedure broadcast at line 100 col 21 changed to sender_b
\* Parameter inputType of procedure broadcast at line 100 col 29 changed to inputType_b
CONSTANT defaultInitValue
VARIABLES proposers, validators, possibleHeights, sig,
          predeterminedBlockHeight, state, prepareSig, commitSig,
          impeachPrepareSig, impeachCommitSig, blockCache, blockReceiver,
          validatorBlockHeight, proposerBlockHeight, validatorChain,
          proposerChain, pc, stack

(* define statement *)
prepareCertificate(v) ==
    Cardinality(prepareSig[v]) >= 3

commitCertificate(v) ==
    Cardinality(commitSig[v]) >= 3

impeachPrepareCertificate(v) ==
    Cardinality(impeachPrepareSig[v]) >= 2

impeachCommitCertificate(v) ==
    Cardinality(impeachCommitSig[v]) >= 2





validatorPrepareSig1 == 1 \notin prepareSig["v1"]
validatorCommitSig1 == 1 \notin commitSig["v1"]
validatorPrepareCertificate1 == ~prepareCertificate("v1")
validatorPrepareCertificate4 == ~prepareCertificate("v4")
validatorState1 == state["v1"] /= 9
validatorState4 == state["v4"] /= 2

GetToNextHeight ==
    state["v1"] /=9 \/
    state["v2"] /=9 \/
    state["v3"] /=9 \/
    state["v4"] /=9

VARIABLES receiver, inputType_, sender_, sender_b, inputType_b, sender,
          inputType, block, height, consensus

vars == << proposers, validators, possibleHeights, sig,
           predeterminedBlockHeight, state, prepareSig, commitSig,
           impeachPrepareSig, impeachCommitSig, blockCache, blockReceiver,
           validatorBlockHeight, proposerBlockHeight, validatorChain,
           proposerChain, pc, stack, receiver, inputType_, sender_, sender_b,
           inputType_b, sender, inputType, block, height, consensus >>

ProcSet == (validators) \cup (proposers)

Init == (* Global variables *)
        /\ proposers = {"p1"}
        /\ validators = {"v1","v2","v3","v4"}
        /\ possibleHeights = {1}
        /\ sig = [v1|->1,v2|->2,v3|->3,v4|->4]
        /\ predeterminedBlockHeight = [p1|->1]
        /\ state = [va \in validators |-> 0]
        /\ prepareSig = [va \in validators |->{}]
        /\ commitSig = [va \in validators |->{}]
        /\ impeachPrepareSig = [va \in validators |->{}]
        /\ impeachCommitSig = [va \in validators |->{}]
        /\ blockCache = [va \in validators|->""]
        /\ blockReceiver = [va \in validators |->""]
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
                    /\ UNCHANGED << proposers, validators, possibleHeights,
                                    sig, predeterminedBlockHeight, state,
                                    commitSig, impeachPrepareSig,
                                    impeachCommitSig, blockCache,
                                    blockReceiver, validatorBlockHeight,
                                    proposerBlockHeight, validatorChain,
                                    proposerChain, stack, receiver, inputType_,
                                    sender_, sender_b, inputType_b, sender,
                                    inputType, block, height, consensus >>

CommitMsg(self) == /\ pc[self] = "CommitMsg"
                   /\ IF inputType_[self] = "commitMsg"
                         THEN /\ prepareSig' = [prepareSig EXCEPT ![receiver[self]] = prepareSig[receiver[self]] \union prepareSig[sender_[self]]]
                              /\ commitSig' = [commitSig EXCEPT ![receiver[self]] = commitSig[receiver[self]] \union commitSig[sender_[self]]]
                         ELSE /\ TRUE
                              /\ UNCHANGED << prepareSig, commitSig >>
                   /\ pc' = [pc EXCEPT ![self] = "ValidateMsg"]
                   /\ UNCHANGED << proposers, validators, possibleHeights, sig,
                                   predeterminedBlockHeight, state,
                                   impeachPrepareSig, impeachCommitSig,
                                   blockCache, blockReceiver,
                                   validatorBlockHeight, proposerBlockHeight,
                                   validatorChain, proposerChain, stack,
                                   receiver, inputType_, sender_, sender_b,
                                   inputType_b, sender, inputType, block,
                                   height, consensus >>

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
                     /\ UNCHANGED << proposers, validators, possibleHeights,
                                     sig, predeterminedBlockHeight, state,
                                     impeachPrepareSig, impeachCommitSig,
                                     blockCache, blockReceiver,
                                     validatorBlockHeight, proposerBlockHeight,
                                     validatorChain, proposerChain, sender_b,
                                     inputType_b, sender, inputType, block,
                                     height, consensus >>

addSig(self) == PrepareMsg(self) \/ CommitMsg(self) \/ ValidateMsg(self)

Forever(self) == /\ pc[self] = "Forever"
                 /\ state["v1"] = 9
                 /\ pc' = [pc EXCEPT ![self] = "Error"]
                 /\ UNCHANGED << proposers, validators, possibleHeights, sig,
                                 predeterminedBlockHeight, state, prepareSig,
                                 commitSig, impeachPrepareSig,
                                 impeachCommitSig, blockCache, blockReceiver,
                                 validatorBlockHeight, proposerBlockHeight,
                                 validatorChain, proposerChain, stack,
                                 receiver, inputType_, sender_, sender_b,
                                 inputType_b, sender, inputType, block, height,
                                 consensus >>

foreverLoop(self) == Forever(self)

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
                    /\ UNCHANGED << proposers, validators, possibleHeights,
                                    sig, predeterminedBlockHeight, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, blockCache,
                                    blockReceiver, validatorBlockHeight,
                                    proposerBlockHeight, validatorChain,
                                    proposerChain, sender_b, inputType_b,
                                    sender, inputType, block, height,
                                    consensus >>

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
                    /\ UNCHANGED << proposers, validators, possibleHeights,
                                    sig, predeterminedBlockHeight, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, blockCache,
                                    blockReceiver, validatorBlockHeight,
                                    proposerBlockHeight, validatorChain,
                                    proposerChain, sender_b, inputType_b,
                                    sender, inputType, block, height,
                                    consensus >>

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
                    /\ UNCHANGED << proposers, validators, possibleHeights,
                                    sig, predeterminedBlockHeight, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, blockCache,
                                    blockReceiver, validatorBlockHeight,
                                    proposerBlockHeight, validatorChain,
                                    proposerChain, sender_b, inputType_b,
                                    sender, inputType, block, height,
                                    consensus >>

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
                    /\ UNCHANGED << proposers, validators, possibleHeights,
                                    sig, predeterminedBlockHeight, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, blockCache,
                                    blockReceiver, validatorBlockHeight,
                                    proposerBlockHeight, validatorChain,
                                    proposerChain, sender_b, inputType_b,
                                    sender, inputType, block, height,
                                    consensus >>

broadcast(self) == Broadcast1(self) \/ Broadcast2(self) \/ Broadcast3(self)
                      \/ Broadcast4(self)

broadcastAll_(self) == /\ pc[self] = "broadcastAll_"
                       /\ IF inputType[self] = "blockInsertMsg"
                             THEN /\ \E proposer \in proposers:
                                       IF proposerBlockHeight[proposer] = height[self]
                                          THEN /\ proposerChain' = [proposerChain EXCEPT ![proposer] = Append(proposerChain[proposer],block[self])]
                                               /\ proposerBlockHeight' = [proposerBlockHeight EXCEPT ![proposer] = proposerBlockHeight[proposer]+1]
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
                       /\ UNCHANGED << proposers, validators, possibleHeights,
                                       sig, predeterminedBlockHeight, state,
                                       prepareSig, commitSig,
                                       impeachPrepareSig, impeachCommitSig,
                                       blockCache, blockReceiver,
                                       validatorBlockHeight, validatorChain,
                                       receiver, inputType_, sender_, sender_b,
                                       inputType_b, consensus >>

broadcastAll(self) == broadcastAll_(self)

Fsm(self) == /\ pc[self] = "Fsm"
             /\ IF ~consensus[self]
                   THEN /\ \/ /\ state[self] = 0
                              /\ predeterminedBlockHeight[blockReceiver[self]] = validatorBlockHeight[self]
                              /\ blockCache' = [blockCache EXCEPT ![self] = blockReceiver[self]]
                              /\ prepareSig' = [prepareSig EXCEPT ![self] = prepareSig[self] \union {sig[self]}]
                              /\ state' = [state EXCEPT ![self] = 1]
                              /\ PrintT(prepareSig')
                              /\ /\ inputType_b' = [inputType_b EXCEPT ![self] = "prepareMsg"]
                                 /\ sender_b' = [sender_b EXCEPT ![self] = self]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcast",
                                                                          pc        |->  "Fsm",
                                                                          sender_b  |->  sender_b[self],
                                                                          inputType_b |->  inputType_b[self] ] >>
                                                                      \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "Broadcast1"]
                              /\ UNCHANGED <<commitSig, validatorChain, consensus>>
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
                              /\ UNCHANGED <<prepareSig, blockCache, validatorChain, consensus>>
                           \/ /\ state[self] = 2
                              /\ commitCertificate(self)
                              /\ state' = [state EXCEPT ![self] = 9]
                              /\ consensus' = [consensus EXCEPT ![self] = TRUE]
                              /\ validatorChain' = [validatorChain EXCEPT ![self] = Append(validatorChain[self], blockCache[self])]
                              /\ /\ inputType_b' = [inputType_b EXCEPT ![self] = "validateMsg"]
                                 /\ sender_b' = [sender_b EXCEPT ![self] = self]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcast",
                                                                          pc        |->  "BroadcastAll",
                                                                          sender_b  |->  sender_b[self],
                                                                          inputType_b |->  inputType_b[self] ] >>
                                                                      \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "Broadcast1"]
                              /\ UNCHANGED <<prepareSig, commitSig, blockCache>>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << state, prepareSig, commitSig,
                                        blockCache, validatorChain, stack,
                                        sender_b, inputType_b, consensus >>
             /\ UNCHANGED << proposers, validators, possibleHeights, sig,
                             predeterminedBlockHeight, impeachPrepareSig,
                             impeachCommitSig, blockReceiver,
                             validatorBlockHeight, proposerBlockHeight,
                             proposerChain, receiver, inputType_, sender_,
                             sender, inputType, block, height >>

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
                      /\ UNCHANGED << proposers, validators, possibleHeights,
                                      sig, predeterminedBlockHeight, state,
                                      prepareSig, commitSig, impeachPrepareSig,
                                      impeachCommitSig, blockCache,
                                      blockReceiver, validatorBlockHeight,
                                      proposerBlockHeight, validatorChain,
                                      proposerChain, receiver, inputType_,
                                      sender_, sender_b, inputType_b,
                                      consensus >>

HeightAugmentation(self) == /\ pc[self] = "HeightAugmentation"
                            /\ validatorBlockHeight' = [validatorBlockHeight EXCEPT ![self] = validatorBlockHeight[self]+1]
                            /\ pc' = [pc EXCEPT ![self] = "Fsm"]
                            /\ UNCHANGED << proposers, validators,
                                            possibleHeights, sig,
                                            predeterminedBlockHeight, state,
                                            prepareSig, commitSig,
                                            impeachPrepareSig,
                                            impeachCommitSig, blockCache,
                                            blockReceiver, proposerBlockHeight,
                                            validatorChain, proposerChain,
                                            stack, receiver, inputType_,
                                            sender_, sender_b, inputType_b,
                                            sender, inputType, block, height,
                                            consensus >>

validator(self) == Fsm(self) \/ BroadcastAll(self)
                      \/ HeightAugmentation(self)

Proposer(self) == /\ pc[self] = "Proposer"
                  /\ proposerBlockHeight[self] = predeterminedBlockHeight[self]
                  /\ pc' = [pc EXCEPT ![self] = "SendBlock1"]
                  /\ UNCHANGED << proposers, validators, possibleHeights, sig,
                                  predeterminedBlockHeight, state, prepareSig,
                                  commitSig, impeachPrepareSig,
                                  impeachCommitSig, blockCache, blockReceiver,
                                  validatorBlockHeight, proposerBlockHeight,
                                  validatorChain, proposerChain, stack,
                                  receiver, inputType_, sender_, sender_b,
                                  inputType_b, sender, inputType, block,
                                  height, consensus >>

SendBlock1(self) == /\ pc[self] = "SendBlock1"
                    /\ blockReceiver' = [blockReceiver EXCEPT !["v1"] = self]
                    /\ pc' = [pc EXCEPT ![self] = "SendBlock2"]
                    /\ UNCHANGED << proposers, validators, possibleHeights,
                                    sig, predeterminedBlockHeight, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, blockCache,
                                    validatorBlockHeight, proposerBlockHeight,
                                    validatorChain, proposerChain, stack,
                                    receiver, inputType_, sender_, sender_b,
                                    inputType_b, sender, inputType, block,
                                    height, consensus >>

SendBlock2(self) == /\ pc[self] = "SendBlock2"
                    /\ blockReceiver' = [blockReceiver EXCEPT !["v2"] = self]
                    /\ pc' = [pc EXCEPT ![self] = "SendBlock3"]
                    /\ UNCHANGED << proposers, validators, possibleHeights,
                                    sig, predeterminedBlockHeight, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, blockCache,
                                    validatorBlockHeight, proposerBlockHeight,
                                    validatorChain, proposerChain, stack,
                                    receiver, inputType_, sender_, sender_b,
                                    inputType_b, sender, inputType, block,
                                    height, consensus >>

SendBlock3(self) == /\ pc[self] = "SendBlock3"
                    /\ blockReceiver' = [blockReceiver EXCEPT !["v3"] = self]
                    /\ pc' = [pc EXCEPT ![self] = "SendBlock4"]
                    /\ UNCHANGED << proposers, validators, possibleHeights,
                                    sig, predeterminedBlockHeight, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, blockCache,
                                    validatorBlockHeight, proposerBlockHeight,
                                    validatorChain, proposerChain, stack,
                                    receiver, inputType_, sender_, sender_b,
                                    inputType_b, sender, inputType, block,
                                    height, consensus >>

SendBlock4(self) == /\ pc[self] = "SendBlock4"
                    /\ blockReceiver' = [blockReceiver EXCEPT !["v4"] = self]
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << proposers, validators, possibleHeights,
                                    sig, predeterminedBlockHeight, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, blockCache,
                                    validatorBlockHeight, proposerBlockHeight,
                                    validatorChain, proposerChain, stack,
                                    receiver, inputType_, sender_, sender_b,
                                    inputType_b, sender, inputType, block,
                                    height, consensus >>

proposer(self) == Proposer(self) \/ SendBlock1(self) \/ SendBlock2(self)
                     \/ SendBlock3(self) \/ SendBlock4(self)

Next == (\E self \in ProcSet:  \/ addSig(self) \/ foreverLoop(self)
                               \/ broadcast(self) \/ broadcastAll(self))
           \/ (\E self \in validators: validator(self))
           \/ (\E self \in proposers: proposer(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Jul 23 15:12:09 CST 2019 by Dell
\* Created Mon Jul 22 15:23:05 CST 2019 by Dell
