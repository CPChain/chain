------------------------------- MODULE lbft3 -------------------------------


EXTENDS Integers, Sequences, FiniteSets, TLC


(*
--algorithm lbft3
variables
    proposers = <<"p1","p2">>,
    \* sequence of proposers
    validators = {"v1","v2","v3","v4"},
    sig = [v1|->1,v2|->2,v3|->3,v4|->4],
    state = [va \in validators |-> 0],
    prepareSig = [va \in validators |->{}],
    commitSig = [va \in validators |->{}],
    impeachPrepareSig = [va \in validators |->{}],
    impeachCommitSig = [va \in validators |->{}],
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
\*    GetToNextHeight ==
\*        validators[1].state /=9 \/
\*        validators[2].state /=9 \/
\*        validators[3].state /=9 \/
\*        validators[4].state /=9
\*

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

process validator \in validators
variables consensus = FALSE;
begin
Fsm:
    while ~consensus do
        either \* idle state
            \* transfer to prepare state given a block
            await state[self] = 0;
            prepareSig[self] := prepareSig[self] \union {sig[self]};
            state[self] := 1;
            \* print prepareSig;
            call broadcast(self, "prepareMsg");

        or  \* prepare state
            \* states of both v and input should be prepare state
            await state[self] = 1;
            await prepareCertificate(self);
            \* transfer to commit state if collect a certificate
            commitSig[self] := commitSig[self] \union {sig[self]};
            state[self] := 2;
            print commitSig;
            call broadcast(self,"commitMsg");

        or  \* commit state
            \* states of both v and input should be commit state
            await state[self] = 2;
            await commitCertificate(self);
            \* transfer to idle state in next height given the certificate
            state[self] := 9;
            consensus := TRUE;
            call broadcast(self,"validateMsg");
        or
            skip;
        end either;
    end while;
end process




end algorithm;*)
\* BEGIN TRANSLATION
\* Parameter inputType of procedure addSig at line 59 col 28 changed to inputType_
\* Parameter sender of procedure addSig at line 59 col 39 changed to sender_
CONSTANT defaultInitValue
VARIABLES proposers, validators, sig, state, prepareSig, commitSig,
          impeachPrepareSig, impeachCommitSig, pc, stack

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

VARIABLES receiver, inputType_, sender_, sender, inputType, consensus

vars == << proposers, validators, sig, state, prepareSig, commitSig,
           impeachPrepareSig, impeachCommitSig, pc, stack, receiver,
           inputType_, sender_, sender, inputType, consensus >>

ProcSet == (validators)

Init == (* Global variables *)
        /\ proposers = <<"p1","p2">>
        /\ validators = {"v1","v2","v3","v4"}
        /\ sig = [v1|->1,v2|->2,v3|->3,v4|->4]
        /\ state = [va \in validators |-> 0]
        /\ prepareSig = [va \in validators |->{}]
        /\ commitSig = [va \in validators |->{}]
        /\ impeachPrepareSig = [va \in validators |->{}]
        /\ impeachCommitSig = [va \in validators |->{}]
        (* Procedure addSig *)
        /\ receiver = [ self \in ProcSet |-> defaultInitValue]
        /\ inputType_ = [ self \in ProcSet |-> defaultInitValue]
        /\ sender_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure broadcast *)
        /\ sender = [ self \in ProcSet |-> defaultInitValue]
        /\ inputType = [ self \in ProcSet |-> defaultInitValue]
        (* Process validator *)
        /\ consensus = [self \in validators |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Fsm"]

PrepareMsg(self) == /\ pc[self] = "PrepareMsg"
                    /\ IF inputType_[self] = "prepareMsg"
                          THEN /\ prepareSig' = [prepareSig EXCEPT ![receiver[self]] = prepareSig[receiver[self]] \union prepareSig[sender_[self]]]
                          ELSE /\ TRUE
                               /\ UNCHANGED prepareSig
                    /\ pc' = [pc EXCEPT ![self] = "CommitMsg"]
                    /\ UNCHANGED << proposers, validators, sig, state,
                                    commitSig, impeachPrepareSig,
                                    impeachCommitSig, stack, receiver,
                                    inputType_, sender_, sender, inputType,
                                    consensus >>

CommitMsg(self) == /\ pc[self] = "CommitMsg"
                   /\ IF inputType_[self] = "commitMsg"
                         THEN /\ prepareSig' = [prepareSig EXCEPT ![receiver[self]] = prepareSig[receiver[self]] \union prepareSig[sender_[self]]]
                              /\ commitSig' = [commitSig EXCEPT ![receiver[self]] = commitSig[receiver[self]] \union commitSig[sender_[self]]]
                         ELSE /\ TRUE
                              /\ UNCHANGED << prepareSig, commitSig >>
                   /\ pc' = [pc EXCEPT ![self] = "ValidateMsg"]
                   /\ UNCHANGED << proposers, validators, sig, state,
                                   impeachPrepareSig, impeachCommitSig, stack,
                                   receiver, inputType_, sender_, sender,
                                   inputType, consensus >>

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
                     /\ UNCHANGED << proposers, validators, sig, state,
                                     impeachPrepareSig, impeachCommitSig,
                                     sender, inputType, consensus >>

addSig(self) == PrepareMsg(self) \/ CommitMsg(self) \/ ValidateMsg(self)

Forever(self) == /\ pc[self] = "Forever"
                 /\ state["v1"] = 9
                 /\ pc' = [pc EXCEPT ![self] = "Error"]
                 /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                                 commitSig, impeachPrepareSig,
                                 impeachCommitSig, stack, receiver, inputType_,
                                 sender_, sender, inputType, consensus >>

foreverLoop(self) == Forever(self)

Broadcast1(self) == /\ pc[self] = "Broadcast1"
                    /\ /\ inputType_' = [inputType_ EXCEPT ![self] = inputType[self]]
                       /\ receiver' = [receiver EXCEPT ![self] = "v1"]
                       /\ sender_' = [sender_ EXCEPT ![self] = sender[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "addSig",
                                                                pc        |->  "Broadcast2",
                                                                receiver  |->  receiver[self],
                                                                inputType_ |->  inputType_[self],
                                                                sender_   |->  sender_[self] ] >>
                                                            \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "PrepareMsg"]
                    /\ UNCHANGED << proposers, validators, sig, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, sender, inputType,
                                    consensus >>

Broadcast2(self) == /\ pc[self] = "Broadcast2"
                    /\ /\ inputType_' = [inputType_ EXCEPT ![self] = inputType[self]]
                       /\ receiver' = [receiver EXCEPT ![self] = "v2"]
                       /\ sender_' = [sender_ EXCEPT ![self] = sender[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "addSig",
                                                                pc        |->  "Broadcast3",
                                                                receiver  |->  receiver[self],
                                                                inputType_ |->  inputType_[self],
                                                                sender_   |->  sender_[self] ] >>
                                                            \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "PrepareMsg"]
                    /\ UNCHANGED << proposers, validators, sig, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, sender, inputType,
                                    consensus >>

Broadcast3(self) == /\ pc[self] = "Broadcast3"
                    /\ /\ inputType_' = [inputType_ EXCEPT ![self] = inputType[self]]
                       /\ receiver' = [receiver EXCEPT ![self] = "v3"]
                       /\ sender_' = [sender_ EXCEPT ![self] = sender[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "addSig",
                                                                pc        |->  "Broadcast4",
                                                                receiver  |->  receiver[self],
                                                                inputType_ |->  inputType_[self],
                                                                sender_   |->  sender_[self] ] >>
                                                            \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "PrepareMsg"]
                    /\ UNCHANGED << proposers, validators, sig, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, sender, inputType,
                                    consensus >>

Broadcast4(self) == /\ pc[self] = "Broadcast4"
                    /\ /\ inputType_' = [inputType_ EXCEPT ![self] = inputType[self]]
                       /\ receiver' = [receiver EXCEPT ![self] = "v4"]
                       /\ sender_' = [sender_ EXCEPT ![self] = sender[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "addSig",
                                                                pc        |->  Head(stack[self]).pc,
                                                                receiver  |->  receiver[self],
                                                                inputType_ |->  inputType_[self],
                                                                sender_   |->  sender_[self] ] >>
                                                            \o Tail(stack[self])]
                    /\ pc' = [pc EXCEPT ![self] = "PrepareMsg"]
                    /\ UNCHANGED << proposers, validators, sig, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, sender, inputType,
                                    consensus >>

broadcast(self) == Broadcast1(self) \/ Broadcast2(self) \/ Broadcast3(self)
                      \/ Broadcast4(self)

Fsm(self) == /\ pc[self] = "Fsm"
             /\ IF ~consensus[self]
                   THEN /\ \/ /\ state[self] = 0
                              /\ prepareSig' = [prepareSig EXCEPT ![self] = prepareSig[self] \union {sig[self]}]
                              /\ state' = [state EXCEPT ![self] = 1]
                              /\ /\ inputType' = [inputType EXCEPT ![self] = "prepareMsg"]
                                 /\ sender' = [sender EXCEPT ![self] = self]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcast",
                                                                          pc        |->  "Fsm",
                                                                          sender    |->  sender[self],
                                                                          inputType |->  inputType[self] ] >>
                                                                      \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "Broadcast1"]
                              /\ UNCHANGED <<commitSig, consensus>>
                           \/ /\ state[self] = 1
                              /\ prepareCertificate(self)
                              /\ commitSig' = [commitSig EXCEPT ![self] = commitSig[self] \union {sig[self]}]
                              /\ state' = [state EXCEPT ![self] = 2]
                              /\ PrintT(commitSig')
                              /\ /\ inputType' = [inputType EXCEPT ![self] = "commitMsg"]
                                 /\ sender' = [sender EXCEPT ![self] = self]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcast",
                                                                          pc        |->  "Fsm",
                                                                          sender    |->  sender[self],
                                                                          inputType |->  inputType[self] ] >>
                                                                      \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "Broadcast1"]
                              /\ UNCHANGED <<prepareSig, consensus>>
                           \/ /\ state[self] = 2
                              /\ commitCertificate(self)
                              /\ state' = [state EXCEPT ![self] = 9]
                              /\ consensus' = [consensus EXCEPT ![self] = TRUE]
                              /\ /\ inputType' = [inputType EXCEPT ![self] = "validateMsg"]
                                 /\ sender' = [sender EXCEPT ![self] = self]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcast",
                                                                          pc        |->  "Fsm",
                                                                          sender    |->  sender[self],
                                                                          inputType |->  inputType[self] ] >>
                                                                      \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "Broadcast1"]
                              /\ UNCHANGED <<prepareSig, commitSig>>
                           \/ /\ TRUE
                              /\ pc' = [pc EXCEPT ![self] = "Fsm"]
                              /\ UNCHANGED <<state, prepareSig, commitSig, stack, sender, inputType, consensus>>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << state, prepareSig, commitSig, stack,
                                        sender, inputType, consensus >>
             /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                             impeachCommitSig, receiver, inputType_, sender_ >>

validator(self) == Fsm(self)

Next == (\E self \in ProcSet:  \/ addSig(self) \/ foreverLoop(self)
                               \/ broadcast(self))
           \/ (\E self \in validators: validator(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
