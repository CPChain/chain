------------------------------- MODULE lbft2 -------------------------------

EXTENDS Integers, Sequences, FiniteSets


(*
--algorithm lbft2
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
    validatorState1 == state["v1"] /= 2
    validatorState4 == state["v4"] /= 2
    \* GoToNextHeight is violated when all validators have advanced to next block height
\*    GetToNextHeight ==
\*        validators[1].state /=9 \/
\*        validators[2].state /=9 \/
\*        validators[3].state /=9 \/
\*        validators[4].state /=9
\*

end define;


procedure fsm(v, inputType, input) begin
Fsm:
    either \* idle state
        \* transfer to prepare state given a block
        await state[v] = 0;
        await inputType = "block";
        prepareSig[v] := {sig[v]};
        state[v] := 1;

    or  \* prepare state
        \* states of both v and input should be prepare state
        await state[v] = 1;
        await inputType = "prepareMsg" \/ inputType = "commitMsg";
        await state[input] = 1 \/ state[input] = 2;
        \* accumulate prepare signatures
        prepareSig[v] := prepareSig[v] \union prepareSig[input];
        if prepareCertificate(v)
        then
        \* transfer to commit state if collect a certificate
\*            v.prepareSig := {};
            commitSig[v] := {sig[v]};
            state[v] := 2;
        end if;

    or  \* commit state
        \* states of both v and input should be commit state
        await state[v] = 2;
        await inputType = "commitMsg";
        await state[input] = 2;
        \* accumulate commit signatures
        commitSig[v] := commitSig[v] \union commitSig[input];
        if commitCertificate(v)
        then
        \* transfer to idle state in next height given the certificate
\*            v.commitSig := {};
            state[v] := 9;
        end if;
    or  \* the case of receiving validate message
        await inputType = "validateMsg";
        await state[input] = 9;
        \* a validate message has at least 3 commit signatures
        commitSig[v] := commitSig[v] \union commitSig[input];
        if commitCertificate(v)
        then
        \* transfer to idle state in next height given the certificate
            state[v] := 9;
        end if;
    or
        \* await state[v] = 9;
        skip;
    end either;
    return;
end procedure;

\*macro broadcast2(sender, inputType) begin
\*    \* otherValidators := validatorIndices \ {number};
\*
\*        fsm("v1",inputType,sender);
\*        fsm("v2",inputType,sender);
\*        fsm("v3",inputType,sender);
\*        fsm("v4",inputType,sender);
\*end macro;

procedure foreverLoop() begin
Forever:
    await state["v1"] = 9;
end procedure

procedure broadcast(sender, inputType) begin
    \* otherValidators := validatorIndices \ {number};
\*    while \E receiver \in validators \ {sender}: state[receiver] = 0 \/ state[receiver] = 1 do
\*        receiver := CHOOSE x \in validators \ {sender}: state[x] = 0 \/ state[x] = 1;
\*        fsm(receiver, inputType, sender);
\*    end while;
\*\*    with receiver \in (validators \ {sender}) do
\*\*        \* skip;
\*\*        fsm(receiver, inputType, sender);
Broadcast1:
        call fsm("v1",inputType,sender);
Broadcast2:
        call fsm("v2",inputType,sender);
Broadcast3:
        call fsm("v3",inputType,sender);
Broadcast4:
        call fsm("v4",inputType,sender);
\*    end with;
    return;
end procedure;

process validator \in validators
begin
Idle:
    call fsm(self,"block","");
Prepare:
    call broadcast(self, "prepareMsg");
Commit:
    call broadcast(self, "commitMsg");
Validate:
    call broadcast(self, "validateMsg");
end process

\*begin
\*    \* all validators receive the block message
\*    fsm("v1", "block", "");
\*    fsm("v2", "block", "");
\*    fsm("v3", "block", "");
\*    fsm("v4", "block", "");
\*
\*    \* broadcast prepare message
\*    call broadcast("v1","prepareMsg");
\*    call broadcast("v2","prepareMsg");
\*    call broadcast("v3","prepareMsg");
\*    call broadcast("v4","prepareMsg");

\*    call foreverLoop()

\*    broadcast2("v1","prepareMsg");
\*    broadcast2("v2","prepareMsg");
\*    broadcast2("v3","prepareMsg");
\*    broadcast2("v4","prepareMsg");
\*
\*
    \* broadcast commit message
\*    call broadcast("v1","commitMsg");
\*    call broadcast("v2","commitMsg");
\*    call broadcast("v3","commitMsg");
\*    call broadcast("v4","commitMsg");
\*\*
\*    \* broadcast validate message
\*    call broadcast("v1","validateMsg");
\*    call broadcast("v2","validateMsg");
\*    call broadcast("v3","validateMsg");
\*    call broadcast("v4","validateMsg");
\*




end algorithm;*)


\* BEGIN TRANSLATION
\* Parameter inputType of procedure fsm at line 59 col 18 changed to inputType_
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
validatorState1 == state["v1"] /= 2
validatorState4 == state["v4"] /= 2

VARIABLES v, inputType_, input, sender, inputType

vars == << proposers, validators, sig, state, prepareSig, commitSig,
           impeachPrepareSig, impeachCommitSig, pc, stack, v, inputType_,
           input, sender, inputType >>

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
        (* Procedure fsm *)
        /\ v = [ self \in ProcSet |-> defaultInitValue]
        /\ inputType_ = [ self \in ProcSet |-> defaultInitValue]
        /\ input = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure broadcast *)
        /\ sender = [ self \in ProcSet |-> defaultInitValue]
        /\ inputType = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Idle"]

Fsm(self) == /\ pc[self] = "Fsm"
             /\ \/ /\ state[v[self]] = 0
                   /\ inputType_[self] = "block"
                   /\ prepareSig' = [prepareSig EXCEPT ![v[self]] = {sig[v[self]]}]
                   /\ state' = [state EXCEPT ![v[self]] = 1]
                   /\ UNCHANGED commitSig
                \/ /\ state[v[self]] = 1
                   /\ inputType_[self] = "prepareMsg" \/ inputType_[self] = "commitMsg"
                   /\ state[input[self]] = 1 \/ state[input[self]] = 2
                   /\ prepareSig' = [prepareSig EXCEPT ![v[self]] = prepareSig[v[self]] \union prepareSig[input[self]]]
                   /\ IF prepareCertificate(v[self])
                         THEN /\ commitSig' = [commitSig EXCEPT ![v[self]] = {sig[v[self]]}]
                              /\ state' = [state EXCEPT ![v[self]] = 2]
                         ELSE /\ TRUE
                              /\ UNCHANGED << state, commitSig >>
                \/ /\ state[v[self]] = 2
                   /\ inputType_[self] = "commitMsg"
                   /\ state[input[self]] = 2
                   /\ commitSig' = [commitSig EXCEPT ![v[self]] = commitSig[v[self]] \union commitSig[input[self]]]
                   /\ IF commitCertificate(v[self])
                         THEN /\ state' = [state EXCEPT ![v[self]] = 9]
                         ELSE /\ TRUE
                              /\ state' = state
                   /\ UNCHANGED prepareSig
                \/ /\ inputType_[self] = "validateMsg"
                   /\ state[input[self]] = 9
                   /\ commitSig' = [commitSig EXCEPT ![v[self]] = commitSig[v[self]] \union commitSig[input[self]]]
                   /\ IF commitCertificate(v[self])
                         THEN /\ state' = [state EXCEPT ![v[self]] = 9]
                         ELSE /\ TRUE
                              /\ state' = state
                   /\ UNCHANGED prepareSig
                \/ /\ TRUE
                   /\ UNCHANGED <<state, prepareSig, commitSig>>
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ v' = [v EXCEPT ![self] = Head(stack[self]).v]
             /\ inputType_' = [inputType_ EXCEPT ![self] = Head(stack[self]).inputType_]
             /\ input' = [input EXCEPT ![self] = Head(stack[self]).input]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                             impeachCommitSig, sender, inputType >>

fsm(self) == Fsm(self)

Forever(self) == /\ pc[self] = "Forever"
                 /\ state["v1"] = 9
                 /\ pc' = [pc EXCEPT ![self] = "Error"]
                 /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                                 commitSig, impeachPrepareSig,
                                 impeachCommitSig, stack, v, inputType_, input,
                                 sender, inputType >>

foreverLoop(self) == Forever(self)

Broadcast1(self) == /\ pc[self] = "Broadcast1"
                    /\ /\ input' = [input EXCEPT ![self] = sender[self]]
                       /\ inputType_' = [inputType_ EXCEPT ![self] = inputType[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "fsm",
                                                                pc        |->  "Broadcast2",
                                                                v         |->  v[self],
                                                                inputType_ |->  inputType_[self],
                                                                input     |->  input[self] ] >>
                                                            \o stack[self]]
                       /\ v' = [v EXCEPT ![self] = "v1"]
                    /\ pc' = [pc EXCEPT ![self] = "Fsm"]
                    /\ UNCHANGED << proposers, validators, sig, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, sender, inputType >>

Broadcast2(self) == /\ pc[self] = "Broadcast2"
                    /\ /\ input' = [input EXCEPT ![self] = sender[self]]
                       /\ inputType_' = [inputType_ EXCEPT ![self] = inputType[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "fsm",
                                                                pc        |->  "Broadcast3",
                                                                v         |->  v[self],
                                                                inputType_ |->  inputType_[self],
                                                                input     |->  input[self] ] >>
                                                            \o stack[self]]
                       /\ v' = [v EXCEPT ![self] = "v2"]
                    /\ pc' = [pc EXCEPT ![self] = "Fsm"]
                    /\ UNCHANGED << proposers, validators, sig, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, sender, inputType >>

Broadcast3(self) == /\ pc[self] = "Broadcast3"
                    /\ /\ input' = [input EXCEPT ![self] = sender[self]]
                       /\ inputType_' = [inputType_ EXCEPT ![self] = inputType[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "fsm",
                                                                pc        |->  "Broadcast4",
                                                                v         |->  v[self],
                                                                inputType_ |->  inputType_[self],
                                                                input     |->  input[self] ] >>
                                                            \o stack[self]]
                       /\ v' = [v EXCEPT ![self] = "v3"]
                    /\ pc' = [pc EXCEPT ![self] = "Fsm"]
                    /\ UNCHANGED << proposers, validators, sig, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, sender, inputType >>

Broadcast4(self) == /\ pc[self] = "Broadcast4"
                    /\ /\ input' = [input EXCEPT ![self] = sender[self]]
                       /\ inputType_' = [inputType_ EXCEPT ![self] = inputType[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "fsm",
                                                                pc        |->  Head(stack[self]).pc,
                                                                v         |->  v[self],
                                                                inputType_ |->  inputType_[self],
                                                                input     |->  input[self] ] >>
                                                            \o Tail(stack[self])]
                       /\ v' = [v EXCEPT ![self] = "v4"]
                    /\ pc' = [pc EXCEPT ![self] = "Fsm"]
                    /\ UNCHANGED << proposers, validators, sig, state,
                                    prepareSig, commitSig, impeachPrepareSig,
                                    impeachCommitSig, sender, inputType >>

broadcast(self) == Broadcast1(self) \/ Broadcast2(self) \/ Broadcast3(self)
                      \/ Broadcast4(self)

Idle(self) == /\ pc[self] = "Idle"
              /\ /\ input' = [input EXCEPT ![self] = ""]
                 /\ inputType_' = [inputType_ EXCEPT ![self] = "block"]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "fsm",
                                                          pc        |->  "Prepare",
                                                          v         |->  v[self],
                                                          inputType_ |->  inputType_[self],
                                                          input     |->  input[self] ] >>
                                                      \o stack[self]]
                 /\ v' = [v EXCEPT ![self] = self]
              /\ pc' = [pc EXCEPT ![self] = "Fsm"]
              /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                              commitSig, impeachPrepareSig, impeachCommitSig,
                              sender, inputType >>

Prepare(self) == /\ pc[self] = "Prepare"
                 /\ /\ inputType' = [inputType EXCEPT ![self] = "prepareMsg"]
                    /\ sender' = [sender EXCEPT ![self] = self]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcast",
                                                             pc        |->  "Commit",
                                                             sender    |->  sender[self],
                                                             inputType |->  inputType[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Broadcast1"]
                 /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                                 commitSig, impeachPrepareSig,
                                 impeachCommitSig, v, inputType_, input >>

Commit(self) == /\ pc[self] = "Commit"
                /\ /\ inputType' = [inputType EXCEPT ![self] = "commitMsg"]
                   /\ sender' = [sender EXCEPT ![self] = self]
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcast",
                                                            pc        |->  "Validate",
                                                            sender    |->  sender[self],
                                                            inputType |->  inputType[self] ] >>
                                                        \o stack[self]]
                /\ pc' = [pc EXCEPT ![self] = "Broadcast1"]
                /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                                commitSig, impeachPrepareSig, impeachCommitSig,
                                v, inputType_, input >>

Validate(self) == /\ pc[self] = "Validate"
                  /\ /\ inputType' = [inputType EXCEPT ![self] = "validateMsg"]
                     /\ sender' = [sender EXCEPT ![self] = self]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "broadcast",
                                                              pc        |->  "Done",
                                                              sender    |->  sender[self],
                                                              inputType |->  inputType[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "Broadcast1"]
                  /\ UNCHANGED << proposers, validators, sig, state,
                                  prepareSig, commitSig, impeachPrepareSig,
                                  impeachCommitSig, v, inputType_, input >>

validator(self) == Idle(self) \/ Prepare(self) \/ Commit(self)
                      \/ Validate(self)

Next == (\E self \in ProcSet:  \/ fsm(self) \/ foreverLoop(self)
                               \/ broadcast(self))
           \/ (\E self \in validators: validator(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu Jul 18 17:48:27 CST 2019 by Dell
\* Created Tue Jul 16 19:39:20 CST 2019 by Dell
