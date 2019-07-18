------------------------------- MODULE lbft2 -------------------------------

EXTENDS Integers, Sequences, FiniteSets


(*
--algorithm lbft2
variables
    proposers = <<"p1","p2">>,
    \* sequence of proposers
    validators = {"v1","v2","v3","v4"},
    sig = [v1|->1,v2|->2,v3|->3,v4|->4],
    state = [v \in validators |-> 0],
    prepareSig = [v \in validators |->{}],
    commitSig = [v \in validators |->{}],
    impeachPrepareSig = [v \in validators |->{}],
    impeachCommitSig = [v \in validators |->{}],
    \* sequence of validators
    \* 0,1,2 represent idle, prepare, commit
    \* 3,4 represent impeach prepare and impeach commit state
    \* 9 represents a consensus of normal case
    \* imp represents impeachment
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


macro fsm(v, inputType, input) begin
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
        await input.state = 9;
        \* a validate message has at least 3 commit signatures
        commitSig[v] := commitSig[v] \union commitSig[input];
        if commitCertificate(v)
        then
        \* transfer to idle state in next height given the certificate
            state[v] := 9;
        end if;
\*    or
\*        await state[v] = 9;
\*        skip;
    end either;
end macro;

macro broadcast2(sender, inputType) begin
    \* otherValidators := validatorIndices \ {number};

        fsm("v1",inputType,sender);
        fsm("v2",inputType,sender);
        fsm("v3",inputType,sender);
        fsm("v4",inputType,sender);
end macro;

procedure foreverLoop() begin
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
        fsm("v1",inputType,sender);
        fsm("v2",inputType,sender);
        fsm("v3",inputType,sender);
        fsm("v4",inputType,sender);
\*    end with;
    return;
end procedure;


begin
    \* all validators receive the block message
    fsm("v1", "block", "");
    fsm("v2", "block", "");
    fsm("v3", "block", "");
    fsm("v4", "block", "");

    \* broadcast prepare message
    call broadcast("v1","prepareMsg");
    call broadcast("v2","prepareMsg");
    call broadcast("v3","prepareMsg");
    call broadcast("v4","prepareMsg");

\*    call foreverLoop()

\*    broadcast2("v1","prepareMsg");
\*    broadcast2("v2","prepareMsg");
\*    broadcast2("v3","prepareMsg");
\*    broadcast2("v4","prepareMsg");
\*
\*
    \* broadcast commit message
    call broadcast("v1","commitMsg");
    call broadcast("v2","commitMsg");
    call broadcast("v3","commitMsg");
    call broadcast("v4","commitMsg");
\*
    \* broadcast validate message
    call broadcast("v1","validateMsg");
    call broadcast("v2","validateMsg");
    call broadcast("v3","validateMsg");
    call broadcast("v4","validateMsg");





end algorithm;*)


\* BEGIN TRANSLATION
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

VARIABLES sender, inputType

vars == << proposers, validators, sig, state, prepareSig, commitSig,
           impeachPrepareSig, impeachCommitSig, pc, stack, sender, inputType
        >>

Init == (* Global variables *)
        /\ proposers = <<"p1","p2">>
        /\ validators = {"v1","v2","v3","v4"}
        /\ sig = [v1|->1,v2|->2,v3|->3,v4|->4]
        /\ state = [v \in validators |-> 0]
        /\ prepareSig = [v \in validators |->{}]
        /\ commitSig = [v \in validators |->{}]
        /\ impeachPrepareSig = [v \in validators |->{}]
        /\ impeachCommitSig = [v \in validators |->{}]
        (* Procedure broadcast *)
        /\ sender = defaultInitValue
        /\ inputType = defaultInitValue
        /\ stack = << >>
        /\ pc = "Lbl_13"

Lbl_1 == /\ pc = "Lbl_1"
         /\ state["v1"] = 9
         /\ pc' = "Error"
         /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                         commitSig, impeachPrepareSig, impeachCommitSig, stack,
                         sender, inputType >>

foreverLoop == Lbl_1

Lbl_2 == /\ pc = "Lbl_2"
         /\ \/ /\ state["v1"] = 0
               /\ inputType = "block"
               /\ prepareSig' = [prepareSig EXCEPT !["v1"] = {sig["v1"]}]
               /\ state' = [state EXCEPT !["v1"] = 1]
               /\ UNCHANGED commitSig
            \/ /\ state["v1"] = 1
               /\ inputType = "prepareMsg" \/ inputType = "commitMsg"
               /\ state[sender] = 1 \/ state[sender] = 2
               /\ prepareSig' = [prepareSig EXCEPT !["v1"] = prepareSig["v1"] \union prepareSig[sender]]
               /\ IF prepareCertificate("v1")
                     THEN /\ commitSig' = [commitSig EXCEPT !["v1"] = {sig["v1"]}]
                          /\ state' = [state EXCEPT !["v1"] = 2]
                     ELSE /\ TRUE
                          /\ UNCHANGED << state, commitSig >>
            \/ /\ state["v1"] = 2
               /\ inputType = "commitMsg"
               /\ state[sender] = 2
               /\ commitSig' = [commitSig EXCEPT !["v1"] = commitSig["v1"] \union commitSig[sender]]
               /\ IF commitCertificate("v1")
                     THEN /\ state' = [state EXCEPT !["v1"] = 9]
                     ELSE /\ TRUE
                          /\ state' = state
               /\ UNCHANGED prepareSig
            \/ /\ inputType = "validateMsg"
               /\ sender.state = 9
               /\ commitSig' = [commitSig EXCEPT !["v1"] = commitSig["v1"] \union commitSig[sender]]
               /\ IF commitCertificate("v1")
                     THEN /\ state' = [state EXCEPT !["v1"] = 9]
                     ELSE /\ TRUE
                          /\ state' = state
               /\ UNCHANGED prepareSig
         /\ \/ /\ state'["v2"] = 0
               /\ inputType = "block"
               /\ pc' = "Lbl_3"
            \/ /\ state'["v2"] = 1
               /\ inputType = "prepareMsg" \/ inputType = "commitMsg"
               /\ state'[sender] = 1 \/ state'[sender] = 2
               /\ pc' = "Lbl_4"
            \/ /\ state'["v2"] = 2
               /\ inputType = "commitMsg"
               /\ state'[sender] = 2
               /\ pc' = "Lbl_5"
            \/ /\ inputType = "validateMsg"
               /\ sender.state = 9
               /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, stack, sender, inputType >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ prepareSig' = [prepareSig EXCEPT !["v2"] = {sig["v2"]}]
         /\ state' = [state EXCEPT !["v2"] = 1]
         /\ pc' = "Lbl_7"
         /\ UNCHANGED << proposers, validators, sig, commitSig,
                         impeachPrepareSig, impeachCommitSig, stack, sender,
                         inputType >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ prepareSig' = [prepareSig EXCEPT !["v2"] = prepareSig["v2"] \union prepareSig[sender]]
         /\ IF prepareCertificate("v2")
               THEN /\ commitSig' = [commitSig EXCEPT !["v2"] = {sig["v2"]}]
                    /\ state' = [state EXCEPT !["v2"] = 2]
               ELSE /\ TRUE
                    /\ UNCHANGED << state, commitSig >>
         /\ pc' = "Lbl_7"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, stack, sender, inputType >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig[sender]]
         /\ IF commitCertificate("v2")
               THEN /\ state' = [state EXCEPT !["v2"] = 9]
               ELSE /\ TRUE
                    /\ state' = state
         /\ pc' = "Lbl_7"
         /\ UNCHANGED << proposers, validators, sig, prepareSig,
                         impeachPrepareSig, impeachCommitSig, stack, sender,
                         inputType >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig[sender]]
         /\ IF commitCertificate("v2")
               THEN /\ state' = [state EXCEPT !["v2"] = 9]
               ELSE /\ TRUE
                    /\ state' = state
         /\ pc' = "Lbl_7"
         /\ UNCHANGED << proposers, validators, sig, prepareSig,
                         impeachPrepareSig, impeachCommitSig, stack, sender,
                         inputType >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ \/ /\ state["v3"] = 0
               /\ inputType = "block"
               /\ prepareSig' = [prepareSig EXCEPT !["v3"] = {sig["v3"]}]
               /\ state' = [state EXCEPT !["v3"] = 1]
               /\ UNCHANGED commitSig
            \/ /\ state["v3"] = 1
               /\ inputType = "prepareMsg" \/ inputType = "commitMsg"
               /\ state[sender] = 1 \/ state[sender] = 2
               /\ prepareSig' = [prepareSig EXCEPT !["v3"] = prepareSig["v3"] \union prepareSig[sender]]
               /\ IF prepareCertificate("v3")
                     THEN /\ commitSig' = [commitSig EXCEPT !["v3"] = {sig["v3"]}]
                          /\ state' = [state EXCEPT !["v3"] = 2]
                     ELSE /\ TRUE
                          /\ UNCHANGED << state, commitSig >>
            \/ /\ state["v3"] = 2
               /\ inputType = "commitMsg"
               /\ state[sender] = 2
               /\ commitSig' = [commitSig EXCEPT !["v3"] = commitSig["v3"] \union commitSig[sender]]
               /\ IF commitCertificate("v3")
                     THEN /\ state' = [state EXCEPT !["v3"] = 9]
                     ELSE /\ TRUE
                          /\ state' = state
               /\ UNCHANGED prepareSig
            \/ /\ inputType = "validateMsg"
               /\ sender.state = 9
               /\ commitSig' = [commitSig EXCEPT !["v3"] = commitSig["v3"] \union commitSig[sender]]
               /\ IF commitCertificate("v3")
                     THEN /\ state' = [state EXCEPT !["v3"] = 9]
                     ELSE /\ TRUE
                          /\ state' = state
               /\ UNCHANGED prepareSig
         /\ \/ /\ state'["v4"] = 0
               /\ inputType = "block"
               /\ pc' = "Lbl_8"
            \/ /\ state'["v4"] = 1
               /\ inputType = "prepareMsg" \/ inputType = "commitMsg"
               /\ state'[sender] = 1 \/ state'[sender] = 2
               /\ pc' = "Lbl_9"
            \/ /\ state'["v4"] = 2
               /\ inputType = "commitMsg"
               /\ state'[sender] = 2
               /\ pc' = "Lbl_10"
            \/ /\ inputType = "validateMsg"
               /\ sender.state = 9
               /\ pc' = "Lbl_11"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, stack, sender, inputType >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ prepareSig' = [prepareSig EXCEPT !["v4"] = {sig["v4"]}]
         /\ state' = [state EXCEPT !["v4"] = 1]
         /\ pc' = "Lbl_12"
         /\ UNCHANGED << proposers, validators, sig, commitSig,
                         impeachPrepareSig, impeachCommitSig, stack, sender,
                         inputType >>

Lbl_9 == /\ pc = "Lbl_9"
         /\ prepareSig' = [prepareSig EXCEPT !["v4"] = prepareSig["v4"] \union prepareSig[sender]]
         /\ IF prepareCertificate("v4")
               THEN /\ commitSig' = [commitSig EXCEPT !["v4"] = {sig["v4"]}]
                    /\ state' = [state EXCEPT !["v4"] = 2]
               ELSE /\ TRUE
                    /\ UNCHANGED << state, commitSig >>
         /\ pc' = "Lbl_12"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, stack, sender, inputType >>

Lbl_10 == /\ pc = "Lbl_10"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig[sender]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_12"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_11 == /\ pc = "Lbl_11"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig[sender]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_12"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_12 == /\ pc = "Lbl_12"
          /\ pc' = Head(stack).pc
          /\ sender' = Head(stack).sender
          /\ inputType' = Head(stack).inputType
          /\ stack' = Tail(stack)
          /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                          commitSig, impeachPrepareSig, impeachCommitSig >>

broadcast == Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_6 \/ Lbl_7 \/ Lbl_8
                \/ Lbl_9 \/ Lbl_10 \/ Lbl_11 \/ Lbl_12

Lbl_13 == /\ pc = "Lbl_13"
          /\ \/ /\ state["v1"] = 0
                /\ "block" = "block"
                /\ prepareSig' = [prepareSig EXCEPT !["v1"] = {sig["v1"]}]
                /\ state' = [state EXCEPT !["v1"] = 1]
                /\ UNCHANGED commitSig
             \/ /\ state["v1"] = 1
                /\ "block" = "prepareMsg" \/ "block" = "commitMsg"
                /\ state[""] = 1 \/ state[""] = 2
                /\ prepareSig' = [prepareSig EXCEPT !["v1"] = prepareSig["v1"] \union prepareSig[""]]
                /\ IF prepareCertificate("v1")
                      THEN /\ commitSig' = [commitSig EXCEPT !["v1"] = {sig["v1"]}]
                           /\ state' = [state EXCEPT !["v1"] = 2]
                      ELSE /\ TRUE
                           /\ UNCHANGED << state, commitSig >>
             \/ /\ state["v1"] = 2
                /\ "block" = "commitMsg"
                /\ state[""] = 2
                /\ commitSig' = [commitSig EXCEPT !["v1"] = commitSig["v1"] \union commitSig[""]]
                /\ IF commitCertificate("v1")
                      THEN /\ state' = [state EXCEPT !["v1"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ "block" = "validateMsg"
                /\ "".state = 9
                /\ commitSig' = [commitSig EXCEPT !["v1"] = commitSig["v1"] \union commitSig[""]]
                /\ IF commitCertificate("v1")
                      THEN /\ state' = [state EXCEPT !["v1"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
          /\ \/ /\ state'["v2"] = 0
                /\ "block" = "block"
                /\ pc' = "Lbl_14"
             \/ /\ state'["v2"] = 1
                /\ "block" = "prepareMsg" \/ "block" = "commitMsg"
                /\ state'[""] = 1 \/ state'[""] = 2
                /\ pc' = "Lbl_15"
             \/ /\ state'["v2"] = 2
                /\ "block" = "commitMsg"
                /\ state'[""] = 2
                /\ pc' = "Lbl_16"
             \/ /\ "block" = "validateMsg"
                /\ "".state = 9
                /\ pc' = "Lbl_17"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_14 == /\ pc = "Lbl_14"
          /\ prepareSig' = [prepareSig EXCEPT !["v2"] = {sig["v2"]}]
          /\ state' = [state EXCEPT !["v2"] = 1]
          /\ pc' = "Lbl_18"
          /\ UNCHANGED << proposers, validators, sig, commitSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_15 == /\ pc = "Lbl_15"
          /\ prepareSig' = [prepareSig EXCEPT !["v2"] = prepareSig["v2"] \union prepareSig[""]]
          /\ IF prepareCertificate("v2")
                THEN /\ commitSig' = [commitSig EXCEPT !["v2"] = {sig["v2"]}]
                     /\ state' = [state EXCEPT !["v2"] = 2]
                ELSE /\ TRUE
                     /\ UNCHANGED << state, commitSig >>
          /\ pc' = "Lbl_18"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_16 == /\ pc = "Lbl_16"
          /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig[""]]
          /\ IF commitCertificate("v2")
                THEN /\ state' = [state EXCEPT !["v2"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_18"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_17 == /\ pc = "Lbl_17"
          /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig[""]]
          /\ IF commitCertificate("v2")
                THEN /\ state' = [state EXCEPT !["v2"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_18"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_18 == /\ pc = "Lbl_18"
          /\ \/ /\ state["v3"] = 0
                /\ "block" = "block"
                /\ prepareSig' = [prepareSig EXCEPT !["v3"] = {sig["v3"]}]
                /\ state' = [state EXCEPT !["v3"] = 1]
                /\ UNCHANGED commitSig
             \/ /\ state["v3"] = 1
                /\ "block" = "prepareMsg" \/ "block" = "commitMsg"
                /\ state[""] = 1 \/ state[""] = 2
                /\ prepareSig' = [prepareSig EXCEPT !["v3"] = prepareSig["v3"] \union prepareSig[""]]
                /\ IF prepareCertificate("v3")
                      THEN /\ commitSig' = [commitSig EXCEPT !["v3"] = {sig["v3"]}]
                           /\ state' = [state EXCEPT !["v3"] = 2]
                      ELSE /\ TRUE
                           /\ UNCHANGED << state, commitSig >>
             \/ /\ state["v3"] = 2
                /\ "block" = "commitMsg"
                /\ state[""] = 2
                /\ commitSig' = [commitSig EXCEPT !["v3"] = commitSig["v3"] \union commitSig[""]]
                /\ IF commitCertificate("v3")
                      THEN /\ state' = [state EXCEPT !["v3"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ "block" = "validateMsg"
                /\ "".state = 9
                /\ commitSig' = [commitSig EXCEPT !["v3"] = commitSig["v3"] \union commitSig[""]]
                /\ IF commitCertificate("v3")
                      THEN /\ state' = [state EXCEPT !["v3"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
          /\ \/ /\ state'["v4"] = 0
                /\ "block" = "block"
                /\ pc' = "Lbl_19"
             \/ /\ state'["v4"] = 1
                /\ "block" = "prepareMsg" \/ "block" = "commitMsg"
                /\ state'[""] = 1 \/ state'[""] = 2
                /\ pc' = "Lbl_20"
             \/ /\ state'["v4"] = 2
                /\ "block" = "commitMsg"
                /\ state'[""] = 2
                /\ pc' = "Lbl_21"
             \/ /\ "block" = "validateMsg"
                /\ "".state = 9
                /\ pc' = "Lbl_22"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_19 == /\ pc = "Lbl_19"
          /\ prepareSig' = [prepareSig EXCEPT !["v4"] = {sig["v4"]}]
          /\ state' = [state EXCEPT !["v4"] = 1]
          /\ pc' = "Lbl_23"
          /\ UNCHANGED << proposers, validators, sig, commitSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_20 == /\ pc = "Lbl_20"
          /\ prepareSig' = [prepareSig EXCEPT !["v4"] = prepareSig["v4"] \union prepareSig[""]]
          /\ IF prepareCertificate("v4")
                THEN /\ commitSig' = [commitSig EXCEPT !["v4"] = {sig["v4"]}]
                     /\ state' = [state EXCEPT !["v4"] = 2]
                ELSE /\ TRUE
                     /\ UNCHANGED << state, commitSig >>
          /\ pc' = "Lbl_23"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_21 == /\ pc = "Lbl_21"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig[""]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_23"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_22 == /\ pc = "Lbl_22"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig[""]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_23"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_23 == /\ pc = "Lbl_23"
          /\ /\ inputType' = "prepareMsg"
             /\ sender' = "v1"
             /\ stack' = << [ procedure |->  "broadcast",
                              pc        |->  "Lbl_24",
                              sender    |->  sender,
                              inputType |->  inputType ] >>
                          \o stack
          /\ pc' = "Lbl_2"
          /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                          commitSig, impeachPrepareSig, impeachCommitSig >>

Lbl_24 == /\ pc = "Lbl_24"
          /\ /\ inputType' = "prepareMsg"
             /\ sender' = "v2"
             /\ stack' = << [ procedure |->  "broadcast",
                              pc        |->  "Lbl_25",
                              sender    |->  sender,
                              inputType |->  inputType ] >>
                          \o stack
          /\ pc' = "Lbl_2"
          /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                          commitSig, impeachPrepareSig, impeachCommitSig >>

Lbl_25 == /\ pc = "Lbl_25"
          /\ /\ inputType' = "prepareMsg"
             /\ sender' = "v3"
             /\ stack' = << [ procedure |->  "broadcast",
                              pc        |->  "Lbl_26",
                              sender    |->  sender,
                              inputType |->  inputType ] >>
                          \o stack
          /\ pc' = "Lbl_2"
          /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                          commitSig, impeachPrepareSig, impeachCommitSig >>

Lbl_26 == /\ pc = "Lbl_26"
          /\ /\ inputType' = "prepareMsg"
             /\ sender' = "v4"
             /\ stack' = << [ procedure |->  "broadcast",
                              pc        |->  "Lbl_27",
                              sender    |->  sender,
                              inputType |->  inputType ] >>
                          \o stack
          /\ pc' = "Lbl_2"
          /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                          commitSig, impeachPrepareSig, impeachCommitSig >>

Lbl_27 == /\ pc = "Lbl_27"
          /\ /\ inputType' = "commitMsg"
             /\ sender' = "v1"
             /\ stack' = << [ procedure |->  "broadcast",
                              pc        |->  "Lbl_28",
                              sender    |->  sender,
                              inputType |->  inputType ] >>
                          \o stack
          /\ pc' = "Lbl_2"
          /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                          commitSig, impeachPrepareSig, impeachCommitSig >>

Lbl_28 == /\ pc = "Lbl_28"
          /\ /\ inputType' = "commitMsg"
             /\ sender' = "v2"
             /\ stack' = << [ procedure |->  "broadcast",
                              pc        |->  "Lbl_29",
                              sender    |->  sender,
                              inputType |->  inputType ] >>
                          \o stack
          /\ pc' = "Lbl_2"
          /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                          commitSig, impeachPrepareSig, impeachCommitSig >>

Lbl_29 == /\ pc = "Lbl_29"
          /\ /\ inputType' = "commitMsg"
             /\ sender' = "v3"
             /\ stack' = << [ procedure |->  "broadcast",
                              pc        |->  "Lbl_30",
                              sender    |->  sender,
                              inputType |->  inputType ] >>
                          \o stack
          /\ pc' = "Lbl_2"
          /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                          commitSig, impeachPrepareSig, impeachCommitSig >>

Lbl_30 == /\ pc = "Lbl_30"
          /\ /\ inputType' = "commitMsg"
             /\ sender' = "v4"
             /\ stack' = << [ procedure |->  "broadcast",
                              pc        |->  "Done",
                              sender    |->  sender,
                              inputType |->  inputType ] >>
                          \o stack
          /\ pc' = "Lbl_2"
          /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                          commitSig, impeachPrepareSig, impeachCommitSig >>

Next == foreverLoop \/ broadcast \/ Lbl_13 \/ Lbl_14 \/ Lbl_15 \/ Lbl_16
           \/ Lbl_17 \/ Lbl_18 \/ Lbl_19 \/ Lbl_20 \/ Lbl_21 \/ Lbl_22 \/ Lbl_23
           \/ Lbl_24 \/ Lbl_25 \/ Lbl_26 \/ Lbl_27 \/ Lbl_28 \/ Lbl_29 \/ Lbl_30
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu Jul 18 16:56:09 CST 2019 by Dell
\* Created Tue Jul 16 19:39:20 CST 2019 by Dell
