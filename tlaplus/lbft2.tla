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
    validatorState1 == state["v1"] /= 9
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
        await inputType = "prepareMsg";
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
    or
        skip;
    end either;
end macro;

macro broadcast2(sender, inputType) begin
    \* otherValidators := validatorIndices \ {number};

        fsm("v1",inputType,sender);
        fsm("v2",inputType,sender);
        fsm("v3",inputType,sender);
        fsm("v4",inputType,sender);
end macro;

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

\*    call broadcast("v1","prepareMsg");
\*    call broadcast("v2","prepareMsg");
\*    call broadcast("v3","prepareMsg");
\*    call broadcast("v4","prepareMSg");

    broadcast2("v1","prepareMsg");
    broadcast2("v2","prepareMsg");
    broadcast2("v3","prepareMsg");
    broadcast2("v4","prepareMSg");

\*
\*    \* broadcast commit message
\*    broadcast("v1","commitMsg");
\*    broadcast("v2","commitMsg");
\*    broadcast("v3","commitMsg");
\*    broadcast("v4","commitMsg");
\*
\*    \* broadcast validate message
\*    broadcast("v1","validateMsg");
\*    broadcast("v2","validateMsg");
\*    broadcast("v3","validateMsg");
\*    broadcast("v4","validateMsg");





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
validatorState1 == state["v1"] /= 9

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
        /\ pc = "Lbl_12"

Lbl_1 == /\ pc = "Lbl_1"
         /\ \/ /\ state["v1"] = 0
               /\ inputType = "block"
               /\ prepareSig' = [prepareSig EXCEPT !["v1"] = {sig["v1"]}]
               /\ state' = [state EXCEPT !["v1"] = 1]
               /\ UNCHANGED commitSig
            \/ /\ state["v1"] = 1
               /\ inputType = "prepareMsg"
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
            \/ /\ TRUE
               /\ UNCHANGED <<state, prepareSig, commitSig>>
         /\ \/ /\ state'["v2"] = 0
               /\ inputType = "block"
               /\ pc' = "Lbl_2"
            \/ /\ state'["v2"] = 1
               /\ inputType = "prepareMsg"
               /\ state'[sender] = 1 \/ state'[sender] = 2
               /\ pc' = "Lbl_3"
            \/ /\ state'["v2"] = 2
               /\ inputType = "commitMsg"
               /\ state'[sender] = 2
               /\ pc' = "Lbl_4"
            \/ /\ inputType = "validateMsg"
               /\ sender.state = 9
               /\ pc' = "Lbl_5"
            \/ /\ TRUE
               /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, stack, sender, inputType >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ prepareSig' = [prepareSig EXCEPT !["v2"] = {sig["v2"]}]
         /\ state' = [state EXCEPT !["v2"] = 1]
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, commitSig,
                         impeachPrepareSig, impeachCommitSig, stack, sender,
                         inputType >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ prepareSig' = [prepareSig EXCEPT !["v2"] = prepareSig["v2"] \union prepareSig[sender]]
         /\ IF prepareCertificate("v2")
               THEN /\ commitSig' = [commitSig EXCEPT !["v2"] = {sig["v2"]}]
                    /\ state' = [state EXCEPT !["v2"] = 2]
               ELSE /\ TRUE
                    /\ UNCHANGED << state, commitSig >>
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, stack, sender, inputType >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig[sender]]
         /\ IF commitCertificate("v2")
               THEN /\ state' = [state EXCEPT !["v2"] = 9]
               ELSE /\ TRUE
                    /\ state' = state
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, prepareSig,
                         impeachPrepareSig, impeachCommitSig, stack, sender,
                         inputType >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig[sender]]
         /\ IF commitCertificate("v2")
               THEN /\ state' = [state EXCEPT !["v2"] = 9]
               ELSE /\ TRUE
                    /\ state' = state
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, prepareSig,
                         impeachPrepareSig, impeachCommitSig, stack, sender,
                         inputType >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ \/ /\ state["v3"] = 0
               /\ inputType = "block"
               /\ prepareSig' = [prepareSig EXCEPT !["v3"] = {sig["v3"]}]
               /\ state' = [state EXCEPT !["v3"] = 1]
               /\ UNCHANGED commitSig
            \/ /\ state["v3"] = 1
               /\ inputType = "prepareMsg"
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
            \/ /\ TRUE
               /\ UNCHANGED <<state, prepareSig, commitSig>>
         /\ \/ /\ state'["v4"] = 0
               /\ inputType = "block"
               /\ pc' = "Lbl_7"
            \/ /\ state'["v4"] = 1
               /\ inputType = "prepareMsg"
               /\ state'[sender] = 1 \/ state'[sender] = 2
               /\ pc' = "Lbl_8"
            \/ /\ state'["v4"] = 2
               /\ inputType = "commitMsg"
               /\ state'[sender] = 2
               /\ pc' = "Lbl_9"
            \/ /\ inputType = "validateMsg"
               /\ sender.state = 9
               /\ pc' = "Lbl_10"
            \/ /\ TRUE
               /\ pc' = "Lbl_11"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, stack, sender, inputType >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ prepareSig' = [prepareSig EXCEPT !["v4"] = {sig["v4"]}]
         /\ state' = [state EXCEPT !["v4"] = 1]
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << proposers, validators, sig, commitSig,
                         impeachPrepareSig, impeachCommitSig, stack, sender,
                         inputType >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ prepareSig' = [prepareSig EXCEPT !["v4"] = prepareSig["v4"] \union prepareSig[sender]]
         /\ IF prepareCertificate("v4")
               THEN /\ commitSig' = [commitSig EXCEPT !["v4"] = {sig["v4"]}]
                    /\ state' = [state EXCEPT !["v4"] = 2]
               ELSE /\ TRUE
                    /\ UNCHANGED << state, commitSig >>
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, stack, sender, inputType >>

Lbl_9 == /\ pc = "Lbl_9"
         /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig[sender]]
         /\ IF commitCertificate("v4")
               THEN /\ state' = [state EXCEPT !["v4"] = 9]
               ELSE /\ TRUE
                    /\ state' = state
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << proposers, validators, sig, prepareSig,
                         impeachPrepareSig, impeachCommitSig, stack, sender,
                         inputType >>

Lbl_10 == /\ pc = "Lbl_10"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig[sender]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_11"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_11 == /\ pc = "Lbl_11"
          /\ pc' = Head(stack).pc
          /\ sender' = Head(stack).sender
          /\ inputType' = Head(stack).inputType
          /\ stack' = Tail(stack)
          /\ UNCHANGED << proposers, validators, sig, state, prepareSig,
                          commitSig, impeachPrepareSig, impeachCommitSig >>

broadcast == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_6 \/ Lbl_7
                \/ Lbl_8 \/ Lbl_9 \/ Lbl_10 \/ Lbl_11

Lbl_12 == /\ pc = "Lbl_12"
          /\ \/ /\ state["v1"] = 0
                /\ "block" = "block"
                /\ prepareSig' = [prepareSig EXCEPT !["v1"] = {sig["v1"]}]
                /\ state' = [state EXCEPT !["v1"] = 1]
                /\ UNCHANGED commitSig
             \/ /\ state["v1"] = 1
                /\ "block" = "prepareMsg"
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
             \/ /\ TRUE
                /\ UNCHANGED <<state, prepareSig, commitSig>>
          /\ \/ /\ state'["v2"] = 0
                /\ "block" = "block"
                /\ pc' = "Lbl_13"
             \/ /\ state'["v2"] = 1
                /\ "block" = "prepareMsg"
                /\ state'[""] = 1 \/ state'[""] = 2
                /\ pc' = "Lbl_14"
             \/ /\ state'["v2"] = 2
                /\ "block" = "commitMsg"
                /\ state'[""] = 2
                /\ pc' = "Lbl_15"
             \/ /\ "block" = "validateMsg"
                /\ "".state = 9
                /\ pc' = "Lbl_16"
             \/ /\ TRUE
                /\ pc' = "Lbl_17"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_13 == /\ pc = "Lbl_13"
          /\ prepareSig' = [prepareSig EXCEPT !["v2"] = {sig["v2"]}]
          /\ state' = [state EXCEPT !["v2"] = 1]
          /\ pc' = "Lbl_17"
          /\ UNCHANGED << proposers, validators, sig, commitSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_14 == /\ pc = "Lbl_14"
          /\ prepareSig' = [prepareSig EXCEPT !["v2"] = prepareSig["v2"] \union prepareSig[""]]
          /\ IF prepareCertificate("v2")
                THEN /\ commitSig' = [commitSig EXCEPT !["v2"] = {sig["v2"]}]
                     /\ state' = [state EXCEPT !["v2"] = 2]
                ELSE /\ TRUE
                     /\ UNCHANGED << state, commitSig >>
          /\ pc' = "Lbl_17"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_15 == /\ pc = "Lbl_15"
          /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig[""]]
          /\ IF commitCertificate("v2")
                THEN /\ state' = [state EXCEPT !["v2"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_17"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_16 == /\ pc = "Lbl_16"
          /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig[""]]
          /\ IF commitCertificate("v2")
                THEN /\ state' = [state EXCEPT !["v2"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_17"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_17 == /\ pc = "Lbl_17"
          /\ \/ /\ state["v3"] = 0
                /\ "block" = "block"
                /\ prepareSig' = [prepareSig EXCEPT !["v3"] = {sig["v3"]}]
                /\ state' = [state EXCEPT !["v3"] = 1]
                /\ UNCHANGED commitSig
             \/ /\ state["v3"] = 1
                /\ "block" = "prepareMsg"
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
             \/ /\ TRUE
                /\ UNCHANGED <<state, prepareSig, commitSig>>
          /\ \/ /\ state'["v4"] = 0
                /\ "block" = "block"
                /\ pc' = "Lbl_18"
             \/ /\ state'["v4"] = 1
                /\ "block" = "prepareMsg"
                /\ state'[""] = 1 \/ state'[""] = 2
                /\ pc' = "Lbl_19"
             \/ /\ state'["v4"] = 2
                /\ "block" = "commitMsg"
                /\ state'[""] = 2
                /\ pc' = "Lbl_20"
             \/ /\ "block" = "validateMsg"
                /\ "".state = 9
                /\ pc' = "Lbl_21"
             \/ /\ TRUE
                /\ pc' = "Lbl_22"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_18 == /\ pc = "Lbl_18"
          /\ prepareSig' = [prepareSig EXCEPT !["v4"] = {sig["v4"]}]
          /\ state' = [state EXCEPT !["v4"] = 1]
          /\ pc' = "Lbl_22"
          /\ UNCHANGED << proposers, validators, sig, commitSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_19 == /\ pc = "Lbl_19"
          /\ prepareSig' = [prepareSig EXCEPT !["v4"] = prepareSig["v4"] \union prepareSig[""]]
          /\ IF prepareCertificate("v4")
                THEN /\ commitSig' = [commitSig EXCEPT !["v4"] = {sig["v4"]}]
                     /\ state' = [state EXCEPT !["v4"] = 2]
                ELSE /\ TRUE
                     /\ UNCHANGED << state, commitSig >>
          /\ pc' = "Lbl_22"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_20 == /\ pc = "Lbl_20"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig[""]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_22"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_21 == /\ pc = "Lbl_21"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig[""]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_22"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_22 == /\ pc = "Lbl_22"
          /\ \/ /\ state["v1"] = 0
                /\ "prepareMsg" = "block"
                /\ prepareSig' = [prepareSig EXCEPT !["v1"] = {sig["v1"]}]
                /\ state' = [state EXCEPT !["v1"] = 1]
                /\ UNCHANGED commitSig
             \/ /\ state["v1"] = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ state["v1"] = 1 \/ state["v1"] = 2
                /\ prepareSig' = [prepareSig EXCEPT !["v1"] = prepareSig["v1"] \union prepareSig["v1"]]
                /\ IF prepareCertificate("v1")
                      THEN /\ commitSig' = [commitSig EXCEPT !["v1"] = {sig["v1"]}]
                           /\ state' = [state EXCEPT !["v1"] = 2]
                      ELSE /\ TRUE
                           /\ UNCHANGED << state, commitSig >>
             \/ /\ state["v1"] = 2
                /\ "prepareMsg" = "commitMsg"
                /\ state["v1"] = 2
                /\ commitSig' = [commitSig EXCEPT !["v1"] = commitSig["v1"] \union commitSig["v1"]]
                /\ IF commitCertificate("v1")
                      THEN /\ state' = [state EXCEPT !["v1"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ "prepareMsg" = "validateMsg"
                /\ "v1".state = 9
                /\ commitSig' = [commitSig EXCEPT !["v1"] = commitSig["v1"] \union commitSig["v1"]]
                /\ IF commitCertificate("v1")
                      THEN /\ state' = [state EXCEPT !["v1"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ TRUE
                /\ UNCHANGED <<state, prepareSig, commitSig>>
          /\ \/ /\ state'["v2"] = 0
                /\ "prepareMsg" = "block"
                /\ pc' = "Lbl_23"
             \/ /\ state'["v2"] = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ state'["v1"] = 1 \/ state'["v1"] = 2
                /\ pc' = "Lbl_24"
             \/ /\ state'["v2"] = 2
                /\ "prepareMsg" = "commitMsg"
                /\ state'["v1"] = 2
                /\ pc' = "Lbl_25"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ "v1".state = 9
                /\ pc' = "Lbl_26"
             \/ /\ TRUE
                /\ pc' = "Lbl_27"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_23 == /\ pc = "Lbl_23"
          /\ prepareSig' = [prepareSig EXCEPT !["v2"] = {sig["v2"]}]
          /\ state' = [state EXCEPT !["v2"] = 1]
          /\ pc' = "Lbl_27"
          /\ UNCHANGED << proposers, validators, sig, commitSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_24 == /\ pc = "Lbl_24"
          /\ prepareSig' = [prepareSig EXCEPT !["v2"] = prepareSig["v2"] \union prepareSig["v1"]]
          /\ IF prepareCertificate("v2")
                THEN /\ commitSig' = [commitSig EXCEPT !["v2"] = {sig["v2"]}]
                     /\ state' = [state EXCEPT !["v2"] = 2]
                ELSE /\ TRUE
                     /\ UNCHANGED << state, commitSig >>
          /\ pc' = "Lbl_27"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_25 == /\ pc = "Lbl_25"
          /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig["v1"]]
          /\ IF commitCertificate("v2")
                THEN /\ state' = [state EXCEPT !["v2"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_27"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_26 == /\ pc = "Lbl_26"
          /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig["v1"]]
          /\ IF commitCertificate("v2")
                THEN /\ state' = [state EXCEPT !["v2"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_27"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_27 == /\ pc = "Lbl_27"
          /\ \/ /\ state["v3"] = 0
                /\ "prepareMsg" = "block"
                /\ prepareSig' = [prepareSig EXCEPT !["v3"] = {sig["v3"]}]
                /\ state' = [state EXCEPT !["v3"] = 1]
                /\ UNCHANGED commitSig
             \/ /\ state["v3"] = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ state["v1"] = 1 \/ state["v1"] = 2
                /\ prepareSig' = [prepareSig EXCEPT !["v3"] = prepareSig["v3"] \union prepareSig["v1"]]
                /\ IF prepareCertificate("v3")
                      THEN /\ commitSig' = [commitSig EXCEPT !["v3"] = {sig["v3"]}]
                           /\ state' = [state EXCEPT !["v3"] = 2]
                      ELSE /\ TRUE
                           /\ UNCHANGED << state, commitSig >>
             \/ /\ state["v3"] = 2
                /\ "prepareMsg" = "commitMsg"
                /\ state["v1"] = 2
                /\ commitSig' = [commitSig EXCEPT !["v3"] = commitSig["v3"] \union commitSig["v1"]]
                /\ IF commitCertificate("v3")
                      THEN /\ state' = [state EXCEPT !["v3"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ "prepareMsg" = "validateMsg"
                /\ "v1".state = 9
                /\ commitSig' = [commitSig EXCEPT !["v3"] = commitSig["v3"] \union commitSig["v1"]]
                /\ IF commitCertificate("v3")
                      THEN /\ state' = [state EXCEPT !["v3"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ TRUE
                /\ UNCHANGED <<state, prepareSig, commitSig>>
          /\ \/ /\ state'["v4"] = 0
                /\ "prepareMsg" = "block"
                /\ pc' = "Lbl_28"
             \/ /\ state'["v4"] = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ state'["v1"] = 1 \/ state'["v1"] = 2
                /\ pc' = "Lbl_29"
             \/ /\ state'["v4"] = 2
                /\ "prepareMsg" = "commitMsg"
                /\ state'["v1"] = 2
                /\ pc' = "Lbl_30"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ "v1".state = 9
                /\ pc' = "Lbl_31"
             \/ /\ TRUE
                /\ pc' = "Lbl_32"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_28 == /\ pc = "Lbl_28"
          /\ prepareSig' = [prepareSig EXCEPT !["v4"] = {sig["v4"]}]
          /\ state' = [state EXCEPT !["v4"] = 1]
          /\ pc' = "Lbl_32"
          /\ UNCHANGED << proposers, validators, sig, commitSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_29 == /\ pc = "Lbl_29"
          /\ prepareSig' = [prepareSig EXCEPT !["v4"] = prepareSig["v4"] \union prepareSig["v1"]]
          /\ IF prepareCertificate("v4")
                THEN /\ commitSig' = [commitSig EXCEPT !["v4"] = {sig["v4"]}]
                     /\ state' = [state EXCEPT !["v4"] = 2]
                ELSE /\ TRUE
                     /\ UNCHANGED << state, commitSig >>
          /\ pc' = "Lbl_32"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_30 == /\ pc = "Lbl_30"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig["v1"]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_32"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_31 == /\ pc = "Lbl_31"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig["v1"]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_32"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_32 == /\ pc = "Lbl_32"
          /\ \/ /\ state["v1"] = 0
                /\ "prepareMsg" = "block"
                /\ prepareSig' = [prepareSig EXCEPT !["v1"] = {sig["v1"]}]
                /\ state' = [state EXCEPT !["v1"] = 1]
                /\ UNCHANGED commitSig
             \/ /\ state["v1"] = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ state["v2"] = 1 \/ state["v2"] = 2
                /\ prepareSig' = [prepareSig EXCEPT !["v1"] = prepareSig["v1"] \union prepareSig["v2"]]
                /\ IF prepareCertificate("v1")
                      THEN /\ commitSig' = [commitSig EXCEPT !["v1"] = {sig["v1"]}]
                           /\ state' = [state EXCEPT !["v1"] = 2]
                      ELSE /\ TRUE
                           /\ UNCHANGED << state, commitSig >>
             \/ /\ state["v1"] = 2
                /\ "prepareMsg" = "commitMsg"
                /\ state["v2"] = 2
                /\ commitSig' = [commitSig EXCEPT !["v1"] = commitSig["v1"] \union commitSig["v2"]]
                /\ IF commitCertificate("v1")
                      THEN /\ state' = [state EXCEPT !["v1"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ "prepareMsg" = "validateMsg"
                /\ "v2".state = 9
                /\ commitSig' = [commitSig EXCEPT !["v1"] = commitSig["v1"] \union commitSig["v2"]]
                /\ IF commitCertificate("v1")
                      THEN /\ state' = [state EXCEPT !["v1"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ TRUE
                /\ UNCHANGED <<state, prepareSig, commitSig>>
          /\ \/ /\ state'["v2"] = 0
                /\ "prepareMsg" = "block"
                /\ pc' = "Lbl_33"
             \/ /\ state'["v2"] = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ state'["v2"] = 1 \/ state'["v2"] = 2
                /\ pc' = "Lbl_34"
             \/ /\ state'["v2"] = 2
                /\ "prepareMsg" = "commitMsg"
                /\ state'["v2"] = 2
                /\ pc' = "Lbl_35"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ "v2".state = 9
                /\ pc' = "Lbl_36"
             \/ /\ TRUE
                /\ pc' = "Lbl_37"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_33 == /\ pc = "Lbl_33"
          /\ prepareSig' = [prepareSig EXCEPT !["v2"] = {sig["v2"]}]
          /\ state' = [state EXCEPT !["v2"] = 1]
          /\ pc' = "Lbl_37"
          /\ UNCHANGED << proposers, validators, sig, commitSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_34 == /\ pc = "Lbl_34"
          /\ prepareSig' = [prepareSig EXCEPT !["v2"] = prepareSig["v2"] \union prepareSig["v2"]]
          /\ IF prepareCertificate("v2")
                THEN /\ commitSig' = [commitSig EXCEPT !["v2"] = {sig["v2"]}]
                     /\ state' = [state EXCEPT !["v2"] = 2]
                ELSE /\ TRUE
                     /\ UNCHANGED << state, commitSig >>
          /\ pc' = "Lbl_37"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_35 == /\ pc = "Lbl_35"
          /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig["v2"]]
          /\ IF commitCertificate("v2")
                THEN /\ state' = [state EXCEPT !["v2"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_37"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_36 == /\ pc = "Lbl_36"
          /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig["v2"]]
          /\ IF commitCertificate("v2")
                THEN /\ state' = [state EXCEPT !["v2"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_37"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_37 == /\ pc = "Lbl_37"
          /\ \/ /\ state["v3"] = 0
                /\ "prepareMsg" = "block"
                /\ prepareSig' = [prepareSig EXCEPT !["v3"] = {sig["v3"]}]
                /\ state' = [state EXCEPT !["v3"] = 1]
                /\ UNCHANGED commitSig
             \/ /\ state["v3"] = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ state["v2"] = 1 \/ state["v2"] = 2
                /\ prepareSig' = [prepareSig EXCEPT !["v3"] = prepareSig["v3"] \union prepareSig["v2"]]
                /\ IF prepareCertificate("v3")
                      THEN /\ commitSig' = [commitSig EXCEPT !["v3"] = {sig["v3"]}]
                           /\ state' = [state EXCEPT !["v3"] = 2]
                      ELSE /\ TRUE
                           /\ UNCHANGED << state, commitSig >>
             \/ /\ state["v3"] = 2
                /\ "prepareMsg" = "commitMsg"
                /\ state["v2"] = 2
                /\ commitSig' = [commitSig EXCEPT !["v3"] = commitSig["v3"] \union commitSig["v2"]]
                /\ IF commitCertificate("v3")
                      THEN /\ state' = [state EXCEPT !["v3"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ "prepareMsg" = "validateMsg"
                /\ "v2".state = 9
                /\ commitSig' = [commitSig EXCEPT !["v3"] = commitSig["v3"] \union commitSig["v2"]]
                /\ IF commitCertificate("v3")
                      THEN /\ state' = [state EXCEPT !["v3"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ TRUE
                /\ UNCHANGED <<state, prepareSig, commitSig>>
          /\ \/ /\ state'["v4"] = 0
                /\ "prepareMsg" = "block"
                /\ pc' = "Lbl_38"
             \/ /\ state'["v4"] = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ state'["v2"] = 1 \/ state'["v2"] = 2
                /\ pc' = "Lbl_39"
             \/ /\ state'["v4"] = 2
                /\ "prepareMsg" = "commitMsg"
                /\ state'["v2"] = 2
                /\ pc' = "Lbl_40"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ "v2".state = 9
                /\ pc' = "Lbl_41"
             \/ /\ TRUE
                /\ pc' = "Lbl_42"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_38 == /\ pc = "Lbl_38"
          /\ prepareSig' = [prepareSig EXCEPT !["v4"] = {sig["v4"]}]
          /\ state' = [state EXCEPT !["v4"] = 1]
          /\ pc' = "Lbl_42"
          /\ UNCHANGED << proposers, validators, sig, commitSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_39 == /\ pc = "Lbl_39"
          /\ prepareSig' = [prepareSig EXCEPT !["v4"] = prepareSig["v4"] \union prepareSig["v2"]]
          /\ IF prepareCertificate("v4")
                THEN /\ commitSig' = [commitSig EXCEPT !["v4"] = {sig["v4"]}]
                     /\ state' = [state EXCEPT !["v4"] = 2]
                ELSE /\ TRUE
                     /\ UNCHANGED << state, commitSig >>
          /\ pc' = "Lbl_42"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_40 == /\ pc = "Lbl_40"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig["v2"]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_42"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_41 == /\ pc = "Lbl_41"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig["v2"]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_42"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_42 == /\ pc = "Lbl_42"
          /\ \/ /\ state["v1"] = 0
                /\ "prepareMsg" = "block"
                /\ prepareSig' = [prepareSig EXCEPT !["v1"] = {sig["v1"]}]
                /\ state' = [state EXCEPT !["v1"] = 1]
                /\ UNCHANGED commitSig
             \/ /\ state["v1"] = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ state["v3"] = 1 \/ state["v3"] = 2
                /\ prepareSig' = [prepareSig EXCEPT !["v1"] = prepareSig["v1"] \union prepareSig["v3"]]
                /\ IF prepareCertificate("v1")
                      THEN /\ commitSig' = [commitSig EXCEPT !["v1"] = {sig["v1"]}]
                           /\ state' = [state EXCEPT !["v1"] = 2]
                      ELSE /\ TRUE
                           /\ UNCHANGED << state, commitSig >>
             \/ /\ state["v1"] = 2
                /\ "prepareMsg" = "commitMsg"
                /\ state["v3"] = 2
                /\ commitSig' = [commitSig EXCEPT !["v1"] = commitSig["v1"] \union commitSig["v3"]]
                /\ IF commitCertificate("v1")
                      THEN /\ state' = [state EXCEPT !["v1"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ "prepareMsg" = "validateMsg"
                /\ "v3".state = 9
                /\ commitSig' = [commitSig EXCEPT !["v1"] = commitSig["v1"] \union commitSig["v3"]]
                /\ IF commitCertificate("v1")
                      THEN /\ state' = [state EXCEPT !["v1"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ TRUE
                /\ UNCHANGED <<state, prepareSig, commitSig>>
          /\ \/ /\ state'["v2"] = 0
                /\ "prepareMsg" = "block"
                /\ pc' = "Lbl_43"
             \/ /\ state'["v2"] = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ state'["v3"] = 1 \/ state'["v3"] = 2
                /\ pc' = "Lbl_44"
             \/ /\ state'["v2"] = 2
                /\ "prepareMsg" = "commitMsg"
                /\ state'["v3"] = 2
                /\ pc' = "Lbl_45"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ "v3".state = 9
                /\ pc' = "Lbl_46"
             \/ /\ TRUE
                /\ pc' = "Lbl_47"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_43 == /\ pc = "Lbl_43"
          /\ prepareSig' = [prepareSig EXCEPT !["v2"] = {sig["v2"]}]
          /\ state' = [state EXCEPT !["v2"] = 1]
          /\ pc' = "Lbl_47"
          /\ UNCHANGED << proposers, validators, sig, commitSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_44 == /\ pc = "Lbl_44"
          /\ prepareSig' = [prepareSig EXCEPT !["v2"] = prepareSig["v2"] \union prepareSig["v3"]]
          /\ IF prepareCertificate("v2")
                THEN /\ commitSig' = [commitSig EXCEPT !["v2"] = {sig["v2"]}]
                     /\ state' = [state EXCEPT !["v2"] = 2]
                ELSE /\ TRUE
                     /\ UNCHANGED << state, commitSig >>
          /\ pc' = "Lbl_47"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_45 == /\ pc = "Lbl_45"
          /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig["v3"]]
          /\ IF commitCertificate("v2")
                THEN /\ state' = [state EXCEPT !["v2"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_47"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_46 == /\ pc = "Lbl_46"
          /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig["v3"]]
          /\ IF commitCertificate("v2")
                THEN /\ state' = [state EXCEPT !["v2"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_47"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_47 == /\ pc = "Lbl_47"
          /\ \/ /\ state["v3"] = 0
                /\ "prepareMsg" = "block"
                /\ prepareSig' = [prepareSig EXCEPT !["v3"] = {sig["v3"]}]
                /\ state' = [state EXCEPT !["v3"] = 1]
                /\ UNCHANGED commitSig
             \/ /\ state["v3"] = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ state["v3"] = 1 \/ state["v3"] = 2
                /\ prepareSig' = [prepareSig EXCEPT !["v3"] = prepareSig["v3"] \union prepareSig["v3"]]
                /\ IF prepareCertificate("v3")
                      THEN /\ commitSig' = [commitSig EXCEPT !["v3"] = {sig["v3"]}]
                           /\ state' = [state EXCEPT !["v3"] = 2]
                      ELSE /\ TRUE
                           /\ UNCHANGED << state, commitSig >>
             \/ /\ state["v3"] = 2
                /\ "prepareMsg" = "commitMsg"
                /\ state["v3"] = 2
                /\ commitSig' = [commitSig EXCEPT !["v3"] = commitSig["v3"] \union commitSig["v3"]]
                /\ IF commitCertificate("v3")
                      THEN /\ state' = [state EXCEPT !["v3"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ "prepareMsg" = "validateMsg"
                /\ "v3".state = 9
                /\ commitSig' = [commitSig EXCEPT !["v3"] = commitSig["v3"] \union commitSig["v3"]]
                /\ IF commitCertificate("v3")
                      THEN /\ state' = [state EXCEPT !["v3"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ TRUE
                /\ UNCHANGED <<state, prepareSig, commitSig>>
          /\ \/ /\ state'["v4"] = 0
                /\ "prepareMsg" = "block"
                /\ pc' = "Lbl_48"
             \/ /\ state'["v4"] = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ state'["v3"] = 1 \/ state'["v3"] = 2
                /\ pc' = "Lbl_49"
             \/ /\ state'["v4"] = 2
                /\ "prepareMsg" = "commitMsg"
                /\ state'["v3"] = 2
                /\ pc' = "Lbl_50"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ "v3".state = 9
                /\ pc' = "Lbl_51"
             \/ /\ TRUE
                /\ pc' = "Lbl_52"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_48 == /\ pc = "Lbl_48"
          /\ prepareSig' = [prepareSig EXCEPT !["v4"] = {sig["v4"]}]
          /\ state' = [state EXCEPT !["v4"] = 1]
          /\ pc' = "Lbl_52"
          /\ UNCHANGED << proposers, validators, sig, commitSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_49 == /\ pc = "Lbl_49"
          /\ prepareSig' = [prepareSig EXCEPT !["v4"] = prepareSig["v4"] \union prepareSig["v3"]]
          /\ IF prepareCertificate("v4")
                THEN /\ commitSig' = [commitSig EXCEPT !["v4"] = {sig["v4"]}]
                     /\ state' = [state EXCEPT !["v4"] = 2]
                ELSE /\ TRUE
                     /\ UNCHANGED << state, commitSig >>
          /\ pc' = "Lbl_52"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_50 == /\ pc = "Lbl_50"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig["v3"]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_52"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_51 == /\ pc = "Lbl_51"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig["v3"]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_52"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_52 == /\ pc = "Lbl_52"
          /\ \/ /\ state["v1"] = 0
                /\ "prepareMSg" = "block"
                /\ prepareSig' = [prepareSig EXCEPT !["v1"] = {sig["v1"]}]
                /\ state' = [state EXCEPT !["v1"] = 1]
                /\ UNCHANGED commitSig
             \/ /\ state["v1"] = 1
                /\ "prepareMSg" = "prepareMsg"
                /\ state["v4"] = 1 \/ state["v4"] = 2
                /\ prepareSig' = [prepareSig EXCEPT !["v1"] = prepareSig["v1"] \union prepareSig["v4"]]
                /\ IF prepareCertificate("v1")
                      THEN /\ commitSig' = [commitSig EXCEPT !["v1"] = {sig["v1"]}]
                           /\ state' = [state EXCEPT !["v1"] = 2]
                      ELSE /\ TRUE
                           /\ UNCHANGED << state, commitSig >>
             \/ /\ state["v1"] = 2
                /\ "prepareMSg" = "commitMsg"
                /\ state["v4"] = 2
                /\ commitSig' = [commitSig EXCEPT !["v1"] = commitSig["v1"] \union commitSig["v4"]]
                /\ IF commitCertificate("v1")
                      THEN /\ state' = [state EXCEPT !["v1"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ "prepareMSg" = "validateMsg"
                /\ "v4".state = 9
                /\ commitSig' = [commitSig EXCEPT !["v1"] = commitSig["v1"] \union commitSig["v4"]]
                /\ IF commitCertificate("v1")
                      THEN /\ state' = [state EXCEPT !["v1"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ TRUE
                /\ UNCHANGED <<state, prepareSig, commitSig>>
          /\ \/ /\ state'["v2"] = 0
                /\ "prepareMSg" = "block"
                /\ pc' = "Lbl_53"
             \/ /\ state'["v2"] = 1
                /\ "prepareMSg" = "prepareMsg"
                /\ state'["v4"] = 1 \/ state'["v4"] = 2
                /\ pc' = "Lbl_54"
             \/ /\ state'["v2"] = 2
                /\ "prepareMSg" = "commitMsg"
                /\ state'["v4"] = 2
                /\ pc' = "Lbl_55"
             \/ /\ "prepareMSg" = "validateMsg"
                /\ "v4".state = 9
                /\ pc' = "Lbl_56"
             \/ /\ TRUE
                /\ pc' = "Lbl_57"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_53 == /\ pc = "Lbl_53"
          /\ prepareSig' = [prepareSig EXCEPT !["v2"] = {sig["v2"]}]
          /\ state' = [state EXCEPT !["v2"] = 1]
          /\ pc' = "Lbl_57"
          /\ UNCHANGED << proposers, validators, sig, commitSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_54 == /\ pc = "Lbl_54"
          /\ prepareSig' = [prepareSig EXCEPT !["v2"] = prepareSig["v2"] \union prepareSig["v4"]]
          /\ IF prepareCertificate("v2")
                THEN /\ commitSig' = [commitSig EXCEPT !["v2"] = {sig["v2"]}]
                     /\ state' = [state EXCEPT !["v2"] = 2]
                ELSE /\ TRUE
                     /\ UNCHANGED << state, commitSig >>
          /\ pc' = "Lbl_57"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_55 == /\ pc = "Lbl_55"
          /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig["v4"]]
          /\ IF commitCertificate("v2")
                THEN /\ state' = [state EXCEPT !["v2"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_57"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_56 == /\ pc = "Lbl_56"
          /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig["v4"]]
          /\ IF commitCertificate("v2")
                THEN /\ state' = [state EXCEPT !["v2"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_57"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_57 == /\ pc = "Lbl_57"
          /\ \/ /\ state["v3"] = 0
                /\ "prepareMSg" = "block"
                /\ prepareSig' = [prepareSig EXCEPT !["v3"] = {sig["v3"]}]
                /\ state' = [state EXCEPT !["v3"] = 1]
                /\ UNCHANGED commitSig
             \/ /\ state["v3"] = 1
                /\ "prepareMSg" = "prepareMsg"
                /\ state["v4"] = 1 \/ state["v4"] = 2
                /\ prepareSig' = [prepareSig EXCEPT !["v3"] = prepareSig["v3"] \union prepareSig["v4"]]
                /\ IF prepareCertificate("v3")
                      THEN /\ commitSig' = [commitSig EXCEPT !["v3"] = {sig["v3"]}]
                           /\ state' = [state EXCEPT !["v3"] = 2]
                      ELSE /\ TRUE
                           /\ UNCHANGED << state, commitSig >>
             \/ /\ state["v3"] = 2
                /\ "prepareMSg" = "commitMsg"
                /\ state["v4"] = 2
                /\ commitSig' = [commitSig EXCEPT !["v3"] = commitSig["v3"] \union commitSig["v4"]]
                /\ IF commitCertificate("v3")
                      THEN /\ state' = [state EXCEPT !["v3"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ "prepareMSg" = "validateMsg"
                /\ "v4".state = 9
                /\ commitSig' = [commitSig EXCEPT !["v3"] = commitSig["v3"] \union commitSig["v4"]]
                /\ IF commitCertificate("v3")
                      THEN /\ state' = [state EXCEPT !["v3"] = 9]
                      ELSE /\ TRUE
                           /\ state' = state
                /\ UNCHANGED prepareSig
             \/ /\ TRUE
                /\ UNCHANGED <<state, prepareSig, commitSig>>
          /\ \/ /\ state'["v4"] = 0
                /\ "prepareMSg" = "block"
                /\ pc' = "Lbl_58"
             \/ /\ state'["v4"] = 1
                /\ "prepareMSg" = "prepareMsg"
                /\ state'["v4"] = 1 \/ state'["v4"] = 2
                /\ pc' = "Lbl_59"
             \/ /\ state'["v4"] = 2
                /\ "prepareMSg" = "commitMsg"
                /\ state'["v4"] = 2
                /\ pc' = "Lbl_60"
             \/ /\ "prepareMSg" = "validateMsg"
                /\ "v4".state = 9
                /\ pc' = "Lbl_61"
             \/ /\ TRUE
                /\ pc' = "Done"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_58 == /\ pc = "Lbl_58"
          /\ prepareSig' = [prepareSig EXCEPT !["v4"] = {sig["v4"]}]
          /\ state' = [state EXCEPT !["v4"] = 1]
          /\ pc' = "Done"
          /\ UNCHANGED << proposers, validators, sig, commitSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_59 == /\ pc = "Lbl_59"
          /\ prepareSig' = [prepareSig EXCEPT !["v4"] = prepareSig["v4"] \union prepareSig["v4"]]
          /\ IF prepareCertificate("v4")
                THEN /\ commitSig' = [commitSig EXCEPT !["v4"] = {sig["v4"]}]
                     /\ state' = [state EXCEPT !["v4"] = 2]
                ELSE /\ TRUE
                     /\ UNCHANGED << state, commitSig >>
          /\ pc' = "Done"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, stack, sender, inputType >>

Lbl_60 == /\ pc = "Lbl_60"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig["v4"]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Done"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Lbl_61 == /\ pc = "Lbl_61"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig["v4"]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Done"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig, stack, sender,
                          inputType >>

Next == broadcast \/ Lbl_12 \/ Lbl_13 \/ Lbl_14 \/ Lbl_15 \/ Lbl_16
           \/ Lbl_17 \/ Lbl_18 \/ Lbl_19 \/ Lbl_20 \/ Lbl_21 \/ Lbl_22 \/ Lbl_23
           \/ Lbl_24 \/ Lbl_25 \/ Lbl_26 \/ Lbl_27 \/ Lbl_28 \/ Lbl_29 \/ Lbl_30
           \/ Lbl_31 \/ Lbl_32 \/ Lbl_33 \/ Lbl_34 \/ Lbl_35 \/ Lbl_36 \/ Lbl_37
           \/ Lbl_38 \/ Lbl_39 \/ Lbl_40 \/ Lbl_41 \/ Lbl_42 \/ Lbl_43 \/ Lbl_44
           \/ Lbl_45 \/ Lbl_46 \/ Lbl_47 \/ Lbl_48 \/ Lbl_49 \/ Lbl_50 \/ Lbl_51
           \/ Lbl_52 \/ Lbl_53 \/ Lbl_54 \/ Lbl_55 \/ Lbl_56 \/ Lbl_57 \/ Lbl_58
           \/ Lbl_59 \/ Lbl_60 \/ Lbl_61
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu Jul 18 16:12:14 CST 2019 by Dell
\* Created Tue Jul 16 19:39:20 CST 2019 by Dell
