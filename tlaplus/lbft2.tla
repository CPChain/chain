------------------------------- MODULE lbft2 -------------------------------

EXTENDS Integers, Sequences, FiniteSets


(*
--algorithm lbft2
variables
    proposers = <<"p1","p2">>,
    \* sequence of proposers
    validators = <<"v1","v2","v3","v4">>,
    sig = [v1|->1,v2|->2,v3|->3,v4|->4],
    state = [v \in validators |-> 0],
    prepareSig = [v \in validators |->{}],
    commitSig = [v \in validators |->{}],
    impeachPrepareSig = [v \in validators |->{}],
    impeachCommitSig = [v \in validators |->{}],
    validatorIndices = {1,2,3,4}
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
    validatorPrepareSig1 == "1" \notin prepareSig["v1"]
    validatorCommitSig1 == "1" \notin commitSig["v1"]
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


macro broadcast(sender, inputType) begin
    \* otherValidators := validatorIndices \ {number};
    with receiver \in (validators \ {sender}) do
        \* skip;
        fsm(receiver, inputType, sender);
\*        fsm("v1",inputType,sender);
\*        fsm("v2",inputType,sender);
\*        fsm("v3",inputType,sender);
\*        fsm("v4",inputType,sender);
    end with;
end macro;

begin

    \* all validators receive the block message
    fsm("v1", "block", "");
    fsm("v2", "block", "");
    fsm("v3", "block", "");
    fsm("v4", "block", "");

    \* broadcast prepare message

    broadcast("v1","prepareMsg");
    broadcast("v2","prepareMsg");
    broadcast("v3","prepareMsg");
    broadcast("v4","prepareMSg");
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
VARIABLES proposers, validators, sig, state, prepareSig, commitSig,
          impeachPrepareSig, impeachCommitSig, validatorIndices, pc

(* define statement *)
prepareCertificate(v) ==
    Cardinality(prepareSig[v]) >= 3

commitCertificate(v) ==
    Cardinality(commitSig[v]) >= 3

impeachPrepareCertificate(v) ==
    Cardinality(impeachPrepareSig[v]) >= 2

impeachCommitCertificate(v) ==
    Cardinality(impeachCommitSig[v]) >= 2





validatorPrepareSig1 == "1" \notin prepareSig["v1"]
validatorCommitSig1 == "1" \notin commitSig["v1"]
validatorState1 == state["v1"] /= 9


vars == << proposers, validators, sig, state, prepareSig, commitSig,
           impeachPrepareSig, impeachCommitSig, validatorIndices, pc >>

Init == (* Global variables *)
        /\ proposers = <<"p1","p2">>
        /\ validators = {"v1","v2","v3","v4"}
        /\ sig = [v1|->1,v2|->2,v3|->3,v4|->4]
        /\ state = [v \in validators |-> 0]
        /\ prepareSig = [v \in validators |->{}]
        /\ commitSig = [v \in validators |->{}]
        /\ impeachPrepareSig = [v \in validators |->{}]
        /\ impeachCommitSig = [v \in validators |->{}]
        /\ validatorIndices = {1,2,3,4}
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
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
               /\ pc' = "Lbl_2"
            \/ /\ state'["v2"] = 1
               /\ "block" = "prepareMsg"
               /\ state'[""] = 1 \/ state'[""] = 2
               /\ pc' = "Lbl_3"
            \/ /\ state'["v2"] = 2
               /\ "block" = "commitMsg"
               /\ state'[""] = 2
               /\ pc' = "Lbl_4"
            \/ /\ "block" = "validateMsg"
               /\ "".state = 9
               /\ pc' = "Lbl_5"
            \/ /\ TRUE
               /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, validatorIndices >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ prepareSig' = [prepareSig EXCEPT !["v2"] = {sig["v2"]}]
         /\ state' = [state EXCEPT !["v2"] = 1]
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, commitSig,
                         impeachPrepareSig, impeachCommitSig, validatorIndices >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ prepareSig' = [prepareSig EXCEPT !["v2"] = prepareSig["v2"] \union prepareSig[""]]
         /\ IF prepareCertificate("v2")
               THEN /\ commitSig' = [commitSig EXCEPT !["v2"] = {sig["v2"]}]
                    /\ state' = [state EXCEPT !["v2"] = 2]
               ELSE /\ TRUE
                    /\ UNCHANGED << state, commitSig >>
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, validatorIndices >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig[""]]
         /\ IF commitCertificate("v2")
               THEN /\ state' = [state EXCEPT !["v2"] = 9]
               ELSE /\ TRUE
                    /\ state' = state
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, prepareSig,
                         impeachPrepareSig, impeachCommitSig, validatorIndices >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ commitSig' = [commitSig EXCEPT !["v2"] = commitSig["v2"] \union commitSig[""]]
         /\ IF commitCertificate("v2")
               THEN /\ state' = [state EXCEPT !["v2"] = 9]
               ELSE /\ TRUE
                    /\ state' = state
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, prepareSig,
                         impeachPrepareSig, impeachCommitSig, validatorIndices >>

Lbl_6 == /\ pc = "Lbl_6"
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
               /\ pc' = "Lbl_7"
            \/ /\ state'["v4"] = 1
               /\ "block" = "prepareMsg"
               /\ state'[""] = 1 \/ state'[""] = 2
               /\ pc' = "Lbl_8"
            \/ /\ state'["v4"] = 2
               /\ "block" = "commitMsg"
               /\ state'[""] = 2
               /\ pc' = "Lbl_9"
            \/ /\ "block" = "validateMsg"
               /\ "".state = 9
               /\ pc' = "Lbl_10"
            \/ /\ TRUE
               /\ pc' = "Done"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, validatorIndices >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ prepareSig' = [prepareSig EXCEPT !["v4"] = {sig["v4"]}]
         /\ state' = [state EXCEPT !["v4"] = 1]
         /\ pc' = "Done"
         /\ UNCHANGED << proposers, validators, sig, commitSig,
                         impeachPrepareSig, impeachCommitSig, validatorIndices >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ prepareSig' = [prepareSig EXCEPT !["v4"] = prepareSig["v4"] \union prepareSig[""]]
         /\ IF prepareCertificate("v4")
               THEN /\ commitSig' = [commitSig EXCEPT !["v4"] = {sig["v4"]}]
                    /\ state' = [state EXCEPT !["v4"] = 2]
               ELSE /\ TRUE
                    /\ UNCHANGED << state, commitSig >>
         /\ pc' = "Done"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, validatorIndices >>

Lbl_9 == /\ pc = "Lbl_9"
         /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig[""]]
         /\ IF commitCertificate("v4")
               THEN /\ state' = [state EXCEPT !["v4"] = 9]
               ELSE /\ TRUE
                    /\ state' = state
         /\ pc' = "Done"
         /\ UNCHANGED << proposers, validators, sig, prepareSig,
                         impeachPrepareSig, impeachCommitSig, validatorIndices >>

Lbl_10 == /\ pc = "Lbl_10"
          /\ commitSig' = [commitSig EXCEPT !["v4"] = commitSig["v4"] \union commitSig[""]]
          /\ IF commitCertificate("v4")
                THEN /\ state' = [state EXCEPT !["v4"] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Done"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig,
                          validatorIndices >>

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_6 \/ Lbl_7
           \/ Lbl_8 \/ Lbl_9 \/ Lbl_10
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Wed Jul 17 20:44:38 CST 2019 by Dell
\* Created Tue Jul 16 19:39:20 CST 2019 by Dell
