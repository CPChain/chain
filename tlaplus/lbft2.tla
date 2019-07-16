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
    GetToNextHeight ==
        validators[1].state /=9 \/
        validators[2].state /=9 \/
        validators[3].state /=9 \/
        validators[4].state /=9


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
    with receiver \in validators do
        \* skip;
        fsm(receiver, inputType, sender);
    end with;
end macro;

begin

    \* all validators receive the block message
    fsm(validators[1], "block", "");
    fsm(validators[2], "block", "");
    fsm(validators[3], "block", "");
    fsm(validators[4], "block", "");

    \* broadcast prepare message

    broadcast(1,"prepareMsg");
\*    broadcast(2,"prepareMsg");
\*    broadcast(3,"prepareMsg");
\*    broadcast(4,"prepareMSg");
\*
\*    \* broadcast commit message
\*    broadcast(1,"commitMsg");
\*    broadcast(2,"commitMsg");
\*    broadcast(3,"commitMsg");
\*    broadcast(4,"commitMsg");
\*
\*    \* broadcast validate message
\*    broadcast(1,"validateMsg");
\*    broadcast(2,"validateMsg");
\*    broadcast(3,"validateMsg");
\*    broadcast(4,"validateMsg");





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

GetToNextHeight ==
    validators[1].state /=9 \/
    validators[2].state /=9 \/
    validators[3].state /=9 \/
    validators[4].state /=9


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
         /\ \/ /\ state[(validators[1])] = 0
               /\ "block" = "block"
               /\ prepareSig' = [prepareSig EXCEPT ![(validators[1])] = {sig[(validators[1])]}]
               /\ state' = [state EXCEPT ![(validators[1])] = 1]
               /\ UNCHANGED commitSig
            \/ /\ state[(validators[1])] = 1
               /\ "block" = "prepareMsg"
               /\ state[""] = 1 \/ state[""] = 2
               /\ prepareSig' = [prepareSig EXCEPT ![(validators[1])] = prepareSig[(validators[1])] \union prepareSig[""]]
               /\ IF prepareCertificate((validators[1]))
                     THEN /\ commitSig' = [commitSig EXCEPT ![(validators[1])] = {sig[(validators[1])]}]
                          /\ state' = [state EXCEPT ![(validators[1])] = 2]
                     ELSE /\ TRUE
                          /\ UNCHANGED << state, commitSig >>
            \/ /\ state[(validators[1])] = 2
               /\ "block" = "commitMsg"
               /\ state[""] = 2
               /\ commitSig' = [commitSig EXCEPT ![(validators[1])] = commitSig[(validators[1])] \union commitSig[""]]
               /\ IF commitCertificate((validators[1]))
                     THEN /\ state' = [state EXCEPT ![(validators[1])] = 9]
                     ELSE /\ TRUE
                          /\ state' = state
               /\ UNCHANGED prepareSig
            \/ /\ "block" = "validateMsg"
               /\ "".state = 9
               /\ commitSig' = [commitSig EXCEPT ![(validators[1])] = commitSig[(validators[1])] \union commitSig[""]]
               /\ IF commitCertificate((validators[1]))
                     THEN /\ state' = [state EXCEPT ![(validators[1])] = 9]
                     ELSE /\ TRUE
                          /\ state' = state
               /\ UNCHANGED prepareSig
            \/ /\ TRUE
               /\ UNCHANGED <<state, prepareSig, commitSig>>
         /\ \/ /\ state'[(validators[2])] = 0
               /\ "block" = "block"
               /\ pc' = "Lbl_2"
            \/ /\ state'[(validators[2])] = 1
               /\ "block" = "prepareMsg"
               /\ state'[""] = 1 \/ state'[""] = 2
               /\ pc' = "Lbl_3"
            \/ /\ state'[(validators[2])] = 2
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
         /\ prepareSig' = [prepareSig EXCEPT ![(validators[2])] = {sig[(validators[2])]}]
         /\ state' = [state EXCEPT ![(validators[2])] = 1]
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, commitSig,
                         impeachPrepareSig, impeachCommitSig, validatorIndices >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ prepareSig' = [prepareSig EXCEPT ![(validators[2])] = prepareSig[(validators[2])] \union prepareSig[""]]
         /\ IF prepareCertificate((validators[2]))
               THEN /\ commitSig' = [commitSig EXCEPT ![(validators[2])] = {sig[(validators[2])]}]
                    /\ state' = [state EXCEPT ![(validators[2])] = 2]
               ELSE /\ TRUE
                    /\ UNCHANGED << state, commitSig >>
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, validatorIndices >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ commitSig' = [commitSig EXCEPT ![(validators[2])] = commitSig[(validators[2])] \union commitSig[""]]
         /\ IF commitCertificate((validators[2]))
               THEN /\ state' = [state EXCEPT ![(validators[2])] = 9]
               ELSE /\ TRUE
                    /\ state' = state
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, prepareSig,
                         impeachPrepareSig, impeachCommitSig, validatorIndices >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ commitSig' = [commitSig EXCEPT ![(validators[2])] = commitSig[(validators[2])] \union commitSig[""]]
         /\ IF commitCertificate((validators[2]))
               THEN /\ state' = [state EXCEPT ![(validators[2])] = 9]
               ELSE /\ TRUE
                    /\ state' = state
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validators, sig, prepareSig,
                         impeachPrepareSig, impeachCommitSig, validatorIndices >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ \/ /\ state[(validators[3])] = 0
               /\ "block" = "block"
               /\ prepareSig' = [prepareSig EXCEPT ![(validators[3])] = {sig[(validators[3])]}]
               /\ state' = [state EXCEPT ![(validators[3])] = 1]
               /\ UNCHANGED commitSig
            \/ /\ state[(validators[3])] = 1
               /\ "block" = "prepareMsg"
               /\ state[""] = 1 \/ state[""] = 2
               /\ prepareSig' = [prepareSig EXCEPT ![(validators[3])] = prepareSig[(validators[3])] \union prepareSig[""]]
               /\ IF prepareCertificate((validators[3]))
                     THEN /\ commitSig' = [commitSig EXCEPT ![(validators[3])] = {sig[(validators[3])]}]
                          /\ state' = [state EXCEPT ![(validators[3])] = 2]
                     ELSE /\ TRUE
                          /\ UNCHANGED << state, commitSig >>
            \/ /\ state[(validators[3])] = 2
               /\ "block" = "commitMsg"
               /\ state[""] = 2
               /\ commitSig' = [commitSig EXCEPT ![(validators[3])] = commitSig[(validators[3])] \union commitSig[""]]
               /\ IF commitCertificate((validators[3]))
                     THEN /\ state' = [state EXCEPT ![(validators[3])] = 9]
                     ELSE /\ TRUE
                          /\ state' = state
               /\ UNCHANGED prepareSig
            \/ /\ "block" = "validateMsg"
               /\ "".state = 9
               /\ commitSig' = [commitSig EXCEPT ![(validators[3])] = commitSig[(validators[3])] \union commitSig[""]]
               /\ IF commitCertificate((validators[3]))
                     THEN /\ state' = [state EXCEPT ![(validators[3])] = 9]
                     ELSE /\ TRUE
                          /\ state' = state
               /\ UNCHANGED prepareSig
            \/ /\ TRUE
               /\ UNCHANGED <<state, prepareSig, commitSig>>
         /\ \/ /\ state'[(validators[4])] = 0
               /\ "block" = "block"
               /\ pc' = "Lbl_7"
            \/ /\ state'[(validators[4])] = 1
               /\ "block" = "prepareMsg"
               /\ state'[""] = 1 \/ state'[""] = 2
               /\ pc' = "Lbl_8"
            \/ /\ state'[(validators[4])] = 2
               /\ "block" = "commitMsg"
               /\ state'[""] = 2
               /\ pc' = "Lbl_9"
            \/ /\ "block" = "validateMsg"
               /\ "".state = 9
               /\ pc' = "Lbl_10"
            \/ /\ TRUE
               /\ pc' = "Lbl_11"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, validatorIndices >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ prepareSig' = [prepareSig EXCEPT ![(validators[4])] = {sig[(validators[4])]}]
         /\ state' = [state EXCEPT ![(validators[4])] = 1]
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << proposers, validators, sig, commitSig,
                         impeachPrepareSig, impeachCommitSig, validatorIndices >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ prepareSig' = [prepareSig EXCEPT ![(validators[4])] = prepareSig[(validators[4])] \union prepareSig[""]]
         /\ IF prepareCertificate((validators[4]))
               THEN /\ commitSig' = [commitSig EXCEPT ![(validators[4])] = {sig[(validators[4])]}]
                    /\ state' = [state EXCEPT ![(validators[4])] = 2]
               ELSE /\ TRUE
                    /\ UNCHANGED << state, commitSig >>
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                         impeachCommitSig, validatorIndices >>

Lbl_9 == /\ pc = "Lbl_9"
         /\ commitSig' = [commitSig EXCEPT ![(validators[4])] = commitSig[(validators[4])] \union commitSig[""]]
         /\ IF commitCertificate((validators[4]))
               THEN /\ state' = [state EXCEPT ![(validators[4])] = 9]
               ELSE /\ TRUE
                    /\ state' = state
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << proposers, validators, sig, prepareSig,
                         impeachPrepareSig, impeachCommitSig, validatorIndices >>

Lbl_10 == /\ pc = "Lbl_10"
          /\ commitSig' = [commitSig EXCEPT ![(validators[4])] = commitSig[(validators[4])] \union commitSig[""]]
          /\ IF commitCertificate((validators[4]))
                THEN /\ state' = [state EXCEPT ![(validators[4])] = 9]
                ELSE /\ TRUE
                     /\ state' = state
          /\ pc' = "Lbl_11"
          /\ UNCHANGED << proposers, validators, sig, prepareSig,
                          impeachPrepareSig, impeachCommitSig,
                          validatorIndices >>

Lbl_11 == /\ pc = "Lbl_11"
          /\ \E receiver \in validators:
               \/ /\ state[receiver] = 0
                  /\ "prepareMsg" = "block"
                  /\ prepareSig' = [prepareSig EXCEPT ![receiver] = {sig[receiver]}]
                  /\ state' = [state EXCEPT ![receiver] = 1]
                  /\ UNCHANGED commitSig
               \/ /\ state[receiver] = 1
                  /\ "prepareMsg" = "prepareMsg"
                  /\ state[1] = 1 \/ state[1] = 2
                  /\ prepareSig' = [prepareSig EXCEPT ![receiver] = prepareSig[receiver] \union prepareSig[1]]
                  /\ IF prepareCertificate(receiver)
                        THEN /\ commitSig' = [commitSig EXCEPT ![receiver] = {sig[receiver]}]
                             /\ state' = [state EXCEPT ![receiver] = 2]
                        ELSE /\ TRUE
                             /\ UNCHANGED << state, commitSig >>
               \/ /\ state[receiver] = 2
                  /\ "prepareMsg" = "commitMsg"
                  /\ state[1] = 2
                  /\ commitSig' = [commitSig EXCEPT ![receiver] = commitSig[receiver] \union commitSig[1]]
                  /\ IF commitCertificate(receiver)
                        THEN /\ state' = [state EXCEPT ![receiver] = 9]
                        ELSE /\ TRUE
                             /\ state' = state
                  /\ UNCHANGED prepareSig
               \/ /\ "prepareMsg" = "validateMsg"
                  /\ 1.state = 9
                  /\ commitSig' = [commitSig EXCEPT ![receiver] = commitSig[receiver] \union commitSig[1]]
                  /\ IF commitCertificate(receiver)
                        THEN /\ state' = [state EXCEPT ![receiver] = 9]
                        ELSE /\ TRUE
                             /\ state' = state
                  /\ UNCHANGED prepareSig
               \/ /\ TRUE
                  /\ UNCHANGED <<state, prepareSig, commitSig>>
          /\ pc' = "Done"
          /\ UNCHANGED << proposers, validators, sig, impeachPrepareSig,
                          impeachCommitSig, validatorIndices >>

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_6 \/ Lbl_7
           \/ Lbl_8 \/ Lbl_9 \/ Lbl_10 \/ Lbl_11
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Tue Jul 16 20:03:33 CST 2019 by Dell
\* Created Tue Jul 16 19:39:20 CST 2019 by Dell
