-------------------------------- MODULE lbft --------------------------------

EXTENDS Integers, Sequences, FiniteSets


(*
--algorithm lbft
variables
    proposers = <<"p1","p2">>,
    \* sequence of proposers
    validators = <<
    [state |-> 0, sig |-> "1", prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
    [state |-> 0, sig |-> "2", prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
    [state |-> 0, sig |-> "3", prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
    [state |-> 0, sig |-> "4", prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}]
    >>,
    \* sequence of validators
    \* 0,1,2 represent idle, prepare, commit
    \* 3,4 represent impeach prepare and impeach commit state
    \* 9 represents idle state in next block height
    \* imp represents impeachment
    \* four sigs refers to signatures for different messages

define
    \* return true if suffice a certificate
    prepareCertificate(v) ==
        Cardinality(v.prepareSig) >= 3

    commitCertificate(v) ==
        Cardinality(v.commitSig) >= 3

    impeachPrepareCertificate(v) ==
        Cardinality(v.impeachPrepareSig) >= 2

    impeachCommitCertificate(v) ==
        Cardinality(v.impeachCommitSig) >= 2

    validatorState1 == validators[1].state >= 0
    \* testing variables to check if sig has been added
    \* if these variables violates invariant properties,
    \* the validator successfully transit to next state.
    validatorPrepareSig1 == "1" \notin validators[1].prepareSig
    validatorCommitSig1 == "1" \notin validators[1].commitSig


end define;


macro fsm(v, inputType, input) begin
    either \* idle state
    \* transfer to prepare state given a block
        await v.state = 0;
        await inputType = "block";
        v.prepareSig := {v.sig};
        v.state := 1;

    or  \* prepare state
        await v.state = 1;
        await inputType = "prepareMsg";
        \* accumulate prepare signatures
        v.prepareSig := v.prepareSig \union input.prepareSig;
        if prepareCertificate(v)
        then
        \* transfer to commit state if collect a certificate
            v.prepareSig := {};
            v.commitSig := {v.sig};
            v.state := 2;
        end if;

    or  \* commit state
        await v.state = 2;
        await inputType = "commitMsg";
        \* accumulate commit signatures
        v.commitSig := v.commitSig \union input.commitSig;
        if commitCertificate(v)
        then
        \* transfer to idle state in next height given the certificate
            v.commitSig := {};
            v.state := 9;
        end if;
    end either
end macro;




begin

\* Validator1:
    fsm(validators[1], "block", "");
    fsm(validators[2], "block", "");
    fsm(validators[3], "block", "");
    fsm(validators[4], "block", "");
    fsm(validators[1], "prepareMsg", validators[2]);
    fsm(validators[1], "prepareMsg", validators[3]);
    fsm(validators[1], "prepareMsg", validators[4]);



end algorithm;*)


\* BEGIN TRANSLATION
VARIABLES proposers, validators, pc

(* define statement *)
prepareCertificate(v) ==
    Cardinality(v.prepareSig) >= 3

commitCertificate(v) ==
    Cardinality(v.commitSig) >= 3

impeachPrepareCertificate(v) ==
    Cardinality(v.impeachPrepareSig) >= 2

impeachCommitCertificate(v) ==
    Cardinality(v.impeachCommitSig) >= 2

validatorState1 == validators[1].state >= 0



validatorPrepareSig1 == "1" \notin validators[1].prepareSig
validatorCommitSig1 == "1" \notin validators[1].commitSig


vars == << proposers, validators, pc >>

Init == (* Global variables *)
        /\ proposers = <<"p1","p2">>
        /\ validators =              <<
                        [state |-> 0, sig |-> "1", prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
                        [state |-> 0, sig |-> "2", prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
                        [state |-> 0, sig |-> "3", prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
                        [state |-> 0, sig |-> "4", prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}]
                        >>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ \/ /\ (validators[1]).state = 0
               /\ "block" = "block"
               /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
               /\ pc' = "Lbl_2"
            \/ /\ (validators[1]).state = 1
               /\ "block" = "prepareMsg"
               /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union "".prepareSig]
               /\ IF prepareCertificate((validators'[1]))
                     THEN /\ pc' = "Lbl_3"
                     ELSE /\ pc' = "Lbl_8"
            \/ /\ (validators[1]).state = 2
               /\ "block" = "commitMsg"
               /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union "".commitSig]
               /\ IF commitCertificate((validators'[1]))
                     THEN /\ pc' = "Lbl_6"
                     ELSE /\ pc' = "Lbl_8"
         /\ UNCHANGED proposers

Lbl_2 == /\ pc = "Lbl_2"
         /\ validators' = [validators EXCEPT ![1].state = 1]
         /\ pc' = "Lbl_8"
         /\ UNCHANGED proposers

Lbl_3 == /\ pc = "Lbl_3"
         /\ validators' = [validators EXCEPT ![1].prepareSig = {}]
         /\ pc' = "Lbl_4"
         /\ UNCHANGED proposers

Lbl_4 == /\ pc = "Lbl_4"
         /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
         /\ pc' = "Lbl_5"
         /\ UNCHANGED proposers

Lbl_5 == /\ pc = "Lbl_5"
         /\ validators' = [validators EXCEPT ![1].state = 2]
         /\ pc' = "Lbl_8"
         /\ UNCHANGED proposers

Lbl_6 == /\ pc = "Lbl_6"
         /\ validators' = [validators EXCEPT ![1].commitSig = {}]
         /\ pc' = "Lbl_7"
         /\ UNCHANGED proposers

Lbl_7 == /\ pc = "Lbl_7"
         /\ validators' = [validators EXCEPT ![1].state = 9]
         /\ pc' = "Lbl_8"
         /\ UNCHANGED proposers

Lbl_8 == /\ pc = "Lbl_8"
         /\ \/ /\ (validators[2]).state = 0
               /\ "block" = "block"
               /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
               /\ pc' = "Lbl_9"
            \/ /\ (validators[2]).state = 1
               /\ "block" = "prepareMsg"
               /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union "".prepareSig]
               /\ IF prepareCertificate((validators'[2]))
                     THEN /\ pc' = "Lbl_10"
                     ELSE /\ pc' = "Lbl_15"
            \/ /\ (validators[2]).state = 2
               /\ "block" = "commitMsg"
               /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union "".commitSig]
               /\ IF commitCertificate((validators'[2]))
                     THEN /\ pc' = "Lbl_13"
                     ELSE /\ pc' = "Lbl_15"
         /\ UNCHANGED proposers

Lbl_9 == /\ pc = "Lbl_9"
         /\ validators' = [validators EXCEPT ![2].state = 1]
         /\ pc' = "Lbl_15"
         /\ UNCHANGED proposers

Lbl_10 == /\ pc = "Lbl_10"
          /\ validators' = [validators EXCEPT ![2].prepareSig = {}]
          /\ pc' = "Lbl_11"
          /\ UNCHANGED proposers

Lbl_11 == /\ pc = "Lbl_11"
          /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
          /\ pc' = "Lbl_12"
          /\ UNCHANGED proposers

Lbl_12 == /\ pc = "Lbl_12"
          /\ validators' = [validators EXCEPT ![2].state = 2]
          /\ pc' = "Lbl_15"
          /\ UNCHANGED proposers

Lbl_13 == /\ pc = "Lbl_13"
          /\ validators' = [validators EXCEPT ![2].commitSig = {}]
          /\ pc' = "Lbl_14"
          /\ UNCHANGED proposers

Lbl_14 == /\ pc = "Lbl_14"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_15"
          /\ UNCHANGED proposers

Lbl_15 == /\ pc = "Lbl_15"
          /\ \/ /\ (validators[3]).state = 0
                /\ "block" = "block"
                /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                /\ pc' = "Lbl_16"
             \/ /\ (validators[3]).state = 1
                /\ "block" = "prepareMsg"
                /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union "".prepareSig]
                /\ IF prepareCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_17"
                      ELSE /\ pc' = "Lbl_22"
             \/ /\ (validators[3]).state = 2
                /\ "block" = "commitMsg"
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union "".commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_20"
                      ELSE /\ pc' = "Lbl_22"
          /\ UNCHANGED proposers

Lbl_16 == /\ pc = "Lbl_16"
          /\ validators' = [validators EXCEPT ![3].state = 1]
          /\ pc' = "Lbl_22"
          /\ UNCHANGED proposers

Lbl_17 == /\ pc = "Lbl_17"
          /\ validators' = [validators EXCEPT ![3].prepareSig = {}]
          /\ pc' = "Lbl_18"
          /\ UNCHANGED proposers

Lbl_18 == /\ pc = "Lbl_18"
          /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
          /\ pc' = "Lbl_19"
          /\ UNCHANGED proposers

Lbl_19 == /\ pc = "Lbl_19"
          /\ validators' = [validators EXCEPT ![3].state = 2]
          /\ pc' = "Lbl_22"
          /\ UNCHANGED proposers

Lbl_20 == /\ pc = "Lbl_20"
          /\ validators' = [validators EXCEPT ![3].commitSig = {}]
          /\ pc' = "Lbl_21"
          /\ UNCHANGED proposers

Lbl_21 == /\ pc = "Lbl_21"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_22"
          /\ UNCHANGED proposers

Lbl_22 == /\ pc = "Lbl_22"
          /\ \/ /\ (validators[4]).state = 0
                /\ "block" = "block"
                /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                /\ pc' = "Lbl_23"
             \/ /\ (validators[4]).state = 1
                /\ "block" = "prepareMsg"
                /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union "".prepareSig]
                /\ IF prepareCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_24"
                      ELSE /\ pc' = "Lbl_29"
             \/ /\ (validators[4]).state = 2
                /\ "block" = "commitMsg"
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union "".commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_27"
                      ELSE /\ pc' = "Lbl_29"
          /\ UNCHANGED proposers

Lbl_23 == /\ pc = "Lbl_23"
          /\ validators' = [validators EXCEPT ![4].state = 1]
          /\ pc' = "Lbl_29"
          /\ UNCHANGED proposers

Lbl_24 == /\ pc = "Lbl_24"
          /\ validators' = [validators EXCEPT ![4].prepareSig = {}]
          /\ pc' = "Lbl_25"
          /\ UNCHANGED proposers

Lbl_25 == /\ pc = "Lbl_25"
          /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
          /\ pc' = "Lbl_26"
          /\ UNCHANGED proposers

Lbl_26 == /\ pc = "Lbl_26"
          /\ validators' = [validators EXCEPT ![4].state = 2]
          /\ pc' = "Lbl_29"
          /\ UNCHANGED proposers

Lbl_27 == /\ pc = "Lbl_27"
          /\ validators' = [validators EXCEPT ![4].commitSig = {}]
          /\ pc' = "Lbl_28"
          /\ UNCHANGED proposers

Lbl_28 == /\ pc = "Lbl_28"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_29"
          /\ UNCHANGED proposers

Lbl_29 == /\ pc = "Lbl_29"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_30"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[2]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_31"
                      ELSE /\ pc' = "Lbl_36"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_34"
                      ELSE /\ pc' = "Lbl_36"
          /\ UNCHANGED proposers

Lbl_30 == /\ pc = "Lbl_30"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Lbl_36"
          /\ UNCHANGED proposers

Lbl_31 == /\ pc = "Lbl_31"
          /\ validators' = [validators EXCEPT ![1].prepareSig = {}]
          /\ pc' = "Lbl_32"
          /\ UNCHANGED proposers

Lbl_32 == /\ pc = "Lbl_32"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_33"
          /\ UNCHANGED proposers

Lbl_33 == /\ pc = "Lbl_33"
          /\ validators' = [validators EXCEPT ![1].state = 2]
          /\ pc' = "Lbl_36"
          /\ UNCHANGED proposers

Lbl_34 == /\ pc = "Lbl_34"
          /\ validators' = [validators EXCEPT ![1].commitSig = {}]
          /\ pc' = "Lbl_35"
          /\ UNCHANGED proposers

Lbl_35 == /\ pc = "Lbl_35"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_36"
          /\ UNCHANGED proposers

Lbl_36 == /\ pc = "Lbl_36"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_37"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[3]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_38"
                      ELSE /\ pc' = "Lbl_43"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_41"
                      ELSE /\ pc' = "Lbl_43"
          /\ UNCHANGED proposers

Lbl_37 == /\ pc = "Lbl_37"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Lbl_43"
          /\ UNCHANGED proposers

Lbl_38 == /\ pc = "Lbl_38"
          /\ validators' = [validators EXCEPT ![1].prepareSig = {}]
          /\ pc' = "Lbl_39"
          /\ UNCHANGED proposers

Lbl_39 == /\ pc = "Lbl_39"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_40"
          /\ UNCHANGED proposers

Lbl_40 == /\ pc = "Lbl_40"
          /\ validators' = [validators EXCEPT ![1].state = 2]
          /\ pc' = "Lbl_43"
          /\ UNCHANGED proposers

Lbl_41 == /\ pc = "Lbl_41"
          /\ validators' = [validators EXCEPT ![1].commitSig = {}]
          /\ pc' = "Lbl_42"
          /\ UNCHANGED proposers

Lbl_42 == /\ pc = "Lbl_42"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_43"
          /\ UNCHANGED proposers

Lbl_43 == /\ pc = "Lbl_43"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_44"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[4]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_45"
                      ELSE /\ pc' = "Done"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[4]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_48"
                      ELSE /\ pc' = "Done"
          /\ UNCHANGED proposers

Lbl_44 == /\ pc = "Lbl_44"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Done"
          /\ UNCHANGED proposers

Lbl_45 == /\ pc = "Lbl_45"
          /\ validators' = [validators EXCEPT ![1].prepareSig = {}]
          /\ pc' = "Lbl_46"
          /\ UNCHANGED proposers

Lbl_46 == /\ pc = "Lbl_46"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_47"
          /\ UNCHANGED proposers

Lbl_47 == /\ pc = "Lbl_47"
          /\ validators' = [validators EXCEPT ![1].state = 2]
          /\ pc' = "Done"
          /\ UNCHANGED proposers

Lbl_48 == /\ pc = "Lbl_48"
          /\ validators' = [validators EXCEPT ![1].commitSig = {}]
          /\ pc' = "Lbl_49"
          /\ UNCHANGED proposers

Lbl_49 == /\ pc = "Lbl_49"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Done"
          /\ UNCHANGED proposers

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_6 \/ Lbl_7
           \/ Lbl_8 \/ Lbl_9 \/ Lbl_10 \/ Lbl_11 \/ Lbl_12 \/ Lbl_13 \/ Lbl_14
           \/ Lbl_15 \/ Lbl_16 \/ Lbl_17 \/ Lbl_18 \/ Lbl_19 \/ Lbl_20 \/ Lbl_21
           \/ Lbl_22 \/ Lbl_23 \/ Lbl_24 \/ Lbl_25 \/ Lbl_26 \/ Lbl_27 \/ Lbl_28
           \/ Lbl_29 \/ Lbl_30 \/ Lbl_31 \/ Lbl_32 \/ Lbl_33 \/ Lbl_34 \/ Lbl_35
           \/ Lbl_36 \/ Lbl_37 \/ Lbl_38 \/ Lbl_39 \/ Lbl_40 \/ Lbl_41 \/ Lbl_42
           \/ Lbl_43 \/ Lbl_44 \/ Lbl_45 \/ Lbl_46 \/ Lbl_47 \/ Lbl_48 \/ Lbl_49
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


