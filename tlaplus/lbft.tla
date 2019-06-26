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


    \* testing variables to check if sig has been added
    \* if these variables violates invariant properties,
    \* the validator successfully transit to next state.
    validatorPrepareSig1 == "1" \notin validators[1].prepareSig
    validatorCommitSig1 == "1" \notin validators[1].commitSig
    validatorState1 == validators[1].state /= 9



end define;


macro fsm(v, inputType, input) begin
    either \* idle state
        \* transfer to prepare state given a block
        await v.state = 0;
        await inputType = "block";
        v.prepareSig := {v.sig};
        v.state := 1;

    or  \* prepare state
        \* states of both v and input should be prepare state
        await v.state = 1;
        await inputType = "prepareMsg";
        await input.state = 1 \/ input.state = 2;
        \* accumulate prepare signatures
        v.prepareSig := v.prepareSig \union input.prepareSig;
        if prepareCertificate(v)
        then
        \* transfer to commit state if collect a certificate
\*            v.prepareSig := {};
            v.commitSig := {v.sig};
            v.state := 2;
        end if;

    or  \* commit state
        \* states of both v and input should be commit state
        await v.state = 2;
        await inputType = "commitMsg";
        await input.state = 2;
        \* accumulate commit signatures
        v.commitSig := v.commitSig \union input.commitSig;
        if commitCertificate(v)
        then
        \* transfer to idle state in next height given the certificate
\*            v.commitSig := {};
            v.state := 9;
        end if;
    or
        skip;
    end either
end macro;




begin

\* Validator1:

    \* all validators receive the block message
    fsm(validators[1], "block", "");
    fsm(validators[2], "block", "");
    fsm(validators[3], "block", "");
    fsm(validators[4], "block", "");

    \* validators[1] receives prepare msg from other validators
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





validatorPrepareSig1 == "1" \notin validators[1].prepareSig
validatorCommitSig1 == "1" \notin validators[1].commitSig
validatorState1 == validators[1].state /= 9


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
               /\ "".state = 1 \/ "".state = 2
               /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union "".prepareSig]
               /\ IF prepareCertificate((validators'[1]))
                     THEN /\ pc' = "Lbl_3"
                     ELSE /\ pc' = "Lbl_6"
            \/ /\ (validators[1]).state = 2
               /\ "block" = "commitMsg"
               /\ "".state = 2
               /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union "".commitSig]
               /\ IF commitCertificate((validators'[1]))
                     THEN /\ pc' = "Lbl_5"
                     ELSE /\ pc' = "Lbl_6"
            \/ /\ TRUE
               /\ pc' = "Lbl_6"
               /\ UNCHANGED validators
         /\ UNCHANGED proposers

Lbl_2 == /\ pc = "Lbl_2"
         /\ validators' = [validators EXCEPT ![1].state = 1]
         /\ pc' = "Lbl_6"
         /\ UNCHANGED proposers

Lbl_3 == /\ pc = "Lbl_3"
         /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
         /\ pc' = "Lbl_4"
         /\ UNCHANGED proposers

Lbl_4 == /\ pc = "Lbl_4"
         /\ validators' = [validators EXCEPT ![1].state = 2]
         /\ pc' = "Lbl_6"
         /\ UNCHANGED proposers

Lbl_5 == /\ pc = "Lbl_5"
         /\ validators' = [validators EXCEPT ![1].state = 9]
         /\ pc' = "Lbl_6"
         /\ UNCHANGED proposers

Lbl_6 == /\ pc = "Lbl_6"
         /\ \/ /\ (validators[2]).state = 0
               /\ "block" = "block"
               /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
               /\ pc' = "Lbl_7"
            \/ /\ (validators[2]).state = 1
               /\ "block" = "prepareMsg"
               /\ "".state = 1 \/ "".state = 2
               /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union "".prepareSig]
               /\ IF prepareCertificate((validators'[2]))
                     THEN /\ pc' = "Lbl_8"
                     ELSE /\ pc' = "Lbl_11"
            \/ /\ (validators[2]).state = 2
               /\ "block" = "commitMsg"
               /\ "".state = 2
               /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union "".commitSig]
               /\ IF commitCertificate((validators'[2]))
                     THEN /\ pc' = "Lbl_10"
                     ELSE /\ pc' = "Lbl_11"
            \/ /\ TRUE
               /\ pc' = "Lbl_11"
               /\ UNCHANGED validators
         /\ UNCHANGED proposers

Lbl_7 == /\ pc = "Lbl_7"
         /\ validators' = [validators EXCEPT ![2].state = 1]
         /\ pc' = "Lbl_11"
         /\ UNCHANGED proposers

Lbl_8 == /\ pc = "Lbl_8"
         /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
         /\ pc' = "Lbl_9"
         /\ UNCHANGED proposers

Lbl_9 == /\ pc = "Lbl_9"
         /\ validators' = [validators EXCEPT ![2].state = 2]
         /\ pc' = "Lbl_11"
         /\ UNCHANGED proposers

Lbl_10 == /\ pc = "Lbl_10"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_11"
          /\ UNCHANGED proposers

Lbl_11 == /\ pc = "Lbl_11"
          /\ \/ /\ (validators[3]).state = 0
                /\ "block" = "block"
                /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                /\ pc' = "Lbl_12"
             \/ /\ (validators[3]).state = 1
                /\ "block" = "prepareMsg"
                /\ "".state = 1 \/ "".state = 2
                /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union "".prepareSig]
                /\ IF prepareCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_13"
                      ELSE /\ pc' = "Lbl_16"
             \/ /\ (validators[3]).state = 2
                /\ "block" = "commitMsg"
                /\ "".state = 2
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union "".commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_15"
                      ELSE /\ pc' = "Lbl_16"
             \/ /\ TRUE
                /\ pc' = "Lbl_16"
                /\ UNCHANGED validators
          /\ UNCHANGED proposers

Lbl_12 == /\ pc = "Lbl_12"
          /\ validators' = [validators EXCEPT ![3].state = 1]
          /\ pc' = "Lbl_16"
          /\ UNCHANGED proposers

Lbl_13 == /\ pc = "Lbl_13"
          /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
          /\ pc' = "Lbl_14"
          /\ UNCHANGED proposers

Lbl_14 == /\ pc = "Lbl_14"
          /\ validators' = [validators EXCEPT ![3].state = 2]
          /\ pc' = "Lbl_16"
          /\ UNCHANGED proposers

Lbl_15 == /\ pc = "Lbl_15"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_16"
          /\ UNCHANGED proposers

Lbl_16 == /\ pc = "Lbl_16"
          /\ \/ /\ (validators[4]).state = 0
                /\ "block" = "block"
                /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                /\ pc' = "Lbl_17"
             \/ /\ (validators[4]).state = 1
                /\ "block" = "prepareMsg"
                /\ "".state = 1 \/ "".state = 2
                /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union "".prepareSig]
                /\ IF prepareCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_18"
                      ELSE /\ pc' = "Lbl_21"
             \/ /\ (validators[4]).state = 2
                /\ "block" = "commitMsg"
                /\ "".state = 2
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union "".commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_20"
                      ELSE /\ pc' = "Lbl_21"
             \/ /\ TRUE
                /\ pc' = "Lbl_21"
                /\ UNCHANGED validators
          /\ UNCHANGED proposers

Lbl_17 == /\ pc = "Lbl_17"
          /\ validators' = [validators EXCEPT ![4].state = 1]
          /\ pc' = "Lbl_21"
          /\ UNCHANGED proposers

Lbl_18 == /\ pc = "Lbl_18"
          /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
          /\ pc' = "Lbl_19"
          /\ UNCHANGED proposers

Lbl_19 == /\ pc = "Lbl_19"
          /\ validators' = [validators EXCEPT ![4].state = 2]
          /\ pc' = "Lbl_21"
          /\ UNCHANGED proposers

Lbl_20 == /\ pc = "Lbl_20"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_21"
          /\ UNCHANGED proposers

Lbl_21 == /\ pc = "Lbl_21"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_22"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[2]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_23"
                      ELSE /\ pc' = "Lbl_26"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_25"
                      ELSE /\ pc' = "Lbl_26"
             \/ /\ TRUE
                /\ pc' = "Lbl_26"
                /\ UNCHANGED validators
          /\ UNCHANGED proposers

Lbl_22 == /\ pc = "Lbl_22"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Lbl_26"
          /\ UNCHANGED proposers

Lbl_23 == /\ pc = "Lbl_23"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_24"
          /\ UNCHANGED proposers

Lbl_24 == /\ pc = "Lbl_24"
          /\ validators' = [validators EXCEPT ![1].state = 2]
          /\ pc' = "Lbl_26"
          /\ UNCHANGED proposers

Lbl_25 == /\ pc = "Lbl_25"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_26"
          /\ UNCHANGED proposers

Lbl_26 == /\ pc = "Lbl_26"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_27"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[3]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_28"
                      ELSE /\ pc' = "Lbl_31"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_30"
                      ELSE /\ pc' = "Lbl_31"
             \/ /\ TRUE
                /\ pc' = "Lbl_31"
                /\ UNCHANGED validators
          /\ UNCHANGED proposers

Lbl_27 == /\ pc = "Lbl_27"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Lbl_31"
          /\ UNCHANGED proposers

Lbl_28 == /\ pc = "Lbl_28"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_29"
          /\ UNCHANGED proposers

Lbl_29 == /\ pc = "Lbl_29"
          /\ validators' = [validators EXCEPT ![1].state = 2]
          /\ pc' = "Lbl_31"
          /\ UNCHANGED proposers

Lbl_30 == /\ pc = "Lbl_30"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_31"
          /\ UNCHANGED proposers

Lbl_31 == /\ pc = "Lbl_31"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_32"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[4]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_33"
                      ELSE /\ pc' = "Done"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[4]).state = 2
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[4]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_35"
                      ELSE /\ pc' = "Done"
             \/ /\ TRUE
                /\ pc' = "Done"
                /\ UNCHANGED validators
          /\ UNCHANGED proposers

Lbl_32 == /\ pc = "Lbl_32"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Done"
          /\ UNCHANGED proposers

Lbl_33 == /\ pc = "Lbl_33"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_34"
          /\ UNCHANGED proposers

Lbl_34 == /\ pc = "Lbl_34"
          /\ validators' = [validators EXCEPT ![1].state = 2]
          /\ pc' = "Done"
          /\ UNCHANGED proposers

Lbl_35 == /\ pc = "Lbl_35"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Done"
          /\ UNCHANGED proposers

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_6 \/ Lbl_7
           \/ Lbl_8 \/ Lbl_9 \/ Lbl_10 \/ Lbl_11 \/ Lbl_12 \/ Lbl_13 \/ Lbl_14
           \/ Lbl_15 \/ Lbl_16 \/ Lbl_17 \/ Lbl_18 \/ Lbl_19 \/ Lbl_20 \/ Lbl_21
           \/ Lbl_22 \/ Lbl_23 \/ Lbl_24 \/ Lbl_25 \/ Lbl_26 \/ Lbl_27 \/ Lbl_28
           \/ Lbl_29 \/ Lbl_30 \/ Lbl_31 \/ Lbl_32 \/ Lbl_33 \/ Lbl_34 \/ Lbl_35
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================

