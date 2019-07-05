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
    validatorIndices = {1,2,3,4}
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
    end either;
end macro;


macro broadcast(number, inputType) begin
    \* otherValidators := validatorIndices \ {number};
    \* with id \in {1} do
        \* skip;
        fsm(validators[1],inputType,validators[number]);
        fsm(validators[2],inputType,validators[number]);
        fsm(validators[3],inputType,validators[number]);
        fsm(validators[4],inputType,validators[number]);
    \* end with;
end macro;

begin

    \* all validators receive the block message
    fsm(validators[1], "block", "");
    fsm(validators[2], "block", "");
    fsm(validators[3], "block", "");
    fsm(validators[4], "block", "");

    \* broadcast prepare message
    broadcast(1,"prepareMsg");
    broadcast(2,"prepareMsg");
    broadcast(3,"prepareMsg");
    broadcast(4,"prepareMSg");

    broadcast(1,"commitMsg");
    broadcast(2,"commitMsg");
    broadcast(3,"commitMsg");
    broadcast(4,"commitMsg");





end algorithm;*)


\* BEGIN TRANSLATION
VARIABLES proposers, validators, validatorIndices, pc

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


vars == << proposers, validators, validatorIndices, pc >>

Init == (* Global variables *)
        /\ proposers = <<"p1","p2">>
        /\ validators =              <<
                        [state |-> 0, sig |-> "1", prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
                        [state |-> 0, sig |-> "2", prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
                        [state |-> 0, sig |-> "3", prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
                        [state |-> 0, sig |-> "4", prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}]
                        >>
        /\ validatorIndices = {1,2,3,4}
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
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ validators' = [validators EXCEPT ![1].state = 1]
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
         /\ pc' = "Lbl_4"
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ validators' = [validators EXCEPT ![1].state = 2]
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ validators' = [validators EXCEPT ![1].state = 9]
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << proposers, validatorIndices >>

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
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ validators' = [validators EXCEPT ![2].state = 1]
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
         /\ pc' = "Lbl_9"
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_9 == /\ pc = "Lbl_9"
         /\ validators' = [validators EXCEPT ![2].state = 2]
         /\ pc' = "Lbl_11"
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_10 == /\ pc = "Lbl_10"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_11"
          /\ UNCHANGED << proposers, validatorIndices >>

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
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_12 == /\ pc = "Lbl_12"
          /\ validators' = [validators EXCEPT ![3].state = 1]
          /\ pc' = "Lbl_16"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_13 == /\ pc = "Lbl_13"
          /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
          /\ pc' = "Lbl_14"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_14 == /\ pc = "Lbl_14"
          /\ validators' = [validators EXCEPT ![3].state = 2]
          /\ pc' = "Lbl_16"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_15 == /\ pc = "Lbl_15"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_16"
          /\ UNCHANGED << proposers, validatorIndices >>

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
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_17 == /\ pc = "Lbl_17"
          /\ validators' = [validators EXCEPT ![4].state = 1]
          /\ pc' = "Lbl_21"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_18 == /\ pc = "Lbl_18"
          /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
          /\ pc' = "Lbl_19"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_19 == /\ pc = "Lbl_19"
          /\ validators' = [validators EXCEPT ![4].state = 2]
          /\ pc' = "Lbl_21"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_20 == /\ pc = "Lbl_20"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_21"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_21 == /\ pc = "Lbl_21"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_22"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[1]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_23"
                      ELSE /\ pc' = "Lbl_26"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[1]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_25"
                      ELSE /\ pc' = "Lbl_26"
             \/ /\ TRUE
                /\ pc' = "Lbl_26"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_22 == /\ pc = "Lbl_22"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Lbl_26"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_23 == /\ pc = "Lbl_23"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_24"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_24 == /\ pc = "Lbl_24"
          /\ validators' = [validators EXCEPT ![1].state = 2]
          /\ pc' = "Lbl_26"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_25 == /\ pc = "Lbl_25"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_26"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_26 == /\ pc = "Lbl_26"
          /\ \/ /\ (validators[2]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                /\ pc' = "Lbl_27"
             \/ /\ (validators[2]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[1]).prepareSig]
                /\ IF prepareCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_28"
                      ELSE /\ pc' = "Lbl_31"
             \/ /\ (validators[2]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[1]).commitSig]
                /\ IF commitCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_30"
                      ELSE /\ pc' = "Lbl_31"
             \/ /\ TRUE
                /\ pc' = "Lbl_31"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_27 == /\ pc = "Lbl_27"
          /\ validators' = [validators EXCEPT ![2].state = 1]
          /\ pc' = "Lbl_31"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_28 == /\ pc = "Lbl_28"
          /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
          /\ pc' = "Lbl_29"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_29 == /\ pc = "Lbl_29"
          /\ validators' = [validators EXCEPT ![2].state = 2]
          /\ pc' = "Lbl_31"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_30 == /\ pc = "Lbl_30"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_31"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_31 == /\ pc = "Lbl_31"
          /\ \/ /\ (validators[3]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                /\ pc' = "Lbl_32"
             \/ /\ (validators[3]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[1]).prepareSig]
                /\ IF prepareCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_33"
                      ELSE /\ pc' = "Lbl_36"
             \/ /\ (validators[3]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[1]).commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_35"
                      ELSE /\ pc' = "Lbl_36"
             \/ /\ TRUE
                /\ pc' = "Lbl_36"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_32 == /\ pc = "Lbl_32"
          /\ validators' = [validators EXCEPT ![3].state = 1]
          /\ pc' = "Lbl_36"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_33 == /\ pc = "Lbl_33"
          /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
          /\ pc' = "Lbl_34"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_34 == /\ pc = "Lbl_34"
          /\ validators' = [validators EXCEPT ![3].state = 2]
          /\ pc' = "Lbl_36"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_35 == /\ pc = "Lbl_35"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_36"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_36 == /\ pc = "Lbl_36"
          /\ \/ /\ (validators[4]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                /\ pc' = "Lbl_37"
             \/ /\ (validators[4]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[1]).prepareSig]
                /\ IF prepareCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_38"
                      ELSE /\ pc' = "Lbl_41"
             \/ /\ (validators[4]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[1]).commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_40"
                      ELSE /\ pc' = "Lbl_41"
             \/ /\ TRUE
                /\ pc' = "Lbl_41"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_37 == /\ pc = "Lbl_37"
          /\ validators' = [validators EXCEPT ![4].state = 1]
          /\ pc' = "Lbl_41"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_38 == /\ pc = "Lbl_38"
          /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
          /\ pc' = "Lbl_39"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_39 == /\ pc = "Lbl_39"
          /\ validators' = [validators EXCEPT ![4].state = 2]
          /\ pc' = "Lbl_41"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_40 == /\ pc = "Lbl_40"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_41"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_41 == /\ pc = "Lbl_41"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_42"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[2]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_43"
                      ELSE /\ pc' = "Lbl_46"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_45"
                      ELSE /\ pc' = "Lbl_46"
             \/ /\ TRUE
                /\ pc' = "Lbl_46"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_42 == /\ pc = "Lbl_42"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Lbl_46"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_43 == /\ pc = "Lbl_43"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_44"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_44 == /\ pc = "Lbl_44"
          /\ validators' = [validators EXCEPT ![1].state = 2]
          /\ pc' = "Lbl_46"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_45 == /\ pc = "Lbl_45"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_46"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_46 == /\ pc = "Lbl_46"
          /\ \/ /\ (validators[2]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                /\ pc' = "Lbl_47"
             \/ /\ (validators[2]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[2]).prepareSig]
                /\ IF prepareCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_48"
                      ELSE /\ pc' = "Lbl_51"
             \/ /\ (validators[2]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_50"
                      ELSE /\ pc' = "Lbl_51"
             \/ /\ TRUE
                /\ pc' = "Lbl_51"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_47 == /\ pc = "Lbl_47"
          /\ validators' = [validators EXCEPT ![2].state = 1]
          /\ pc' = "Lbl_51"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_48 == /\ pc = "Lbl_48"
          /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
          /\ pc' = "Lbl_49"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_49 == /\ pc = "Lbl_49"
          /\ validators' = [validators EXCEPT ![2].state = 2]
          /\ pc' = "Lbl_51"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_50 == /\ pc = "Lbl_50"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_51"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_51 == /\ pc = "Lbl_51"
          /\ \/ /\ (validators[3]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                /\ pc' = "Lbl_52"
             \/ /\ (validators[3]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[2]).prepareSig]
                /\ IF prepareCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_53"
                      ELSE /\ pc' = "Lbl_56"
             \/ /\ (validators[3]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_55"
                      ELSE /\ pc' = "Lbl_56"
             \/ /\ TRUE
                /\ pc' = "Lbl_56"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_52 == /\ pc = "Lbl_52"
          /\ validators' = [validators EXCEPT ![3].state = 1]
          /\ pc' = "Lbl_56"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_53 == /\ pc = "Lbl_53"
          /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
          /\ pc' = "Lbl_54"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_54 == /\ pc = "Lbl_54"
          /\ validators' = [validators EXCEPT ![3].state = 2]
          /\ pc' = "Lbl_56"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_55 == /\ pc = "Lbl_55"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_56"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_56 == /\ pc = "Lbl_56"
          /\ \/ /\ (validators[4]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                /\ pc' = "Lbl_57"
             \/ /\ (validators[4]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[2]).prepareSig]
                /\ IF prepareCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_58"
                      ELSE /\ pc' = "Lbl_61"
             \/ /\ (validators[4]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_60"
                      ELSE /\ pc' = "Lbl_61"
             \/ /\ TRUE
                /\ pc' = "Lbl_61"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_57 == /\ pc = "Lbl_57"
          /\ validators' = [validators EXCEPT ![4].state = 1]
          /\ pc' = "Lbl_61"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_58 == /\ pc = "Lbl_58"
          /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
          /\ pc' = "Lbl_59"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_59 == /\ pc = "Lbl_59"
          /\ validators' = [validators EXCEPT ![4].state = 2]
          /\ pc' = "Lbl_61"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_60 == /\ pc = "Lbl_60"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_61"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_61 == /\ pc = "Lbl_61"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_62"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[3]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_63"
                      ELSE /\ pc' = "Lbl_66"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_65"
                      ELSE /\ pc' = "Lbl_66"
             \/ /\ TRUE
                /\ pc' = "Lbl_66"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_62 == /\ pc = "Lbl_62"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Lbl_66"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_63 == /\ pc = "Lbl_63"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_64"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_64 == /\ pc = "Lbl_64"
          /\ validators' = [validators EXCEPT ![1].state = 2]
          /\ pc' = "Lbl_66"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_65 == /\ pc = "Lbl_65"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_66"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_66 == /\ pc = "Lbl_66"
          /\ \/ /\ (validators[2]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                /\ pc' = "Lbl_67"
             \/ /\ (validators[2]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[3]).prepareSig]
                /\ IF prepareCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_68"
                      ELSE /\ pc' = "Lbl_71"
             \/ /\ (validators[2]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_70"
                      ELSE /\ pc' = "Lbl_71"
             \/ /\ TRUE
                /\ pc' = "Lbl_71"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_67 == /\ pc = "Lbl_67"
          /\ validators' = [validators EXCEPT ![2].state = 1]
          /\ pc' = "Lbl_71"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_68 == /\ pc = "Lbl_68"
          /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
          /\ pc' = "Lbl_69"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_69 == /\ pc = "Lbl_69"
          /\ validators' = [validators EXCEPT ![2].state = 2]
          /\ pc' = "Lbl_71"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_70 == /\ pc = "Lbl_70"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_71"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_71 == /\ pc = "Lbl_71"
          /\ \/ /\ (validators[3]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                /\ pc' = "Lbl_72"
             \/ /\ (validators[3]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[3]).prepareSig]
                /\ IF prepareCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_73"
                      ELSE /\ pc' = "Lbl_76"
             \/ /\ (validators[3]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_75"
                      ELSE /\ pc' = "Lbl_76"
             \/ /\ TRUE
                /\ pc' = "Lbl_76"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_72 == /\ pc = "Lbl_72"
          /\ validators' = [validators EXCEPT ![3].state = 1]
          /\ pc' = "Lbl_76"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_73 == /\ pc = "Lbl_73"
          /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
          /\ pc' = "Lbl_74"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_74 == /\ pc = "Lbl_74"
          /\ validators' = [validators EXCEPT ![3].state = 2]
          /\ pc' = "Lbl_76"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_75 == /\ pc = "Lbl_75"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_76"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_76 == /\ pc = "Lbl_76"
          /\ \/ /\ (validators[4]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                /\ pc' = "Lbl_77"
             \/ /\ (validators[4]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[3]).prepareSig]
                /\ IF prepareCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_78"
                      ELSE /\ pc' = "Lbl_81"
             \/ /\ (validators[4]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_80"
                      ELSE /\ pc' = "Lbl_81"
             \/ /\ TRUE
                /\ pc' = "Lbl_81"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_77 == /\ pc = "Lbl_77"
          /\ validators' = [validators EXCEPT ![4].state = 1]
          /\ pc' = "Lbl_81"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_78 == /\ pc = "Lbl_78"
          /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
          /\ pc' = "Lbl_79"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_79 == /\ pc = "Lbl_79"
          /\ validators' = [validators EXCEPT ![4].state = 2]
          /\ pc' = "Lbl_81"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_80 == /\ pc = "Lbl_80"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_81"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_81 == /\ pc = "Lbl_81"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMSg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_82"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMSg" = "prepareMsg"
                /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[4]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_83"
                      ELSE /\ pc' = "Lbl_86"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMSg" = "commitMsg"
                /\ (validators[4]).state = 2
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[4]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_85"
                      ELSE /\ pc' = "Lbl_86"
             \/ /\ TRUE
                /\ pc' = "Lbl_86"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_82 == /\ pc = "Lbl_82"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Lbl_86"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_83 == /\ pc = "Lbl_83"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_84"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_84 == /\ pc = "Lbl_84"
          /\ validators' = [validators EXCEPT ![1].state = 2]
          /\ pc' = "Lbl_86"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_85 == /\ pc = "Lbl_85"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_86"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_86 == /\ pc = "Lbl_86"
          /\ \/ /\ (validators[2]).state = 0
                /\ "prepareMSg" = "block"
                /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                /\ pc' = "Lbl_87"
             \/ /\ (validators[2]).state = 1
                /\ "prepareMSg" = "prepareMsg"
                /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[4]).prepareSig]
                /\ IF prepareCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_88"
                      ELSE /\ pc' = "Lbl_91"
             \/ /\ (validators[2]).state = 2
                /\ "prepareMSg" = "commitMsg"
                /\ (validators[4]).state = 2
                /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[4]).commitSig]
                /\ IF commitCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_90"
                      ELSE /\ pc' = "Lbl_91"
             \/ /\ TRUE
                /\ pc' = "Lbl_91"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_87 == /\ pc = "Lbl_87"
          /\ validators' = [validators EXCEPT ![2].state = 1]
          /\ pc' = "Lbl_91"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_88 == /\ pc = "Lbl_88"
          /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
          /\ pc' = "Lbl_89"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_89 == /\ pc = "Lbl_89"
          /\ validators' = [validators EXCEPT ![2].state = 2]
          /\ pc' = "Lbl_91"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_90 == /\ pc = "Lbl_90"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_91"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_91 == /\ pc = "Lbl_91"
          /\ \/ /\ (validators[3]).state = 0
                /\ "prepareMSg" = "block"
                /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                /\ pc' = "Lbl_92"
             \/ /\ (validators[3]).state = 1
                /\ "prepareMSg" = "prepareMsg"
                /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[4]).prepareSig]
                /\ IF prepareCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_93"
                      ELSE /\ pc' = "Lbl_96"
             \/ /\ (validators[3]).state = 2
                /\ "prepareMSg" = "commitMsg"
                /\ (validators[4]).state = 2
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[4]).commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_95"
                      ELSE /\ pc' = "Lbl_96"
             \/ /\ TRUE
                /\ pc' = "Lbl_96"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_92 == /\ pc = "Lbl_92"
          /\ validators' = [validators EXCEPT ![3].state = 1]
          /\ pc' = "Lbl_96"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_93 == /\ pc = "Lbl_93"
          /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
          /\ pc' = "Lbl_94"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_94 == /\ pc = "Lbl_94"
          /\ validators' = [validators EXCEPT ![3].state = 2]
          /\ pc' = "Lbl_96"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_95 == /\ pc = "Lbl_95"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_96"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_96 == /\ pc = "Lbl_96"
          /\ \/ /\ (validators[4]).state = 0
                /\ "prepareMSg" = "block"
                /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                /\ pc' = "Lbl_97"
             \/ /\ (validators[4]).state = 1
                /\ "prepareMSg" = "prepareMsg"
                /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[4]).prepareSig]
                /\ IF prepareCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_98"
                      ELSE /\ pc' = "Lbl_101"
             \/ /\ (validators[4]).state = 2
                /\ "prepareMSg" = "commitMsg"
                /\ (validators[4]).state = 2
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[4]).commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_100"
                      ELSE /\ pc' = "Lbl_101"
             \/ /\ TRUE
                /\ pc' = "Lbl_101"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_97 == /\ pc = "Lbl_97"
          /\ validators' = [validators EXCEPT ![4].state = 1]
          /\ pc' = "Lbl_101"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_98 == /\ pc = "Lbl_98"
          /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
          /\ pc' = "Lbl_99"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_99 == /\ pc = "Lbl_99"
          /\ validators' = [validators EXCEPT ![4].state = 2]
          /\ pc' = "Lbl_101"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_100 == /\ pc = "Lbl_100"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_101"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_101 == /\ pc = "Lbl_101"
           /\ \/ /\ (validators[1]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                 /\ pc' = "Lbl_102"
              \/ /\ (validators[1]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[1]).prepareSig]
                 /\ IF prepareCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_103"
                       ELSE /\ pc' = "Lbl_106"
              \/ /\ (validators[1]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_105"
                       ELSE /\ pc' = "Lbl_106"
              \/ /\ TRUE
                 /\ pc' = "Lbl_106"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_102 == /\ pc = "Lbl_102"
           /\ validators' = [validators EXCEPT ![1].state = 1]
           /\ pc' = "Lbl_106"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_103 == /\ pc = "Lbl_103"
           /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
           /\ pc' = "Lbl_104"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_104 == /\ pc = "Lbl_104"
           /\ validators' = [validators EXCEPT ![1].state = 2]
           /\ pc' = "Lbl_106"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_105 == /\ pc = "Lbl_105"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_106"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_106 == /\ pc = "Lbl_106"
           /\ \/ /\ (validators[2]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                 /\ pc' = "Lbl_107"
              \/ /\ (validators[2]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[1]).prepareSig]
                 /\ IF prepareCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_108"
                       ELSE /\ pc' = "Lbl_111"
              \/ /\ (validators[2]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_110"
                       ELSE /\ pc' = "Lbl_111"
              \/ /\ TRUE
                 /\ pc' = "Lbl_111"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_107 == /\ pc = "Lbl_107"
           /\ validators' = [validators EXCEPT ![2].state = 1]
           /\ pc' = "Lbl_111"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_108 == /\ pc = "Lbl_108"
           /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
           /\ pc' = "Lbl_109"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_109 == /\ pc = "Lbl_109"
           /\ validators' = [validators EXCEPT ![2].state = 2]
           /\ pc' = "Lbl_111"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_110 == /\ pc = "Lbl_110"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_111"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_111 == /\ pc = "Lbl_111"
           /\ \/ /\ (validators[3]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                 /\ pc' = "Lbl_112"
              \/ /\ (validators[3]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[1]).prepareSig]
                 /\ IF prepareCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_113"
                       ELSE /\ pc' = "Lbl_116"
              \/ /\ (validators[3]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_115"
                       ELSE /\ pc' = "Lbl_116"
              \/ /\ TRUE
                 /\ pc' = "Lbl_116"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_112 == /\ pc = "Lbl_112"
           /\ validators' = [validators EXCEPT ![3].state = 1]
           /\ pc' = "Lbl_116"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_113 == /\ pc = "Lbl_113"
           /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
           /\ pc' = "Lbl_114"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_114 == /\ pc = "Lbl_114"
           /\ validators' = [validators EXCEPT ![3].state = 2]
           /\ pc' = "Lbl_116"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_115 == /\ pc = "Lbl_115"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_116"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_116 == /\ pc = "Lbl_116"
           /\ \/ /\ (validators[4]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                 /\ pc' = "Lbl_117"
              \/ /\ (validators[4]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[1]).prepareSig]
                 /\ IF prepareCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_118"
                       ELSE /\ pc' = "Lbl_121"
              \/ /\ (validators[4]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_120"
                       ELSE /\ pc' = "Lbl_121"
              \/ /\ TRUE
                 /\ pc' = "Lbl_121"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_117 == /\ pc = "Lbl_117"
           /\ validators' = [validators EXCEPT ![4].state = 1]
           /\ pc' = "Lbl_121"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_118 == /\ pc = "Lbl_118"
           /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
           /\ pc' = "Lbl_119"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_119 == /\ pc = "Lbl_119"
           /\ validators' = [validators EXCEPT ![4].state = 2]
           /\ pc' = "Lbl_121"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_120 == /\ pc = "Lbl_120"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_121"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_121 == /\ pc = "Lbl_121"
           /\ \/ /\ (validators[1]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                 /\ pc' = "Lbl_122"
              \/ /\ (validators[1]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[2]).prepareSig]
                 /\ IF prepareCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_123"
                       ELSE /\ pc' = "Lbl_126"
              \/ /\ (validators[1]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_125"
                       ELSE /\ pc' = "Lbl_126"
              \/ /\ TRUE
                 /\ pc' = "Lbl_126"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_122 == /\ pc = "Lbl_122"
           /\ validators' = [validators EXCEPT ![1].state = 1]
           /\ pc' = "Lbl_126"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_123 == /\ pc = "Lbl_123"
           /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
           /\ pc' = "Lbl_124"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_124 == /\ pc = "Lbl_124"
           /\ validators' = [validators EXCEPT ![1].state = 2]
           /\ pc' = "Lbl_126"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_125 == /\ pc = "Lbl_125"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_126"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_126 == /\ pc = "Lbl_126"
           /\ \/ /\ (validators[2]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                 /\ pc' = "Lbl_127"
              \/ /\ (validators[2]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[2]).prepareSig]
                 /\ IF prepareCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_128"
                       ELSE /\ pc' = "Lbl_131"
              \/ /\ (validators[2]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_130"
                       ELSE /\ pc' = "Lbl_131"
              \/ /\ TRUE
                 /\ pc' = "Lbl_131"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_127 == /\ pc = "Lbl_127"
           /\ validators' = [validators EXCEPT ![2].state = 1]
           /\ pc' = "Lbl_131"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_128 == /\ pc = "Lbl_128"
           /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
           /\ pc' = "Lbl_129"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_129 == /\ pc = "Lbl_129"
           /\ validators' = [validators EXCEPT ![2].state = 2]
           /\ pc' = "Lbl_131"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_130 == /\ pc = "Lbl_130"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_131"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_131 == /\ pc = "Lbl_131"
           /\ \/ /\ (validators[3]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                 /\ pc' = "Lbl_132"
              \/ /\ (validators[3]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[2]).prepareSig]
                 /\ IF prepareCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_133"
                       ELSE /\ pc' = "Lbl_136"
              \/ /\ (validators[3]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_135"
                       ELSE /\ pc' = "Lbl_136"
              \/ /\ TRUE
                 /\ pc' = "Lbl_136"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_132 == /\ pc = "Lbl_132"
           /\ validators' = [validators EXCEPT ![3].state = 1]
           /\ pc' = "Lbl_136"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_133 == /\ pc = "Lbl_133"
           /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
           /\ pc' = "Lbl_134"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_134 == /\ pc = "Lbl_134"
           /\ validators' = [validators EXCEPT ![3].state = 2]
           /\ pc' = "Lbl_136"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_135 == /\ pc = "Lbl_135"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_136"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_136 == /\ pc = "Lbl_136"
           /\ \/ /\ (validators[4]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                 /\ pc' = "Lbl_137"
              \/ /\ (validators[4]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[2]).prepareSig]
                 /\ IF prepareCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_138"
                       ELSE /\ pc' = "Lbl_141"
              \/ /\ (validators[4]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_140"
                       ELSE /\ pc' = "Lbl_141"
              \/ /\ TRUE
                 /\ pc' = "Lbl_141"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_137 == /\ pc = "Lbl_137"
           /\ validators' = [validators EXCEPT ![4].state = 1]
           /\ pc' = "Lbl_141"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_138 == /\ pc = "Lbl_138"
           /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
           /\ pc' = "Lbl_139"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_139 == /\ pc = "Lbl_139"
           /\ validators' = [validators EXCEPT ![4].state = 2]
           /\ pc' = "Lbl_141"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_140 == /\ pc = "Lbl_140"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_141"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_141 == /\ pc = "Lbl_141"
           /\ \/ /\ (validators[1]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                 /\ pc' = "Lbl_142"
              \/ /\ (validators[1]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[3]).prepareSig]
                 /\ IF prepareCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_143"
                       ELSE /\ pc' = "Lbl_146"
              \/ /\ (validators[1]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_145"
                       ELSE /\ pc' = "Lbl_146"
              \/ /\ TRUE
                 /\ pc' = "Lbl_146"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_142 == /\ pc = "Lbl_142"
           /\ validators' = [validators EXCEPT ![1].state = 1]
           /\ pc' = "Lbl_146"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_143 == /\ pc = "Lbl_143"
           /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
           /\ pc' = "Lbl_144"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_144 == /\ pc = "Lbl_144"
           /\ validators' = [validators EXCEPT ![1].state = 2]
           /\ pc' = "Lbl_146"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_145 == /\ pc = "Lbl_145"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_146"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_146 == /\ pc = "Lbl_146"
           /\ \/ /\ (validators[2]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                 /\ pc' = "Lbl_147"
              \/ /\ (validators[2]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[3]).prepareSig]
                 /\ IF prepareCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_148"
                       ELSE /\ pc' = "Lbl_151"
              \/ /\ (validators[2]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_150"
                       ELSE /\ pc' = "Lbl_151"
              \/ /\ TRUE
                 /\ pc' = "Lbl_151"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_147 == /\ pc = "Lbl_147"
           /\ validators' = [validators EXCEPT ![2].state = 1]
           /\ pc' = "Lbl_151"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_148 == /\ pc = "Lbl_148"
           /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
           /\ pc' = "Lbl_149"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_149 == /\ pc = "Lbl_149"
           /\ validators' = [validators EXCEPT ![2].state = 2]
           /\ pc' = "Lbl_151"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_150 == /\ pc = "Lbl_150"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_151"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_151 == /\ pc = "Lbl_151"
           /\ \/ /\ (validators[3]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                 /\ pc' = "Lbl_152"
              \/ /\ (validators[3]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[3]).prepareSig]
                 /\ IF prepareCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_153"
                       ELSE /\ pc' = "Lbl_156"
              \/ /\ (validators[3]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_155"
                       ELSE /\ pc' = "Lbl_156"
              \/ /\ TRUE
                 /\ pc' = "Lbl_156"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_152 == /\ pc = "Lbl_152"
           /\ validators' = [validators EXCEPT ![3].state = 1]
           /\ pc' = "Lbl_156"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_153 == /\ pc = "Lbl_153"
           /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
           /\ pc' = "Lbl_154"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_154 == /\ pc = "Lbl_154"
           /\ validators' = [validators EXCEPT ![3].state = 2]
           /\ pc' = "Lbl_156"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_155 == /\ pc = "Lbl_155"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_156"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_156 == /\ pc = "Lbl_156"
           /\ \/ /\ (validators[4]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                 /\ pc' = "Lbl_157"
              \/ /\ (validators[4]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[3]).prepareSig]
                 /\ IF prepareCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_158"
                       ELSE /\ pc' = "Lbl_161"
              \/ /\ (validators[4]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_160"
                       ELSE /\ pc' = "Lbl_161"
              \/ /\ TRUE
                 /\ pc' = "Lbl_161"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_157 == /\ pc = "Lbl_157"
           /\ validators' = [validators EXCEPT ![4].state = 1]
           /\ pc' = "Lbl_161"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_158 == /\ pc = "Lbl_158"
           /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
           /\ pc' = "Lbl_159"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_159 == /\ pc = "Lbl_159"
           /\ validators' = [validators EXCEPT ![4].state = 2]
           /\ pc' = "Lbl_161"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_160 == /\ pc = "Lbl_160"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_161"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_161 == /\ pc = "Lbl_161"
           /\ \/ /\ (validators[1]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                 /\ pc' = "Lbl_162"
              \/ /\ (validators[1]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_163"
                       ELSE /\ pc' = "Lbl_166"
              \/ /\ (validators[1]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_165"
                       ELSE /\ pc' = "Lbl_166"
              \/ /\ TRUE
                 /\ pc' = "Lbl_166"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_162 == /\ pc = "Lbl_162"
           /\ validators' = [validators EXCEPT ![1].state = 1]
           /\ pc' = "Lbl_166"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_163 == /\ pc = "Lbl_163"
           /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
           /\ pc' = "Lbl_164"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_164 == /\ pc = "Lbl_164"
           /\ validators' = [validators EXCEPT ![1].state = 2]
           /\ pc' = "Lbl_166"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_165 == /\ pc = "Lbl_165"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_166"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_166 == /\ pc = "Lbl_166"
           /\ \/ /\ (validators[2]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                 /\ pc' = "Lbl_167"
              \/ /\ (validators[2]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_168"
                       ELSE /\ pc' = "Lbl_171"
              \/ /\ (validators[2]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_170"
                       ELSE /\ pc' = "Lbl_171"
              \/ /\ TRUE
                 /\ pc' = "Lbl_171"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_167 == /\ pc = "Lbl_167"
           /\ validators' = [validators EXCEPT ![2].state = 1]
           /\ pc' = "Lbl_171"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_168 == /\ pc = "Lbl_168"
           /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
           /\ pc' = "Lbl_169"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_169 == /\ pc = "Lbl_169"
           /\ validators' = [validators EXCEPT ![2].state = 2]
           /\ pc' = "Lbl_171"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_170 == /\ pc = "Lbl_170"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_171"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_171 == /\ pc = "Lbl_171"
           /\ \/ /\ (validators[3]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                 /\ pc' = "Lbl_172"
              \/ /\ (validators[3]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_173"
                       ELSE /\ pc' = "Lbl_176"
              \/ /\ (validators[3]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_175"
                       ELSE /\ pc' = "Lbl_176"
              \/ /\ TRUE
                 /\ pc' = "Lbl_176"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_172 == /\ pc = "Lbl_172"
           /\ validators' = [validators EXCEPT ![3].state = 1]
           /\ pc' = "Lbl_176"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_173 == /\ pc = "Lbl_173"
           /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
           /\ pc' = "Lbl_174"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_174 == /\ pc = "Lbl_174"
           /\ validators' = [validators EXCEPT ![3].state = 2]
           /\ pc' = "Lbl_176"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_175 == /\ pc = "Lbl_175"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_176"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_176 == /\ pc = "Lbl_176"
           /\ \/ /\ (validators[4]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                 /\ pc' = "Lbl_177"
              \/ /\ (validators[4]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_178"
                       ELSE /\ pc' = "Done"
              \/ /\ (validators[4]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_180"
                       ELSE /\ pc' = "Done"
              \/ /\ TRUE
                 /\ pc' = "Done"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_177 == /\ pc = "Lbl_177"
           /\ validators' = [validators EXCEPT ![4].state = 1]
           /\ pc' = "Done"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_178 == /\ pc = "Lbl_178"
           /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
           /\ pc' = "Lbl_179"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_179 == /\ pc = "Lbl_179"
           /\ validators' = [validators EXCEPT ![4].state = 2]
           /\ pc' = "Done"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_180 == /\ pc = "Lbl_180"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Done"
           /\ UNCHANGED << proposers, validatorIndices >>

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_6 \/ Lbl_7
           \/ Lbl_8 \/ Lbl_9 \/ Lbl_10 \/ Lbl_11 \/ Lbl_12 \/ Lbl_13 \/ Lbl_14
           \/ Lbl_15 \/ Lbl_16 \/ Lbl_17 \/ Lbl_18 \/ Lbl_19 \/ Lbl_20 \/ Lbl_21
           \/ Lbl_22 \/ Lbl_23 \/ Lbl_24 \/ Lbl_25 \/ Lbl_26 \/ Lbl_27 \/ Lbl_28
           \/ Lbl_29 \/ Lbl_30 \/ Lbl_31 \/ Lbl_32 \/ Lbl_33 \/ Lbl_34 \/ Lbl_35
           \/ Lbl_36 \/ Lbl_37 \/ Lbl_38 \/ Lbl_39 \/ Lbl_40 \/ Lbl_41 \/ Lbl_42
           \/ Lbl_43 \/ Lbl_44 \/ Lbl_45 \/ Lbl_46 \/ Lbl_47 \/ Lbl_48 \/ Lbl_49
           \/ Lbl_50 \/ Lbl_51 \/ Lbl_52 \/ Lbl_53 \/ Lbl_54 \/ Lbl_55 \/ Lbl_56
           \/ Lbl_57 \/ Lbl_58 \/ Lbl_59 \/ Lbl_60 \/ Lbl_61 \/ Lbl_62 \/ Lbl_63
           \/ Lbl_64 \/ Lbl_65 \/ Lbl_66 \/ Lbl_67 \/ Lbl_68 \/ Lbl_69 \/ Lbl_70
           \/ Lbl_71 \/ Lbl_72 \/ Lbl_73 \/ Lbl_74 \/ Lbl_75 \/ Lbl_76 \/ Lbl_77
           \/ Lbl_78 \/ Lbl_79 \/ Lbl_80 \/ Lbl_81 \/ Lbl_82 \/ Lbl_83 \/ Lbl_84
           \/ Lbl_85 \/ Lbl_86 \/ Lbl_87 \/ Lbl_88 \/ Lbl_89 \/ Lbl_90 \/ Lbl_91
           \/ Lbl_92 \/ Lbl_93 \/ Lbl_94 \/ Lbl_95 \/ Lbl_96 \/ Lbl_97 \/ Lbl_98
           \/ Lbl_99 \/ Lbl_100 \/ Lbl_101 \/ Lbl_102 \/ Lbl_103 \/ Lbl_104
           \/ Lbl_105 \/ Lbl_106 \/ Lbl_107 \/ Lbl_108 \/ Lbl_109 \/ Lbl_110
           \/ Lbl_111 \/ Lbl_112 \/ Lbl_113 \/ Lbl_114 \/ Lbl_115 \/ Lbl_116
           \/ Lbl_117 \/ Lbl_118 \/ Lbl_119 \/ Lbl_120 \/ Lbl_121 \/ Lbl_122
           \/ Lbl_123 \/ Lbl_124 \/ Lbl_125 \/ Lbl_126 \/ Lbl_127 \/ Lbl_128
           \/ Lbl_129 \/ Lbl_130 \/ Lbl_131 \/ Lbl_132 \/ Lbl_133 \/ Lbl_134
           \/ Lbl_135 \/ Lbl_136 \/ Lbl_137 \/ Lbl_138 \/ Lbl_139 \/ Lbl_140
           \/ Lbl_141 \/ Lbl_142 \/ Lbl_143 \/ Lbl_144 \/ Lbl_145 \/ Lbl_146
           \/ Lbl_147 \/ Lbl_148 \/ Lbl_149 \/ Lbl_150 \/ Lbl_151 \/ Lbl_152
           \/ Lbl_153 \/ Lbl_154 \/ Lbl_155 \/ Lbl_156 \/ Lbl_157 \/ Lbl_158
           \/ Lbl_159 \/ Lbl_160 \/ Lbl_161 \/ Lbl_162 \/ Lbl_163 \/ Lbl_164
           \/ Lbl_165 \/ Lbl_166 \/ Lbl_167 \/ Lbl_168 \/ Lbl_169 \/ Lbl_170
           \/ Lbl_171 \/ Lbl_172 \/ Lbl_173 \/ Lbl_174 \/ Lbl_175 \/ Lbl_176
           \/ Lbl_177 \/ Lbl_178 \/ Lbl_179 \/ Lbl_180
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================

