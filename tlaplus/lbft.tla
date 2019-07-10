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
    \* 9 represents a consensus of normal case
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
    or  \* the case of receiving validate message
        await inputType = "validateMsg";
        await input.state = 9;
        \* a validate message has at least 3 commit signatures
        v.commitSig := v.commitSig \union input.commitSig;
        if commitCertificate(v)
        then
        \* transfer to idle state in next height given the certificate
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

    \* broadcast commit message
    broadcast(1,"commitMsg");
    broadcast(2,"commitMsg");
    broadcast(3,"commitMsg");
    broadcast(4,"commitMsg");

    \* broadcast validate message
    broadcast(1,"validateMsg");
    broadcast(2,"validateMsg");
    broadcast(3,"validateMsg");
    broadcast(4,"validateMsg");





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

GetToNextHeight ==
    validators[1].state /=9 \/
    validators[2].state /=9 \/
    validators[3].state /=9 \/
    validators[4].state /=9


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
                     ELSE /\ pc' = "Lbl_7"
            \/ /\ (validators[1]).state = 2
               /\ "block" = "commitMsg"
               /\ "".state = 2
               /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union "".commitSig]
               /\ IF commitCertificate((validators'[1]))
                     THEN /\ pc' = "Lbl_5"
                     ELSE /\ pc' = "Lbl_7"
            \/ /\ "block" = "validateMsg"
               /\ "".state = 9
               /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union "".commitSig]
               /\ IF commitCertificate((validators'[1]))
                     THEN /\ pc' = "Lbl_6"
                     ELSE /\ pc' = "Lbl_7"
            \/ /\ TRUE
               /\ pc' = "Lbl_7"
               /\ UNCHANGED validators
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ validators' = [validators EXCEPT ![1].state = 1]
         /\ pc' = "Lbl_7"
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
         /\ pc' = "Lbl_4"
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ validators' = [validators EXCEPT ![1].state = 2]
         /\ pc' = "Lbl_7"
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ validators' = [validators EXCEPT ![1].state = 9]
         /\ pc' = "Lbl_7"
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ validators' = [validators EXCEPT ![1].state = 9]
         /\ pc' = "Lbl_7"
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ \/ /\ (validators[2]).state = 0
               /\ "block" = "block"
               /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
               /\ pc' = "Lbl_8"
            \/ /\ (validators[2]).state = 1
               /\ "block" = "prepareMsg"
               /\ "".state = 1 \/ "".state = 2
               /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union "".prepareSig]
               /\ IF prepareCertificate((validators'[2]))
                     THEN /\ pc' = "Lbl_9"
                     ELSE /\ pc' = "Lbl_13"
            \/ /\ (validators[2]).state = 2
               /\ "block" = "commitMsg"
               /\ "".state = 2
               /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union "".commitSig]
               /\ IF commitCertificate((validators'[2]))
                     THEN /\ pc' = "Lbl_11"
                     ELSE /\ pc' = "Lbl_13"
            \/ /\ "block" = "validateMsg"
               /\ "".state = 9
               /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union "".commitSig]
               /\ IF commitCertificate((validators'[2]))
                     THEN /\ pc' = "Lbl_12"
                     ELSE /\ pc' = "Lbl_13"
            \/ /\ TRUE
               /\ pc' = "Lbl_13"
               /\ UNCHANGED validators
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ validators' = [validators EXCEPT ![2].state = 1]
         /\ pc' = "Lbl_13"
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_9 == /\ pc = "Lbl_9"
         /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
         /\ pc' = "Lbl_10"
         /\ UNCHANGED << proposers, validatorIndices >>

Lbl_10 == /\ pc = "Lbl_10"
          /\ validators' = [validators EXCEPT ![2].state = 2]
          /\ pc' = "Lbl_13"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_11 == /\ pc = "Lbl_11"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_13"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_12 == /\ pc = "Lbl_12"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_13"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_13 == /\ pc = "Lbl_13"
          /\ \/ /\ (validators[3]).state = 0
                /\ "block" = "block"
                /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                /\ pc' = "Lbl_14"
             \/ /\ (validators[3]).state = 1
                /\ "block" = "prepareMsg"
                /\ "".state = 1 \/ "".state = 2
                /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union "".prepareSig]
                /\ IF prepareCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_15"
                      ELSE /\ pc' = "Lbl_19"
             \/ /\ (validators[3]).state = 2
                /\ "block" = "commitMsg"
                /\ "".state = 2
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union "".commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_17"
                      ELSE /\ pc' = "Lbl_19"
             \/ /\ "block" = "validateMsg"
                /\ "".state = 9
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union "".commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_18"
                      ELSE /\ pc' = "Lbl_19"
             \/ /\ TRUE
                /\ pc' = "Lbl_19"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_14 == /\ pc = "Lbl_14"
          /\ validators' = [validators EXCEPT ![3].state = 1]
          /\ pc' = "Lbl_19"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_15 == /\ pc = "Lbl_15"
          /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
          /\ pc' = "Lbl_16"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_16 == /\ pc = "Lbl_16"
          /\ validators' = [validators EXCEPT ![3].state = 2]
          /\ pc' = "Lbl_19"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_17 == /\ pc = "Lbl_17"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_19"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_18 == /\ pc = "Lbl_18"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_19"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_19 == /\ pc = "Lbl_19"
          /\ \/ /\ (validators[4]).state = 0
                /\ "block" = "block"
                /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                /\ pc' = "Lbl_20"
             \/ /\ (validators[4]).state = 1
                /\ "block" = "prepareMsg"
                /\ "".state = 1 \/ "".state = 2
                /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union "".prepareSig]
                /\ IF prepareCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_21"
                      ELSE /\ pc' = "Lbl_25"
             \/ /\ (validators[4]).state = 2
                /\ "block" = "commitMsg"
                /\ "".state = 2
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union "".commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_23"
                      ELSE /\ pc' = "Lbl_25"
             \/ /\ "block" = "validateMsg"
                /\ "".state = 9
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union "".commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_24"
                      ELSE /\ pc' = "Lbl_25"
             \/ /\ TRUE
                /\ pc' = "Lbl_25"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_20 == /\ pc = "Lbl_20"
          /\ validators' = [validators EXCEPT ![4].state = 1]
          /\ pc' = "Lbl_25"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_21 == /\ pc = "Lbl_21"
          /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
          /\ pc' = "Lbl_22"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_22 == /\ pc = "Lbl_22"
          /\ validators' = [validators EXCEPT ![4].state = 2]
          /\ pc' = "Lbl_25"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_23 == /\ pc = "Lbl_23"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_25"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_24 == /\ pc = "Lbl_24"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_25"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_25 == /\ pc = "Lbl_25"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_26"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[1]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_27"
                      ELSE /\ pc' = "Lbl_31"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[1]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_29"
                      ELSE /\ pc' = "Lbl_31"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ (validators[1]).state = 9
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[1]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_30"
                      ELSE /\ pc' = "Lbl_31"
             \/ /\ TRUE
                /\ pc' = "Lbl_31"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_26 == /\ pc = "Lbl_26"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Lbl_31"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_27 == /\ pc = "Lbl_27"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_28"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_28 == /\ pc = "Lbl_28"
          /\ validators' = [validators EXCEPT ![1].state = 2]
          /\ pc' = "Lbl_31"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_29 == /\ pc = "Lbl_29"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_31"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_30 == /\ pc = "Lbl_30"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_31"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_31 == /\ pc = "Lbl_31"
          /\ \/ /\ (validators[2]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                /\ pc' = "Lbl_32"
             \/ /\ (validators[2]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[1]).prepareSig]
                /\ IF prepareCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_33"
                      ELSE /\ pc' = "Lbl_37"
             \/ /\ (validators[2]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[1]).commitSig]
                /\ IF commitCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_35"
                      ELSE /\ pc' = "Lbl_37"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ (validators[1]).state = 9
                /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[1]).commitSig]
                /\ IF commitCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_36"
                      ELSE /\ pc' = "Lbl_37"
             \/ /\ TRUE
                /\ pc' = "Lbl_37"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_32 == /\ pc = "Lbl_32"
          /\ validators' = [validators EXCEPT ![2].state = 1]
          /\ pc' = "Lbl_37"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_33 == /\ pc = "Lbl_33"
          /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
          /\ pc' = "Lbl_34"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_34 == /\ pc = "Lbl_34"
          /\ validators' = [validators EXCEPT ![2].state = 2]
          /\ pc' = "Lbl_37"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_35 == /\ pc = "Lbl_35"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_37"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_36 == /\ pc = "Lbl_36"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_37"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_37 == /\ pc = "Lbl_37"
          /\ \/ /\ (validators[3]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                /\ pc' = "Lbl_38"
             \/ /\ (validators[3]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[1]).prepareSig]
                /\ IF prepareCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_39"
                      ELSE /\ pc' = "Lbl_43"
             \/ /\ (validators[3]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[1]).commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_41"
                      ELSE /\ pc' = "Lbl_43"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ (validators[1]).state = 9
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[1]).commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_42"
                      ELSE /\ pc' = "Lbl_43"
             \/ /\ TRUE
                /\ pc' = "Lbl_43"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_38 == /\ pc = "Lbl_38"
          /\ validators' = [validators EXCEPT ![3].state = 1]
          /\ pc' = "Lbl_43"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_39 == /\ pc = "Lbl_39"
          /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
          /\ pc' = "Lbl_40"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_40 == /\ pc = "Lbl_40"
          /\ validators' = [validators EXCEPT ![3].state = 2]
          /\ pc' = "Lbl_43"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_41 == /\ pc = "Lbl_41"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_43"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_42 == /\ pc = "Lbl_42"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_43"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_43 == /\ pc = "Lbl_43"
          /\ \/ /\ (validators[4]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                /\ pc' = "Lbl_44"
             \/ /\ (validators[4]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[1]).prepareSig]
                /\ IF prepareCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_45"
                      ELSE /\ pc' = "Lbl_49"
             \/ /\ (validators[4]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[1]).state = 2
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[1]).commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_47"
                      ELSE /\ pc' = "Lbl_49"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ (validators[1]).state = 9
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[1]).commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_48"
                      ELSE /\ pc' = "Lbl_49"
             \/ /\ TRUE
                /\ pc' = "Lbl_49"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_44 == /\ pc = "Lbl_44"
          /\ validators' = [validators EXCEPT ![4].state = 1]
          /\ pc' = "Lbl_49"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_45 == /\ pc = "Lbl_45"
          /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
          /\ pc' = "Lbl_46"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_46 == /\ pc = "Lbl_46"
          /\ validators' = [validators EXCEPT ![4].state = 2]
          /\ pc' = "Lbl_49"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_47 == /\ pc = "Lbl_47"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_49"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_48 == /\ pc = "Lbl_48"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_49"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_49 == /\ pc = "Lbl_49"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_50"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[2]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_51"
                      ELSE /\ pc' = "Lbl_55"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_53"
                      ELSE /\ pc' = "Lbl_55"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ (validators[2]).state = 9
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_54"
                      ELSE /\ pc' = "Lbl_55"
             \/ /\ TRUE
                /\ pc' = "Lbl_55"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_50 == /\ pc = "Lbl_50"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Lbl_55"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_51 == /\ pc = "Lbl_51"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_52"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_52 == /\ pc = "Lbl_52"
          /\ validators' = [validators EXCEPT ![1].state = 2]
          /\ pc' = "Lbl_55"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_53 == /\ pc = "Lbl_53"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_55"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_54 == /\ pc = "Lbl_54"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_55"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_55 == /\ pc = "Lbl_55"
          /\ \/ /\ (validators[2]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                /\ pc' = "Lbl_56"
             \/ /\ (validators[2]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[2]).prepareSig]
                /\ IF prepareCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_57"
                      ELSE /\ pc' = "Lbl_61"
             \/ /\ (validators[2]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_59"
                      ELSE /\ pc' = "Lbl_61"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ (validators[2]).state = 9
                /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_60"
                      ELSE /\ pc' = "Lbl_61"
             \/ /\ TRUE
                /\ pc' = "Lbl_61"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_56 == /\ pc = "Lbl_56"
          /\ validators' = [validators EXCEPT ![2].state = 1]
          /\ pc' = "Lbl_61"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_57 == /\ pc = "Lbl_57"
          /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
          /\ pc' = "Lbl_58"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_58 == /\ pc = "Lbl_58"
          /\ validators' = [validators EXCEPT ![2].state = 2]
          /\ pc' = "Lbl_61"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_59 == /\ pc = "Lbl_59"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_61"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_60 == /\ pc = "Lbl_60"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_61"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_61 == /\ pc = "Lbl_61"
          /\ \/ /\ (validators[3]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                /\ pc' = "Lbl_62"
             \/ /\ (validators[3]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[2]).prepareSig]
                /\ IF prepareCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_63"
                      ELSE /\ pc' = "Lbl_67"
             \/ /\ (validators[3]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_65"
                      ELSE /\ pc' = "Lbl_67"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ (validators[2]).state = 9
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_66"
                      ELSE /\ pc' = "Lbl_67"
             \/ /\ TRUE
                /\ pc' = "Lbl_67"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_62 == /\ pc = "Lbl_62"
          /\ validators' = [validators EXCEPT ![3].state = 1]
          /\ pc' = "Lbl_67"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_63 == /\ pc = "Lbl_63"
          /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
          /\ pc' = "Lbl_64"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_64 == /\ pc = "Lbl_64"
          /\ validators' = [validators EXCEPT ![3].state = 2]
          /\ pc' = "Lbl_67"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_65 == /\ pc = "Lbl_65"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_67"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_66 == /\ pc = "Lbl_66"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_67"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_67 == /\ pc = "Lbl_67"
          /\ \/ /\ (validators[4]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                /\ pc' = "Lbl_68"
             \/ /\ (validators[4]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[2]).prepareSig]
                /\ IF prepareCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_69"
                      ELSE /\ pc' = "Lbl_73"
             \/ /\ (validators[4]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[2]).state = 2
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_71"
                      ELSE /\ pc' = "Lbl_73"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ (validators[2]).state = 9
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[2]).commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_72"
                      ELSE /\ pc' = "Lbl_73"
             \/ /\ TRUE
                /\ pc' = "Lbl_73"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_68 == /\ pc = "Lbl_68"
          /\ validators' = [validators EXCEPT ![4].state = 1]
          /\ pc' = "Lbl_73"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_69 == /\ pc = "Lbl_69"
          /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
          /\ pc' = "Lbl_70"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_70 == /\ pc = "Lbl_70"
          /\ validators' = [validators EXCEPT ![4].state = 2]
          /\ pc' = "Lbl_73"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_71 == /\ pc = "Lbl_71"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_73"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_72 == /\ pc = "Lbl_72"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_73"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_73 == /\ pc = "Lbl_73"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_74"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[3]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_75"
                      ELSE /\ pc' = "Lbl_79"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_77"
                      ELSE /\ pc' = "Lbl_79"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ (validators[3]).state = 9
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_78"
                      ELSE /\ pc' = "Lbl_79"
             \/ /\ TRUE
                /\ pc' = "Lbl_79"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_74 == /\ pc = "Lbl_74"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Lbl_79"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_75 == /\ pc = "Lbl_75"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_76"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_76 == /\ pc = "Lbl_76"
          /\ validators' = [validators EXCEPT ![1].state = 2]
          /\ pc' = "Lbl_79"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_77 == /\ pc = "Lbl_77"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_79"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_78 == /\ pc = "Lbl_78"
          /\ validators' = [validators EXCEPT ![1].state = 9]
          /\ pc' = "Lbl_79"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_79 == /\ pc = "Lbl_79"
          /\ \/ /\ (validators[2]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                /\ pc' = "Lbl_80"
             \/ /\ (validators[2]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[3]).prepareSig]
                /\ IF prepareCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_81"
                      ELSE /\ pc' = "Lbl_85"
             \/ /\ (validators[2]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_83"
                      ELSE /\ pc' = "Lbl_85"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ (validators[3]).state = 9
                /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[2]))
                      THEN /\ pc' = "Lbl_84"
                      ELSE /\ pc' = "Lbl_85"
             \/ /\ TRUE
                /\ pc' = "Lbl_85"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_80 == /\ pc = "Lbl_80"
          /\ validators' = [validators EXCEPT ![2].state = 1]
          /\ pc' = "Lbl_85"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_81 == /\ pc = "Lbl_81"
          /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
          /\ pc' = "Lbl_82"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_82 == /\ pc = "Lbl_82"
          /\ validators' = [validators EXCEPT ![2].state = 2]
          /\ pc' = "Lbl_85"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_83 == /\ pc = "Lbl_83"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_85"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_84 == /\ pc = "Lbl_84"
          /\ validators' = [validators EXCEPT ![2].state = 9]
          /\ pc' = "Lbl_85"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_85 == /\ pc = "Lbl_85"
          /\ \/ /\ (validators[3]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                /\ pc' = "Lbl_86"
             \/ /\ (validators[3]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[3]).prepareSig]
                /\ IF prepareCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_87"
                      ELSE /\ pc' = "Lbl_91"
             \/ /\ (validators[3]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_89"
                      ELSE /\ pc' = "Lbl_91"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ (validators[3]).state = 9
                /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[3]))
                      THEN /\ pc' = "Lbl_90"
                      ELSE /\ pc' = "Lbl_91"
             \/ /\ TRUE
                /\ pc' = "Lbl_91"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_86 == /\ pc = "Lbl_86"
          /\ validators' = [validators EXCEPT ![3].state = 1]
          /\ pc' = "Lbl_91"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_87 == /\ pc = "Lbl_87"
          /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
          /\ pc' = "Lbl_88"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_88 == /\ pc = "Lbl_88"
          /\ validators' = [validators EXCEPT ![3].state = 2]
          /\ pc' = "Lbl_91"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_89 == /\ pc = "Lbl_89"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_91"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_90 == /\ pc = "Lbl_90"
          /\ validators' = [validators EXCEPT ![3].state = 9]
          /\ pc' = "Lbl_91"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_91 == /\ pc = "Lbl_91"
          /\ \/ /\ (validators[4]).state = 0
                /\ "prepareMsg" = "block"
                /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                /\ pc' = "Lbl_92"
             \/ /\ (validators[4]).state = 1
                /\ "prepareMsg" = "prepareMsg"
                /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[3]).prepareSig]
                /\ IF prepareCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_93"
                      ELSE /\ pc' = "Lbl_97"
             \/ /\ (validators[4]).state = 2
                /\ "prepareMsg" = "commitMsg"
                /\ (validators[3]).state = 2
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_95"
                      ELSE /\ pc' = "Lbl_97"
             \/ /\ "prepareMsg" = "validateMsg"
                /\ (validators[3]).state = 9
                /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[3]).commitSig]
                /\ IF commitCertificate((validators'[4]))
                      THEN /\ pc' = "Lbl_96"
                      ELSE /\ pc' = "Lbl_97"
             \/ /\ TRUE
                /\ pc' = "Lbl_97"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_92 == /\ pc = "Lbl_92"
          /\ validators' = [validators EXCEPT ![4].state = 1]
          /\ pc' = "Lbl_97"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_93 == /\ pc = "Lbl_93"
          /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
          /\ pc' = "Lbl_94"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_94 == /\ pc = "Lbl_94"
          /\ validators' = [validators EXCEPT ![4].state = 2]
          /\ pc' = "Lbl_97"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_95 == /\ pc = "Lbl_95"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_97"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_96 == /\ pc = "Lbl_96"
          /\ validators' = [validators EXCEPT ![4].state = 9]
          /\ pc' = "Lbl_97"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_97 == /\ pc = "Lbl_97"
          /\ \/ /\ (validators[1]).state = 0
                /\ "prepareMSg" = "block"
                /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                /\ pc' = "Lbl_98"
             \/ /\ (validators[1]).state = 1
                /\ "prepareMSg" = "prepareMsg"
                /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[4]).prepareSig]
                /\ IF prepareCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_99"
                      ELSE /\ pc' = "Lbl_103"
             \/ /\ (validators[1]).state = 2
                /\ "prepareMSg" = "commitMsg"
                /\ (validators[4]).state = 2
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[4]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_101"
                      ELSE /\ pc' = "Lbl_103"
             \/ /\ "prepareMSg" = "validateMsg"
                /\ (validators[4]).state = 9
                /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[4]).commitSig]
                /\ IF commitCertificate((validators'[1]))
                      THEN /\ pc' = "Lbl_102"
                      ELSE /\ pc' = "Lbl_103"
             \/ /\ TRUE
                /\ pc' = "Lbl_103"
                /\ UNCHANGED validators
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_98 == /\ pc = "Lbl_98"
          /\ validators' = [validators EXCEPT ![1].state = 1]
          /\ pc' = "Lbl_103"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_99 == /\ pc = "Lbl_99"
          /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
          /\ pc' = "Lbl_100"
          /\ UNCHANGED << proposers, validatorIndices >>

Lbl_100 == /\ pc = "Lbl_100"
           /\ validators' = [validators EXCEPT ![1].state = 2]
           /\ pc' = "Lbl_103"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_101 == /\ pc = "Lbl_101"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_103"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_102 == /\ pc = "Lbl_102"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_103"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_103 == /\ pc = "Lbl_103"
           /\ \/ /\ (validators[2]).state = 0
                 /\ "prepareMSg" = "block"
                 /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                 /\ pc' = "Lbl_104"
              \/ /\ (validators[2]).state = 1
                 /\ "prepareMSg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_105"
                       ELSE /\ pc' = "Lbl_109"
              \/ /\ (validators[2]).state = 2
                 /\ "prepareMSg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_107"
                       ELSE /\ pc' = "Lbl_109"
              \/ /\ "prepareMSg" = "validateMsg"
                 /\ (validators[4]).state = 9
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_108"
                       ELSE /\ pc' = "Lbl_109"
              \/ /\ TRUE
                 /\ pc' = "Lbl_109"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_104 == /\ pc = "Lbl_104"
           /\ validators' = [validators EXCEPT ![2].state = 1]
           /\ pc' = "Lbl_109"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_105 == /\ pc = "Lbl_105"
           /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
           /\ pc' = "Lbl_106"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_106 == /\ pc = "Lbl_106"
           /\ validators' = [validators EXCEPT ![2].state = 2]
           /\ pc' = "Lbl_109"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_107 == /\ pc = "Lbl_107"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_109"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_108 == /\ pc = "Lbl_108"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_109"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_109 == /\ pc = "Lbl_109"
           /\ \/ /\ (validators[3]).state = 0
                 /\ "prepareMSg" = "block"
                 /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                 /\ pc' = "Lbl_110"
              \/ /\ (validators[3]).state = 1
                 /\ "prepareMSg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_111"
                       ELSE /\ pc' = "Lbl_115"
              \/ /\ (validators[3]).state = 2
                 /\ "prepareMSg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_113"
                       ELSE /\ pc' = "Lbl_115"
              \/ /\ "prepareMSg" = "validateMsg"
                 /\ (validators[4]).state = 9
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_114"
                       ELSE /\ pc' = "Lbl_115"
              \/ /\ TRUE
                 /\ pc' = "Lbl_115"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_110 == /\ pc = "Lbl_110"
           /\ validators' = [validators EXCEPT ![3].state = 1]
           /\ pc' = "Lbl_115"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_111 == /\ pc = "Lbl_111"
           /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
           /\ pc' = "Lbl_112"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_112 == /\ pc = "Lbl_112"
           /\ validators' = [validators EXCEPT ![3].state = 2]
           /\ pc' = "Lbl_115"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_113 == /\ pc = "Lbl_113"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_115"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_114 == /\ pc = "Lbl_114"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_115"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_115 == /\ pc = "Lbl_115"
           /\ \/ /\ (validators[4]).state = 0
                 /\ "prepareMSg" = "block"
                 /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                 /\ pc' = "Lbl_116"
              \/ /\ (validators[4]).state = 1
                 /\ "prepareMSg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_117"
                       ELSE /\ pc' = "Lbl_121"
              \/ /\ (validators[4]).state = 2
                 /\ "prepareMSg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_119"
                       ELSE /\ pc' = "Lbl_121"
              \/ /\ "prepareMSg" = "validateMsg"
                 /\ (validators[4]).state = 9
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_120"
                       ELSE /\ pc' = "Lbl_121"
              \/ /\ TRUE
                 /\ pc' = "Lbl_121"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_116 == /\ pc = "Lbl_116"
           /\ validators' = [validators EXCEPT ![4].state = 1]
           /\ pc' = "Lbl_121"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_117 == /\ pc = "Lbl_117"
           /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
           /\ pc' = "Lbl_118"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_118 == /\ pc = "Lbl_118"
           /\ validators' = [validators EXCEPT ![4].state = 2]
           /\ pc' = "Lbl_121"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_119 == /\ pc = "Lbl_119"
           /\ validators' = [validators EXCEPT ![4].state = 9]
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
                 /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[1]).prepareSig]
                 /\ IF prepareCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_123"
                       ELSE /\ pc' = "Lbl_127"
              \/ /\ (validators[1]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_125"
                       ELSE /\ pc' = "Lbl_127"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[1]).state = 9
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_126"
                       ELSE /\ pc' = "Lbl_127"
              \/ /\ TRUE
                 /\ pc' = "Lbl_127"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_122 == /\ pc = "Lbl_122"
           /\ validators' = [validators EXCEPT ![1].state = 1]
           /\ pc' = "Lbl_127"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_123 == /\ pc = "Lbl_123"
           /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
           /\ pc' = "Lbl_124"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_124 == /\ pc = "Lbl_124"
           /\ validators' = [validators EXCEPT ![1].state = 2]
           /\ pc' = "Lbl_127"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_125 == /\ pc = "Lbl_125"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_127"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_126 == /\ pc = "Lbl_126"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_127"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_127 == /\ pc = "Lbl_127"
           /\ \/ /\ (validators[2]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                 /\ pc' = "Lbl_128"
              \/ /\ (validators[2]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[1]).prepareSig]
                 /\ IF prepareCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_129"
                       ELSE /\ pc' = "Lbl_133"
              \/ /\ (validators[2]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_131"
                       ELSE /\ pc' = "Lbl_133"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[1]).state = 9
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_132"
                       ELSE /\ pc' = "Lbl_133"
              \/ /\ TRUE
                 /\ pc' = "Lbl_133"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_128 == /\ pc = "Lbl_128"
           /\ validators' = [validators EXCEPT ![2].state = 1]
           /\ pc' = "Lbl_133"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_129 == /\ pc = "Lbl_129"
           /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
           /\ pc' = "Lbl_130"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_130 == /\ pc = "Lbl_130"
           /\ validators' = [validators EXCEPT ![2].state = 2]
           /\ pc' = "Lbl_133"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_131 == /\ pc = "Lbl_131"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_133"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_132 == /\ pc = "Lbl_132"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_133"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_133 == /\ pc = "Lbl_133"
           /\ \/ /\ (validators[3]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                 /\ pc' = "Lbl_134"
              \/ /\ (validators[3]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[1]).prepareSig]
                 /\ IF prepareCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_135"
                       ELSE /\ pc' = "Lbl_139"
              \/ /\ (validators[3]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_137"
                       ELSE /\ pc' = "Lbl_139"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[1]).state = 9
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_138"
                       ELSE /\ pc' = "Lbl_139"
              \/ /\ TRUE
                 /\ pc' = "Lbl_139"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_134 == /\ pc = "Lbl_134"
           /\ validators' = [validators EXCEPT ![3].state = 1]
           /\ pc' = "Lbl_139"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_135 == /\ pc = "Lbl_135"
           /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
           /\ pc' = "Lbl_136"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_136 == /\ pc = "Lbl_136"
           /\ validators' = [validators EXCEPT ![3].state = 2]
           /\ pc' = "Lbl_139"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_137 == /\ pc = "Lbl_137"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_139"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_138 == /\ pc = "Lbl_138"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_139"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_139 == /\ pc = "Lbl_139"
           /\ \/ /\ (validators[4]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                 /\ pc' = "Lbl_140"
              \/ /\ (validators[4]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[1]).prepareSig]
                 /\ IF prepareCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_141"
                       ELSE /\ pc' = "Lbl_145"
              \/ /\ (validators[4]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_143"
                       ELSE /\ pc' = "Lbl_145"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[1]).state = 9
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_144"
                       ELSE /\ pc' = "Lbl_145"
              \/ /\ TRUE
                 /\ pc' = "Lbl_145"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_140 == /\ pc = "Lbl_140"
           /\ validators' = [validators EXCEPT ![4].state = 1]
           /\ pc' = "Lbl_145"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_141 == /\ pc = "Lbl_141"
           /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
           /\ pc' = "Lbl_142"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_142 == /\ pc = "Lbl_142"
           /\ validators' = [validators EXCEPT ![4].state = 2]
           /\ pc' = "Lbl_145"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_143 == /\ pc = "Lbl_143"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_145"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_144 == /\ pc = "Lbl_144"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_145"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_145 == /\ pc = "Lbl_145"
           /\ \/ /\ (validators[1]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                 /\ pc' = "Lbl_146"
              \/ /\ (validators[1]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[2]).prepareSig]
                 /\ IF prepareCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_147"
                       ELSE /\ pc' = "Lbl_151"
              \/ /\ (validators[1]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_149"
                       ELSE /\ pc' = "Lbl_151"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[2]).state = 9
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_150"
                       ELSE /\ pc' = "Lbl_151"
              \/ /\ TRUE
                 /\ pc' = "Lbl_151"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_146 == /\ pc = "Lbl_146"
           /\ validators' = [validators EXCEPT ![1].state = 1]
           /\ pc' = "Lbl_151"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_147 == /\ pc = "Lbl_147"
           /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
           /\ pc' = "Lbl_148"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_148 == /\ pc = "Lbl_148"
           /\ validators' = [validators EXCEPT ![1].state = 2]
           /\ pc' = "Lbl_151"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_149 == /\ pc = "Lbl_149"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_151"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_150 == /\ pc = "Lbl_150"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_151"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_151 == /\ pc = "Lbl_151"
           /\ \/ /\ (validators[2]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                 /\ pc' = "Lbl_152"
              \/ /\ (validators[2]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[2]).prepareSig]
                 /\ IF prepareCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_153"
                       ELSE /\ pc' = "Lbl_157"
              \/ /\ (validators[2]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_155"
                       ELSE /\ pc' = "Lbl_157"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[2]).state = 9
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_156"
                       ELSE /\ pc' = "Lbl_157"
              \/ /\ TRUE
                 /\ pc' = "Lbl_157"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_152 == /\ pc = "Lbl_152"
           /\ validators' = [validators EXCEPT ![2].state = 1]
           /\ pc' = "Lbl_157"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_153 == /\ pc = "Lbl_153"
           /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
           /\ pc' = "Lbl_154"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_154 == /\ pc = "Lbl_154"
           /\ validators' = [validators EXCEPT ![2].state = 2]
           /\ pc' = "Lbl_157"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_155 == /\ pc = "Lbl_155"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_157"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_156 == /\ pc = "Lbl_156"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_157"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_157 == /\ pc = "Lbl_157"
           /\ \/ /\ (validators[3]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                 /\ pc' = "Lbl_158"
              \/ /\ (validators[3]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[2]).prepareSig]
                 /\ IF prepareCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_159"
                       ELSE /\ pc' = "Lbl_163"
              \/ /\ (validators[3]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_161"
                       ELSE /\ pc' = "Lbl_163"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[2]).state = 9
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_162"
                       ELSE /\ pc' = "Lbl_163"
              \/ /\ TRUE
                 /\ pc' = "Lbl_163"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_158 == /\ pc = "Lbl_158"
           /\ validators' = [validators EXCEPT ![3].state = 1]
           /\ pc' = "Lbl_163"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_159 == /\ pc = "Lbl_159"
           /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
           /\ pc' = "Lbl_160"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_160 == /\ pc = "Lbl_160"
           /\ validators' = [validators EXCEPT ![3].state = 2]
           /\ pc' = "Lbl_163"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_161 == /\ pc = "Lbl_161"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_163"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_162 == /\ pc = "Lbl_162"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_163"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_163 == /\ pc = "Lbl_163"
           /\ \/ /\ (validators[4]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                 /\ pc' = "Lbl_164"
              \/ /\ (validators[4]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[2]).prepareSig]
                 /\ IF prepareCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_165"
                       ELSE /\ pc' = "Lbl_169"
              \/ /\ (validators[4]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_167"
                       ELSE /\ pc' = "Lbl_169"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[2]).state = 9
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_168"
                       ELSE /\ pc' = "Lbl_169"
              \/ /\ TRUE
                 /\ pc' = "Lbl_169"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_164 == /\ pc = "Lbl_164"
           /\ validators' = [validators EXCEPT ![4].state = 1]
           /\ pc' = "Lbl_169"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_165 == /\ pc = "Lbl_165"
           /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
           /\ pc' = "Lbl_166"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_166 == /\ pc = "Lbl_166"
           /\ validators' = [validators EXCEPT ![4].state = 2]
           /\ pc' = "Lbl_169"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_167 == /\ pc = "Lbl_167"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_169"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_168 == /\ pc = "Lbl_168"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_169"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_169 == /\ pc = "Lbl_169"
           /\ \/ /\ (validators[1]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                 /\ pc' = "Lbl_170"
              \/ /\ (validators[1]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[3]).prepareSig]
                 /\ IF prepareCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_171"
                       ELSE /\ pc' = "Lbl_175"
              \/ /\ (validators[1]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_173"
                       ELSE /\ pc' = "Lbl_175"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[3]).state = 9
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_174"
                       ELSE /\ pc' = "Lbl_175"
              \/ /\ TRUE
                 /\ pc' = "Lbl_175"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_170 == /\ pc = "Lbl_170"
           /\ validators' = [validators EXCEPT ![1].state = 1]
           /\ pc' = "Lbl_175"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_171 == /\ pc = "Lbl_171"
           /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
           /\ pc' = "Lbl_172"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_172 == /\ pc = "Lbl_172"
           /\ validators' = [validators EXCEPT ![1].state = 2]
           /\ pc' = "Lbl_175"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_173 == /\ pc = "Lbl_173"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_175"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_174 == /\ pc = "Lbl_174"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_175"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_175 == /\ pc = "Lbl_175"
           /\ \/ /\ (validators[2]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                 /\ pc' = "Lbl_176"
              \/ /\ (validators[2]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[3]).prepareSig]
                 /\ IF prepareCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_177"
                       ELSE /\ pc' = "Lbl_181"
              \/ /\ (validators[2]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_179"
                       ELSE /\ pc' = "Lbl_181"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[3]).state = 9
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_180"
                       ELSE /\ pc' = "Lbl_181"
              \/ /\ TRUE
                 /\ pc' = "Lbl_181"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_176 == /\ pc = "Lbl_176"
           /\ validators' = [validators EXCEPT ![2].state = 1]
           /\ pc' = "Lbl_181"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_177 == /\ pc = "Lbl_177"
           /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
           /\ pc' = "Lbl_178"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_178 == /\ pc = "Lbl_178"
           /\ validators' = [validators EXCEPT ![2].state = 2]
           /\ pc' = "Lbl_181"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_179 == /\ pc = "Lbl_179"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_181"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_180 == /\ pc = "Lbl_180"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_181"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_181 == /\ pc = "Lbl_181"
           /\ \/ /\ (validators[3]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                 /\ pc' = "Lbl_182"
              \/ /\ (validators[3]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[3]).prepareSig]
                 /\ IF prepareCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_183"
                       ELSE /\ pc' = "Lbl_187"
              \/ /\ (validators[3]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_185"
                       ELSE /\ pc' = "Lbl_187"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[3]).state = 9
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_186"
                       ELSE /\ pc' = "Lbl_187"
              \/ /\ TRUE
                 /\ pc' = "Lbl_187"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_182 == /\ pc = "Lbl_182"
           /\ validators' = [validators EXCEPT ![3].state = 1]
           /\ pc' = "Lbl_187"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_183 == /\ pc = "Lbl_183"
           /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
           /\ pc' = "Lbl_184"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_184 == /\ pc = "Lbl_184"
           /\ validators' = [validators EXCEPT ![3].state = 2]
           /\ pc' = "Lbl_187"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_185 == /\ pc = "Lbl_185"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_187"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_186 == /\ pc = "Lbl_186"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_187"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_187 == /\ pc = "Lbl_187"
           /\ \/ /\ (validators[4]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                 /\ pc' = "Lbl_188"
              \/ /\ (validators[4]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[3]).prepareSig]
                 /\ IF prepareCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_189"
                       ELSE /\ pc' = "Lbl_193"
              \/ /\ (validators[4]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_191"
                       ELSE /\ pc' = "Lbl_193"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[3]).state = 9
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_192"
                       ELSE /\ pc' = "Lbl_193"
              \/ /\ TRUE
                 /\ pc' = "Lbl_193"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_188 == /\ pc = "Lbl_188"
           /\ validators' = [validators EXCEPT ![4].state = 1]
           /\ pc' = "Lbl_193"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_189 == /\ pc = "Lbl_189"
           /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
           /\ pc' = "Lbl_190"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_190 == /\ pc = "Lbl_190"
           /\ validators' = [validators EXCEPT ![4].state = 2]
           /\ pc' = "Lbl_193"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_191 == /\ pc = "Lbl_191"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_193"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_192 == /\ pc = "Lbl_192"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_193"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_193 == /\ pc = "Lbl_193"
           /\ \/ /\ (validators[1]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                 /\ pc' = "Lbl_194"
              \/ /\ (validators[1]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_195"
                       ELSE /\ pc' = "Lbl_199"
              \/ /\ (validators[1]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_197"
                       ELSE /\ pc' = "Lbl_199"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[4]).state = 9
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_198"
                       ELSE /\ pc' = "Lbl_199"
              \/ /\ TRUE
                 /\ pc' = "Lbl_199"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_194 == /\ pc = "Lbl_194"
           /\ validators' = [validators EXCEPT ![1].state = 1]
           /\ pc' = "Lbl_199"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_195 == /\ pc = "Lbl_195"
           /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
           /\ pc' = "Lbl_196"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_196 == /\ pc = "Lbl_196"
           /\ validators' = [validators EXCEPT ![1].state = 2]
           /\ pc' = "Lbl_199"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_197 == /\ pc = "Lbl_197"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_199"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_198 == /\ pc = "Lbl_198"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_199"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_199 == /\ pc = "Lbl_199"
           /\ \/ /\ (validators[2]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                 /\ pc' = "Lbl_200"
              \/ /\ (validators[2]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_201"
                       ELSE /\ pc' = "Lbl_205"
              \/ /\ (validators[2]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_203"
                       ELSE /\ pc' = "Lbl_205"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[4]).state = 9
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_204"
                       ELSE /\ pc' = "Lbl_205"
              \/ /\ TRUE
                 /\ pc' = "Lbl_205"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_200 == /\ pc = "Lbl_200"
           /\ validators' = [validators EXCEPT ![2].state = 1]
           /\ pc' = "Lbl_205"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_201 == /\ pc = "Lbl_201"
           /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
           /\ pc' = "Lbl_202"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_202 == /\ pc = "Lbl_202"
           /\ validators' = [validators EXCEPT ![2].state = 2]
           /\ pc' = "Lbl_205"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_203 == /\ pc = "Lbl_203"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_205"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_204 == /\ pc = "Lbl_204"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_205"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_205 == /\ pc = "Lbl_205"
           /\ \/ /\ (validators[3]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                 /\ pc' = "Lbl_206"
              \/ /\ (validators[3]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_207"
                       ELSE /\ pc' = "Lbl_211"
              \/ /\ (validators[3]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_209"
                       ELSE /\ pc' = "Lbl_211"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[4]).state = 9
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_210"
                       ELSE /\ pc' = "Lbl_211"
              \/ /\ TRUE
                 /\ pc' = "Lbl_211"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_206 == /\ pc = "Lbl_206"
           /\ validators' = [validators EXCEPT ![3].state = 1]
           /\ pc' = "Lbl_211"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_207 == /\ pc = "Lbl_207"
           /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
           /\ pc' = "Lbl_208"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_208 == /\ pc = "Lbl_208"
           /\ validators' = [validators EXCEPT ![3].state = 2]
           /\ pc' = "Lbl_211"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_209 == /\ pc = "Lbl_209"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_211"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_210 == /\ pc = "Lbl_210"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_211"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_211 == /\ pc = "Lbl_211"
           /\ \/ /\ (validators[4]).state = 0
                 /\ "commitMsg" = "block"
                 /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                 /\ pc' = "Lbl_212"
              \/ /\ (validators[4]).state = 1
                 /\ "commitMsg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_213"
                       ELSE /\ pc' = "Lbl_217"
              \/ /\ (validators[4]).state = 2
                 /\ "commitMsg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_215"
                       ELSE /\ pc' = "Lbl_217"
              \/ /\ "commitMsg" = "validateMsg"
                 /\ (validators[4]).state = 9
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_216"
                       ELSE /\ pc' = "Lbl_217"
              \/ /\ TRUE
                 /\ pc' = "Lbl_217"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_212 == /\ pc = "Lbl_212"
           /\ validators' = [validators EXCEPT ![4].state = 1]
           /\ pc' = "Lbl_217"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_213 == /\ pc = "Lbl_213"
           /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
           /\ pc' = "Lbl_214"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_214 == /\ pc = "Lbl_214"
           /\ validators' = [validators EXCEPT ![4].state = 2]
           /\ pc' = "Lbl_217"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_215 == /\ pc = "Lbl_215"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_217"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_216 == /\ pc = "Lbl_216"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_217"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_217 == /\ pc = "Lbl_217"
           /\ \/ /\ (validators[1]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                 /\ pc' = "Lbl_218"
              \/ /\ (validators[1]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[1]).prepareSig]
                 /\ IF prepareCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_219"
                       ELSE /\ pc' = "Lbl_223"
              \/ /\ (validators[1]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_221"
                       ELSE /\ pc' = "Lbl_223"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[1]).state = 9
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_222"
                       ELSE /\ pc' = "Lbl_223"
              \/ /\ TRUE
                 /\ pc' = "Lbl_223"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_218 == /\ pc = "Lbl_218"
           /\ validators' = [validators EXCEPT ![1].state = 1]
           /\ pc' = "Lbl_223"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_219 == /\ pc = "Lbl_219"
           /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
           /\ pc' = "Lbl_220"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_220 == /\ pc = "Lbl_220"
           /\ validators' = [validators EXCEPT ![1].state = 2]
           /\ pc' = "Lbl_223"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_221 == /\ pc = "Lbl_221"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_223"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_222 == /\ pc = "Lbl_222"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_223"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_223 == /\ pc = "Lbl_223"
           /\ \/ /\ (validators[2]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                 /\ pc' = "Lbl_224"
              \/ /\ (validators[2]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[1]).prepareSig]
                 /\ IF prepareCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_225"
                       ELSE /\ pc' = "Lbl_229"
              \/ /\ (validators[2]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_227"
                       ELSE /\ pc' = "Lbl_229"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[1]).state = 9
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_228"
                       ELSE /\ pc' = "Lbl_229"
              \/ /\ TRUE
                 /\ pc' = "Lbl_229"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_224 == /\ pc = "Lbl_224"
           /\ validators' = [validators EXCEPT ![2].state = 1]
           /\ pc' = "Lbl_229"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_225 == /\ pc = "Lbl_225"
           /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
           /\ pc' = "Lbl_226"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_226 == /\ pc = "Lbl_226"
           /\ validators' = [validators EXCEPT ![2].state = 2]
           /\ pc' = "Lbl_229"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_227 == /\ pc = "Lbl_227"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_229"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_228 == /\ pc = "Lbl_228"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_229"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_229 == /\ pc = "Lbl_229"
           /\ \/ /\ (validators[3]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                 /\ pc' = "Lbl_230"
              \/ /\ (validators[3]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[1]).prepareSig]
                 /\ IF prepareCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_231"
                       ELSE /\ pc' = "Lbl_235"
              \/ /\ (validators[3]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_233"
                       ELSE /\ pc' = "Lbl_235"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[1]).state = 9
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_234"
                       ELSE /\ pc' = "Lbl_235"
              \/ /\ TRUE
                 /\ pc' = "Lbl_235"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_230 == /\ pc = "Lbl_230"
           /\ validators' = [validators EXCEPT ![3].state = 1]
           /\ pc' = "Lbl_235"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_231 == /\ pc = "Lbl_231"
           /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
           /\ pc' = "Lbl_232"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_232 == /\ pc = "Lbl_232"
           /\ validators' = [validators EXCEPT ![3].state = 2]
           /\ pc' = "Lbl_235"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_233 == /\ pc = "Lbl_233"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_235"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_234 == /\ pc = "Lbl_234"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_235"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_235 == /\ pc = "Lbl_235"
           /\ \/ /\ (validators[4]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                 /\ pc' = "Lbl_236"
              \/ /\ (validators[4]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[1]).state = 1 \/ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[1]).prepareSig]
                 /\ IF prepareCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_237"
                       ELSE /\ pc' = "Lbl_241"
              \/ /\ (validators[4]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[1]).state = 2
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_239"
                       ELSE /\ pc' = "Lbl_241"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[1]).state = 9
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[1]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_240"
                       ELSE /\ pc' = "Lbl_241"
              \/ /\ TRUE
                 /\ pc' = "Lbl_241"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_236 == /\ pc = "Lbl_236"
           /\ validators' = [validators EXCEPT ![4].state = 1]
           /\ pc' = "Lbl_241"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_237 == /\ pc = "Lbl_237"
           /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
           /\ pc' = "Lbl_238"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_238 == /\ pc = "Lbl_238"
           /\ validators' = [validators EXCEPT ![4].state = 2]
           /\ pc' = "Lbl_241"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_239 == /\ pc = "Lbl_239"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_241"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_240 == /\ pc = "Lbl_240"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_241"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_241 == /\ pc = "Lbl_241"
           /\ \/ /\ (validators[1]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                 /\ pc' = "Lbl_242"
              \/ /\ (validators[1]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[2]).prepareSig]
                 /\ IF prepareCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_243"
                       ELSE /\ pc' = "Lbl_247"
              \/ /\ (validators[1]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_245"
                       ELSE /\ pc' = "Lbl_247"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[2]).state = 9
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_246"
                       ELSE /\ pc' = "Lbl_247"
              \/ /\ TRUE
                 /\ pc' = "Lbl_247"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_242 == /\ pc = "Lbl_242"
           /\ validators' = [validators EXCEPT ![1].state = 1]
           /\ pc' = "Lbl_247"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_243 == /\ pc = "Lbl_243"
           /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
           /\ pc' = "Lbl_244"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_244 == /\ pc = "Lbl_244"
           /\ validators' = [validators EXCEPT ![1].state = 2]
           /\ pc' = "Lbl_247"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_245 == /\ pc = "Lbl_245"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_247"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_246 == /\ pc = "Lbl_246"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_247"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_247 == /\ pc = "Lbl_247"
           /\ \/ /\ (validators[2]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                 /\ pc' = "Lbl_248"
              \/ /\ (validators[2]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[2]).prepareSig]
                 /\ IF prepareCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_249"
                       ELSE /\ pc' = "Lbl_253"
              \/ /\ (validators[2]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_251"
                       ELSE /\ pc' = "Lbl_253"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[2]).state = 9
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_252"
                       ELSE /\ pc' = "Lbl_253"
              \/ /\ TRUE
                 /\ pc' = "Lbl_253"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_248 == /\ pc = "Lbl_248"
           /\ validators' = [validators EXCEPT ![2].state = 1]
           /\ pc' = "Lbl_253"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_249 == /\ pc = "Lbl_249"
           /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
           /\ pc' = "Lbl_250"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_250 == /\ pc = "Lbl_250"
           /\ validators' = [validators EXCEPT ![2].state = 2]
           /\ pc' = "Lbl_253"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_251 == /\ pc = "Lbl_251"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_253"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_252 == /\ pc = "Lbl_252"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_253"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_253 == /\ pc = "Lbl_253"
           /\ \/ /\ (validators[3]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                 /\ pc' = "Lbl_254"
              \/ /\ (validators[3]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[2]).prepareSig]
                 /\ IF prepareCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_255"
                       ELSE /\ pc' = "Lbl_259"
              \/ /\ (validators[3]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_257"
                       ELSE /\ pc' = "Lbl_259"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[2]).state = 9
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_258"
                       ELSE /\ pc' = "Lbl_259"
              \/ /\ TRUE
                 /\ pc' = "Lbl_259"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_254 == /\ pc = "Lbl_254"
           /\ validators' = [validators EXCEPT ![3].state = 1]
           /\ pc' = "Lbl_259"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_255 == /\ pc = "Lbl_255"
           /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
           /\ pc' = "Lbl_256"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_256 == /\ pc = "Lbl_256"
           /\ validators' = [validators EXCEPT ![3].state = 2]
           /\ pc' = "Lbl_259"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_257 == /\ pc = "Lbl_257"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_259"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_258 == /\ pc = "Lbl_258"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_259"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_259 == /\ pc = "Lbl_259"
           /\ \/ /\ (validators[4]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                 /\ pc' = "Lbl_260"
              \/ /\ (validators[4]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[2]).state = 1 \/ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[2]).prepareSig]
                 /\ IF prepareCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_261"
                       ELSE /\ pc' = "Lbl_265"
              \/ /\ (validators[4]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[2]).state = 2
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_263"
                       ELSE /\ pc' = "Lbl_265"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[2]).state = 9
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[2]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_264"
                       ELSE /\ pc' = "Lbl_265"
              \/ /\ TRUE
                 /\ pc' = "Lbl_265"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_260 == /\ pc = "Lbl_260"
           /\ validators' = [validators EXCEPT ![4].state = 1]
           /\ pc' = "Lbl_265"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_261 == /\ pc = "Lbl_261"
           /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
           /\ pc' = "Lbl_262"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_262 == /\ pc = "Lbl_262"
           /\ validators' = [validators EXCEPT ![4].state = 2]
           /\ pc' = "Lbl_265"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_263 == /\ pc = "Lbl_263"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_265"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_264 == /\ pc = "Lbl_264"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_265"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_265 == /\ pc = "Lbl_265"
           /\ \/ /\ (validators[1]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                 /\ pc' = "Lbl_266"
              \/ /\ (validators[1]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[3]).prepareSig]
                 /\ IF prepareCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_267"
                       ELSE /\ pc' = "Lbl_271"
              \/ /\ (validators[1]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_269"
                       ELSE /\ pc' = "Lbl_271"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[3]).state = 9
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_270"
                       ELSE /\ pc' = "Lbl_271"
              \/ /\ TRUE
                 /\ pc' = "Lbl_271"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_266 == /\ pc = "Lbl_266"
           /\ validators' = [validators EXCEPT ![1].state = 1]
           /\ pc' = "Lbl_271"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_267 == /\ pc = "Lbl_267"
           /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
           /\ pc' = "Lbl_268"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_268 == /\ pc = "Lbl_268"
           /\ validators' = [validators EXCEPT ![1].state = 2]
           /\ pc' = "Lbl_271"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_269 == /\ pc = "Lbl_269"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_271"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_270 == /\ pc = "Lbl_270"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_271"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_271 == /\ pc = "Lbl_271"
           /\ \/ /\ (validators[2]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                 /\ pc' = "Lbl_272"
              \/ /\ (validators[2]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[3]).prepareSig]
                 /\ IF prepareCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_273"
                       ELSE /\ pc' = "Lbl_277"
              \/ /\ (validators[2]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_275"
                       ELSE /\ pc' = "Lbl_277"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[3]).state = 9
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_276"
                       ELSE /\ pc' = "Lbl_277"
              \/ /\ TRUE
                 /\ pc' = "Lbl_277"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_272 == /\ pc = "Lbl_272"
           /\ validators' = [validators EXCEPT ![2].state = 1]
           /\ pc' = "Lbl_277"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_273 == /\ pc = "Lbl_273"
           /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
           /\ pc' = "Lbl_274"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_274 == /\ pc = "Lbl_274"
           /\ validators' = [validators EXCEPT ![2].state = 2]
           /\ pc' = "Lbl_277"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_275 == /\ pc = "Lbl_275"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_277"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_276 == /\ pc = "Lbl_276"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_277"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_277 == /\ pc = "Lbl_277"
           /\ \/ /\ (validators[3]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                 /\ pc' = "Lbl_278"
              \/ /\ (validators[3]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[3]).prepareSig]
                 /\ IF prepareCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_279"
                       ELSE /\ pc' = "Lbl_283"
              \/ /\ (validators[3]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_281"
                       ELSE /\ pc' = "Lbl_283"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[3]).state = 9
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_282"
                       ELSE /\ pc' = "Lbl_283"
              \/ /\ TRUE
                 /\ pc' = "Lbl_283"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_278 == /\ pc = "Lbl_278"
           /\ validators' = [validators EXCEPT ![3].state = 1]
           /\ pc' = "Lbl_283"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_279 == /\ pc = "Lbl_279"
           /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
           /\ pc' = "Lbl_280"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_280 == /\ pc = "Lbl_280"
           /\ validators' = [validators EXCEPT ![3].state = 2]
           /\ pc' = "Lbl_283"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_281 == /\ pc = "Lbl_281"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_283"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_282 == /\ pc = "Lbl_282"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_283"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_283 == /\ pc = "Lbl_283"
           /\ \/ /\ (validators[4]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                 /\ pc' = "Lbl_284"
              \/ /\ (validators[4]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[3]).state = 1 \/ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[3]).prepareSig]
                 /\ IF prepareCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_285"
                       ELSE /\ pc' = "Lbl_289"
              \/ /\ (validators[4]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[3]).state = 2
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_287"
                       ELSE /\ pc' = "Lbl_289"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[3]).state = 9
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[3]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_288"
                       ELSE /\ pc' = "Lbl_289"
              \/ /\ TRUE
                 /\ pc' = "Lbl_289"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_284 == /\ pc = "Lbl_284"
           /\ validators' = [validators EXCEPT ![4].state = 1]
           /\ pc' = "Lbl_289"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_285 == /\ pc = "Lbl_285"
           /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
           /\ pc' = "Lbl_286"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_286 == /\ pc = "Lbl_286"
           /\ validators' = [validators EXCEPT ![4].state = 2]
           /\ pc' = "Lbl_289"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_287 == /\ pc = "Lbl_287"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_289"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_288 == /\ pc = "Lbl_288"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Lbl_289"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_289 == /\ pc = "Lbl_289"
           /\ \/ /\ (validators[1]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![1].prepareSig = {(validators[1]).sig}]
                 /\ pc' = "Lbl_290"
              \/ /\ (validators[1]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_291"
                       ELSE /\ pc' = "Lbl_295"
              \/ /\ (validators[1]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_293"
                       ELSE /\ pc' = "Lbl_295"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[4]).state = 9
                 /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[1]))
                       THEN /\ pc' = "Lbl_294"
                       ELSE /\ pc' = "Lbl_295"
              \/ /\ TRUE
                 /\ pc' = "Lbl_295"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_290 == /\ pc = "Lbl_290"
           /\ validators' = [validators EXCEPT ![1].state = 1]
           /\ pc' = "Lbl_295"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_291 == /\ pc = "Lbl_291"
           /\ validators' = [validators EXCEPT ![1].commitSig = {(validators[1]).sig}]
           /\ pc' = "Lbl_292"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_292 == /\ pc = "Lbl_292"
           /\ validators' = [validators EXCEPT ![1].state = 2]
           /\ pc' = "Lbl_295"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_293 == /\ pc = "Lbl_293"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_295"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_294 == /\ pc = "Lbl_294"
           /\ validators' = [validators EXCEPT ![1].state = 9]
           /\ pc' = "Lbl_295"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_295 == /\ pc = "Lbl_295"
           /\ \/ /\ (validators[2]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![2].prepareSig = {(validators[2]).sig}]
                 /\ pc' = "Lbl_296"
              \/ /\ (validators[2]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![2].prepareSig = (validators[2]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_297"
                       ELSE /\ pc' = "Lbl_301"
              \/ /\ (validators[2]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_299"
                       ELSE /\ pc' = "Lbl_301"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[4]).state = 9
                 /\ validators' = [validators EXCEPT ![2].commitSig = (validators[2]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[2]))
                       THEN /\ pc' = "Lbl_300"
                       ELSE /\ pc' = "Lbl_301"
              \/ /\ TRUE
                 /\ pc' = "Lbl_301"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_296 == /\ pc = "Lbl_296"
           /\ validators' = [validators EXCEPT ![2].state = 1]
           /\ pc' = "Lbl_301"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_297 == /\ pc = "Lbl_297"
           /\ validators' = [validators EXCEPT ![2].commitSig = {(validators[2]).sig}]
           /\ pc' = "Lbl_298"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_298 == /\ pc = "Lbl_298"
           /\ validators' = [validators EXCEPT ![2].state = 2]
           /\ pc' = "Lbl_301"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_299 == /\ pc = "Lbl_299"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_301"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_300 == /\ pc = "Lbl_300"
           /\ validators' = [validators EXCEPT ![2].state = 9]
           /\ pc' = "Lbl_301"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_301 == /\ pc = "Lbl_301"
           /\ \/ /\ (validators[3]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![3].prepareSig = {(validators[3]).sig}]
                 /\ pc' = "Lbl_302"
              \/ /\ (validators[3]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![3].prepareSig = (validators[3]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_303"
                       ELSE /\ pc' = "Lbl_307"
              \/ /\ (validators[3]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_305"
                       ELSE /\ pc' = "Lbl_307"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[4]).state = 9
                 /\ validators' = [validators EXCEPT ![3].commitSig = (validators[3]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[3]))
                       THEN /\ pc' = "Lbl_306"
                       ELSE /\ pc' = "Lbl_307"
              \/ /\ TRUE
                 /\ pc' = "Lbl_307"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_302 == /\ pc = "Lbl_302"
           /\ validators' = [validators EXCEPT ![3].state = 1]
           /\ pc' = "Lbl_307"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_303 == /\ pc = "Lbl_303"
           /\ validators' = [validators EXCEPT ![3].commitSig = {(validators[3]).sig}]
           /\ pc' = "Lbl_304"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_304 == /\ pc = "Lbl_304"
           /\ validators' = [validators EXCEPT ![3].state = 2]
           /\ pc' = "Lbl_307"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_305 == /\ pc = "Lbl_305"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_307"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_306 == /\ pc = "Lbl_306"
           /\ validators' = [validators EXCEPT ![3].state = 9]
           /\ pc' = "Lbl_307"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_307 == /\ pc = "Lbl_307"
           /\ \/ /\ (validators[4]).state = 0
                 /\ "validateMsg" = "block"
                 /\ validators' = [validators EXCEPT ![4].prepareSig = {(validators[4]).sig}]
                 /\ pc' = "Lbl_308"
              \/ /\ (validators[4]).state = 1
                 /\ "validateMsg" = "prepareMsg"
                 /\ (validators[4]).state = 1 \/ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![4].prepareSig = (validators[4]).prepareSig \union (validators[4]).prepareSig]
                 /\ IF prepareCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_309"
                       ELSE /\ pc' = "Done"
              \/ /\ (validators[4]).state = 2
                 /\ "validateMsg" = "commitMsg"
                 /\ (validators[4]).state = 2
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_311"
                       ELSE /\ pc' = "Done"
              \/ /\ "validateMsg" = "validateMsg"
                 /\ (validators[4]).state = 9
                 /\ validators' = [validators EXCEPT ![4].commitSig = (validators[4]).commitSig \union (validators[4]).commitSig]
                 /\ IF commitCertificate((validators'[4]))
                       THEN /\ pc' = "Lbl_312"
                       ELSE /\ pc' = "Done"
              \/ /\ TRUE
                 /\ pc' = "Done"
                 /\ UNCHANGED validators
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_308 == /\ pc = "Lbl_308"
           /\ validators' = [validators EXCEPT ![4].state = 1]
           /\ pc' = "Done"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_309 == /\ pc = "Lbl_309"
           /\ validators' = [validators EXCEPT ![4].commitSig = {(validators[4]).sig}]
           /\ pc' = "Lbl_310"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_310 == /\ pc = "Lbl_310"
           /\ validators' = [validators EXCEPT ![4].state = 2]
           /\ pc' = "Done"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_311 == /\ pc = "Lbl_311"
           /\ validators' = [validators EXCEPT ![4].state = 9]
           /\ pc' = "Done"
           /\ UNCHANGED << proposers, validatorIndices >>

Lbl_312 == /\ pc = "Lbl_312"
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
           \/ Lbl_177 \/ Lbl_178 \/ Lbl_179 \/ Lbl_180 \/ Lbl_181 \/ Lbl_182
           \/ Lbl_183 \/ Lbl_184 \/ Lbl_185 \/ Lbl_186 \/ Lbl_187 \/ Lbl_188
           \/ Lbl_189 \/ Lbl_190 \/ Lbl_191 \/ Lbl_192 \/ Lbl_193 \/ Lbl_194
           \/ Lbl_195 \/ Lbl_196 \/ Lbl_197 \/ Lbl_198 \/ Lbl_199 \/ Lbl_200
           \/ Lbl_201 \/ Lbl_202 \/ Lbl_203 \/ Lbl_204 \/ Lbl_205 \/ Lbl_206
           \/ Lbl_207 \/ Lbl_208 \/ Lbl_209 \/ Lbl_210 \/ Lbl_211 \/ Lbl_212
           \/ Lbl_213 \/ Lbl_214 \/ Lbl_215 \/ Lbl_216 \/ Lbl_217 \/ Lbl_218
           \/ Lbl_219 \/ Lbl_220 \/ Lbl_221 \/ Lbl_222 \/ Lbl_223 \/ Lbl_224
           \/ Lbl_225 \/ Lbl_226 \/ Lbl_227 \/ Lbl_228 \/ Lbl_229 \/ Lbl_230
           \/ Lbl_231 \/ Lbl_232 \/ Lbl_233 \/ Lbl_234 \/ Lbl_235 \/ Lbl_236
           \/ Lbl_237 \/ Lbl_238 \/ Lbl_239 \/ Lbl_240 \/ Lbl_241 \/ Lbl_242
           \/ Lbl_243 \/ Lbl_244 \/ Lbl_245 \/ Lbl_246 \/ Lbl_247 \/ Lbl_248
           \/ Lbl_249 \/ Lbl_250 \/ Lbl_251 \/ Lbl_252 \/ Lbl_253 \/ Lbl_254
           \/ Lbl_255 \/ Lbl_256 \/ Lbl_257 \/ Lbl_258 \/ Lbl_259 \/ Lbl_260
           \/ Lbl_261 \/ Lbl_262 \/ Lbl_263 \/ Lbl_264 \/ Lbl_265 \/ Lbl_266
           \/ Lbl_267 \/ Lbl_268 \/ Lbl_269 \/ Lbl_270 \/ Lbl_271 \/ Lbl_272
           \/ Lbl_273 \/ Lbl_274 \/ Lbl_275 \/ Lbl_276 \/ Lbl_277 \/ Lbl_278
           \/ Lbl_279 \/ Lbl_280 \/ Lbl_281 \/ Lbl_282 \/ Lbl_283 \/ Lbl_284
           \/ Lbl_285 \/ Lbl_286 \/ Lbl_287 \/ Lbl_288 \/ Lbl_289 \/ Lbl_290
           \/ Lbl_291 \/ Lbl_292 \/ Lbl_293 \/ Lbl_294 \/ Lbl_295 \/ Lbl_296
           \/ Lbl_297 \/ Lbl_298 \/ Lbl_299 \/ Lbl_300 \/ Lbl_301 \/ Lbl_302
           \/ Lbl_303 \/ Lbl_304 \/ Lbl_305 \/ Lbl_306 \/ Lbl_307 \/ Lbl_308
           \/ Lbl_309 \/ Lbl_310 \/ Lbl_311 \/ Lbl_312
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================

