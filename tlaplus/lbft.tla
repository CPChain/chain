-------------------------------- MODULE lbft --------------------------------

EXTENDS Integers, Sequences


(*
--algorithm lbft
variables
    proposers = <<"p1","p2">>,
    \* sequence of proposers
    validators = <<
    [state |-> 0, prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
    [state |-> 0, prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
    [state |-> 0, prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
    [state |-> 0, prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}]
    >>,
    \* sequence of validators
    \* 0,1,2 represent idle, prepare, commit
    \* 3,4 represent impeach prepare and impeach commit state
    \* 9 represents ilde state in next block height
    \* pre and cmt are short for prepare and commit respectively
    \* imp represents impeachment
    \* four sigs refers to signatures for different messages

define
    \* return true if suffice a certificate
    prepareCertificate(v) ==
        Len(v.prepareSig) >= 3

    commitCertificate(v) ==
        Len(v.commitSig) >= 3

    impeachPrepareCertificate(v) ==
        Len(v.impeachPrepareSig) >= 2

    impeachCommitCertificate(v) ==
        Len(v.impeachCommitSig) >= 2

end define;


macro fsm(v, inputType, input) begin
    either \* idle state
    \* transfer to prepare state given a block
        await v.state = 0;
        await inputType = "block";
        v.state := 1

    or  \* prepare state
        await v.state = 1;
        await inputType = "prepareMsg";
        \* accumulate prepare signatures
        v.prepareSig := v.prepareSig \union {input.prepareSig};
        if prepareCertificate(v)
        then
        \* transfer to commit state if collect a certificate
            v.prepareSig := {};
            v.state := 2;
        end if;

    or  \* commit state
        await v.state = 2;
        await inputType = "commitMsg";
        \* accumulate commit signatures
        v.commitSig := v.commitSig \union {input.commitSig};
        if commitCertificate(v)
        then
        \* transfer to ilde state in next height given the certificate
            v.commitSig := {};
            v.state := 9;
        end if;
    end either
end macro;




begin

\* Validator1:
    fsm(validators[1], "block", "");
\*    fsm(validators[2], "block");
\*    fsm(validators[3], "block");
\*    fsm(validators[4], "block");



end algorithm;*)


\* BEGIN TRANSLATION
VARIABLES proposers, validators, pc

(* define statement *)
prepareCertificate(v) ==
    Len(v.prepareSig) >= 3

commitCertificate(v) ==
    Len(v.commitSig) >= 3

impeachPrepareCertificate(v) ==
    Len(v.impeachPrepareSig) >= 2

impeachCommitCertificate(v) ==
    Len(v.impeachCommitSig) >= 2


vars == << proposers, validators, pc >>

Init == (* Global variables *)
        /\ proposers = <<"p1","p2">>
        /\ validators =              <<
                        [state |-> 0, prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
                        [state |-> 0, prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
                        [state |-> 0, prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
                        [state |-> 0, prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}]
                        >>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ \/ /\ (validators[1]).state = 0
               /\ "block" = "block"
               /\ validators' = [validators EXCEPT ![1].state = 1]
               /\ pc' = "Done"
            \/ /\ (validators[1]).state = 1
               /\ "block" = "prepareMsg"
               /\ validators' = [validators EXCEPT ![1].prepareSig = (validators[1]).prepareSig \union {input.prepareSig}]
               /\ IF prepareCertificate((validators'[1]))
                     THEN /\ pc' = "Lbl_2"
                     ELSE /\ pc' = "Done"
            \/ /\ (validators[1]).state = 2
               /\ "block" = "commitMsg"
               /\ validators' = [validators EXCEPT ![1].commitSig = (validators[1]).commitSig \union {input.commitSig}]
               /\ IF commitCertificate((validators'[1]))
                     THEN /\ pc' = "Lbl_4"
                     ELSE /\ pc' = "Done"
         /\ UNCHANGED proposers

Lbl_2 == /\ pc = "Lbl_2"
         /\ validators' = [validators EXCEPT ![1].prepareSig = {}]
         /\ pc' = "Lbl_3"
         /\ UNCHANGED proposers

Lbl_3 == /\ pc = "Lbl_3"
         /\ validators' = [validators EXCEPT ![1].state = 2]
         /\ pc' = "Done"
         /\ UNCHANGED proposers

Lbl_4 == /\ pc = "Lbl_4"
         /\ validators' = [validators EXCEPT ![1].commitSig = {}]
         /\ pc' = "Lbl_5"
         /\ UNCHANGED proposers

Lbl_5 == /\ pc = "Lbl_5"
         /\ validators' = [validators EXCEPT ![1].state = 9]
         /\ pc' = "Done"
         /\ UNCHANGED proposers

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Wed Apr 03 09:40:06 CST 2019 by Dell
\* Created Thu Feb 14 11:05:47 CST 2019 by Dell
