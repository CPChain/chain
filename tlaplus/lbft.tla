-------------------------------- MODULE lbft --------------------------------
EXTENDS Integers

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
    \* pre and cmt are short for prepare and commit respectively
    \* imp represents impeachment
    \* four sigs refers to signatures for different messages

define
    \* return true if suffice a certificate
    prepareCertificate(v) ==
        Len(v.preSig) >= 3

    commitCertificate(v) ==
        Len(v.cmtSig) >= 3

    impeachPrepareCertificate(v) ==
        Len(v.impPreSig) >= 2

    impeachCommitCertificate(v) ==
        Len(v.impCmtSig) >= 2


end define;


macro fsm(v, inputType) begin
    either \* idle state
        await v.state = 0;
        await inputType = "block";
        v.state := 1

    or  \* prepare state
        await v.state = 1;
        await inputType = "prepareMsg";
        v.prepareSig := v.prepareSig \union {input.prepareSig};
        await prepareCertificate(v);
        v.prepareSig := {};
        v.state := 2

    or  \* commit state
        await v.state = 2;
        await inputType = "commitMsg";
        v.commitSig := v.commitSig \union {input.commitSig};
        await commitCertificate(v);
        v.commitSig := {};
        v.state := 0
    end either
end macro;




begin




end algorithm;*)
====

\* BEGIN TRANSLATION
VARIABLES proposers, validators

(* define statement *)
prepareCertificate(v) ==
    Len(v.preSig) >= 3

commitCertificate(v) ==
    Len(v.cmtSig) >= 3

impeachPrepareCertificate(v) ==
    Len(v.impPreSig) >= 2

impeachCommitCertificate(v) ==
    Len(v.impCmtSig) >= 2


vars == << proposers, validators >>

Init == (* Global variables *)
        /\ proposers = <<"p1","p2">>
        /\ validators =              <<
                        [state |-> 0, prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
                        [state |-> 0, prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
                        [state |-> 0, prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}],
                        [state |-> 0, prepareSig |-> {}, commitSig |->{}, impeachPrepareSig |->{}, impeachCommitSig |->{}]
                        >>

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
