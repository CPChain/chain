-------------------------------- MODULE lbft --------------------------------
EXTENDS Integers

(*
--algorithm lbft
variables
    proposers = <<"p1","p2">>,
    \* sequence of proposers
    validators = <<
    [state |-> 0, preSig |-> <<>>, cmtSig |-><<>>, impPreSig |-><<>>, impCmtSig |-><<>>],
    [state |-> 0, preSig |-> <<>>, cmtSig |-><<>>, impPreSig |-><<>>, impCmtSig |-><<>>],
    [state |-> 0, preSig |-> <<>>, cmtSig |-><<>>, impPreSig |-><<>>, impCmtSig |-><<>>],
    [state |-> 0, preSig |-> <<>>, cmtSig |-><<>>, impPreSig |-><<>>, impCmtSig |-><<>>]
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

macro fsm(v) begin
    either v.state = 0
        v.state 1 := 0
    or v.state = 1
        v.state := 2
    or v.state = 2
        v.stat := 1
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
                        [state |-> 0, preSig |-> <<>>, cmtSig |-><<>>, impPreSig |-><<>>, impCmtSig |-><<>>],
                        [state |-> 0, preSig |-> <<>>, cmtSig |-><<>>, impPreSig |-><<>>, impCmtSig |-><<>>],
                        [state |-> 0, preSig |-> <<>>, cmtSig |-><<>>, impPreSig |-><<>>, impCmtSig |-><<>>],
                        [state |-> 0, preSig |-> <<>>, cmtSig |-><<>>, impPreSig |-><<>>, impCmtSig |-><<>>]
                        >>

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Wed Mar 20 20:33:03 CST 2019 by Dell
\* Created Thu Feb 21 18:37:39 CST 2019 by Dell
