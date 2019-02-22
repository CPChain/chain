-------------------------------- MODULE lbft --------------------------------
EXTENDS Integers

(*--algorithm lbft
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
    prepareCertificate(v) ==
        Len(v.preSig) >= 3

    commitCertificate(v) ==
        Len(v.cmtSig) >= 3

    impeachPrepareCertificate(v) ==
        Len(v.impPreSig) >= 2

    impeachCommitCertificate(v) ==
        Len(v.impCmtSig) >= 2

    \* return true if suffice a certificate
end define;

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
\* Last modified Fri Feb 22 20:37:36 CST 2019 by Dell
\* Created Thu Feb 21 18:37:39 CST 2019 by Dell
