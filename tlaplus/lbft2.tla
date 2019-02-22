-------------------------------- MODULE lbft --------------------------------
EXTENDS Integers

(*--algorithm lbft
    variables
        proposers = <<"p1","p2">>,
        \* sequence of proposers
        validators = <<
        [state |-> 0, preCnt |->0, cmtCnt |->0, impPreCnt |->0, impCmtCnt |->0],
        [state |-> 0, preCnt |->0, cmtCnt |->0, impPreCnt |->0, impCmtCnt |->0],
        [state |-> 0, preCnt |->0, cmtCnt |->0, impPreCnt |->0, impCmtCnt |->0],
        [state |-> 0, preCnt |->0, cmtCnt |->0, impPreCnt |->0, impCmtCnt |->0]
        >>,
        \* sequence of validators
        \* 0,1,2 represent idle, prepare, commit
        \* 3,4 represent impeach prepare and impeach commit state
        \* pre and cmt are short for prepare and commit respectively
        \* imp represents impeachment, and cnt is counter

define
    prepareCertificate(v) ==
        v.preCnt >= 3

    commitCertificate(v) ==
        v.cmtCNt >= 3

    impeachPrepareCertificate(v) ==
        v.impPreCnt >= 2

    impeachCommitCertificate(v) ==
        v.impCmtCnt >= 2

    \* return true if suffice a certificate
end define;

begin

end algorithm;*)
====

\* BEGIN TRANSLATION
VARIABLES proposers, validators

(* define statement *)
prepareCertificate(v) ==
    v.preCnt >= 3

commitCertificate(v) ==
    v.cmtCNt >= 3

impeachPrepareCertificate(v) ==
    v.impPreCnt >= 2

impeachCommitCertificate(v) ==
    v.impCmtCnt >= 2


vars == << proposers, validators >>

Init == (* Global variables *)
        /\ proposers = <<"p1","p2">>
        /\ validators =              <<
                        [state |-> 0, preCnt |->0, cmtCnt |->0, impPreCnt |->0, impCmtCnt |->0],
                        [state |-> 0, preCnt |->0, cmtCnt |->0, impPreCnt |->0, impCmtCnt |->0],
                        [state |-> 0, preCnt |->0, cmtCnt |->0, impPreCnt |->0, impCmtCnt |->0],
                        [state |-> 0, preCnt |->0, cmtCnt |->0, impPreCnt |->0, impCmtCnt |->0]
                        >>

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Fri Feb 22 20:27:59 CST 2019 by Dell
\* Created Thu Feb 21 18:37:39 CST 2019 by Dell
