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


macro fsm(v, inputType) begin
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
        v.commitSig := v.commitSig \union {input.commitSig};
        await commitCertificate(v);
        \* transfer to ilde state in next height given the certificate
        v.commitSig := {};
        v.state := 9
    end either
end macro;


begin

\* Validator1:
\*   fsm(validators[1], "block");
\*   fsm(validators[2], "block");
\*   fsm(validators[3], "block");
\*   fsm(validators[4], "block");


end algorithm;*)
====

\* BEGIN TRANSLATION
VARIABLES proposers, validators

(* define statement *)
prepareCertificate(v) ==
    Len(v.prepareSig) >= 3

commitCertificate(v) ==
    Len(v.commitSig) >= 3

impeachPrepareCertificate(v) ==
    Len(v.impeachPrepareSig) >= 2

impeachCommitCertificate(v) ==
    Len(v.impeachCommitSig) >= 2


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
