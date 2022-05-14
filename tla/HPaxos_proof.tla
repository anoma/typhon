---------------------------- MODULE HPaxos_proof ----------------------------
EXTENDS HPaxos

LEMMA BallotLeqTransBis ==
    ASSUME NEW A \in Ballot, NEW B \in Ballot, NEW C \in Ballot, A =< B, B =< C PROVE A =< C
PROOF BY DEF Ballot

=============================================================================
