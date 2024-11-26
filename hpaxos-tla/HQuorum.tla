------------------------------ MODULE HQuorum -------------------------------
CONSTANTS Proposer,
          SafeAcceptor,
          FakeAcceptor,
          ByzQuorum

Acceptor == SafeAcceptor \cup FakeAcceptor

ASSUME AcceptorAssumption ==
    /\ SafeAcceptor \cap FakeAcceptor = {}

ASSUME BQAssumption ==
    /\ SafeAcceptor \in ByzQuorum
    /\ \A Q \in ByzQuorum : Q \subseteq Acceptor

=============================================================================
\* Modification History
\* Last modified Tue May 14 16:32:50 CEST 2024 by karbyshev
\* Created Tue May 14 16:29:16 CEST 2024 by karbyshev
