-------------------------- MODULE HPaxos_liveness ---------------------------
EXTENDS HPaxos
-----------------------------------------------------------------------------
(***************************************************************************)
(*                               Liveness                                  *)
(***************************************************************************)

THEOREM Liveness ==
    Spec =>
        \A L \in Learner : \A b \in Ballot, Q \in ByzQuorum :
            Q \subseteq SafeAcceptor /\
            [lr |-> L, q |-> Q] \in TrustLive =>
            (
              (
                /\ \A a \in Q : WF_vars(Disconnect(a))
                /\ \A m \in msgs :
                    m.type = "1a" /\ m.lr = L => m.bal < b
                /\ \A c \in Ballot :
                    c > b => [][~Phase1a(L, c)]_vars
                /\ WF_vars(Phase1a(L, b))
                /\ WF_vars(\E v \in Value : Phase1c(L, b, v))
                /\ \A a \in Q : WF_vars(Phase1b(L, b, a))
                /\ \A a \in Q :
                    WF_vars(\E v \in Value : Phase2av(L, b, a, v))
                /\ \A a \in Q :
                    \E v \in Value : WF_vars(Phase2b(L, b, a, v))
              )
              ~>
              (\E B \in Ballot : decision[L, B] # {})
            )

CONSTANTS bb, LL, QQ

CSpec ==
    /\ QQ \subseteq SafeAcceptor
    /\ [lr |-> LL, q |-> QQ] \in TrustLive
    /\ Init
    /\ [][Next]_vars
    /\ [][\A c \in Ballot : c > bb => ~Phase1a(LL, c)]_vars
    /\ WF_vars(Phase1a(LL, bb))
    /\ WF_vars(\E v \in Value : Phase1c(LL, bb, v))
    /\ \A a \in QQ : WF_vars(\E v \in Value : Phase2av(LL, bb, a, v))
    /\ \A a \in QQ : WF_vars(Phase1b(LL, bb, a))
    /\ \A a \in QQ : \E v \in Value : WF_vars(Phase2b(LL, bb, a, v))

CLiveness ==
    (\A m \in msgs : m.type = "1a" /\ m.lr = LL => m.bal < bb)
    ~>
    (\E B \in Ballot : decision # {})


=============================================================================
