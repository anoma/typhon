----------------------- MODULE HPaxosTR_liveness ----------------------------
EXTENDS HPaxosTR
-----------------------------------------------------------------------------
(***************************************************************************)
(*                               Liveness                                  *)
(*                                                                         *)
(* For any learner L, ballot b and quorum Q of safe acceptors trusted by L *)
(* such that                                                               *)
(*                                                                         *)
(*  1. No phase 1a messages (a) have been or (b) ever will be sent for any *)
(*     ballot number greater than b.                                       *)
(*                                                                         *)
(*  2. The ballot b leader eventually sends a 1a message for ballot b.     *)
(*                                                                         *)
(*  3. Each acceptor in Q eventually receives a 1a message of ballot b and *)
(*     responds to it by sending a 1b message.                             *)
(*                                                                         *)
(*  4. (a) Each acceptor in Q eventually receives a 1b message of ballot b *)
(*         from themself and every other acceptor of Q, and                *)
(*     (b) sends 2a containing the quorum of 1b messages to every learner  *)
(*         which live-trusts the quorum Q. In particular, the 2a messages  *)
(*         are sent to the learner L.                                      *)
(*                                                                         *)
(*  5. The learner L receives all 2a messages of ballot b addressed to it. *)
(*                                                                         *)
(*  6. Learner L eventually executes its decision action for ballot b if   *)
(*     it has a chance to do so.                                           *)
(*                                                                         *)
(* then some value is eventually chosen.                                   *)
(***************************************************************************)

THEOREM Liveness ==
    Spec =>
        \A L \in Learner : \A b \in Ballot, Q \in ByzQuorum :
            Q \subseteq SafeAcceptor /\
            [lr |-> L, q |-> Q] \in TrustLive =>
            (
              (
                \* (1a)
                /\ \A m \in msgs : m.type = "1a" => m.bal < b
                \* (1b)
                /\ \A c \in Ballot : (c > b) => [][~Send1a(c)]_vars
                \* (2)
                /\ WF_vars(Send1a(b))
                \* (3)
                /\ \A a \in Q : \A m \in msgs :
                    B(m, b) => WF_vars(Process1a(a, m))
                \* (4a)
                /\ \A a \in Q : \A m \in msgs :
                    B(m, b) => WF_vars(Process1b(a, m))
                \* (4b)
                /\ \A a \in Q : WF_vars(Process1bLearnerLoop(a))
                \* (5)
                /\ \A a \in Q : \A m \in msgs :
                    B(m, b) => WF_vars(Process2a(a, m))
                \* (6)
                /\ WF_vars(\E v \in Value : LearnerDecide(L, b, v))
              )
              ~>
              (\E B \in Ballot : decision[L, B] # {})
            )

\*CONSTANTS bb, LL, QQ
\*
\*CSpec ==
\*    /\ QQ \subseteq SafeAcceptor
\*    /\ [lr |-> LL, q |-> QQ] \in TrustLive
\*    /\ Init
\*    /\ [][Next]_vars
\*    /\ [][\A m \in msgs : m.type = "1a" => m.bal <= bb]_vars
\*    /\ \A a \in QQ : \A m \in msgs : WF_vars(Process1a(a, m))
\*    /\ \A a \in QQ : \A m \in msgs : WF_vars(Process1b(a, m))
\*    /\ \A a \in QQ : WF_vars(Process1bLearnerLoop(a))
\*    /\ \A a \in QQ : \A m \in msgs : WF_vars(Process2a(a, m))
\*    /\ WF_vars(\E v \in Value : LearnerDecide(L, b, v))
\*
\*CLiveness ==
\*    (\A m \in msgs : m.type = "1a" /\ m.lr = LL => m.bal < bb)
\*    ~>
\*    (\E B \in Ballot : decision # {})

=============================================================================
\* Modification History
\* Last modified Fri Oct 14 17:22:51 CEST 2022 by aleph
\* Created Mon Oct 14 10:13:01 CEST 2022 by aleph

