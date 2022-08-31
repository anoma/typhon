------------------------------ MODULE HPaxosTR ------------------------------
EXTENDS Naturals, FiniteSets

-----------------------------------------------------------------------------
CONSTANT LastBallot
ASSUME LastBallot \in Nat

Ballot == 0..LastBallot
\*Ballot == Nat

CONSTANT Value
ASSUME ValueNotEmpty == Value # {}

-----------------------------------------------------------------------------
CONSTANTS Acceptor,
          SafeAcceptor,
          ByzQuorum,
          Learner

ASSUME AcceptorLearner == Acceptor \cap Learner = {}

FakeAcceptor == Acceptor \ SafeAcceptor

ASSUME BQAssumption == \A Q \in ByzQuorum : Q \subseteq Acceptor

\*ASSUME BallotAssumption ==
\*        /\ (Ballot \cup {-1}) \cap Acceptor = {}
\*        /\ (Ballot \cup {-1}) \cap ByzQuorum = {}
\*        /\ (Ballot \cup {-1}) \cap Learner = {}

-----------------------------------------------------------------------------
(* Learner graph *)

CONSTANT TrustLive
ASSUME TrustLiveAssumption == TrustLive \in SUBSET [lr : Learner, q : ByzQuorum]

CONSTANT TrustSafe
ASSUME TrustSafeAssumption == TrustSafe \in SUBSET [from : Learner, to : Learner, q : ByzQuorum]

ASSUME LearnerGraphAssumption ==
        (* symmetry *)
        /\ \A E \in TrustSafe :
            [from |-> E.to, to |-> E.from, q |-> E.q] \in TrustSafe
        (* transitivity *)
        /\ \A E1, E2 \in TrustSafe :
            E1.q = E2.q /\ E1.to = E2.from =>
            [from |-> E1.from, to |-> E2.to, q |-> E1.q] \in TrustSafe
        (* closure *)
        /\ \A E \in TrustSafe : \A Q \in ByzQuorum :
            E.q \subseteq Q =>
            [from |-> E.from, to |-> E.to, q |-> Q] \in TrustSafe
        (* validity *)
        /\ \A E \in TrustSafe : \A Q1, Q2 \in ByzQuorum :
            [lr |-> E.from, q |-> Q1] \in TrustLive /\
            [lr |-> E.to, q |-> Q2] \in TrustLive =>
            \E N \in E.q : N \in Q1 /\ N \in Q2

(* Entanglement relation *)
Ent == { LL \in Learner \X Learner :
         [from |-> LL[1], to |-> LL[2], q |-> SafeAcceptor] \in TrustSafe }

-----------------------------------------------------------------------------
(* Messages *)

CONSTANT MaxRefCardinality
ASSUME MaxRefCardinality \in Nat

\*RefCardinalityRange == Nat
RefCardinalityRange == 0..MaxRefCardinality

MessageRec0 ==
    [ type : {"1a"}, bal : Ballot, val : Value, ref : {} ] \cup
    [ type : {"1b"}, acc : Acceptor, ref : {} ] \cup
    [ type : {"2a"}, lrn : Learner, acc : Acceptor, ref : {} ]

MessageRec1(M, n) ==
    M \cup
    [ type : {"1b"},
      acc : Acceptor,
      ref : { MM \in SUBSET M : Cardinality(MM) \in RefCardinalityRange } ] \cup
    [ type : {"2a"},
      lrn : Learner,
      acc : Acceptor,
      ref : { MM \in SUBSET M : Cardinality(MM) \in RefCardinalityRange } ]

\*MessageRec ==
\*    CHOOSE MessageRec :
\*    MessageRec = [n \in Nat |->
\*                    IF n = 0
\*                    THEN MessageRec0
\*                    ELSE MessageRec1(MessageRec[n-1], n)]

MessageRec[n \in Nat] ==
    IF n = 0
    THEN MessageRec0
    ELSE MessageRec1(MessageRec[n-1], n)

CONSTANT MaxMessageDepth
ASSUME MaxMessageDepth \in Nat

\*MessageDepthRange == Nat
MessageDepthRange == 0..MaxMessageDepth

Message == UNION { MessageRec[n] : n \in MessageDepthRange }

-----------------------------------------------------------------------------
(* Transitive references *)

\* Bounded transitive references
TranBound0 == [m \in Message |-> {m}]
TranBound1(tr, n) ==
    [m \in Message |-> {m} \cup UNION {tr[r] : r \in m.ref}]

\*TranBound ==
\*    CHOOSE TranBound :
\*    TranBound = [n \in Nat |->
\*                    IF n = 0
\*                    THEN TranBound0
\*                    ELSE TranBound1(TranBound[n-1], n)]

TranBound[n \in Nat] ==
    IF n = 0
    THEN TranBound0
    ELSE TranBound1(TranBound[n-1], n)

\* Countable transitive references
\*TranDepthRange == Nat
TranDepthRange == MessageDepthRange

Tran(m) == UNION {TranBound[n][m] : n \in TranDepthRange}

-----------------------------------------------------------------------------

\* We assume that each 1a-message has a unique value and ballot number,
\* which could be accomplished by incorporating a hash of the value and the
\* sender signature information in the ballot number.
ASSUME 1aAssumption ==
    \A m1, m2 \in Message :
        m1.type = "1a" /\ m2.type = "1a" /\ m1.bal = m2.bal =>
        m1 = m2

-----------------------------------------------------------------------------
\*None == CHOOSE v : v \notin Value /\ v \notin Message

-----------------------------------------------------------------------------
(* Algorithm specification *)

VARIABLES msgs,
          known_msgs,
          recent_msgs,
          2a_lrn_loop,
          processed_lrns,
          decision

Get1a(m, x) ==
    /\ x.type = "1a"
    /\ x \in Tran(m)
    /\ \A y \in Tran(m) :
        y.type = "1a" => y.bal <= x.bal
\* Invariant: Get1a(m, x) /\ Get1a(m, y) => x = y
\* TODO: totality for 1b, 2a messages. Required invariant:
\*   each well-formed 1b references a 1a.

B(m, bal) == \E x \in Message : Get1a(m, x) /\ x.bal = bal

V(m, v) == \E x \in Message : Get1a(m, x) /\ x.val = v

\* Maximal ballot number of any messages known to acceptor a
MaxBal(a, mbal) ==
    /\ \E m \in known_msgs[a] : B(m, mbal)
    /\ \A x \in known_msgs[a] :
        \A b \in Ballot : B(x, b) => b =< mbal

SameBallot(x, y) ==
    \A b \in Ballot : B(x, b) <=> B(y, b)

\* The acceptor is _caught_ in a message x if the transitive references of x
\* include evidence such as two messages both signed by the acceptor, in which
\* neither is featured in the other's transitive references.
Caught(x) ==
    LET P == { m \in Tran(x) :
                /\ m.type # "1a"
                /\ \E m1 \in Tran(x) :
                    /\ m1.type # "1a"
                    /\ m.acc = m1.acc
                    /\ m \notin Tran(m1)
                    /\ m1 \notin Tran(m) }
    IN UNION { m.acc : m \in P }

\* Connected
Con(a, x) ==
    { b \in Learner :
        \E S \in ByzQuorum :
            /\ [from |-> a, to |-> b, q |-> S] \in TrustSafe
            /\ S \cap Caught(x) = {} }

\* 2a-message is _buried_ if there exists a quorum of acceptors that have seen
\* 2a-messages with different values, the same learner, and higher ballot
\* numbers.
Buried(x, y) ==
    LET Q == { m \in Tran(y) :
                \E z \in Tran(m) :
                    /\ z.type = "2a"
                    /\ z.lrn = x.lrn
                    /\ \A bx, bz \in Ballot :
                        B(x, bx) /\ B(z, bz) => bx < bz
                    /\ \A vx, vz \in Value :
                        V(x, vx) /\ V(z, vz) => vx # vz }
    IN [lr |-> x.lrn, q |-> {a \in Acceptor : \E m \in Q : m.acc = a}] \in TrustLive

\* Connected 2a messages
Con2as(l, x) ==
    { m \in Tran(x) :
        /\ m.type = "2a"
        /\ m.acc = x.acc
        /\ ~Buried(m, x)
        /\ m.lrn \in Con(l, x) }

\* Fresh 1b messages
Fresh(l, x) ==
    \A m \in Con2as(l, x) : \A v \in Value : V(x, v) <=> V(m, v)

\* Quorum of messages referenced by 2a
q(x) ==
    { m \in Tran(x) :
        /\ m.type = "1b"
        /\ Fresh(x.lrn, m)
        /\ \A mb, xb \in Ballot :
            B(m, mb) /\ B(x, xb) => mb = xb }

WellFormed(m) ==
    /\ m \in Message
    /\ m.type = "1b" =>
        /\ \E r1a \in m.ref :
            /\ r1a.type = "1a"
\*            /\ r1a.bal = m.bal
\*        /\ \A r \in m.ref : r.bal =< m.bal
\*        /\ \A r1, r2 \in m.ref :
\*            r1.bal = m.bal /\ r2.bal = m.bal => r1 = r2
        /\ \A y \in Tran(m) :
            m # y /\ ~Get1a(m, y) => ~SameBallot(m, y)
    /\ m.type = "2a" =>
        /\ [lr |-> m.lrn, q |-> q(m)] \in TrustLive

vars == << msgs, known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns, decision >>

Init ==
    /\ msgs = {}
    /\ known_msgs = [x \in Acceptor \cup Learner |-> {}]
    /\ recent_msgs = [a \in Acceptor |-> {}]
    /\ 2a_lrn_loop = [a \in Acceptor |-> FALSE]
    /\ processed_lrns = [a \in Acceptor |-> {}]
    /\ decision = [lb \in Learner \X Ballot |-> {}]
\*    /\ \A acc \in SafeAcceptor : known_msgs[acc] = {}
\*    /\ \A lrn \in Learner : known_msgs[lrn] = {}
\*    /\ \A acc \in SafeAcceptor : recent_msgs[acc] = {}
\*    /\ \A acc \in SafeAcceptor : 2a_lrn_loop[acc] = TRUE
\*    /\ \A acc \in SafeAcceptor : processed_lrns[acc] = TRUE

Send(m) == msgs' = msgs \cup {m}

Proper(a, m) ==
    /\ \A r \in m.ref : r \in known_msgs[a]

Recv(a, m) ==
    /\ WellFormed(m)
    /\ Proper(a, m)
    /\ known_msgs' = [known_msgs EXCEPT ![a] = known_msgs[a] \cup {m}]

Send1a(b, v) ==
    /\ Send([type |-> "1a", bal |-> b, val |-> v, ref |-> {}])
    /\ UNCHANGED << known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns, decision >>

Process1a(a, m) ==
    LET new1b == [type |-> "1b", acc |-> a, ref |-> recent_msgs[a] \cup {m}] IN
    /\ Recv(a, m)
    /\ m.type = "1a"
    /\ WellFormed(new1b) =>
        /\ recent_msgs' = [recent_msgs EXCEPT ![a] = {}]
        /\ Send(new1b)
    /\ (~WellFormed(new1b)) =>
        /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
        /\ UNCHANGED msgs
    /\ UNCHANGED << 2a_lrn_loop, processed_lrns, decision >>

Process1b(a, m) ==
    /\ Recv(a, m)
    /\ m.type = "1b"
    /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
    /\ (\A b \in Ballot : B(m, b) => MaxBal(a, b)) =>
        /\ 2a_lrn_loop' = [2a_lrn_loop EXCEPT ![a] = TRUE]
        /\ processed_lrns' = [processed_lrns EXCEPT ![a] = {}]
    /\ (~(\A b \in Ballot : B(m, b) => MaxBal(a, b))) =>
        UNCHANGED << 2a_lrn_loop, processed_lrns >>
    /\ UNCHANGED << msgs, decision >>

Process1bLearnerLoop(a) ==
    \/ \E lrn \in Learner \ processed_lrns[a] :
        LET new2a == [type |-> "2a", lrn |-> lrn, ref |-> recent_msgs[a]] IN
        /\ processed_lrns' =
            [processed_lrns EXCEPT ![a] = processed_lrns[a] \cup {lrn}]
        /\ WellFormed(new2a) =>
            /\ Send(new2a)
            /\ recent_msgs' = [recent_msgs EXCEPT ![a] = {new2a}]
        /\ (~WellFormed(new2a)) =>
            UNCHANGED << msgs, recent_msgs >>
        /\ UNCHANGED << known_msgs, 2a_lrn_loop, decision >>
    \/ /\ Learner \ processed_lrns[a] = {}
       /\ 2a_lrn_loop' = [2a_lrn_loop EXCEPT ![a] = FALSE]
       /\ UNCHANGED << msgs, known_msgs, recent_msgs, processed_lrns, decision >>

Process2a(a, m) ==
    /\ Recv(a, m)
    /\ m.type = "2a"
    /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
    /\ UNCHANGED << msgs, 2a_lrn_loop, processed_lrns, decision >>

ProposerSendAction(a) ==
    \E bal \in Ballot : \E val \in Value :
        Send1a(bal, val)

\* vars == << msgs, known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns, decision >>

AcceptorProcessAction(a) ==
    \/ /\ 2a_lrn_loop[a] = FALSE
       /\ \E m \in msgs :
            /\ m \notin known_msgs[a]
            /\ \/ Process1a(a, m)
               \/ Process1b(a, m)
    \/ /\ 2a_lrn_loop[a] = TRUE
       /\ Process1bLearnerLoop(a)

FakeSend(a) ==
    /\ \E m \in { mm \in Message :
                    /\ WellFormed(mm)  \* assume that adversaries can send only
                                       \* wellformed messages
                    /\ mm.acc = a
                    /\ \/ mm.type = "1b"
                       \/ mm.type = "2a" } :
        Send(m)
    /\ UNCHANGED << known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns, decision >>

LearnerRecv(l) ==
    /\ \E m \in msgs :
        /\ Proper(l, m)
        /\ Recv(l, m)
    /\ UNCHANGED << msgs, recent_msgs, 2a_lrn_loop, processed_lrns, decision >>

ChosenIn(l, b, v) ==
    \E S \in SUBSET { x \in known_msgs[l] :
                            /\ x.type = "2a"
                            /\ x.lrn = l
                            /\ B(x, b) } :
        \E Q \in ByzQuorum :
            /\ [lr |-> l, q |-> Q] \in TrustLive
            /\ \A a \in Q :
                \E m \in S : m.acc = a

LearnerDecide(l, b, v) ==
    /\ ChosenIn(l, b, v)
    /\ decision' = [decision EXCEPT ![<<l, b>>] = decision[l, b] \cup {v}]
    /\ UNCHANGED << msgs, known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns >>

LearnerAction ==
    \E lrn \in Learner :
        \/ \E bal \in Ballot :
           \E val \in Value :
            LearnerDecide(lrn, bal, val)
        \/ LearnerRecv(lrn)

FakeAcceptorAction == \E a \in FakeAcceptor : FakeSend(a)

\*MessageNumLimit == 10

Next ==
\*    /\ Cardinality(msgs) < MessageNumLimit
    /\ \/ \E acc \in Acceptor : ProposerSendAction(acc)
       \/ \E acc \in Acceptor : AcceptorProcessAction(acc)
       \/ LearnerAction
       \/ FakeAcceptorAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

Safety ==
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        <<L1, L2>> \in Ent /\
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] =>
        V1 = V2

THEOREM SafetyResult == Spec => []Safety

=============================================================================
\* Modification History
\* Last modified Thu Aug 25 15:34:46 CEST 2022 by aleph
\* Created Mon Jul 25 14:24:03 CEST 2022 by aleph
