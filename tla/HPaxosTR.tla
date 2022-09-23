------------------------------ MODULE HPaxosTR ------------------------------
EXTENDS Naturals, FiniteSets, Functions

-----------------------------------------------------------------------------
CONSTANT LastBallot
ASSUME LastBallot \in Nat

Ballot == Nat

CONSTANT Value
ASSUME ValueNotEmpty == Value # {}

-----------------------------------------------------------------------------
CONSTANTS SafeAcceptor,
          FakeAcceptor,
          ByzQuorum,
          Learner

Acceptor == SafeAcceptor \cup FakeAcceptor

ASSUME AcceptorAssumption ==
    /\ SafeAcceptor \cap FakeAcceptor = {}
    /\ Acceptor \cap Learner = {}

ASSUME BQAssumption ==
    /\ SafeAcceptor \in ByzQuorum
    /\ \A Q \in ByzQuorum : Q \subseteq Acceptor

-----------------------------------------------------------------------------
(* Learner graph *)

CONSTANT TrustLive
ASSUME TrustLiveAssumption ==
    TrustLive \in SUBSET [lr : Learner, q : ByzQuorum]

CONSTANT TrustSafe
ASSUME TrustSafeAssumption ==
    TrustSafe \in SUBSET [from : Learner, to : Learner, q : ByzQuorum]

ASSUME LearnerGraphAssumptionSymmetry ==
    \A E \in TrustSafe :
        [from |-> E.to, to |-> E.from, q |-> E.q] \in TrustSafe

ASSUME LearnerGraphAssumptionTransitivity ==
    \A E1, E2 \in TrustSafe :
        E1.q = E2.q /\ E1.to = E2.from =>
        [from |-> E1.from, to |-> E2.to, q |-> E1.q] \in TrustSafe

ASSUME LearnerGraphAssumptionClosure ==
    \A E \in TrustSafe : \A Q \in ByzQuorum :
        E.q \subseteq Q =>
        [from |-> E.from, to |-> E.to, q |-> Q] \in TrustSafe

ASSUME LearnerGraphAssumptionValidity ==
    \A E \in TrustSafe : \A Q1, Q2 \in ByzQuorum :
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

RefCardinality == Nat

FINSUBSET(S, R) == { Range(seq) : seq \in [R -> S] }
\*FINSUBSET(S, K) == { Range(seq) : seq \in [1..K -> S] }
\*FINSUBSET(S, R) == UNION { {Range(seq) : seq \in [1..K -> S]} : K \in R }

\* TODO remove 1b, 2a cases
MessageRec0 ==
    [ type : {"1a"}, bal : Ballot, ref : {{}} ] \cup
    [ type : {"1b"}, acc : Acceptor, ref : {{}} ] \cup
    [ type : {"2a"}, lrn : Learner, acc : Acceptor, ref : {{}} ]

MessageRec1(M, n) ==
    M \cup
    [ type : {"1b"},
      acc : Acceptor,
      ref : FINSUBSET(M, RefCardinality) ] \cup
    [ type : {"2a"},
      lrn : Learner,
      acc : Acceptor,
      ref : FINSUBSET(M, RefCardinality) ]

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

MessageDepthRange == Nat

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
\*ASSUME 1aAssumption ==
\*    \A m1, m2 \in Message :
\*        m1.type = "1a" /\ m2.type = "1a" /\ m1.bal = m2.bal =>
\*        m1 = m2

-----------------------------------------------------------------------------
\*None == CHOOSE v : v \notin Value /\ v \notin Message

-----------------------------------------------------------------------------
(* Algorithm specification *)

VARIABLES msgs,
          known_msgs,
          recent_msgs,
          2a_lrn_loop,
          processed_lrns,
          decision,
          BVal \* TODO comment

Get1a(m) ==
    { x \in Tran(m) :
        /\ x.type = "1a"
        /\ \A y \in Tran(m) :
            y.type = "1a" => y.bal <= x.bal }
\* Invariant: x \in Get1a(m) /\ y \in Get1a(m) => x = y
\* TODO: totality for 1b, 2a messages. Required invariant:
\*   each well-formed 1b references a 1a.

B(m, bal) == \E x \in Get1a(m) : bal = x.bal

V(m, val) == \E x \in Get1a(m) : val = BVal[x.bal]

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
CaughtMsg(x) ==
    { m \in Tran(x) :
        /\ m.type # "1a"
        /\ \E m1 \in Tran(x) :
            /\ m1.type # "1a"
            /\ m.acc = m1.acc
            /\ m \notin Tran(m1)
            /\ m1 \notin Tran(m) }

Caught(x) == { m.acc : m \in CaughtMsg(x) }

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
    IN [lr |-> x.lrn, q |-> { m.acc : m \in Q }] \in TrustLive

\* Connected 2a messages
Con2as(l, x) ==
    { m \in Tran(x) :
        /\ m.type = "2a"
        /\ m.acc = x.acc
        /\ ~Buried(m, x)
        /\ m.lrn \in Con(l, x) }

\* Fresh 1b messages
Fresh(l, x) == \* x : 1b
    \A m \in Con2as(l, x) : \A v \in Value : V(x, v) <=> V(m, v)

\* Quorum of messages referenced by 2a
q(x) ==
    LET Q == { m \in Tran(x) :
                /\ m.type = "1b"
                /\ Fresh(x.lrn, m)
                /\ \A b \in Ballot : B(m, b) <=> B(x, b) }
    IN { m.acc : m \in Q }

WellFormed(m) ==
    /\ m \in Message
    /\ m.type = "1b" =>
        \* TODO remove \E r1a part
        /\ \E r1a \in m.ref :
            /\ r1a.type = "1a"
            /\ \A r \in m.ref : r.type = "1a" => r = r1a
\*            /\ r1a.bal = m.bal
\*        /\ \A r \in m.ref : r.bal =< m.bal
\*        /\ \A r1, r2 \in m.ref :
\*            r1.bal = m.bal /\ r2.bal = m.bal => r1 = r2
        \* TODO replace with `<`
        /\ \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y \in Get1a(m)
    /\ m.type = "2a" =>
        /\ [lr |-> m.lrn, q |-> q(m)] \in TrustLive
        \* /\ m.acc \in q(m) \* TODO required for liveness?

vars == << msgs, known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns, decision, BVal >>

Init ==
    /\ msgs = {}
    /\ known_msgs = [x \in Acceptor \cup Learner |-> {}]
    /\ recent_msgs = [a \in Acceptor |-> {}]
    /\ 2a_lrn_loop = [a \in Acceptor |-> FALSE]
    /\ processed_lrns = [a \in Acceptor |-> {}]
    /\ decision = [lb \in Learner \X Ballot |-> {}]
    /\ BVal \in [Ballot -> Value]
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
    /\ Send([type |-> "1a", bal |-> b, ref |-> {}])
    /\ UNCHANGED << known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns, decision >>
    /\ UNCHANGED BVal

Process1a(a, m) ==
    LET new1b == [type |-> "1b", acc |-> a, ref |-> recent_msgs[a] \cup {m}] IN
    /\ Recv(a, m)
    /\ m.type = "1a"
    /\ WellFormed(new1b) =>
        /\ Send(new1b)
        /\ recent_msgs' = [recent_msgs EXCEPT ![a] = {new1b}]
    /\ (~WellFormed(new1b)) =>
        /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
        /\ UNCHANGED msgs
    /\ UNCHANGED << 2a_lrn_loop, processed_lrns, decision >>
    /\ UNCHANGED BVal

Process1b(a, m) ==
    /\ Recv(a, m)
    /\ m.type = "1b"
    /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
    /\ (\A mb, b \in Ballot : MaxBal(a, mb) /\ B(m, b) => mb <= b) =>
        /\ 2a_lrn_loop' = [2a_lrn_loop EXCEPT ![a] = TRUE]
        /\ processed_lrns' = [processed_lrns EXCEPT ![a] = {}]
    /\ (~(\A mb, b \in Ballot : MaxBal(a, mb) /\ B(m, b) => mb <= b)) =>
        UNCHANGED << 2a_lrn_loop, processed_lrns >>
    /\ UNCHANGED << msgs, decision >>
    /\ UNCHANGED BVal

Process1bLearnerLoopStep(a, lrn) ==
    LET new2a == [type |-> "2a", lrn |-> lrn, acc |-> a, ref |-> recent_msgs[a]] IN
    /\ processed_lrns' =
        [processed_lrns EXCEPT ![a] = processed_lrns[a] \cup {lrn}]
    /\ WellFormed(new2a) =>
        /\ Send(new2a)
        /\ recent_msgs' = [recent_msgs EXCEPT ![a] = {new2a}]
    /\ (~WellFormed(new2a)) =>
        UNCHANGED << msgs, recent_msgs >>
    /\ UNCHANGED << known_msgs, 2a_lrn_loop, decision >>
    /\ UNCHANGED BVal

Process1bLearnerLoopDone(a) ==
    /\ Learner \ processed_lrns[a] = {}
    /\ 2a_lrn_loop' = [2a_lrn_loop EXCEPT ![a] = FALSE]
    /\ UNCHANGED << msgs, known_msgs, recent_msgs, processed_lrns, decision >>
    /\ UNCHANGED BVal

Process1bLearnerLoop(a) ==
    \/ \E lrn \in Learner \ processed_lrns[a] :
        Process1bLearnerLoopStep(a, lrn)
    \/ Process1bLearnerLoopDone(a)

Process2a(a, m) ==
    /\ Recv(a, m)
    /\ m.type = "2a"
    /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
    /\ UNCHANGED << msgs, 2a_lrn_loop, processed_lrns, decision >>
    /\ UNCHANGED BVal

ProposerSendAction ==
    \E bal \in Ballot : \E val \in Value :
        Send1a(bal, val)

\* vars == << msgs, known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns, decision >>

AcceptorProcessAction ==
    \E a \in SafeAcceptor:
        \/ /\ 2a_lrn_loop[a] = FALSE
           /\ \E m \in msgs :
                /\ m \notin known_msgs[a]
                /\ \/ Process1a(a, m)
                   \/ Process1b(a, m)
        \/ /\ 2a_lrn_loop[a] = TRUE
           /\ Process1bLearnerLoop(a)

FakeSend(a) ==
    /\ \E m \in { mm \in Message :
                    /\ mm.type \in {"1b", "2a"}
                    /\ mm.acc = a
                    /\ WellFormed(mm)  \* assume that adversaries can send only
                                       \* wellformed messages
                } :
        Send(m)
    /\ UNCHANGED << known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns, decision >>
    /\ UNCHANGED BVal

\*FakeRecv(a) ==
\*    /\ UNCHANGED << msgs >>

LearnerRecv(l) ==
    /\ \E m \in msgs : Recv(l, m)
    /\ UNCHANGED << msgs, recent_msgs, 2a_lrn_loop, processed_lrns, decision >>
    /\ UNCHANGED BVal

ChosenIn(l, b, v) ==
    \E S \in SUBSET { x \in known_msgs[l] :
                            /\ x.type = "2a"
                            /\ x.lrn = l
                            /\ B(x, b)
                            /\ V(x, v) } :
        [lr |-> l, q |-> { m.acc : m \in S }] \in TrustLive

LearnerDecide(l, b, v) ==
    /\ ChosenIn(l, b, v)
    /\ decision' = [decision EXCEPT ![<<l, b>>] = decision[l, b] \cup {v}]
    /\ UNCHANGED << msgs, known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns >>
    /\ UNCHANGED BVal

LearnerAction ==
    \E lrn \in Learner :
        \/ LearnerRecv(lrn)
        \/ \E bal \in Ballot :
           \E val \in Value :
            LearnerDecide(lrn, bal, val)

FakeAcceptorAction == \E a \in FakeAcceptor : FakeSend(a)

\*MessageNumLimit == 10

Next ==
\*    /\ Cardinality(msgs) < MessageNumLimit
    /\ \/ ProposerSendAction
       \/ AcceptorProcessAction
       \/ LearnerAction
       \/ FakeAcceptorAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

SanityCheck0 ==
    \A L \in Learner : Cardinality(known_msgs[L]) = 0

SanityCheck1 ==
    \A L \in Learner : \A m1, m2 \in known_msgs[L] :
    \A b1, b2 \in Ballot :
        B(m1, b1) /\ B(m2, b2) => b1 = b2

2aNotSent ==
    \A M \in msgs : M.type # "2a"

2aNotSentBySafeAcceptor ==
    \A M \in msgs : M.type = "2a" => M.acc \notin SafeAcceptor

1bNotSentBySafeAcceptor ==
    \A M \in msgs : M.type = "1b" => M.acc \notin SafeAcceptor

\*Inv_msgs ==
\*    /\ \A m \in msgs : m \in Message
\*    /\ \A m \in msgs : WellFormed(m)

NoDecision ==
    \A L \in Learner : \A BB \in Ballot : \A VV \in Value :
        VV \notin decision[L, BB]

UniqueDecision ==
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] =>
        V1 = V2

-----------------------------------------------------------------------------

Safety ==
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        <<L1, L2>> \in Ent /\
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] =>
        V1 = V2



THEOREM SafetyResult == Spec => []Safety

=============================================================================
\* Modification History
\* Last modified Fri Sep 23 12:09:47 CEST 2022 by aleph
\* Created Mon Jul 25 14:24:03 CEST 2022 by aleph
