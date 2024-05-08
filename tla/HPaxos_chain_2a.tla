-------------------------- MODULE HPaxos_chain_2a ---------------------------
EXTENDS Naturals, FiniteSets, Functions, TLAPS

-----------------------------------------------------------------------------
CONSTANT LastBallot
ASSUME LastBallot \in Nat

Ballot == Nat

CONSTANT Value
ASSUME ValueNotEmpty == Value # {}

-----------------------------------------------------------------------------
CONSTANTS Proposer,
          SafeAcceptor,
          FakeAcceptor,
          ByzQuorum,
          Learner

Acceptor == SafeAcceptor \cup FakeAcceptor

ASSUME AcceptorAssumption ==
    /\ SafeAcceptor \cap FakeAcceptor = {}
\*    /\ Acceptor \cap Learner = {}

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
ASSUME MaxRefCardinalityAssumption ==
    /\ MaxRefCardinality \in Nat
    /\ MaxRefCardinality >= 1

\*RefCardinality == Nat
RefCardinality == 1..MaxRefCardinality

FINSUBSET(S, R) == { Range(seq) : seq \in [R -> S] }
\*FINSUBSET(S, K) == { Range(seq) : seq \in [1..K -> S] }
\*FINSUBSET(S, R) == UNION { {Range(seq) : seq \in [1..K -> S]} : K \in R }

-----------------------------------------------------------------------------
(* Non-message value *)
NoMessage == [ type |-> "null" ]

MessageRec0 ==
    [ type : {"1a"}, bal : Ballot, prev : {NoMessage}, ref : {{}} ]

MessageRec1(M, n) ==
    M \cup
    [ type : {"1b"},
      acc : Acceptor,
      prev : M \cup {NoMessage},
      ref : FINSUBSET(M, RefCardinality) ] \cup
    [ type : {"2a"},
      lrn : SUBSET Learner,
      acc : Acceptor,
      prev : M \cup {NoMessage},
      ref : FINSUBSET(M, RefCardinality) ]

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

TranBound[n \in Nat] ==
    IF n = 0
    THEN TranBound0
    ELSE TranBound1(TranBound[n-1], n)

\* Countable transitive references
TranDepthRange == MessageDepthRange

Tran(m) == UNION {TranBound[n][m] : n \in TranDepthRange}

-----------------------------------------------------------------------------
(* Transitive references of prev *)

\* Bounded transitive references of prev
PrevTranBound0 == [m \in Message |-> {m}]
PrevTranBound1(tr, n) ==
    [m \in Message |-> {m} \cup IF m.prev = NoMessage THEN {} ELSE tr[m.prev]]

PrevTranBound[n \in Nat] ==
    IF n = 0
    THEN PrevTranBound0
    ELSE PrevTranBound1(PrevTranBound[n-1], n)

\* Countable transitive references of prev
PrevTranDepthRange == MessageDepthRange

PrevTran(m) == UNION {PrevTranBound[n][m] : n \in PrevTranDepthRange}

-----------------------------------------------------------------------------
(* Algorithm specification *)

(****************************************************************************
--algorithm HPaxos2 {
  variables msgs = {},
          known_msgs = [x \in Acceptor \cup Learner |-> {}],
          recent_msgs = [a \in Acceptor \cup Learner |-> {}],
          prev_msg = [a \in Acceptor |-> NoMessage],
          decision = [lb \in Learner \X Ballot |-> {}],
          BVal \in [Ballot -> Value];

  define {
    Get1a(m) ==
        { x \in Tran(m) :
            /\ x.type = "1a"
            /\ \A y \in Tran(m) :
                y.type = "1a" => y.bal <= x.bal }

    B(m, bal) == \E x \in Get1a(m) : bal = x.bal

    V(m, val) == \E x \in Get1a(m) : val = BVal[x.bal]

    SameBallot(x, y) ==
        \A b \in Ballot : B(x, b) <=> B(y, b)

    \* Maximal ballot number of any messages known to acceptor a
    MaxBal(a, mbal) ==
        /\ \E m \in known_msgs[a] : B(m, mbal)
        /\ \A x \in known_msgs[a] :
            \A b \in Ballot : B(x, b) => b =< mbal

    KnownRefs(a, m) == \A r \in m.ref : r \in known_msgs[a]

    \* The acceptor is _caught_ in a message x if the transitive references of x
    \* include evidence such as two different messages both signed by the acceptor,
    \* which have equal previous messges.
    CaughtMsg(x) ==
        { m \in Tran(x) :
            /\ m.type # "1a"
            /\ \E m1 \in Tran(x) :
                /\ m1.type # "1a"
                /\ m.acc = m1.acc
                /\ m # m1
                /\ m \notin PrevTran(m1)
                /\ m1 \notin PrevTran(m) }

    Caught(x) == { m.acc : m \in CaughtMsg(x) }

    CaughtMsg0(x) ==
        { m \in Tran(x) :
            /\ m.type # "1a"
            /\ \E m1 \in Tran(x) :
                /\ m1.type # "1a"
                /\ m.acc = m1.acc
                /\ m # m1
                /\ m.prev = m1.prev }

    Caught0(x) == { m.acc : m \in CaughtMsg0(x) }

    \* Connected
    ConByQuorum(a, b, x, S) == \* a : Learner, b : Learner, x : 1b, S \in ByzQuorum
        /\ [from |-> a, to |-> b, q |-> S] \in TrustSafe
        /\ S \cap Caught(x) = {}

    Con(a, x) == \* a : Learner, x : 1b
        { b \in Learner :
            \E S \in ByzQuorum : ConByQuorum(a, b, x, S) }

    \* 2a-message is _buried_ if there exists a quorum of acceptors that have seen
    \* 2a-messages with different values, the same learner, and higher ballot
    \* numbers.
    Buried(a, x, y) == \* x : 2a, y : 1b
        LET Q == { m \in Tran(y) :
                    \E z \in Tran(m) :
                        /\ z.type = "2a"
                        /\ a \in z.lrn
                        /\ \A bx, bz \in Ballot :
                            B(x, bx) /\ B(z, bz) => bx < bz
                        /\ \A vx, vz \in Value :
                            V(x, vx) /\ V(z, vz) => vx # vz }
        IN [lr |-> a, q |-> { m.acc : m \in Q }] \in TrustLive

    \* Connected 2a messages and learners
    Con2as(l, x) == \* l : Learner, x : 1b
        { m \in Tran(x) :
            /\ m.type = "2a"
            /\ m.acc = x.acc
            /\ \E a \in Learner :
                /\ a \in m.lrn
                /\ ~Buried(a, m, x)
                /\ a \in Con(l, x) }

    \* Fresh 1b messages
    Fresh(l, x) == \* l : Learner, x : 1b
        \A m \in Con2as(l, x) : \A v \in Value : V(x, v) <=> V(m, v)

    \* Quorum of messages referenced by 2a for a learner instance
    q(l, x) == \* x : 2a
        LET Q == { m \in Tran(x) :
                    /\ m.type = "1b"
                    /\ Fresh(l, m)
                    /\ \A b \in Ballot : B(m, b) <=> B(x, b) }
        IN { m.acc : m \in Q }

    UpToDate(a, m) ==
        \A mb, b \in Ballot : MaxBal(a, mb) /\ B(m, b) => mb <= b

    ChainRef(m) == \A r \in m.ref : r.acc = m.acc <=> r = m.prev

    WellFormed(m) ==
        /\ m \in Message
        /\ \E b \in Ballot : B(m, b) \* TODO prove it
        /\ ChainRef(m)
        /\ m.type = "1b" =>
            /\ m.ref # {}
            /\ (m.prev = NoMessage \/ m.prev \in m.ref)
            /\ \A y \in Tran(m) :
                m # y /\ SameBallot(m, y) => y.type = "1a"
        /\ m.type = "2a" =>
            /\ m.ref # {}
            /\ (m.prev = NoMessage \/ m.prev \in m.ref)
            /\ m.lrn = { l \in Learner : [lr |-> l, q |-> q(l, m)] \in TrustLive }

    Known2a(l, b, v) ==
        { x \in known_msgs[l] :
            /\ x.type = "2a"
            /\ l \in x.lrn
            /\ B(x, b)
            /\ V(x, v) }

    ChosenIn(l, b, v) ==
        \E S \in SUBSET Known2a(l, b, v) :
            [lr |-> l, q |-> { m.acc : m \in S }] \in TrustLive
  }

  macro Send(m) { msgs := msgs \cup {m} }

  macro Send1a(b) {
    Send([type |-> "1a", bal |-> b, prev |-> NoMessage, ref |-> {}])
  }

  macro Recv(m) {
    when /\ m \notin known_msgs[self]
         /\ KnownRefs(self, m) ;
    known_msgs[self] := known_msgs[self] \cup {m}
  }

  macro ProposerSendAction(b) { Send1a(b) }

  macro Process1a(m) {
    when m.type = "1a" ;
    with (new1b = [type |-> "1b",
                   acc |-> self,
                   prev |-> prev_msg[self],
                   ref |-> recent_msgs[self] \cup {m}])
    {
      either {
        when WellFormed(new1b) ;
        prev_msg[self] := new1b ;
        recent_msgs[self] := {new1b} ;
        Send(new1b)
      }
      or {
        when ~WellFormed(new1b) ;
        recent_msgs[self] := recent_msgs[self] \cup {m}
      }
    }
  }

  macro Process1b(m) {
    when m.type = "1b" ;
    either {
      when UpToDate(self, m) ;
      with (LL \in SUBSET Learner,
            new2a = [type |-> "2a",
                     lrn |-> LL,
                     acc |-> self,
                     prev |-> prev_msg[self],
                     ref |-> recent_msgs[self] \cup {m}])
      {
        when WellFormed(new2a) ;
        prev_msg[self] := new2a ;
        recent_msgs[self] := {new2a} ;
        Send(new2a)
      }
    }
    or {
      when ~UpToDate(self, m) ;
      recent_msgs[self] := recent_msgs[self] \cup {m}
    }
  }

  macro Process2a(m) {
    when m.type = "2a" ;
    recent_msgs[self] := recent_msgs[self] \cup {m}
  }

  macro FakeSend1b() {
    with (fin \in FINSUBSET(msgs, RefCardinality),
          new1b = [type |-> "1b", acc |-> self, ref |-> fin])
    {
      when WellFormed(new1b) ;
      Send(new1b)
    }
  }

  macro FakeSend2a() {
    with (fin \in FINSUBSET(msgs, RefCardinality),
          LL \in SUBSET Learner,
          new2a = [type |-> "2a", lrn |-> LL, acc |-> self, ref |-> fin])
    {
      when WellFormed(new2a) ;
      Send(new2a)
    }
  }

  macro LearnerRecv(m) {
    when WellFormed(m) ;
    Recv(m)
  }

  macro LearnerDecide(b, v) {
    when ChosenIn(self, b, v) ;
    decision[<<self, b>>] := decision[self, b] \cup {v}
  }

  process (proposer \in Proposer) {
    proposer: while (TRUE) {
      with (b \in Ballot) { ProposerSendAction(b) }
    }
  }

  process (safe_acceptor \in SafeAcceptor) {
    safe: while (TRUE) {
      with (m \in msgs) {
        Recv(m) ;
        when WellFormed(m) ;
        either Process1a(m)
        or     Process1b(m)
        or     Process2a(m)
      }
    }
  }

  process (learner \in Learner) {
    learner: while (TRUE) {
      either with (m \in msgs) LearnerRecv(m)
      or     with (b \in Ballot, v \in Value) LearnerDecide(b, v)
    }
  }

  process (fake_acceptor \in FakeAcceptor) {
    fake: while (TRUE) {
      either FakeSend1b()
      or     FakeSend2a()
    }
  }
}

****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "ba2ddcc6" /\ chksum(tla) = "f7efc146")
\* Label proposer of process proposer at line 375 col 15 changed to proposer_
\* Label learner of process learner at line 393 col 14 changed to learner_
VARIABLES msgs, known_msgs, recent_msgs, prev_msg, decision, BVal

(* define statement *)
Get1a(m) ==
    { x \in Tran(m) :
        /\ x.type = "1a"
        /\ \A y \in Tran(m) :
            y.type = "1a" => y.bal <= x.bal }

B(m, bal) == \E x \in Get1a(m) : bal = x.bal

V(m, val) == \E x \in Get1a(m) : val = BVal[x.bal]

SameBallot(x, y) ==
    \A b \in Ballot : B(x, b) <=> B(y, b)


MaxBal(a, mbal) ==
    /\ \E m \in known_msgs[a] : B(m, mbal)
    /\ \A x \in known_msgs[a] :
        \A b \in Ballot : B(x, b) => b =< mbal

KnownRefs(a, m) == \A r \in m.ref : r \in known_msgs[a]




CaughtMsg(x) ==
    { m \in Tran(x) :
        /\ m.type # "1a"
        /\ \E m1 \in Tran(x) :
            /\ m1.type # "1a"
            /\ m.acc = m1.acc
            /\ m # m1
            /\ m \notin PrevTran(m1)
            /\ m1 \notin PrevTran(m) }

Caught(x) == { m.acc : m \in CaughtMsg(x) }

CaughtMsg0(x) ==
    { m \in Tran(x) :
        /\ m.type # "1a"
        /\ \E m1 \in Tran(x) :
            /\ m1.type # "1a"
            /\ m.acc = m1.acc
            /\ m # m1
            /\ m.prev = m1.prev }

Caught0(x) == { m.acc : m \in CaughtMsg0(x) }


ConByQuorum(a, b, x, S) ==
    /\ [from |-> a, to |-> b, q |-> S] \in TrustSafe
    /\ S \cap Caught(x) = {}

Con(a, x) ==
    { b \in Learner :
        \E S \in ByzQuorum : ConByQuorum(a, b, x, S) }




Buried(a, x, y) ==
    LET Q == { m \in Tran(y) :
                \E z \in Tran(m) :
                    /\ z.type = "2a"
                    /\ a \in z.lrn
                    /\ \A bx, bz \in Ballot :
                        B(x, bx) /\ B(z, bz) => bx < bz
                    /\ \A vx, vz \in Value :
                        V(x, vx) /\ V(z, vz) => vx # vz }
    IN [lr |-> a, q |-> { m.acc : m \in Q }] \in TrustLive


Con2as(l, x) ==
    { m \in Tran(x) :
        /\ m.type = "2a"
        /\ m.acc = x.acc
        /\ \E a \in Learner :
            /\ a \in m.lrn
            /\ ~Buried(a, m, x)
            /\ a \in Con(l, x) }


Fresh(l, x) ==
    \A m \in Con2as(l, x) : \A v \in Value : V(x, v) <=> V(m, v)


q(l, x) ==
    LET Q == { m \in Tran(x) :
                /\ m.type = "1b"
                /\ Fresh(l, m)
                /\ \A b \in Ballot : B(m, b) <=> B(x, b) }
    IN { m.acc : m \in Q }

UpToDate(a, m) ==
    \A mb, b \in Ballot : MaxBal(a, mb) /\ B(m, b) => mb <= b

ChainRef(m) == \A r \in m.ref : r.acc = m.acc <=> r = m.prev

WellFormed(m) ==
    /\ m \in Message
    /\ \E b \in Ballot : B(m, b)
    /\ ChainRef(m)
    /\ m.type = "1b" =>
        /\ m.ref # {}
        /\ (m.prev = NoMessage \/ m.prev \in m.ref)
        /\ \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y.type = "1a"
    /\ m.type = "2a" =>
        /\ m.ref # {}
        /\ (m.prev = NoMessage \/ m.prev \in m.ref)
        /\ m.lrn = { l \in Learner : [lr |-> l, q |-> q(l, m)] \in TrustLive }

Known2a(l, b, v) ==
    { x \in known_msgs[l] :
        /\ x.type = "2a"
        /\ l \in x.lrn
        /\ B(x, b)
        /\ V(x, v) }

ChosenIn(l, b, v) ==
    \E S \in SUBSET Known2a(l, b, v) :
        [lr |-> l, q |-> { m.acc : m \in S }] \in TrustLive


vars == << msgs, known_msgs, recent_msgs, prev_msg, decision, BVal >>

ProcSet == (Proposer) \cup (SafeAcceptor) \cup (Learner) \cup (FakeAcceptor)

Init == (* Global variables *)
        /\ msgs = {}
        /\ known_msgs = [x \in Acceptor \cup Learner |-> {}]
        /\ recent_msgs = [a \in Acceptor \cup Learner |-> {}]
        /\ prev_msg = [a \in Acceptor |-> NoMessage]
        /\ decision = [lb \in Learner \X Ballot |-> {}]
        /\ BVal \in [Ballot -> Value]

proposer(self) == /\ \E b \in Ballot:
                       msgs' = (msgs \cup {([type |-> "1a", bal |-> b, prev |-> NoMessage, ref |-> {}])})
                  /\ UNCHANGED << known_msgs, recent_msgs, prev_msg, decision, 
                                  BVal >>

safe_acceptor(self) == /\ \E m \in msgs:
                            /\ /\ m \notin known_msgs[self]
                               /\ KnownRefs(self, m)
                            /\ known_msgs' = [known_msgs EXCEPT ![self] = known_msgs[self] \cup {m}]
                            /\ WellFormed(m)
                            /\ \/ /\ m.type = "1a"
                                  /\ LET new1b == [type |-> "1b",
                                                   acc |-> self,
                                                   prev |-> prev_msg[self],
                                                   ref |-> recent_msgs[self] \cup {m}] IN
                                       \/ /\ WellFormed(new1b)
                                          /\ prev_msg' = [prev_msg EXCEPT ![self] = new1b]
                                          /\ recent_msgs' = [recent_msgs EXCEPT ![self] = {new1b}]
                                          /\ msgs' = (msgs \cup {new1b})
                                       \/ /\ ~WellFormed(new1b)
                                          /\ recent_msgs' = [recent_msgs EXCEPT ![self] = recent_msgs[self] \cup {m}]
                                          /\ UNCHANGED <<msgs, prev_msg>>
                               \/ /\ m.type = "1b"
                                  /\ \/ /\ UpToDate(self, m)
                                        /\ \E LL \in SUBSET Learner:
                                             LET new2a == [type |-> "2a",
                                                           lrn |-> LL,
                                                           acc |-> self,
                                                           prev |-> prev_msg[self],
                                                           ref |-> recent_msgs[self] \cup {m}] IN
                                               /\ WellFormed(new2a)
                                               /\ prev_msg' = [prev_msg EXCEPT ![self] = new2a]
                                               /\ recent_msgs' = [recent_msgs EXCEPT ![self] = {new2a}]
                                               /\ msgs' = (msgs \cup {new2a})
                                     \/ /\ ~UpToDate(self, m)
                                        /\ recent_msgs' = [recent_msgs EXCEPT ![self] = recent_msgs[self] \cup {m}]
                                        /\ UNCHANGED <<msgs, prev_msg>>
                               \/ /\ m.type = "2a"
                                  /\ recent_msgs' = [recent_msgs EXCEPT ![self] = recent_msgs[self] \cup {m}]
                                  /\ UNCHANGED <<msgs, prev_msg>>
                       /\ UNCHANGED << decision, BVal >>

learner(self) == /\ \/ /\ \E m \in msgs:
                            /\ WellFormed(m)
                            /\ /\ m \notin known_msgs[self]
                               /\ KnownRefs(self, m)
                            /\ known_msgs' = [known_msgs EXCEPT ![self] = known_msgs[self] \cup {m}]
                       /\ UNCHANGED decision
                    \/ /\ \E b \in Ballot:
                            \E v \in Value:
                              /\ ChosenIn(self, b, v)
                              /\ decision' = [decision EXCEPT ![<<self, b>>] = decision[self, b] \cup {v}]
                       /\ UNCHANGED known_msgs
                 /\ UNCHANGED << msgs, recent_msgs, prev_msg, BVal >>

fake_acceptor(self) == /\ \/ /\ \E fin \in FINSUBSET(msgs, RefCardinality):
                                  LET new1b == [type |-> "1b", acc |-> self, ref |-> fin] IN
                                    /\ WellFormed(new1b)
                                    /\ msgs' = (msgs \cup {new1b})
                          \/ /\ \E fin \in FINSUBSET(msgs, RefCardinality):
                                  \E LL \in SUBSET Learner:
                                    LET new2a == [type |-> "2a", lrn |-> LL, acc |-> self, ref |-> fin] IN
                                      /\ WellFormed(new2a)
                                      /\ msgs' = (msgs \cup {new2a})
                       /\ UNCHANGED << known_msgs, recent_msgs, prev_msg, 
                                       decision, BVal >>

Next == (\E self \in Proposer: proposer(self))
           \/ (\E self \in SafeAcceptor: safe_acceptor(self))
           \/ (\E self \in Learner: learner(self))
           \/ (\E self \in FakeAcceptor: fake_acceptor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

Send(m) == msgs' = msgs \cup {m}

Recv(a, m) ==
    /\ m \notin known_msgs[a] \* ignore known messages
    /\ KnownRefs(a, m)
    /\ known_msgs' = [known_msgs EXCEPT ![a] = known_msgs[a] \cup {m}]

Send1a(b) ==
    /\ Send([type |-> "1a", bal |-> b, prev |-> NoMessage, ref |-> {}])
    /\ UNCHANGED << known_msgs, recent_msgs, prev_msg >>
    /\ UNCHANGED decision
    /\ UNCHANGED BVal

Process1a(a, m) ==
    LET new1b == [type |-> "1b", acc |-> a,
                  prev |-> prev_msg[a],
                  ref |-> recent_msgs[a] \cup {m}] IN
    /\ m.type = "1a"
    /\ Recv(a, m)
    /\ WellFormed(m)
    /\ WellFormed(new1b) =>
        /\ Send(new1b)
        /\ recent_msgs' = [recent_msgs EXCEPT ![a] = {new1b}]
        /\ prev_msg' = [prev_msg EXCEPT ![a] = new1b]
    /\ (~WellFormed(new1b)) =>
        /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
        /\ UNCHANGED << msgs, prev_msg >>
    /\ UNCHANGED decision
    /\ UNCHANGED BVal

Process1b(a, m) ==
    /\ m.type = "1b"
    /\ Recv(a, m)
    /\ WellFormed(m)
    /\ UpToDate(a, m) =>
        \E LL \in SUBSET Learner :
            LET new2a == [type |-> "2a", lrn |-> LL, acc |-> a,
                          prev |-> prev_msg[a],
                          ref |-> recent_msgs[a] \cup {m}] IN
            /\ WellFormed(new2a)
            /\ Send(new2a)
            /\ recent_msgs' = [recent_msgs EXCEPT ![a] = {new2a}]
            /\ prev_msg' = [prev_msg EXCEPT ![a] = new2a]
    /\ (~UpToDate(a, m)) =>
        /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
        /\ UNCHANGED << msgs, prev_msg >>
    /\ UNCHANGED decision
    /\ UNCHANGED BVal

Process2a(a, m) ==
    /\ m.type = "2a"
    /\ Recv(a, m)
    /\ WellFormed(m)
    /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
    /\ UNCHANGED << msgs, prev_msg >>
    /\ UNCHANGED decision
    /\ UNCHANGED BVal

ProposerSendAction(p) ==
    \E bal \in Ballot : Send1a(bal)

AcceptorProcessAction(a) ==
        \E m \in msgs :
            \/ Process1a(a, m)
            \/ Process1b(a, m)
            \/ Process2a(a, m)

FakeSend1b(a) ==
    /\ \E fin \in FINSUBSET(msgs, RefCardinality) :
        LET new1b == [type |-> "1b", acc |-> a, ref |-> fin] IN
        /\ WellFormed(new1b)
        /\ Send(new1b)
    /\ UNCHANGED << known_msgs, recent_msgs, prev_msg >>
    /\ UNCHANGED decision
    /\ UNCHANGED BVal

FakeSend2a(a) ==
    /\ \E fin \in FINSUBSET(msgs, RefCardinality) :
        \E LL \in SUBSET Learner :
            LET new2a == [type |-> "2a", lrn |-> LL, acc |-> a, ref |-> fin] IN
            /\ WellFormed(new2a)
            /\ Send(new2a)
    /\ UNCHANGED << known_msgs, recent_msgs, prev_msg  >>
    /\ UNCHANGED decision
    /\ UNCHANGED BVal

LearnerRecv(l, m) ==
    /\ Recv(l, m)
    /\ WellFormed(m)
    /\ UNCHANGED << msgs, recent_msgs, prev_msg >>
    /\ UNCHANGED decision
    /\ UNCHANGED BVal

LearnerDecide(l, b, v) ==
    /\ ChosenIn(l, b, v)
    /\ decision' = [decision EXCEPT ![<<l, b>>] = decision[l, b] \cup {v}]
    /\ UNCHANGED << msgs, known_msgs, recent_msgs, prev_msg >>
    /\ UNCHANGED BVal

LearnerAction(lrn) ==
    \/ \E m \in msgs :
        LearnerRecv(lrn, m)
    \/ \E bal \in Ballot :
        \E val \in Value :
            LearnerDecide(lrn, bal, val)

FakeAcceptorAction(a) ==
    \/ FakeSend1b(a)
    \/ FakeSend2a(a)

NextTLA ==
    \/ \E p \in Proposer :
        ProposerSendAction(p)
    \/ \E acc \in SafeAcceptor :
        AcceptorProcessAction(acc)
    \/ \E lrn \in Learner :
        LearnerAction(lrn)
    \/ \E acc \in FakeAcceptor :
        FakeAcceptorAction(acc)

THEOREM NextDef == (Next <=> NextTLA)
<1>1. ASSUME NEW self \in Proposer
      PROVE proposer(self) <=> ProposerSendAction(self)
      BY DEF proposer, ProposerSendAction, Send1a, Send
<1>2. ASSUME NEW self \in SafeAcceptor
      PROVE safe_acceptor(self) <=> AcceptorProcessAction(self)
      BY Zenon DEF safe_acceptor, AcceptorProcessAction, Process1a, Process1b, Process2a, Recv, Send
<1>3. ASSUME NEW self \in Learner
      PROVE learner(self) <=> LearnerAction(self)
      BY Zenon DEF learner, LearnerAction, LearnerRecv, LearnerDecide, Recv
<1>4. ASSUME NEW self \in FakeAcceptor
      PROVE fake_acceptor(self) <=> FakeAcceptorAction(self)
      BY Zenon DEF fake_acceptor, FakeAcceptorAction, FakeSend1b, FakeSend2a, Send
<1>5. QED BY <1>1, <1>2, <1>3, <1>4 DEF Next, NextTLA

-----------------------------------------------------------------------------
Safety ==
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        <<L1, L2>> \in Ent /\
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] =>
        V1 = V2

\* THEOREM SafetyResult == Spec => []Safety

-----------------------------------------------------------------------------
(* Sanity check propositions *)

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

NoDecision ==
    \A L \in Learner : \A BB \in Ballot : \A VV \in Value :
        VV \notin decision[L, BB]

UniqueDecision ==
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] =>
        V1 = V2

=============================================================================
\* Modification History
\* Last modified Wed May 08 14:16:22 CEST 2024 by karbyshev
\* Created Mon Jun 19 12:24:03 CEST 2022 by karbyshev
