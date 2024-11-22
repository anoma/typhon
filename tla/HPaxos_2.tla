----------------------------- MODULE HPaxos_2 -------------------------------
EXTENDS HQuorum, HLearnerGraph, HMessage, TLAPS

Assert(P, str) == P

CONSTANT WellFormed2a(_)

-----------------------------------------------------------------------------
(* Algorithm specification *)

(****************************************************************************
--algorithm HPaxos2 {
  variables msgs = {},
            known_msgs = [x \in Acceptor \cup Learner |-> {}],
            recent_msgs = [a \in Acceptor |-> {}],
            prev_msg = [a \in Acceptor |-> NoMessage],
            decision = [lb \in Learner \X Ballot |-> {}],
            BVal \in [Ballot -> Value];

  define {
    Get1a(m) ==
        { x \in Tran(m) :
            /\ OneA(x)
            /\ \A y \in Tran(m) :
                OneA(y) => y.bal <= x.bal }

    B(m, bal) == \E x \in Get1a(m) : bal = x.bal

    V(m, val) == \E x \in Get1a(m) : val = BVal[x.bal]

    SameBallot(x, y) ==
        \A b \in Ballot : B(x, b) <=> B(y, b)

\*    \* Maximal ballot number of any messages known to acceptor a
\*    MaxBal(a, mbal) ==
\*        /\ \E m \in known_msgs[a] : B(m, mbal)
\*        /\ \A x \in known_msgs[a] :
\*            \A b \in Ballot : B(x, b) => b =< mbal

    KnownRefs(a, m) == \A r \in m.refs : r \in known_msgs[a]

    \* The acceptor is _caught_ in a message x if the transitive references of x
    \* include evidence such as two different messages both signed by the acceptor,
    \* which have equal previous messages.
    CaughtMsg(x) ==
        { m \in Tran(x) :
            /\ m.type = "acceptor"
            /\ \E m1 \in Tran(x) :
                /\ m1.type = "acceptor"
                /\ m.acc = m1.acc
                /\ m # m1
                /\ m \notin PrevTran(m1)
                /\ m1 \notin PrevTran(m) }

    Caught(x) == { m.acc : m \in CaughtMsg(x) }

    CaughtMsg0(x) ==
        { m \in Tran(x) :
            /\ m.type = "acceptor"
            /\ \E m1 \in Tran(x) :
                /\ m1.type = "acceptor"
                /\ m.acc = m1.acc
                /\ m # m1
                /\ m.prev = m1.prev }

    Caught0(x) == { m.acc : m \in CaughtMsg0(x) }

    \* Connected
    ConByQuorum(alpha, beta, x, S) == \* alpha : Learner, beta : Learner, x : 1b, S \in ByzQuorum
        /\ [from |-> alpha, to |-> beta, q |-> S] \in TrustSafe
        /\ S \cap Caught(x) = {}

    Con(alpha, x) == \* alpha : Learner, x : 1b
        { beta \in Learner :
            \E S \in ByzQuorum : ConByQuorum(alpha, beta, x, S) }

    \* 2a-message is _buried_ if there exists another 2a-messages with
    \* a higher ballot number, a different value, and related to the
    \* given learner value.
    Buried(alpha, x, y) == \* x : 2a, y : 1b
        \E z \in Tran(y) :
            /\ TwoA(z)
            /\ alpha \in z.lrns
            /\ \A bx, bz \in Ballot :
                B(x, bx) /\ B(z, bz) => bx < bz
            /\ \A vx, vz \in Value :
                V(x, vx) /\ V(z, vz) => vx # vz

    \* Connected 2a messages and learners
    Con2as(alpha, x) == \* alpha : Learner, x : 1b
        { m \in Tran(x) :
            /\ TwoA(m)
            /\ m.acc = x.acc
            /\ \E beta \in m.lrns :
                /\ beta \in Con(alpha, x)
                /\ ~Buried(beta, m, x) }

    \* Fresh 1b messages
    Fresh(alpha, x) == \* alpha : Learner, x : 1b
        \A m \in Con2as(alpha, x) : \A v \in Value : V(x, v) <=> V(m, v)

    \* Quorum of messages referenced by 2a for a learner instance
    q(alpha, x) == \* x : 2a
        LET Q == { m \in Tran(x) :
                    /\ OneB(m)
                    /\ Fresh(alpha, m)
                    /\ \A b \in Ballot : B(m, b) <=> B(x, b) }
        IN { m.acc : m \in Q }

    ChainRef(m) ==
        \/ m.prev = NoMessage
        \/ m.prev \in m.refs /\ m.prev.acc = m.acc

    WellFormed1b(m) ==
        \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y.type = "proposer"

    WellFormed(m) ==
        /\ m \in Message
        /\ \E b \in Ballot : B(m, b) \* TODO prove it
        /\ ChainRef(m)
        /\ OneB(m) => WellFormed1b(m)
        /\ TwoA(m) =>
            /\ m.refs # {}
            \* Since the message structure embodies the learner values in our formalization,
            \* we must validate the correctness of these values.
            /\ m.lrns = { l \in Learner : [lr |-> l, q |-> q(l, m)] \in TrustLive }
            /\ WellFormed2a(m)

    Known2a(alpha, b, v) ==
        { x \in known_msgs[alpha] :
            /\ TwoA(x)
            /\ alpha \in x.lrns
            /\ B(x, b)
            /\ V(x, v) }

    ChosenIn(alpha, b, v) ==
        \E S \in SUBSET Known2a(alpha, b, v) :
            [lr |-> alpha, q |-> { m.acc : m \in S }] \in TrustLive
  }

  macro Send(m) { msgs := msgs \cup {m} }

  macro SendProposal(b) {
    Send([type |-> "proposer", bal |-> b, prev |-> NoMessage, refs |-> {}])
  }

  macro Receive(m) {
    when /\ m \notin known_msgs[self]
         /\ KnownRefs(self, m) ;
    known_msgs[self] := known_msgs[self] \cup {m}
  }

  macro Process(m) {
    with (LL \in SUBSET Learner,
          new = [type |-> "acceptor",
                 acc |-> self,
                 prev |-> prev_msg[self],
                 refs |-> recent_msgs[self] \cup {m},
                 lrns |-> LL])
    {
      assert new \in Message ;
      either {
        when WellFormed(new) ;
        prev_msg[self] := new ;
        recent_msgs[self] := {new} ;
        Send(new)
      }
      or {
        when ~WellFormed(new) ;
        when ~OneA(m) ;
        recent_msgs[self] := recent_msgs[self] \cup {m}
      }
    }
  }

  macro FakeSendControlMessage() {
    with (fin \in FINSUBSET(msgs, RefCardinality),
          LL \in SUBSET Learner,
          msg = [type |-> "acceptor", acc |-> self, refs |-> fin, lrns |-> LL])
    {
      when WellFormed(msg) ;
      Send(msg)
    }
  }

  macro LearnerReceive(m) {
    when WellFormed(m) ;
    Receive(m)
  }

  macro LearnerDecide(b, v) {
    when ChosenIn(self, b, v) ;
    decision[<<self, b>>] := decision[self, b] \cup {v}
  }

  process (proposer \in Proposer) {
    propose: while (TRUE) {
      with (b \in Ballot) { SendProposal(b) }
    }
  }

  process (safe_acceptor \in SafeAcceptor) {
    safe: while (TRUE) {
      with (m \in msgs) {
        Receive(m) ;
        when WellFormed(m) ;
        Process(m)
      }
    }
  }

  process (learner \in Learner) {
    learn: while (TRUE) {
      either with (m \in msgs) LearnerReceive(m)
      or     with (b \in Ballot, v \in Value) LearnerDecide(b, v)
    }
  }

  process (fake_acceptor \in FakeAcceptor) {
    fake: while (TRUE) {
      FakeSendControlMessage()
    }
  }
}

****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "71812e9f" /\ chksum(tla) = "f217c7c2")
VARIABLES msgs, known_msgs, recent_msgs, prev_msg, decision, BVal

(* define statement *)
Get1a(m) ==
    { x \in Tran(m) :
        /\ OneA(x)
        /\ \A y \in Tran(m) :
            OneA(y) => y.bal <= x.bal }

B(m, bal) == \E x \in Get1a(m) : bal = x.bal

V(m, val) == \E x \in Get1a(m) : val = BVal[x.bal]

SameBallot(x, y) ==
    \A b \in Ballot : B(x, b) <=> B(y, b)







KnownRefs(a, m) == \A r \in m.refs : r \in known_msgs[a]




CaughtMsg(x) ==
    { m \in Tran(x) :
        /\ m.type = "acceptor"
        /\ \E m1 \in Tran(x) :
            /\ m1.type = "acceptor"
            /\ m.acc = m1.acc
            /\ m # m1
            /\ m \notin PrevTran(m1)
            /\ m1 \notin PrevTran(m) }

Caught(x) == { m.acc : m \in CaughtMsg(x) }

CaughtMsg0(x) ==
    { m \in Tran(x) :
        /\ m.type = "acceptor"
        /\ \E m1 \in Tran(x) :
            /\ m1.type = "acceptor"
            /\ m.acc = m1.acc
            /\ m # m1
            /\ m.prev = m1.prev }

Caught0(x) == { m.acc : m \in CaughtMsg0(x) }


ConByQuorum(alpha, beta, x, S) ==
    /\ [from |-> alpha, to |-> beta, q |-> S] \in TrustSafe
    /\ S \cap Caught(x) = {}

Con(alpha, x) ==
    { beta \in Learner :
        \E S \in ByzQuorum : ConByQuorum(alpha, beta, x, S) }




Buried(alpha, x, y) ==
    \E z \in Tran(y) :
        /\ TwoA(z)
        /\ alpha \in z.lrns
        /\ \A bx, bz \in Ballot :
            B(x, bx) /\ B(z, bz) => bx < bz
        /\ \A vx, vz \in Value :
            V(x, vx) /\ V(z, vz) => vx # vz


Con2as(alpha, x) ==
    { m \in Tran(x) :
        /\ TwoA(m)
        /\ m.acc = x.acc
        /\ \E beta \in m.lrns :
            /\ beta \in Con(alpha, x)
            /\ ~Buried(beta, m, x) }


Fresh(alpha, x) ==
    \A m \in Con2as(alpha, x) : \A v \in Value : V(x, v) <=> V(m, v)


q(alpha, x) ==
    LET Q == { m \in Tran(x) :
                /\ OneB(m)
                /\ Fresh(alpha, m)
                /\ \A b \in Ballot : B(m, b) <=> B(x, b) }
    IN { m.acc : m \in Q }

ChainRef(m) ==
    \/ m.prev = NoMessage
    \/ m.prev \in m.refs /\ m.prev.acc = m.acc

WellFormed1b(m) ==
    \A y \in Tran(m) :
        m # y /\ SameBallot(m, y) => y.type = "proposer"

WellFormed(m) ==
    /\ m \in Message
    /\ \E b \in Ballot : B(m, b)
    /\ ChainRef(m)
    /\ OneB(m) => WellFormed1b(m)
    /\ TwoA(m) =>
        /\ m.refs # {}


        /\ m.lrns = { l \in Learner : [lr |-> l, q |-> q(l, m)] \in TrustLive }
        /\ WellFormed2a(m)

Known2a(alpha, b, v) ==
    { x \in known_msgs[alpha] :
        /\ TwoA(x)
        /\ alpha \in x.lrns
        /\ B(x, b)
        /\ V(x, v) }

ChosenIn(alpha, b, v) ==
    \E S \in SUBSET Known2a(alpha, b, v) :
        [lr |-> alpha, q |-> { m.acc : m \in S }] \in TrustLive


vars == << msgs, known_msgs, recent_msgs, prev_msg, decision, BVal >>

ProcSet == (Proposer) \cup (SafeAcceptor) \cup (Learner) \cup (FakeAcceptor)

Init == (* Global variables *)
        /\ msgs = {}
        /\ known_msgs = [x \in Acceptor \cup Learner |-> {}]
        /\ recent_msgs = [a \in Acceptor |-> {}]
        /\ prev_msg = [a \in Acceptor |-> NoMessage]
        /\ decision = [lb \in Learner \X Ballot |-> {}]
        /\ BVal \in [Ballot -> Value]

proposer(self) == /\ \E b \in Ballot:
                       msgs' = (msgs \cup {([type |-> "proposer", bal |-> b, prev |-> NoMessage, refs |-> {}])})
                  /\ UNCHANGED << known_msgs, recent_msgs, prev_msg, decision, 
                                  BVal >>

safe_acceptor(self) == /\ \E m \in msgs:
                            /\ /\ m \notin known_msgs[self]
                               /\ KnownRefs(self, m)
                            /\ known_msgs' = [known_msgs EXCEPT ![self] = known_msgs[self] \cup {m}]
                            /\ WellFormed(m)
                            /\ \E LL \in SUBSET Learner:
                                 LET new == [type |-> "acceptor",
                                             acc |-> self,
                                             prev |-> prev_msg[self],
                                             refs |-> recent_msgs[self] \cup {m},
                                             lrns |-> LL] IN
                                   /\ Assert(new \in Message, 
                                             "Failure of assertion at line 162, column 7 of macro called at line 208, column 9.")
                                   /\ \/ /\ WellFormed(new)
                                         /\ prev_msg' = [prev_msg EXCEPT ![self] = new]
                                         /\ recent_msgs' = [recent_msgs EXCEPT ![self] = {new}]
                                         /\ msgs' = (msgs \cup {new})
                                      \/ /\ ~WellFormed(new)
                                         /\ ~OneA(m)
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

fake_acceptor(self) == /\ \E fin \in FINSUBSET(msgs, RefCardinality):
                            \E LL \in SUBSET Learner:
                              LET msg == [type |-> "acceptor", acc |-> self, refs |-> fin, lrns |-> LL] IN
                                /\ WellFormed(msg)
                                /\ msgs' = (msgs \cup {msg})
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

SendProposal(b) ==
    /\ Send([type |-> "proposer", bal |-> b, prev |-> NoMessage, refs |-> {}])
    /\ UNCHANGED << known_msgs, recent_msgs, prev_msg >>
    /\ UNCHANGED decision
    /\ UNCHANGED BVal

Process(a, m) ==
    /\ Recv(a, m)
    /\ WellFormed(m)
    /\ \E LL \in SUBSET Learner :
        LET new == [type |-> "acceptor",
                    acc |-> a,
                    prev |-> prev_msg[a],
                    refs |-> recent_msgs[a] \cup {m},
                    lrns |-> LL] IN
        /\ new \in Message
        /\ \/ /\ WellFormed(new)
              /\ prev_msg' = [prev_msg EXCEPT ![a] = new]
              /\ recent_msgs' = [recent_msgs EXCEPT ![a] = {new}]
              /\ Send(new)
           \/ /\ ~WellFormed(new)
              /\ ~OneA(m)
              /\ recent_msgs' = [recent_msgs EXCEPT ![a] = recent_msgs[a] \cup {m}]
              /\ UNCHANGED << msgs, prev_msg >>
    /\ UNCHANGED decision
    /\ UNCHANGED BVal

ProposerAction(p) ==
    \E bal \in Ballot : SendProposal(bal)

SafeAcceptorAction(a) ==
    \E m \in msgs : Process(a, m)

FakeSendControlMessage(a) ==
    /\ \E fin \in FINSUBSET(msgs, RefCardinality) :
        \E LL \in SUBSET Learner :
            LET new == [type |-> "acceptor", acc |-> a, refs |-> fin, lrns |-> LL] IN
            /\ WellFormed(new)
            /\ Send(new)
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

FakeAcceptorAction(a) == FakeSendControlMessage(a)

NextTLA ==
    \/ \E p \in Proposer :
        ProposerAction(p)
    \/ \E acc \in SafeAcceptor :
        SafeAcceptorAction(acc)
    \/ \E lrn \in Learner :
        LearnerAction(lrn)
    \/ \E acc \in FakeAcceptor :
        FakeAcceptorAction(acc)

THEOREM NextDef == Next <=> NextTLA
<1>1. ASSUME NEW self \in Proposer
      PROVE proposer(self) <=> ProposerAction(self)
      BY DEF proposer, ProposerAction, SendProposal, Send
<1>2. ASSUME NEW self \in SafeAcceptor
      PROVE safe_acceptor(self) <=> SafeAcceptorAction(self)
      BY Zenon DEF safe_acceptor, SafeAcceptorAction, Process, Recv, Send, Assert
<1>3. ASSUME NEW self \in Learner
      PROVE learner(self) <=> LearnerAction(self)
      BY Zenon DEF learner, LearnerAction, LearnerRecv, LearnerDecide, Recv
<1>4. ASSUME NEW self \in FakeAcceptor
      PROVE fake_acceptor(self) <=> FakeAcceptorAction(self)
      BY Zenon DEF fake_acceptor, FakeAcceptorAction, FakeSendControlMessage, FakeSendControlMessage, Send
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
    \A M \in msgs : ~TwoA(M)

2aNotSentBySafeAcceptor ==
    \A M \in msgs : TwoA(M) => M.acc \notin SafeAcceptor

1bNotSentBySafeAcceptor ==
    \A M \in msgs : OneB(M) => M.acc \notin SafeAcceptor

NoDecision ==
    \A L \in Learner : \A BB \in Ballot : \A VV \in Value :
        VV \notin decision[L, BB]

UniqueDecision ==
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] =>
        V1 = V2

=============================================================================
\* Modification History
\* Last modified Fri Nov 22 20:57:30 CET 2024 by karbyshev
\* Created Mon Jun 19 12:24:03 CEST 2022 by karbyshev
