---------------------------- MODULE HPaxos_proof ----------------------------
EXTENDS HPaxos, TLAPS, TLC
-----------------------------------------------------------------------------

LEMMA BallotLeqTrans ==
    ASSUME NEW A \in Ballot, NEW B \in Ballot, NEW C \in Ballot, A =< B, B =< C PROVE A =< C
PROOF BY DEF Ballot

LEMMA BallotLeLeqTrans ==
    ASSUME NEW A \in Ballot, NEW B \in Ballot, NEW C \in Ballot, A < B, B =< C PROVE A < C
PROOF BY DEF Ballot

LEMMA BallotLeqLeTrans ==
    ASSUME NEW A \in Ballot, NEW B \in Ballot, NEW C \in Ballot, A =< B, B < C PROVE A < C
PROOF BY DEF Ballot

LEMMA BallotLeNotLeq == ASSUME NEW A \in Ballot, NEW B \in Ballot, A < B PROVE ~B =< A
PROOF BY DEF Ballot

LEMMA BallotOrderCases == ASSUME NEW A \in Ballot, NEW B \in Ballot PROVE A < B \/ B < A \/ A = B
PROOF BY DEF Ballot

-----------------------------------------------------------------------------

LEMMA SafeAcceptorIsAcceptor == SafeAcceptor \subseteq Acceptor
PROOF BY SafeAcceptorAssumption

LEMMA FakeAcceptorIsAcceptor == FakeAcceptor \subseteq Acceptor
PROOF BY SafeAcceptorAssumption

-----------------------------------------------------------------------------

LEMMA EntanglementSym ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner, <<L1, L2>> \in Ent PROVE <<L2, L1>> \in Ent
PROOF BY EntanglementAssumption, LearnerGraphAssumption

LEMMA EntanglementSelf ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner, <<L1, L2>> \in Ent PROVE <<L1, L1>> \in Ent
PROOF BY EntanglementAssumption, LearnerGraphAssumption

LEMMA EntanglementTrustLive ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW Q1 \in ByzQuorum, NEW Q2 \in ByzQuorum,
           <<L1, L2>> \in Ent,
           [lr |-> L1, q |-> Q1] \in TrustLive,
           [lr |-> L2, q |-> Q2] \in TrustLive
    PROVE  \E N \in SafeAcceptor : N \in Q1 /\ N \in Q2
PROOF BY EntanglementAssumption, LearnerGraphAssumption

-----------------------------------------------------------------------------

VotedFor(lr, acc, bal, val) ==
    \E m \in msgs :
        /\ m.type = "2b"
        /\ m.lr =  lr
        /\ m.acc = acc
        /\ m.bal = bal
        /\ m.val = val

Proposed(lr, acc, bal, val) ==
    \E m \in msgs :
        /\ m.type = "2av"
        /\ m.lr =  lr
        /\ m.acc = acc
        /\ m.bal = bal
        /\ m.val = val

LeftBallot(lr, acc, bal) ==
    \E m \in msgs :
        /\ m.type = "1b"
        /\ m.lr = lr
        /\ m.acc = acc
        /\ bal < m.bal

-----------------------------------------------------------------------------

ReceivedSpec == \A A \in SafeAcceptor : received[A] \subseteq msgs

ReceivedByLearnerSpec ==
    /\ receivedByLearner \in [Learner -> SUBSET {mm \in msgs : mm.type = "2b"}]
    /\ \A L \in Learner : \A mm \in Message :
        mm \in receivedByLearner[L] => mm.lr = L

VotesSentSpec1 ==
    \A A \in SafeAcceptor : \A vote \in votesSent[A] : VotedFor(vote.lr, A, vote.bal, vote.val)

VotesSentSpec2 ==
    \A L \in Learner : \A A \in SafeAcceptor : \A B \in Ballot : \A V \in Value :
        VotedFor(L, A, B, V) => [lr |-> L, bal |-> B, val |-> V] \in votesSent[A]

VotesSentSpec3 ==
    \A A \in SafeAcceptor : \A B \in Ballot : \A vote \in votesSent[A] :
        vote.bal < B =>
        \E P \in votesSent[A] :
            MaxVote(A, B, P) /\ P.lr = vote.lr /\ vote.bal =< P.bal

VotesSentSpec4 ==
    \A A \in SafeAcceptor : \A vote1, vote2 \in votesSent[A] :
        << vote1.lr, vote2.lr >> \in Ent /\
        vote1.bal = vote2.bal => vote1.val = vote2.val

2avSentSpec1 == \A A \in SafeAcceptor : \A p \in 2avSent[A] : Proposed(p.lr, A, p.bal, p.val)

2avSentSpec2 ==
    \A L \in Learner : \A A \in SafeAcceptor : \A B \in Ballot : \A V \in Value :
        Proposed(L, A, B, V) => [lr |-> L, bal |-> B, val |-> V] \in 2avSent[A]

2avSentSpec3 ==
    \A L1, L2 \in Learner : \A A \in SafeAcceptor : \A B \in Ballot : \A V1, V2 \in Value :
        << L1, L2 >> \in Ent /\
        [lr |-> L1, bal |-> B, val |-> V1] \in 2avSent[A] /\
        [lr |-> L2, bal |-> B, val |-> V2] \in 2avSent[A] => V1 = V2

ConnectedSpec ==
    \A A \in SafeAcceptor : \A L1, L2 \in Learner :
        <<L1, L2>> \in Ent => <<L1, L2>> \in connected[A]

DecisionSpec ==
    \A L \in Learner : \A B \in Ballot : \A V \in Value :
        V \in decision[L, B] => ChosenIn(L, B, V)

MsgInv1b(m) ==
    /\ m.bal =< maxBal[m.lr, m.acc]
    /\ m.votes = { p \in votesSent[m.acc] : MaxVote(m.acc, m.bal, p) }
    /\ m.proposals = { p \in 2avSent[m.acc] : p.bal < m.bal /\ p.lr = m.lr }

MsgInv2av(m) ==
    /\ InitializedBallot(m.lr, m.bal)
    /\ AnnouncedValue(m.lr, m.bal, m.val)
    /\ KnowsSafeAt(m.lr, m.acc, m.bal, m.val)
    /\ [lr |-> m.lr, bal |-> m.bal, val |-> m.val] \in 2avSent[m.acc] \* TODO check if used
    /\ \E Q \in ByzQuorum :
        /\ [lr |-> m.lr, q |-> Q] \in TrustLive
        /\ \A ba \in Q :
            \E m1b \in received[m.acc] :
                /\ m1b.type = "1b"
                /\ m1b.lr = m.lr
                /\ m1b.acc = ba
                /\ m1b.bal = m.bal

MsgInv2b(m) ==
    /\ [lr |-> m.lr, bal |-> m.bal, val |-> m.val] \in votesSent[m.acc]
    /\ \E Q \in ByzQuorum :
        /\ [lr |-> m.lr, q |-> Q] \in TrustLive
        /\ \A ba \in Q :
            \E m2av \in received[m.acc] :
                /\ m2av.type = "2av"
                /\ m2av.lr = m.lr
                /\ m2av.acc = ba
                /\ m2av.bal = m.bal
                /\ m2av.val = m.val

MsgInv == \A m \in msgs: m.acc \in SafeAcceptor =>
                /\ (m.type = "1b") => MsgInv1b(m)
                /\ (m.type = "2av") => MsgInv2av(m)
                /\ (m.type = "2b") => MsgInv2b(m)

-----------------------------------------------------------------------------

LEMMA MessageType ==
    ASSUME NEW m \in Message
    PROVE /\ m.lr \in Learner
          /\ m.bal \in Ballot
          /\ (m.type = "1b" \/ m.type = "2av" \/ m.type = "2b") => m.acc \in Acceptor
          /\ (m.type = "1c" \/ m.type = "2av" \/ m.type = "2b") => m.val \in Value
          /\ (m.type = "1b") =>
                /\ m.votes \in SUBSET [lr : Learner, bal : Ballot, val : Value]
                /\ m.proposals \in SUBSET [lr : Learner, bal : Ballot, val : Value]
PROOF BY DEF Message

LEMMA TypeOKInvariant == TypeOK /\ Next => TypeOK'
PROOF
<1> SUFFICES ASSUME TypeOK, Next PROVE TypeOK' OBVIOUS
<1> USE DEF Next
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send, TypeOK, Message
<1>2. CASE AcceptorSendAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in Acceptor,
                      NEW val \in Value,
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc, val)
                      \/ Phase2b(lrn, bal, acc, val)
               PROVE  TypeOK'
    BY <1>2, SafeAcceptorIsAcceptor DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc)
    <3>1.(votesSent \in [Acceptor -> SUBSET [lr : Learner, bal : Ballot, val : Value]])'
            BY <2>1 DEF Phase1b, Phase2av, Phase2b, Send, TypeOK, Message
    <3>2. (2avSent \in [Acceptor -> SUBSET [lr : Learner, bal : Ballot, val : Value]])'
            BY <2>1 DEF Phase1b, Phase2av, Phase2b, Send, TypeOK, Message
    <3>3. msgs' \in SUBSET Message
      <4> SUFFICES
            [type |-> "1b", lr |-> lrn, acc |-> acc, bal |-> bal,
             votes |-> { vote \in votesSent[acc] : MaxVote(acc, bal, vote) },
             proposals |-> { p \in 2avSent[acc] : p.bal < bal /\ p.lr = lrn }] \in Message
          BY <2>1 DEF Phase1b, Send, TypeOK
      <4>1. {vote \in votesSent[acc] : MaxVote(acc, bal, vote)}
                \in SUBSET [lr : Learner, bal : Ballot, val : Value]
            BY DEF TypeOK
      <4>2. {p \in 2avSent[acc] : p.bal < bal /\ p.lr = lrn} \in SUBSET [lr : Learner, bal : Ballot, val : Value]
            BY DEF TypeOK
      <4>3. QED BY <4>1, <4>2 DEF Message, TypeOK
    <3>4. QED BY <2>1, <3>1, <3>2, <3>3 DEF Phase1b, TypeOK, Send
  <2>2. CASE Phase2av(lrn, bal, acc, val)
    <3>2. msgs' \in SUBSET Message
        <4>0. [type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val] \in Message
            BY SafeAcceptorIsAcceptor DEF Message
        <4>1. QED BY <2>2, <4>0, SafeAcceptorIsAcceptor DEF Phase2av, Send, TypeOK, Message
    <3>4. (2avSent \in [Acceptor -> SUBSET [lr : Learner, bal : Ballot, val : Value]])'
        <4>0. [lr |-> lrn, bal |-> bal, val |-> val] \in [lr : Learner, bal : Ballot, val : Value]
              BY DEF TypeOK
        <4>1. QED BY <2>2, <1>2, <4>0, SafeAcceptorIsAcceptor DEF Phase2av, Send, TypeOK, Message
    <3>5. QED BY <2>2, <3>2, <3>4 DEF Phase2av, Send, TypeOK
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3>1. val \in Value OBVIOUS
    <3>2. msgs' \in SUBSET Message
        <4>0. [type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val] \in Message
            BY SafeAcceptorIsAcceptor DEF Message
        <4>1. QED BY <4>0, <2>3 DEF Phase2b, Message, Send, TypeOK
    <3>3. votesSent' \in [Acceptor -> SUBSET [lr : Learner, bal : Ballot, val : Value]]
        <4>0. [lr |-> lrn, bal |-> bal, val |-> val] \in [lr : Learner, bal : Ballot, val : Value] BY <3>1
        <4>1 QED BY <2>3, <1>2, <4>0 DEF Phase2b, TypeOK
    <3>5. QED BY <2>3, <1>2, <3>1, <3>2, <3>3 DEF Phase2b, Send, TypeOK
  <2>4. QED BY <1>2, <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW acc \in Acceptor,
                      NEW m \in msgs,
                      received' = [received EXCEPT ![acc] = received[acc] \cup { m }],
                      UNCHANGED << msgs, maxBal, 2avSent, votesSent, connected,
                                       receivedByLearner, decision >>
               PROVE  TypeOK'
    BY SafeAcceptorIsAcceptor, <1>3 DEF AcceptorReceiveAction, Recv
  <2>7. QED BY <1>3 DEF AcceptorReceiveAction, Recv, TypeOK
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, TypeOK, Message
<1>5. CASE LearnerAction
  <2>1. ASSUME NEW lrn \in Learner, NEW bal \in Ballot,
               LearnerDecide(lrn, bal)
               PROVE  TypeOK'
    BY <2>1 DEF LearnerDecide, TypeOK
  <2>2. ASSUME NEW lrn \in Learner, LearnerRecv(lrn)
        PROVE  TypeOK'
    BY <2>2 DEF LearnerRecv, TypeOK
  <2>3. QED BY <1>5, <2>1, <2>2 DEF LearnerAction
<1>6. CASE FakeAcceptorAction
  <2>1. SUFFICES ASSUME NEW a \in Acceptor, FakeSend(a)
                 PROVE TypeOK'
        BY <1>6, FakeAcceptorIsAcceptor DEF FakeAcceptorAction
  <2>2. QED BY <2>1 DEF FakeSend, Send, TypeOK
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA MsgsMonotone == Next => msgs \subseteq msgs'
PROOF
<1> SUFFICES ASSUME Next PROVE msgs \subseteq msgs' OBVIOUS
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send
<1>2. CASE AcceptorSendAction BY <1>2 DEF AcceptorSendAction, Phase1b, Phase2av, Phase2b, Send
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerDecide, LearnerRecv
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA ReceivedSpecInvariant == TypeOK /\ ReceivedSpec /\ Next => ReceivedSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, ReceivedSpec, Next PROVE ReceivedSpec' OBVIOUS
<1>0. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction
      BY <1>1, SafeAcceptorIsAcceptor DEF ProposerAction, Phase1a, Phase1c, ReceivedSpec, Send, Next, TypeOK
<1>2. CASE AcceptorSendAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in Acceptor,
                      NEW val \in Value,
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc, val)
                      \/ Phase2b(lrn, bal, acc, val)
               PROVE  ReceivedSpec'
    BY <1>2, SafeAcceptorIsAcceptor DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1, MsgsMonotone DEF TypeOK, ReceivedSpec, Phase1b
  <2>2. CASE Phase2av(lrn, bal, acc, val) BY <2>2 DEF TypeOK, ReceivedSpec, Phase2av, Send
  <2>3. CASE Phase2b(lrn, bal, acc, val) BY <2>3, MsgsMonotone DEF Phase2b, TypeOK, ReceivedSpec, Send
  <2>4. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW acc \in Acceptor,
                      NEW m \in msgs,
                      received' = [received EXCEPT ![acc] = received[acc] \cup { m }],
                      UNCHANGED << msgs, maxBal, 2avSent, votesSent, connected, receivedByLearner, decision >>
               PROVE  ReceivedSpec'
    BY <1>3, SafeAcceptorIsAcceptor DEF AcceptorReceiveAction, Recv
  <2> QED BY MessageType, SafeAcceptorIsAcceptor DEF ReceivedSpec, TypeOK, Next
<1>4. CASE AcceptorDisconnectAction
  BY <1>4 DEF AcceptorDisconnectAction, Disconnect, ReceivedSpec, TypeOK, Next
<1>5. CASE LearnerAction
  BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, ReceivedSpec, TypeOK, Next
<1>6. CASE FakeAcceptorAction
  <2>1. SUFFICES ASSUME NEW a \in Acceptor, FakeSend(a) PROVE ReceivedSpec'
        BY <1>6, FakeAcceptorIsAcceptor DEF FakeAcceptorAction
  <2>2. QED BY <2>1 DEF FakeSend, Send, TypeOK, ReceivedSpec
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA ReceivedByLearnerSpecInvariant ==
    TypeOK /\ ReceivedByLearnerSpec /\ Next => ReceivedByLearnerSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, ReceivedByLearnerSpec, Next PROVE ReceivedByLearnerSpec' OBVIOUS
<1>1. CASE ProposerAction
  BY <1>1 DEF ProposerAction, Phase1a, Phase1c, ReceivedByLearnerSpec, Send, Next, TypeOK
<1>2. CASE AcceptorSendAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in Acceptor,
                      NEW val \in Value,
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc, val)
                      \/ Phase2b(lrn, bal, acc, val)
               PROVE  ReceivedByLearnerSpec'
    BY <1>2, SafeAcceptorIsAcceptor DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc)
    BY <2>1 DEF TypeOK, ReceivedByLearnerSpec, Phase1b, Send
  <2>2. CASE Phase2av(lrn, bal, acc, val)
    BY <2>2 DEF TypeOK, ReceivedByLearnerSpec, Phase2av, Send
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3> SUFFICES ASSUME Send([type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val])
                 PROVE  ReceivedByLearnerSpec'
      BY <2>3 DEF Phase2b
    <3>0. TypeOK' BY TypeOKInvariant
    <3>1. UNCHANGED <<receivedByLearner>> BY <2>3 DEF Phase2b
    <3>3. (\A L \in Learner : \A mm \in Message : mm \in receivedByLearner[L] => mm.lr = L)'
          BY <3>1 DEF ReceivedByLearnerSpec, TypeOK
    <3>4. (receivedByLearner \in [Learner -> SUBSET {mm \in msgs : mm.type = "2b"}])'
          BY <3>0, <3>1, MessageType DEF ReceivedByLearnerSpec, Send, TypeOK
    <3>5. QED BY <3>3, <3>4 DEF ReceivedByLearnerSpec
  <2>4. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction
  BY <1>3 DEF AcceptorReceiveAction, Recv, ReceivedByLearnerSpec, TypeOK, Next
<1>4. CASE AcceptorDisconnectAction
  BY <1>4 DEF AcceptorDisconnectAction, Disconnect, ReceivedByLearnerSpec, TypeOK, Next
<1>5. CASE LearnerAction
  <2>1. ASSUME NEW lrn \in Learner, NEW bal \in Ballot, LearnerDecide(lrn, bal)
        PROVE  ReceivedByLearnerSpec'
    BY <2>1 DEF LearnerDecide, ReceivedByLearnerSpec, TypeOK, Next
  <2>2. ASSUME NEW lrn \in Learner, LearnerRecv(lrn)
        PROVE  ReceivedByLearnerSpec'
    <3> SUFFICES ASSUME NEW m \in {mm \in msgs : mm.type = "2b" /\ mm.lr = lrn},
                        receivedByLearner' =
                            [receivedByLearner EXCEPT ![lrn] = receivedByLearner[lrn] \cup {m}]
                 PROVE  ReceivedByLearnerSpec'
      BY <2>2 DEF LearnerRecv
    <3>1. UNCHANGED << msgs >> BY <2>2 DEF LearnerAction, LearnerRecv
    <3>5. QED BY <2>2, <3>1 DEF ReceivedByLearnerSpec
  <2>3. QED BY <1>5, <2>1, <2>2 DEF LearnerAction
<1>6. CASE FakeAcceptorAction
  <2>1. SUFFICES ASSUME NEW a \in Acceptor, FakeSend(a) PROVE ReceivedByLearnerSpec'
        BY <1>6, FakeAcceptorIsAcceptor DEF FakeAcceptorAction
  <2>2. QED BY <2>1 DEF FakeSend, Send, TypeOK, ReceivedByLearnerSpec
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA MaxBalMonotone ==
    TypeOK /\ Next => \A l \in Learner : \A a \in SafeAcceptor : maxBal[l, a] =< maxBal'[l, a]
PROOF
<1> SUFFICES ASSUME TypeOK, Next, NEW CONSTANT l \in Learner, NEW CONSTANT a \in SafeAcceptor
             PROVE maxBal[l, a] =< maxBal'[l, a]
    OBVIOUS
<1>1. CASE ProposerAction
      BY <1>1, SafeAcceptorIsAcceptor DEF ProposerAction, Phase1a, Phase1c, Send, TypeOK, Ballot
<1>2. CASE AcceptorSendAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in Acceptor,
                      NEW val \in Value,
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc, val)
                      \/ Phase2b(lrn, bal, acc, val)
               PROVE  maxBal[l, a] =< (maxBal')[l, a]
    BY <1>2, SafeAcceptorIsAcceptor DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc)
    <3>1. CASE <<l, a>> = <<lrn, acc>> BY <2>1, <3>1 DEF Phase1b, TypeOK, Ballot
    <3>2. CASE <<l, a>> # <<lrn, acc>> BY <2>1, <3>2, SafeAcceptorIsAcceptor DEF Phase1b, TypeOK, Ballot
    <3>3. QED BY <3>1, <3>2
  <2>2. CASE Phase2av(lrn, bal, acc, val)
    <3>1. UNCHANGED maxBal BY <2>2 DEF Phase2av
    <3>2. QED BY <3>1, SafeAcceptorIsAcceptor DEF TypeOK, Ballot
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3>1. UNCHANGED maxBal BY <2>3 DEF Phase2b
    <3>2. QED BY <3>1, SafeAcceptorIsAcceptor DEF TypeOK, Ballot
  <2>4. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction
  <2>1. UNCHANGED maxBal BY <1>3 DEF AcceptorReceiveAction, Recv
  <2>2. QED BY <2>1, SafeAcceptorIsAcceptor DEF TypeOK, Ballot
<1>4. CASE AcceptorDisconnectAction
  <2>1. UNCHANGED maxBal BY <1>4 DEF AcceptorDisconnectAction, Disconnect
  <2>2. QED BY <2>1, SafeAcceptorIsAcceptor DEF TypeOK, Ballot
<1>5. CASE LearnerAction
  <2>1. UNCHANGED maxBal BY <1>5 DEF LearnerAction, LearnerDecide, LearnerRecv
  <2>2. QED BY <2>1, SafeAcceptorIsAcceptor DEF TypeOK, Ballot
<1>6. CASE FakeAcceptorAction
  <2>1. UNCHANGED maxBal BY <1>6 DEF FakeAcceptorAction, FakeSend
  <2>2. QED BY <2>1, SafeAcceptorIsAcceptor DEF TypeOK, Ballot
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA 2avSentMonotone == TypeOK /\ Next => \A A \in SafeAcceptor : 2avSent[A] \subseteq 2avSent'[A]
PROOF
<1> SUFFICES ASSUME TypeOK, Next, NEW A \in SafeAcceptor PROVE 2avSent[A] \subseteq 2avSent[A]' OBVIOUS
<1>0a. TypeOK OBVIOUS
<1>0b. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send
<1>2. CASE AcceptorSendAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in Acceptor,
                      NEW val \in Value,
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc, val)
                      \/ Phase2b(lrn, bal, acc, val)
               PROVE  2avSent[A] \subseteq 2avSent[A]'
      BY <1>2, SafeAcceptorIsAcceptor DEF AcceptorSendAction
  <2>1. QED BY <1>0b, SafeAcceptorIsAcceptor DEF AcceptorSendAction, Phase1b, Phase2av, Phase2b, Send, TypeOK
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerDecide, LearnerRecv
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA ReceivedMonotone ==
    TypeOK /\ Next => \A A \in SafeAcceptor : received[A] \subseteq received'[A]
PROOF
<1> SUFFICES ASSUME TypeOK, Next, NEW A \in SafeAcceptor
             PROVE received[A] \subseteq received'[A] OBVIOUS
<1>0a. TypeOK OBVIOUS
<1>0b. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send
<1>2. CASE AcceptorSendAction BY <1>2 DEF AcceptorSendAction, Send, Phase1b, Phase2av, Phase2b
<1>3. CASE AcceptorReceiveAction BY <1>3, <1>0a, <1>0b, SafeAcceptorIsAcceptor DEF AcceptorReceiveAction, Recv, TypeOK
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerDecide, LearnerRecv
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA ReceivedByLearnerMonotone ==
    TypeOK /\ Next => \A L \in Learner : receivedByLearner[L] \subseteq receivedByLearner'[L]
PROOF
<1> SUFFICES ASSUME TypeOK, Next, NEW L \in Learner
             PROVE receivedByLearner[L] \subseteq receivedByLearner'[L] OBVIOUS
<1>0b. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send
<1>2. CASE AcceptorSendAction BY <1>2 DEF AcceptorSendAction, Send, Phase1b, Phase2av, Phase2b
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, TypeOK
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect
<1>5. CASE LearnerAction BY <1>5, <1>0b DEF LearnerAction, LearnerDecide, LearnerRecv, TypeOK
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA VotesSentMonotone ==
    TypeOK /\ Next => \A A \in Acceptor : votesSent[A] \subseteq votesSent'[A]
PROOF
<1> SUFFICES ASSUME TypeOK, Next, NEW A \in Acceptor PROVE votesSent[A] \subseteq votesSent'[A] OBVIOUS
<1>0a. TypeOK OBVIOUS
<1>0b. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send
<1>2. CASE AcceptorSendAction BY <1>2, <1>0a, <1>0b DEF AcceptorSendAction, Send, Phase1b, Phase2av, Phase2b, TypeOK
<1>3. CASE AcceptorReceiveAction BY <1>3, <1>0a, <1>0b DEF AcceptorReceiveAction, Recv, TypeOK
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerDecide, LearnerRecv
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA VotesSentSpec1Invariant == Next /\ VotesSentSpec1 => VotesSentSpec1'
PROOF
<1> SUFFICES ASSUME
  Next, VotesSentSpec1, NEW A \in SafeAcceptor, NEW vote \in votesSent'[A]
    PROVE VotedFor(vote.lr, A, vote.bal, vote.val)'
    BY DEF VotesSentSpec1
<1> USE DEF VotesSentSpec1
<1>1. CASE ProposerAction BY <1>1, SafeAcceptorIsAcceptor DEF ProposerAction, Phase1a, Phase1c, Send, VotedFor
<1>2. CASE AcceptorSendAction
  <2>. SUFFICES ASSUME NEW lrn \in Learner,
                       NEW bal \in Ballot,
                       NEW acc \in SafeAcceptor,
                       NEW val \in Value,
                       \/ Phase1b(lrn, bal, acc)
                       \/ Phase2av(lrn, bal, acc, val)
                       \/ Phase2b(lrn, bal, acc, val)
                PROVE  VotedFor(vote.lr, A, vote.bal, vote.val)'
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF Phase1b, Send, VotedFor
  <2>2. CASE Phase2av(lrn, bal, acc, val) BY <2>2 DEF Phase2av, Send, VotedFor
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3> SUFFICES ASSUME Send([type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]),
                        votesSent' = [votesSent EXCEPT ![acc] =
                                        votesSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> val] }]
                 PROVE VotedFor(vote.lr, A, vote.bal, vote.val)'
        BY <2>3 DEF Phase2b
    <3>2. CASE acc = A
      <4>1. USE DEF VotedFor
      <4>2. CASE vote \in votesSent[acc] BY <3>2, <4>2, MsgsMonotone
      <4>3. CASE vote \notin votesSent[acc]
        <5>1. DEFINE m0 == [type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]
        <5>2. m0 \in msgs' BY DEF Phase2b, Send
        <5>3. WITNESS <5>2
        <5>10 QED BY <3>2, <4>3
      <4>4. QED BY <4>2, <4>3
    <3>3. CASE acc # A BY <3>3 DEF Send, VotedFor
    <3>4 QED BY <3>2, <3>3
  <2>5. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, VotedFor
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, VotedFor
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, VotedFor
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send, VotedFor
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA VotesSentSpec2Invariant == TypeOK /\ Next /\ VotesSentSpec2 => VotesSentSpec2'
PROOF
<1> SUFFICES ASSUME TypeOK, Next, VotesSentSpec2,
                    NEW L \in Learner, NEW A \in SafeAcceptor, NEW B \in Ballot, NEW V \in Value
             PROVE (VotedFor(L, A, B, V) => [lr |-> L, bal |-> B, val |-> V] \in votesSent[A])'
    BY DEF VotesSentSpec2
<1> USE DEF VotesSentSpec2
<1>0a. TypeOK OBVIOUS
<1>0b. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send, VotedFor
<1>2. CASE AcceptorSendAction
  <2>. SUFFICES ASSUME NEW lrn \in Learner,
                       NEW bal \in Ballot,
                       NEW acc \in SafeAcceptor,
                       NEW val \in Value,
                       \/ Phase1b(lrn, bal, acc)
                       \/ Phase2av(lrn, bal, acc, val)
                       \/ Phase2b(lrn, bal, acc, val)
                PROVE (VotedFor(L, A, B, V) => [lr |-> L, bal |-> B, val |-> V] \in votesSent[A])'
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF Phase1b, Send, VotedFor
  <2>2. CASE Phase2av(lrn, bal, acc, val)
    <3>12. SUFFICES ASSUME VotedFor(L, A, B, V)'
                    PROVE [lr |-> L, bal |-> B, val |-> V] \in votesSent[A] BY <2>2 DEF Phase2av
    <3>13. VotedFor(L, A, B, V) BY <3>12, <2>2 DEF Phase2av, Send, VotedFor
    <3>20. QED BY <3>13
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3> SUFFICES ASSUME Send([type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]),
                        votesSent' = [votesSent EXCEPT ![acc] =
                                        votesSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> val] }]
                 PROVE (VotedFor(L, A, B, V) => [lr |-> L, bal |-> B, val |-> V] \in votesSent[A])'
        BY <2>3 DEF Phase2b
    <3>1. QED BY <1>0b DEF Send, VotedFor, TypeOK
  <2>5. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, VotedFor
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, VotedFor
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, VotedFor
<1>6. CASE FakeAcceptorAction
  <2>1. SUFFICES ASSUME VotedFor(L, A, B, V)'
                 PROVE [lr |-> L, bal |-> B, val |-> V] \in votesSent[A]
        BY <1>6 DEF FakeAcceptorAction, FakeSend
  <2>2. VotedFor(L, A, B, V) BY <1>6, <2>1, SafeAcceptorAssumption DEF FakeAcceptorAction, FakeSend, Send, VotedFor
  <2>10. QED BY <2>2
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA VotesSentSpec3Invariant == TypeOK /\ Next /\ VotesSentSpec3 => VotesSentSpec3'
PROOF
<1> SUFFICES ASSUME TypeOK, Next, VotesSentSpec3,
                    NEW A \in SafeAcceptor, NEW B \in Ballot,
                    NEW V \in votesSent'[A],
                    V.bal < B
             PROVE (\E P \in votesSent[A] : MaxVote(A, B, P) /\ P.lr = V.lr /\ V.bal =< P.bal)'
    BY DEF VotesSentSpec3
<1> USE DEF VotesSentSpec3
<1>0a. TypeOK OBVIOUS
<1>0b. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send, MaxVote
<1>2. CASE AcceptorSendAction
  <2>. SUFFICES ASSUME NEW lrn \in Learner,
                       NEW bal \in Ballot,
                       NEW acc \in SafeAcceptor,
                       NEW val \in Value,
                       \/ Phase1b(lrn, bal, acc)
                       \/ Phase2av(lrn, bal, acc, val)
                       \/ Phase2b(lrn, bal, acc, val)
                PROVE (\E P \in votesSent[A] : MaxVote(A, B, P) /\ P.lr = V.lr /\ V.bal =< P.bal)'
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF Phase1b, MaxVote
  <2>2. CASE Phase2av(lrn, bal, acc, val) BY <2>2 DEF Phase2av, MaxVote
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3> SUFFICES ASSUME votesSent' = [votesSent EXCEPT ![acc] =
                                        votesSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> val] }]
                 PROVE (\E P \in votesSent[A] : MaxVote(A, B, P) /\ P.lr = V.lr /\ V.bal =< P.bal)'
        BY <2>3 DEF Phase2b
    <3>1. CASE A = acc
      <4>0. DEFINE v0 == [lr |-> lrn, bal |-> bal, val |-> val]
      <4>1. v0 \in votesSent[A]' BY <3>1, <1>0b DEF TypeOK
      <4>2. CASE V \in votesSent[A]
        <5>1. PICK Pmax \in votesSent[A] : MaxVote(A, B, Pmax) /\ Pmax.lr = V.lr /\ V.bal =< Pmax.bal
              BY <4>2
        <5>1a. Pmax.bal \in Ballot BY SafeAcceptorIsAcceptor DEF TypeOK
        <5>2. CASE lrn # V.lr BY <3>1, <5>1, <5>2 DEF MaxVote, Ballot
        <5>3. CASE lrn = V.lr
          <6>1. CASE B =< bal BY <3>1, <5>1, <5>3, <6>1 DEF MaxVote, Ballot
          <6>2. CASE bal < B
            <7>1. CASE bal <= Pmax.bal BY <5>1, <5>3, <6>2, <7>1 DEF MaxVote
            <7>2. CASE Pmax.bal < bal
              <8>1. WITNESS v0 \in votesSent[A]'
              <8>2. V.bal \in Ballot BY <4>2, SafeAcceptorIsAcceptor DEF TypeOK
              <8>3. V.bal <= bal BY <8>2, <5>1, <5>1a, <7>2 DEF Ballot
              <8>5. SUFFICES MaxVote(A, B, v0)' BY <5>3, <8>3
              <8>10. QED BY <3>1, <5>1, <5>3, <6>2, <7>2, SafeAcceptorIsAcceptor
                         DEF Ballot, MaxVote, TypeOK
            <7>3. QED BY <5>1a, <7>1, <7>2 DEF Ballot
          <6>10. QED BY <6>1, <6>2 DEF Ballot
        <5>10. QED BY <5>2, <5>3
      <4>3. CASE V \notin votesSent[A]
        <5>0. V = v0 BY <4>3, <3>1
        <5>1. CASE \A P \in votesSent[A] : P.lr = lrn => P.bal >= B
          <6>1. WITNESS v0 \in votesSent[A]'
          <6>2. QED BY <3>1, <5>1, <1>0b, <5>0 DEF Ballot, TypeOK, MaxVote
        <5>2. CASE \E P \in votesSent[A] : P.lr = lrn /\ P.bal < B
          <6>1. PICK P \in votesSent[A] : P.lr = lrn /\ P.bal < B BY <5>2
          <6>2. PICK Pmax \in votesSent[A] : MaxVote(A, B, Pmax) /\ Pmax.lr = lrn /\ P.bal =< Pmax.bal BY <6>1
          <6>3. Pmax \in votesSent[A]' BY <3>1, <6>2
          <6>4. CASE Pmax.bal < bal
            <7>1. WITNESS v0 \in votesSent[A]'
            <7>2. SUFFICES MaxVote(A, B, v0)' BY <5>0 DEF Ballot
            <7>3. QED BY <5>0, <6>4, <6>2, <1>0b, <3>1 DEF Ballot, TypeOK, MaxVote
          <6>5. CASE bal =< Pmax.bal
            <7>1. WITNESS Pmax \in votesSent[A]'
            <7>20. QED BY <5>0, <6>5, <6>2, <1>0b, <3>1 DEF TypeOK, MaxVote
          <6>20. QED BY <6>4, <6>5, SafeAcceptorIsAcceptor DEF Ballot, TypeOK
        <5>3. QED BY <5>1, <5>2, SafeAcceptorIsAcceptor DEF Ballot, TypeOK
      <4>4. QED BY <4>2, <4>3
    <3>2. CASE A # acc BY <3>2 DEF MaxVote
    <3>3. QED BY <3>1, <3>2
  <2>5. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, MaxVote
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, MaxVote
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, MaxVote
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send, MaxVote
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA VotesSentSpec4Invariant ==
    TypeOK /\ Next /\ MsgInv /\ ReceivedSpec /\
    VotesSentSpec1 /\ 2avSentSpec2 /\ 2avSentSpec3 /\ VotesSentSpec4 =>
    VotesSentSpec4'
PROOF
<1> SUFFICES ASSUME TypeOK, Next, MsgInv, ReceivedSpec, VotesSentSpec1,
                    2avSentSpec2, 2avSentSpec3, VotesSentSpec4,
                    NEW A \in SafeAcceptor,
                    NEW vote1 \in votesSent'[A], NEW vote2 \in votesSent'[A],
                    <<vote1.lr, vote2.lr>> \in Ent,
                    vote1.bal = vote2.bal
             PROVE vote1.val = vote2.val
    BY DEF VotesSentSpec4
<1> USE DEF MsgInv
<1>0a. TypeOK OBVIOUS
<1>0b. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send, VotesSentSpec4
<1>2. CASE AcceptorSendAction
  <2>. SUFFICES ASSUME NEW lrn \in Learner,
                       NEW bal \in Ballot,
                       NEW acc \in SafeAcceptor,
                       NEW val \in Value,
                       \/ Phase1b(lrn, bal, acc)
                       \/ Phase2av(lrn, bal, acc, val)
                       \/ Phase2b(lrn, bal, acc, val)
                PROVE vote1.val = vote2.val
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF Phase1b, VotesSentSpec4
  <2>2. CASE Phase2av(lrn, bal, acc, val) BY <2>2 DEF Phase2av, VotesSentSpec4
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3> SUFFICES ASSUME votesSent' = [votesSent EXCEPT ![acc] =
                                        votesSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> val] }]
                 PROVE vote1.val = vote2.val
        BY <2>3 DEF Phase2b
    <3>1. CASE A = acc
      <4>1. CASE vote1 \in votesSent[A] /\ vote2 \in votesSent[A] BY <4>1 DEF VotesSentSpec4
      <4>2. CASE vote1 \in votesSent[A] /\ vote2 \notin votesSent[A]
        <5>0. vote1.lr \in Learner /\ vote1.val \in Value BY <4>2 DEF TypeOK
        <5>1. vote2 = [lr |-> lrn, bal |-> bal, val |-> val] BY <4>2
        <5>2. PICK Q2 \in ByzQuorum :
                /\ [lr |-> lrn, q |-> Q2] \in TrustLive
                /\ \A aa \in Q2 :
                    \E m \in {mm \in received[acc] :
                                /\ mm.type = "2av"
                                /\ mm.lr = lrn
                                /\ mm.bal = bal} :
                        /\ m.val = val
                        /\ m.acc = aa
              BY <5>1, <2>3 DEF Phase2b
        <5>3. << vote1.lr, lrn >> \in Ent /\ vote1.bal = bal BY <5>1
        <5>4. PICK m1 \in msgs :
                /\ m1.type = "2b"
                /\ m1.lr = vote1.lr
                /\ m1.acc = A
                /\ m1.bal = bal
                /\ m1.val = vote1.val
              BY <4>2, <5>3 DEF VotesSentSpec1, VotedFor
        <5>5. PICK Q1 \in ByzQuorum :
                /\ [lr |-> vote1.lr, q |-> Q1] \in TrustLive
                /\ \A ba \in Q1 :
                    \E m2av \in received[acc] :
                        /\ m2av.type = "2av"
                        /\ m2av.lr = vote1.lr
                        /\ m2av.acc = ba
                        /\ m2av.bal = bal
                        /\ m2av.val = vote1.val
          <6>1. \E Q1 \in ByzQuorum :
                    /\ [lr |-> m1.lr, q |-> Q1] \in TrustLive
                    /\ \A ba \in Q1 :
                        \E m2av \in received[m1.acc] :
                            /\ m2av.type = "2av"
                            /\ m2av.lr = m1.lr
                            /\ m2av.acc = ba
                            /\ m2av.bal = m1.bal
                            /\ m2av.val = m1.val
              BY <5>4, <3>1 DEF MsgInv2b, TypeOK
          <6>2. QED BY <5>4, <6>1, <3>1
        <5>6. << vote1.lr, lrn >> \in Ent BY <5>3
        <5>7. PICK S \in SafeAcceptor : S \in Q1 /\ S \in Q2 BY <5>2, <5>5, <5>6, <5>0, EntanglementTrustLive
        <5>8. PICK m2av1 \in received[acc]:
                    /\ m2av1.type = "2av"
                    /\ m2av1.lr = vote1.lr
                    /\ m2av1.acc = S
                    /\ m2av1.bal = bal
                    /\ m2av1.val = vote1.val
             BY <5>7, <5>5
        <5>9. /\ m2av1 \in msgs
              /\ m2av1.type = "2av"
              /\ m2av1.lr = vote1.lr
              /\ m2av1.acc = S
              /\ m2av1.bal = bal
              /\ m2av1.val = vote1.val
              BY <5>8, <5>0, SafeAcceptorIsAcceptor DEF ReceivedSpec, TypeOK
        <5>10. [lr |-> vote1.lr, bal |-> bal, val |-> vote1.val] \in 2avSent[S]
               BY <5>9, <5>0 DEF 2avSentSpec2, Proposed
        <5>11. PICK m2av2 \in received[acc]:
                    /\ m2av2.type = "2av"
                    /\ m2av2.lr = lrn
                    /\ m2av2.acc = S
                    /\ m2av2.bal = bal
                    /\ m2av2.val = val
               BY <5>7, <5>2
        <5>12. /\ m2av2 \in msgs
               /\ m2av2.type = "2av"
               /\ m2av2.lr = lrn
               /\ m2av2.acc = S
               /\ m2av2.bal = bal
               /\ m2av2.val = val
               BY <5>11, SafeAcceptorIsAcceptor DEF ReceivedSpec, TypeOK
        <5>13. [lr |-> lrn, bal |-> bal, val |-> val] \in 2avSent[S]
               BY <5>12, SafeAcceptorIsAcceptor DEF 2avSentSpec2, Proposed
        <5>14. vote1.val = val BY <5>10, <5>13, <5>6, <5>0 DEF 2avSentSpec3
        <5>20. QED BY <5>1, <5>14
      <4>3. CASE vote1 \notin votesSent[A] /\ vote2 \in votesSent[A]
        <5>0. vote2.lr \in Learner /\ vote2.val \in Value BY <4>3 DEF TypeOK
        <5>1. vote1 = [lr |-> lrn, bal |-> bal, val |-> val] BY <4>3
        <5>2. PICK Q1 \in ByzQuorum :
                /\ [lr |-> lrn, q |-> Q1] \in TrustLive
                /\ \A aa \in Q1 :
                    \E m \in {mm \in received[acc] :
                                /\ mm.type = "2av"
                                /\ mm.lr = lrn
                                /\ mm.bal = bal} :
                        /\ m.val = val
                        /\ m.acc = aa
              BY <5>1, <2>3 DEF Phase2b
        <5>3. << lrn, vote2.lr >> \in Ent /\ vote2.bal = bal BY <5>1
        <5>4. PICK m2 \in msgs :
                /\ m2.type = "2b"
                /\ m2.lr = vote2.lr
                /\ m2.acc = A
                /\ m2.bal = bal
                /\ m2.val = vote2.val
              BY <4>3, <5>3 DEF VotesSentSpec1, VotedFor
        <5>5. PICK Q2 \in ByzQuorum :
                /\ [lr |-> vote2.lr, q |-> Q2] \in TrustLive
                /\ \A ba \in Q2 :
                    \E m2av \in received[acc] :
                        /\ m2av.type = "2av"
                        /\ m2av.lr = vote2.lr
                        /\ m2av.acc = ba
                        /\ m2av.bal = bal
                        /\ m2av.val = vote2.val
          <6>1. \E Q2 \in ByzQuorum :
                    /\ [lr |-> m2.lr, q |-> Q2] \in TrustLive
                    /\ \A ba \in Q2 :
                        \E m2av \in received[m2.acc] :
                            /\ m2av.type = "2av"
                            /\ m2av.lr = m2.lr
                            /\ m2av.acc = ba
                            /\ m2av.bal = m2.bal
                            /\ m2av.val = m2.val
              BY <5>4, <3>1 DEF MsgInv2b, TypeOK
          <6>2. QED BY <5>4, <6>1, <3>1
        <5>6. << lrn, vote2.lr >> \in Ent BY <5>3
        <5>7. PICK S \in SafeAcceptor : S \in Q1 /\ S \in Q2 BY <5>2, <5>5, <5>6, <5>0, EntanglementTrustLive
        <5>8. PICK m2av2 \in received[acc]:
                    /\ m2av2.type = "2av"
                    /\ m2av2.lr = vote2.lr
                    /\ m2av2.acc = S
                    /\ m2av2.bal = bal
                    /\ m2av2.val = vote2.val
             BY <5>7, <5>5
        <5>9. /\ m2av2 \in msgs
              /\ m2av2.type = "2av"
              /\ m2av2.lr = vote2.lr
              /\ m2av2.acc = S
              /\ m2av2.bal = bal
              /\ m2av2.val = vote2.val
              BY <5>8, <5>0, SafeAcceptorIsAcceptor DEF ReceivedSpec, TypeOK
        <5>10. [lr |-> vote2.lr, bal |-> bal, val |-> vote2.val] \in 2avSent[S]
               BY <5>9, <5>0 DEF 2avSentSpec2, Proposed
        <5>11. PICK m2av1 \in received[acc]:
                    /\ m2av1.type = "2av"
                    /\ m2av1.lr = lrn
                    /\ m2av1.acc = S
                    /\ m2av1.bal = bal
                    /\ m2av1.val = val
               BY <5>7, <5>2
        <5>12. /\ m2av1 \in msgs
               /\ m2av1.type = "2av"
               /\ m2av1.lr = lrn
               /\ m2av1.acc = S
               /\ m2av1.bal = bal
               /\ m2av1.val = val
               BY <5>11, SafeAcceptorIsAcceptor DEF ReceivedSpec, TypeOK
        <5>13. [lr |-> lrn, bal |-> bal, val |-> val] \in 2avSent[S]
               BY <5>12, SafeAcceptorIsAcceptor DEF 2avSentSpec2, Proposed
        <5>14. vote2.val = val BY <5>10, <5>13, <5>6, <5>0 DEF 2avSentSpec3
        <5>20. QED BY <5>1, <5>14
      <4>4. CASE vote1 \notin votesSent[A] /\ vote2 \notin votesSent[A] BY <4>4
      <4>5. QED BY <4>1, <4>2, <4>3, <4>4
    <3>2. CASE A # acc BY <3>2 DEF VotesSentSpec4
    <3>3. QED BY <3>1, <3>2
  <2>4. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, Next, VotesSentSpec4
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Next, VotesSentSpec4
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, Next, VotesSentSpec4
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send, VotesSentSpec4
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA 2avSentSpec1Invariant == Next /\ 2avSentSpec1 => 2avSentSpec1'
PROOF
<1> SUFFICES ASSUME Next, 2avSentSpec1,
             NEW A \in SafeAcceptor, NEW p \in 2avSent'[A]
             PROVE Proposed(p.lr, A, p.bal, p.val)'
    BY DEF 2avSentSpec1
<1> USE DEF 2avSentSpec1
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send, Proposed
<1>2. CASE AcceptorSendAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in SafeAcceptor,
                      NEW val \in Value,
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc, val)
                      \/ Phase2b(lrn, bal, acc, val)
                PROVE  Proposed(p.lr, A, p.bal, p.val)'
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF Phase1b, Send, Proposed
  <2>2. CASE Phase2av(lrn, bal, acc, val)
    <3> SUFFICES ASSUME Send([type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]),
                        2avSent' = [2avSent EXCEPT ![acc] =
                                    2avSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> val] }]
                 PROVE Proposed(p.lr, A, p.bal, p.val)'
          BY <2>2 DEF Phase2av
    <3>2. CASE acc = A
        <4>1. USE DEF Proposed
        <4>2. CASE p \in 2avSent[acc] BY <3>2, <4>2, MsgsMonotone
        <4>3. CASE p \notin 2avSent[acc]
          <5>1. DEFINE m0 == [type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]
          <5>2. m0 \in msgs' BY DEF Phase2b, Send
          <5>3. WITNESS <5>2
          <5>10. QED BY <3>2, <4>3
        <4>10. QED BY <4>2, <4>3
    <3>3. CASE acc # A BY <3>3 DEF Send, Proposed
    <3>4. QED BY <3>2, <3>3
  <2>3. CASE Phase2b(lrn, bal, acc, val) BY <2>3 DEF Phase2b, Send, Proposed
  <2>5. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, Proposed
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Proposed
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, Proposed
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send, Proposed
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA 2avSentSpec2Invariant == TypeOK /\ Next /\ 2avSentSpec2 => 2avSentSpec2'
PROOF
<1> SUFFICES ASSUME TypeOK, Next, 2avSentSpec2,
                    NEW L \in Learner, NEW A \in SafeAcceptor, NEW B \in Ballot, NEW V \in Value,
                    Proposed(L, A, B, V)'
             PROVE ([lr |-> L, bal |-> B, val |-> V] \in 2avSent[A])'
    BY DEF 2avSentSpec2
<1> USE DEF 2avSentSpec2
<1>0. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send, Proposed
<1>2. CASE AcceptorSendAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in SafeAcceptor,
                      NEW val \in Value,
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc, val)
                      \/ Phase2b(lrn, bal, acc, val)
                PROVE ([lr |-> L, bal |-> B, val |-> V] \in 2avSent[A])'
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF Phase1b, Send, Proposed
  <2>2. CASE Phase2av(lrn, bal, acc, val)
    <3> SUFFICES ASSUME Send([type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]),
                        2avSent' = [2avSent EXCEPT ![acc] =
                                    2avSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> val] }]
                 PROVE ([lr |-> L, bal |-> B, val |-> V] \in 2avSent[A])'
          BY <2>2 DEF Phase2av
    <3>1. QED BY <1>0 DEF Send, Proposed, TypeOK
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3>1. SUFFICES [lr |-> L, bal |-> B, val |-> V] \in 2avSent[A] BY <2>3 DEF Phase2b
    <3>2. PICK m \in msgs' :
           /\ m.type = "2av"
           /\ m.lr = L
           /\ m.acc = A
           /\ m.bal = B
           /\ m.val = V
          BY DEF Proposed
    <3>3. m \in msgs BY <2>3, <3>2 DEF Phase2b, Send
    <3>4. QED BY <3>2, <3>3 DEF Proposed
  <2>5. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, Proposed
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Proposed
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, Proposed
<1>6. CASE FakeAcceptorAction BY <1>6, SafeAcceptorAssumption DEF FakeAcceptorAction, FakeSend, Send, Proposed
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA 2avSentSpec3Invariant == Next /\ ConnectedSpec /\ 2avSentSpec3 => 2avSentSpec3'
PROOF
<1> SUFFICES ASSUME Next, ConnectedSpec, 2avSentSpec3,
             NEW L1 \in Learner, NEW L2 \in Learner, NEW A \in SafeAcceptor, NEW B \in Ballot,
             NEW V1 \in Value, NEW V2 \in Value,
             << L1, L2 >> \in Ent,
             [lr |-> L1, bal |-> B, val |-> V1] \in 2avSent'[A],
             [lr |-> L2, bal |-> B, val |-> V2] \in 2avSent'[A]
             PROVE V1 = V2
    BY DEF 2avSentSpec3
<1> USE DEF 2avSentSpec3
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Next, Send
<1>2. CASE AcceptorSendAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in SafeAcceptor,
                      NEW val \in Value,
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc, val)
                      \/ Phase2b(lrn, bal, acc, val)
               PROVE V1 = V2
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF Phase1b
  <2>2. CASE Phase2av(lrn, bal, acc, val)
    <3> SUFFICES
            ASSUME NEW v \in Value,
                   \A P \in { p \in 2avSent[acc] : p.bal = bal /\ << p.lr, lrn >> \in connected[acc] } : P.val = v,
                   2avSent' = [2avSent EXCEPT ![acc] =
                               2avSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> v] }]
            PROVE V1 = V2
        BY <2>2 DEF Phase2av
    <3>1. CASE A = acc
      <4>1. CASE /\ [lr |-> L1, bal |-> B, val |-> V1] \in 2avSent[A]
                 /\ [lr |-> L2, bal |-> B, val |-> V2] \in 2avSent[A]
            BY <4>1, <3>1
      <4>3. CASE /\ [lr |-> L1, bal |-> B, val |-> V1] \notin 2avSent[A]
                 /\ [lr |-> L2, bal |-> B, val |-> V2] \in 2avSent[A]
        <5>1. << L2, L1 >> \in Ent BY EntanglementSym
        <5>2. QED BY <4>3, <3>1, <5>1 DEF ConnectedSpec
      <4>2. CASE /\ [lr |-> L1, bal |-> B, val |-> V1] \in 2avSent[A]
                 /\ [lr |-> L2, bal |-> B, val |-> V2] \notin 2avSent[A]
            BY <4>2, <3>1 DEF ConnectedSpec
      <4>4. CASE /\ [lr |-> L1, bal |-> B, val |-> V1] \notin 2avSent[A]
                 /\ [lr |-> L2, bal |-> B, val |-> V2] \notin 2avSent[A]
            BY <4>4, <3>1
      <4>5. QED BY <4>1, <4>2, <4>3, <4>4
    <3>2. CASE A # acc BY <3>2
    <3>3. QED BY <3>1, <3>2
  <2>3. CASE Phase2b(lrn, bal, acc, val) BY <2>3 DEF Phase2b
  <2>5. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, Next
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Next
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, Next
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA DecisionSpecInvariant == TypeOK /\ Next /\ DecisionSpec => DecisionSpec'
PROOF
<1> SUFFICES ASSUME Next, TypeOK, DecisionSpec,
             NEW L \in Learner, NEW B \in Ballot, NEW V \in Value,
             V \in decision'[L, B]
             PROVE ChosenIn(L, B, V)'
    BY DEF DecisionSpec
<1> USE DEF DecisionSpec
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send, ChosenIn
<1>2. CASE AcceptorSendAction BY <1>2 DEF AcceptorSendAction, Phase1b, Phase2av, Phase2b, Send, ChosenIn
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, ChosenIn
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, ChosenIn
<1>5. CASE LearnerAction
  <2> SUFFICES ASSUME NEW lrn \in Learner, NEW bal \in Ballot,
                      \/ LearnerDecide(lrn, bal)
                      \/ LearnerRecv(lrn)
               PROVE ChosenIn(L, B, V)'
        BY <1>5 DEF LearnerAction
  <2>2. CASE LearnerDecide(lrn, bal)
    <3>0a. TypeOK OBVIOUS
    <3>0b. TypeOK' BY TypeOKInvariant
    <3>1. CASE V \in decision[L, B] BY <3>1, <2>2 DEF ChosenIn, LearnerDecide
    <3>2. CASE V \notin decision[L, B] BY <3>2, <2>2, <3>0a, <3>0b DEF ChosenIn, LearnerDecide, TypeOK
    <3>3. QED BY <3>1, <3>2
  <2>3. CASE LearnerRecv(lrn)
    <3>0. V \in decision[L, B] BY <2>3 DEF LearnerRecv
    <3>2. PICK Q \in ByzQuorum :
                        /\ [lr |-> L, q |-> Q] \in TrustLive
                        /\ \A aa \in Q :
                             \E m
                                \in {mm \in receivedByLearner[L] :
                                       mm.bal = B} :
                                /\ m.val = V
                                /\ m.acc = aa BY <3>0 DEF ChosenIn
    <3> USE DEF ChosenIn
    <3>3. WITNESS Q \in ByzQuorum
    <3>10. QED BY <3>2, ReceivedByLearnerMonotone
  <2>4. QED BY <2>2, <2>3 DEF LearnerAction
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send, ChosenIn
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA ConnectedSpecInvariant == Next /\ ConnectedSpec => ConnectedSpec'
PROOF
<1> SUFFICES ASSUME Next, ConnectedSpec,
                    NEW A \in SafeAcceptor,
                    NEW L1 \in Learner, NEW L2 \in Learner,
                    <<L1, L2>> \in Ent
             PROVE <<L1, L2>> \in connected'[A]
    BY DEF ConnectedSpec
<1> USE DEF ConnectedSpec
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Next
<1>2. CASE AcceptorSendAction BY <1>2 DEF AcceptorSendAction, Phase1b, Phase2b, Phase2av, Next
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, Next
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Next
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, Next
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA ConnectedMonotone ==
    Next => \A A \in SafeAcceptor : connected'[A] \subseteq connected[A]
PROOF
<1> SUFFICES ASSUME Next, NEW A \in SafeAcceptor PROVE connected'[A] \subseteq connected[A] OBVIOUS
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send
<1>2. CASE AcceptorSendAction BY <1>2 DEF AcceptorSendAction, Send, Phase1b, Phase2av, Phase2b
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, TypeOK
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerDecide, LearnerRecv
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA InitializedBallotInv ==
    Next =>
    \A L \in Learner : \A B \in Ballot :
        InitializedBallot(L, B) => InitializedBallot(L, B)'
PROOF BY MsgsMonotone DEF InitializedBallot

LEMMA AnnouncedValueInv ==
    Next =>
    \A L \in Learner : \A B \in Ballot : \A V \in Value :
        AnnouncedValue(L, B, V) => AnnouncedValue(L, B, V)'
PROOF BY MsgsMonotone DEF AnnouncedValue

LEMMA KnowsSafeAtInv ==
    TypeOK /\ Next =>
    \A L \in Learner : \A A \in SafeAcceptor : \A B \in Ballot : \A V \in Value :
        KnowsSafeAt(L, A, B, V) => KnowsSafeAt(L, A, B, V)'
PROOF
<1> SUFFICES ASSUME TypeOK, Next,
                    NEW L \in Learner, NEW A \in SafeAcceptor, NEW B \in Ballot, NEW V \in Value,
                    KnowsSafeAt(L, A, B, V)
             PROVE KnowsSafeAt(L, A, B, V)' OBVIOUS
<1>1. CASE KnowsSafeAt1(L, A, B)
      BY <1>1, ReceivedMonotone, ConnectedMonotone DEF KnowsSafeAt1, KnowsSafeAt
<1>2. CASE KnowsSafeAt2(L, A, B, V)
      BY <1>2, ReceivedMonotone, ConnectedMonotone DEF KnowsSafeAt2, KnowsSafeAt
<1>3. QED BY <1>1, <1>2 DEF KnowsSafeAt

LEMMA MsgInvInvariant ==
    TypeOK /\ MsgInv /\ VotesSentSpec1 /\ VotesSentSpec2 /\ VotesSentSpec3 /\ 2avSentSpec1 /\
    Next => MsgInv'
PROOF
<1> USE DEF MsgInv
<1>1b. ASSUME TypeOK, VotesSentSpec1, VotesSentSpec2, VotesSentSpec3, 2avSentSpec1, Next,
       \A m \in msgs : m.acc \in SafeAcceptor /\ m.type = "1b" => MsgInv1b(m),
       NEW m \in msgs', m.acc \in SafeAcceptor, m.type = "1b"
       PROVE MsgInv1b(m)'
  <2>0. TypeOK BY <1>1b
  <2>0a. TypeOK' BY <1>1b, TypeOKInvariant
  <2>0b. m \in Message BY <2>0a DEF TypeOK
  <2>0c. maxBal \in [Learner \X Acceptor -> Ballot] BY <1>1b DEF TypeOK
  <2>0d. maxBal' \in [Learner \X Acceptor -> Ballot] BY <2>0a DEF TypeOK
  <2>0e. m.type = "1b" BY <1>1b
  <2>0f. m.bal \in Ballot BY <2>0b, <2>0e DEF Message, Ballot
  <2>0g. maxBal[m.lr, m.acc] \in Ballot BY <2>0b, <2>0c, <2>0e DEF Message
  <2>0h. maxBal'[m.lr, m.acc] \in Ballot BY <2>0b, <2>0d, <2>0e DEF Message
  <2>0i. maxBal[m.lr, m.acc] =< maxBal'[m.lr, m.acc] BY <1>1b, <2>0b, MaxBalMonotone DEF TypeOK, Message
  <2>1. CASE ProposerAction
    <3> SUFFICES ASSUME NEW lrn \in Learner, NEW proposer \in Ballot, NEW val \in Value,
                        \/ Phase1a(lrn, proposer)
                        \/ Phase1c(lrn, proposer, val)
                 PROVE MsgInv1b(m)'
        BY <2>1, ValueNotEmpty DEF ProposerAction
    <3>1. CASE Phase1a(lrn, proposer)
      <4>1. m \in msgs BY <3>1, <2>0e DEF Phase1a, Send
      <4>2. QED BY <1>1b, <4>1, <3>1 DEF Phase1a, MsgInv1b, MaxVote
    <3>2. CASE Phase1c(lrn, proposer, val)
      <4>1. m \in msgs BY <3>2, <2>0e DEF Phase1c, Send, TypeOK
      <4>2. QED BY <1>1b, <4>1, <3>2 DEF Phase1c, MsgInv1b, MaxVote
    <3>3. QED BY <3>1, <3>2
  <2>2. CASE AcceptorSendAction
    <3> SUFFICES ASSUME NEW lrn \in Learner,
                        NEW bal \in Ballot,
                        NEW acc \in SafeAcceptor,
                        NEW val \in Value,
                        \/ Phase1b(lrn, bal, acc)
                        \/ Phase2av(lrn, bal, acc, val)
                        \/ Phase2b(lrn, bal, acc, val)
                 PROVE  MsgInv1b(m)'
      BY <2>2 DEF AcceptorSendAction
    <3>1. CASE Phase1b(lrn, bal, acc)
      <4>1. m.bal =< maxBal'[m.lr, m.acc]
        <5>6. CASE m \in msgs
          <6>0. m.bal =< maxBal[m.lr, m.acc] BY <1>1b, <5>6 DEF MsgInv1b
          <6>1. QED BY <6>0, <2>0i, <2>0g, <2>0h, <2>0b, BallotLeqTrans DEF Message
        <5>7. CASE m \notin msgs
          <6>0. m = [type |-> "1b", lr |-> lrn, acc |-> acc, bal |-> bal,
                     votes |-> {p \in votesSent[acc] : MaxVote(acc, bal, p)},
                     proposals |-> {p \in 2avSent[acc] : p.bal < bal /\ p.lr = lrn}]
                BY <3>1, <5>7 DEF Next, Phase1b, Send
          <6>3. SUFFICES bal =< maxBal'[lrn, acc] BY <6>0
          <6>4. maxBal' = [maxBal EXCEPT ![<<lrn, acc>>] = bal] BY <3>1 DEF Phase1b, Send
          <6>5. maxBal'[<<lrn, acc>>] = bal BY <6>4, <2>0c, <2>0d
          <6>6. QED BY <6>0, <6>5 DEF Ballot
        <5>8. QED BY <5>6, <5>7
      <4>5. (m.votes = { p \in votesSent[m.acc] : MaxVote(m.acc, m.bal, p) })'
        <5>1. CASE m \in msgs BY <1>1b, <3>1, <5>1 DEF MsgInv1b, Phase1b, MaxVote
        <5>2. CASE m \notin msgs
          <6>0. m = [type |-> "1b", lr |-> lrn, acc |-> acc, bal |-> bal,
                     votes |-> {p \in votesSent[acc] : MaxVote(acc, bal, p)},
                     proposals |-> {p \in 2avSent[acc] : p.bal < bal /\ p.lr = lrn}]
                BY <3>1, <5>2 DEF Phase1b, Send
          <6>2. QED BY <6>0, <3>1 DEF Phase1b, Send, MaxVote
        <5>3. QED BY <5>1, <5>2
      <4>6. (m.proposals = {p \in 2avSent[m.acc] : p.bal < m.bal /\ p.lr = m.lr})'
        <5>1. CASE m \in msgs BY <1>1b, <3>1, <5>1 DEF Phase1b, MsgInv1b
        <5>2. CASE m \notin msgs
          <6>0. m = [type |-> "1b", lr |-> lrn, acc |-> acc, bal |-> bal,
                     votes |-> {p \in votesSent[acc] : MaxVote(acc, bal, p)},
                     proposals |-> {p \in 2avSent[acc] :
                                    p.bal < bal /\ p.lr = lrn}] BY <3>1, <5>2 DEF Phase1b, Send
          <6>2. QED BY <6>0, <3>1 DEF Phase1b, Send
        <5>3. QED BY <5>1, <5>2
      <4>10. QED BY <4>1, <4>5, <4>6 DEF MsgInv1b
    <3>2. CASE Phase2av(lrn, bal, acc, val)
      <4> SUFFICES
            ASSUME maxBal[lrn, acc] =< bal,
                   Send([type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]),
                   2avSent' = [2avSent EXCEPT ![acc] =
                                 2avSent[acc] \cup {[lr |-> lrn, bal |-> bal, val |-> val]}]
                   PROVE MsgInv1b(m)'
            BY <3>2 DEF Phase2av
      <4>1. m \in msgs BY <2>0e DEF Send
      <4>1a. m.acc \in Acceptor BY <4>1, MessageType, <2>0e, <2>0 DEF TypeOK
      <4>2. (m.bal =< maxBal[m.lr, m.acc])' BY <1>1b, <4>1, <3>2 DEF Phase2av, Send, MsgInv1b
      <4>4. (m.votes = { p \in votesSent[m.acc] : MaxVote(m.acc, m.bal, p) })'
            BY <1>1b, <4>1, <3>2 DEF Phase2av, Send, MsgInv1b, MaxVote
      <4>5. (m.proposals = {p \in 2avSent[m.acc] : p.bal < m.bal /\ p.lr = m.lr})'
        <5>1. CASE m.acc # acc
          <6>1. 2avSent'[m.acc] = 2avSent[m.acc] BY <3>2, <4>1, <5>1, <2>0, <2>0e, MessageType DEF Phase2b, TypeOK
          <6>2. QED BY <6>1, <4>1, <1>1b, <2>0e DEF MsgInv1b
        <5>2. CASE m.acc = acc
          <6>1. m.bal =< maxBal[m.lr, m.acc] BY <1>1b, <4>1 DEF MsgInv1b
          <6>3. m.bal \in Ballot BY <2>0a, MessageType DEF TypeOK
          <6>5. SUFFICES {p \in 2avSent[acc] : p.bal < m.bal /\ p.lr = m.lr} =
                         {p \in 2avSent'[acc] : p.bal < m.bal /\ p.lr = m.lr}
                BY <4>1, <2>0e, <1>1b, <5>2 DEF MsgInv1b
          <6>6. SUFFICES ASSUME NEW p \in 2avSent'[acc], p.bal < m.bal, p.lr = m.lr
                         PROVE p \in 2avSent[acc] BY <2>0a, SafeAcceptorIsAcceptor DEF TypeOK
          <6>7. CASE p \in 2avSent[acc] BY <6>7
          <6>8. CASE p \notin 2avSent[acc]
            <7>1. p = [lr |-> lrn, bal |-> bal, val |-> val] BY <6>8, <2>0a, SafeAcceptorIsAcceptor DEF TypeOK
            <7>2. maxBal[m.lr, m.acc] =< bal BY <5>2, <7>1, <6>6
            <7>4. m.bal =< bal BY <6>1, <7>2, <6>3, <2>0g, BallotLeqTrans
            <7>10. QED BY <7>1, <7>4, <6>6, <6>3, BallotLeNotLeq
          <6>10. QED BY <6>7, <6>8
        <5>3. QED BY <5>1, <5>2
      <4>10. QED BY <4>2, <4>4, <4>5 DEF MsgInv1b
    <3>3. CASE Phase2b(lrn, bal, acc, val)
      <4> SUFFICES
            ASSUME \A L \in Learner : maxBal[L, acc] =< bal,
                   Send([type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]),
                   votesSent' = [votesSent EXCEPT
                                    ![acc] = votesSent[acc] \cup {[lr |-> lrn, bal |-> bal, val |-> val]}]
            PROVE MsgInv1b(m)'
            BY <3>3 DEF Phase2b
      <4>1. m \in msgs BY <2>0e DEF Send
      <4>1a. m.acc \in Acceptor BY <4>1, MessageType, <2>0e, <2>0 DEF TypeOK
      <4>2. (m.bal =< maxBal[m.lr, m.acc])' BY <4>1, <1>1b, <3>3 DEF Phase2b, MsgInv1b
      <4>4. (m.proposals = {p \in 2avSent[m.acc] : p.bal < m.bal /\ p.lr = m.lr})'
            BY <4>1, <1>1b, <3>3 DEF Phase2b, MsgInv1b
      <4>5. (m.votes = { p \in votesSent[m.acc] : MaxVote(m.acc, m.bal, p) })'
          <5>1. CASE m.acc # acc
            <6>1. votesSent'[m.acc] = votesSent[m.acc] BY <3>3, <4>1, <5>1, <2>0, <2>0e, MessageType DEF Phase2b, TypeOK
            <6>2. QED BY <6>1, <4>1, <1>1b, <2>0e DEF MsgInv1b, MaxVote
          <5>2. CASE m.acc = acc
            <6>1. m.bal =< maxBal[m.lr, m.acc] BY <1>1b, <4>1 DEF MsgInv1b
            <6>2. maxBal[m.lr, m.acc] =< bal BY <2>0a, <2>0e, <5>2, MessageType DEF Ballot, TypeOK
            <6>3. m.bal \in Ballot BY <2>0a, MessageType DEF TypeOK
            <6>4. m.bal =< bal BY <6>1, <6>2, <6>3, <2>0g, BallotLeqTrans
            <6>5. SUFFICES {p \in votesSent[acc] : MaxVote(acc, m.bal, p)} =
                           {p \in votesSent'[acc] : MaxVote(acc, m.bal, p)'}
                  BY <4>1, <2>0e, <1>1b, <5>2 DEF MsgInv1b
            <6>6. {p \in votesSent[acc] : MaxVote(acc, m.bal, p)} \subseteq
                  {p \in votesSent'[acc] : MaxVote(acc, m.bal, p)'}
              <7>1. SUFFICES ASSUME NEW p \in votesSent[acc], MaxVote(acc, m.bal, p)
                             PROVE MaxVote(acc, m.bal, p)'
                    BY <2>0, <1>1b, VotesSentMonotone, SafeAcceptorIsAcceptor
              <7>2. SUFFICES ASSUME NEW other \in votesSent'[acc],
                                    other.lr = p.lr /\ other.bal < m.bal
                             PROVE other.bal =< p.bal BY <7>1 DEF MaxVote
              <7>3. CASE other \in votesSent[acc] BY <7>1, <7>2, <7>3 DEF MaxVote
              <7>4. CASE other \notin votesSent[acc]
                <8>1. other = [lr |-> lrn, bal |-> bal, val |-> val]
                      BY <7>2, <7>4, <2>0a, SafeAcceptorIsAcceptor DEF TypeOK
                <8>10. QED BY <8>1, <7>2, <6>4, <6>3, BallotLeNotLeq
              <7>5. QED BY <7>3, <7>4
            <6>7. {p \in votesSent'[acc] : MaxVote(acc, m.bal, p)'} \subseteq
                  {p \in votesSent[acc] : MaxVote(acc, m.bal, p)}
               <7>1. SUFFICES ASSUME NEW p \in votesSent'[acc],
                                     MaxVote(acc, m.bal, p)',
                                     p \notin votesSent[acc]
                              PROVE FALSE
                     BY <2>0a, SafeAcceptorIsAcceptor DEF TypeOK, MaxVote
               <7>2. p = [lr |-> lrn, bal |-> bal, val |-> val]
                     BY <7>1, <5>2, <2>0a, SafeAcceptorIsAcceptor DEF TypeOK
               <7>3. QED BY <7>2, <7>1, <6>4, <6>3, BallotLeNotLeq DEF MaxVote
            <6>8. QED BY <6>6, <6>7
          <5>3. QED BY <5>1, <5>2
      <4>6. QED BY <4>2, <4>4, <4>5 DEF MsgInv1b
    <3>4. QED BY <3>1, <3>2, <3>3
  <2>4. CASE AcceptorReceiveAction BY <1>1b, <2>4 DEF AcceptorReceiveAction, Recv, MsgInv1b, MaxVote
  <2>5. CASE AcceptorDisconnectAction
        BY <2>5, <1>1b DEF AcceptorDisconnectAction, Disconnect, MaxVote, MsgInv1b
  <2>6. CASE LearnerAction BY <1>1b, <2>6 DEF LearnerAction, LearnerRecv, LearnerDecide, MsgInv1b, MaxVote
  <2>7. CASE FakeAcceptorAction
    <3>0. m \in msgs BY <1>1b, <2>7, SafeAcceptorAssumption DEF FakeAcceptorAction, FakeSend, Send
    <3>10. QED BY <3>0, <1>1b, <2>7 DEF MsgInv1b, MaxVote, FakeAcceptorAction, FakeSend
  <2>8. QED BY <1>1b, <2>0a, <2>1, <2>2, <2>4, <2>5, <2>6, <2>7 DEF Next
<1>2av. ASSUME TypeOK, Next,
               \A m \in msgs : m.acc \in SafeAcceptor /\ m.type = "2av" => MsgInv2av(m),
               NEW m \in msgs', m.acc \in SafeAcceptor, m.type = "2av"
        PROVE MsgInv2av(m)'
  <2>0a. TypeOK BY <1>2av
  <2>0b. TypeOK' BY <1>2av, TypeOKInvariant
  <2>0e. m.type = "2av" BY <1>2av
  <2>1. CASE ProposerAction
    <3>0. m \in msgs BY <1>2av, <2>1, <2>0e DEF ProposerAction, Phase1a, Phase1c, MsgInv2av, Next, Send
    <3>1. QED BY <1>2av, <3>0, <2>1, <2>0e DEF ProposerAction, Phase1a, Phase1c, MsgInv2av, Next, Send
  <2>2. CASE AcceptorSendAction
    <3> SUFFICES ASSUME NEW lrn \in Learner,
                        NEW bal \in Ballot,
                        NEW acc \in SafeAcceptor,
                        NEW val \in Value,
                        \/ Phase1b(lrn, bal, acc)
                        \/ Phase2av(lrn, bal, acc, val)
                        \/ Phase2b(lrn, bal, acc, val)
                 PROVE  MsgInv2av(m)'
      BY <2>2 DEF AcceptorSendAction
    <3>1. CASE Phase1b(lrn, bal, acc)
      <4>1. m \in msgs BY <3>1, <2>0e, <2>0b DEF Phase1b, Send, TypeOK
      <4>2. QED BY <1>2av, <4>1, <3>1 DEF Phase1b, MsgInv2av, Send
    <3>2. CASE Phase2av(lrn, bal, acc, val)
      <4> SUFFICES
            ASSUME AnnouncedValue(lrn, bal, val),
                   KnowsSafeAt(lrn, acc, bal, val),
                   Send([type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]),
                   2avSent' = [2avSent EXCEPT ![acc] =
                                2avSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> val] }],
                   UNCHANGED received
                PROVE MsgInv2av(m)'
            BY <3>2 DEF Phase2av
      <4>1. CASE m \in msgs
        <5>1. InitializedBallot(m.lr, m.bal)' BY <4>1, <2>0e, <1>2av, MsgsMonotone DEF MsgInv2av, InitializedBallot
        <5>2. AnnouncedValue(m.lr, m.bal, m.val)'
            BY <4>1, <2>0e, <1>2av, MsgsMonotone DEF MsgInv2av, AnnouncedValue, TypeOK
        <5>3. KnowsSafeAt(m.lr, m.acc, m.bal, m.val)' BY <4>1, <1>2av DEF Phase2av, MsgInv2av
        <5>4. [lr |-> m.lr, bal |-> m.bal, val |-> m.val] \in 2avSent'[m.acc]
            BY <4>1, <2>0e, <1>2av, 2avSentMonotone, MessageType DEF MsgInv2av, TypeOK
        <5>5. (\E Q \in ByzQuorum :
              /\ [lr |-> m.lr, q |-> Q] \in TrustLive
              /\ \A ba \in Q :
                    \E m1b \in received[m.acc] :
                       /\ m1b.type = "1b"
                       /\ m1b.lr = m.lr
                       /\ m1b.acc = ba
                       /\ m1b.bal = m.bal)'
              BY <4>1, <2>0e, <1>2av, 2avSentMonotone, MessageType DEF MsgInv2av, TypeOK
        <5>6. QED BY <5>1, <5>2, <5>3, <5>4, <5>5 DEF MsgInv2av
      <4>2. CASE m \notin msgs
        <5>1. m = [type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val] BY <4>2 DEF Send
        <5>3. InitializedBallot(m.lr, m.bal)' BY <5>1, <3>2 DEF Phase2av
        <5>4. AnnouncedValue(m.lr, m.bal, m.val)' BY <5>1
        <5>5. KnowsSafeAt(m.lr, m.acc, m.bal, m.val)' BY <5>1
        <5>6. ([lr |-> m.lr, bal |-> m.bal, val |-> m.val] \in 2avSent[m.acc])' BY <5>1, <2>0b DEF TypeOK
        <5>7. (\E Q \in ByzQuorum :
              /\ [lr |-> m.lr, q |-> Q] \in TrustLive
              /\ \A ba \in Q :
                    \E m1b \in received[m.acc] :
                       /\ m1b.type = "1b"
                       /\ m1b.lr = m.lr
                       /\ m1b.acc = ba
                       /\ m1b.bal = m.bal)'
          <6>1. CASE KnowsSafeAt1(lrn, acc, bal)
            <7>1. PICK Q1 \in ByzQuorum :
                        /\ [lr |-> lrn, q |-> Q1] \in TrustLive
                        /\ \A a \in Q1 :
                            \E m1b \in received[acc] :
                                /\ m1b.type = "1b"
                                /\ m1b.lr = lrn
                                /\ m1b.bal = bal
                                /\ m1b.acc = a
                  BY <6>1 DEF KnowsSafeAt1
            <7>2. WITNESS Q1 \in ByzQuorum
            <7>3. QED BY <7>1, <5>1
          <6>2. CASE KnowsSafeAt2(lrn, acc, bal, val)
            <7>1. PICK Q2 \in ByzQuorum :
                        /\ [lr |-> lrn, q |-> Q2] \in TrustLive
                        /\ \A a \in Q2 :
                            \E m1b \in received[acc] :
                                /\ m1b.type = "1b"
                                /\ m1b.lr = lrn
                                /\ m1b.bal = bal
                                /\ m1b.acc = a
                  BY <6>2 DEF KnowsSafeAt2
            <7>2. WITNESS Q2 \in ByzQuorum
            <7>3. QED BY <7>1, <5>1
          <6>3. QED BY <6>1, <6>2 DEF KnowsSafeAt
        <5>8. QED BY <5>1, <5>3, <5>4, <5>5, <5>6, <5>7, MessageType DEF MsgInv2av, TypeOK
      <4>20. QED BY <4>1, <4>2
    <3>3. CASE Phase2b(lrn, bal, acc, val)
      <4>1. m \in msgs BY <3>3, <2>0e DEF Phase2b, Send
      <4>2. QED BY <1>2av, <4>1, <3>3 DEF Phase2b, MsgInv2av, Send
    <3>4. QED BY <3>1, <3>2, <3>3
  <2>4. CASE AcceptorReceiveAction
    <3>1. m \in msgs BY <2>4 DEF AcceptorReceiveAction, Recv
    <3>6. (\E Q \in ByzQuorum :
              /\ [lr |-> m.lr, q |-> Q] \in TrustLive
              /\ \A ba \in Q :
                    \E m1b \in received[m.acc] :
                       /\ m1b.type = "1b"
                       /\ m1b.lr = m.lr
                       /\ m1b.acc = ba
                       /\ m1b.bal = m.bal)'
      <7>1. PICK Q0 \in ByzQuorum :
              /\ [lr |-> m.lr, q |-> Q0] \in TrustLive
              /\ \A ba \in Q0 :
                     \E m1b \in received[m.acc] :
                        /\ m1b.type = "1b"
                        /\ m1b.lr = m.lr
                        /\ m1b.acc = ba
                        /\ m1b.bal = m.bal
            BY <1>2av, <3>1, <2>0e DEF MsgInv2av
      <7>2. WITNESS Q0 \in ByzQuorum
      <7>3. QED BY <1>2av, <7>1, ReceivedMonotone, MessageType, <3>1 DEF MsgInv2av, TypeOK
    <3>20. QED BY <1>2av, <2>4, <3>6, MessageType, ReceivedMonotone DEF MsgInv2av, AcceptorReceiveAction, Recv
  <2>5. CASE AcceptorDisconnectAction BY <1>2av, <2>5 DEF AcceptorDisconnectAction, Disconnect, MsgInv2av, Next
  <2>6. CASE LearnerAction BY <1>2av, <2>6 DEF LearnerAction, LearnerRecv, LearnerDecide, MsgInv2av, Next
  <2>7. CASE FakeAcceptorAction
            BY <1>2av, <2>7, SafeAcceptorAssumption DEF FakeAcceptorAction, FakeSend, MsgInv2av, Send
  <2>8. QED BY <1>2av, <2>0b, <2>1, <2>2, <2>4, <2>5, <2>6, <2>7 DEF Next
<1>2b. ASSUME TypeOK, Next, \A m \in msgs : m.acc \in SafeAcceptor /\ m.type = "2b" => MsgInv2b(m),
        NEW m \in msgs', m.acc \in SafeAcceptor, m.type = "2b"
        PROVE MsgInv2b(m)'
  <2>0a. TypeOK BY <1>2b
  <2>0b. TypeOK' BY <1>2b, TypeOKInvariant
  <2>0c. m \in Message BY <2>0b DEF TypeOK
  <2>0d. m.acc \in SafeAcceptor BY <1>2b
  <2>0e. m.type = "2b" BY <1>2b
  <2>1. CASE ProposerAction
    <3>1. m \in msgs BY <2>1, <2>0e DEF ProposerAction, Phase1a, Phase1c, Send
    <3>10. QED BY <1>2b, <2>1, <2>0a, <2>0b, <2>0d, <2>0e, <3>1
               DEF TypeOK, ProposerAction, Phase1a, Phase1c, MsgInv2b, Next, Send
  <2>2. CASE AcceptorSendAction
    <3> HIDE DEF Next
    <3> SUFFICES ASSUME NEW lrn \in Learner,
                        NEW bal \in Ballot,
                        NEW acc \in SafeAcceptor,
                        NEW val \in Value,
                        \/ Phase1b(lrn, bal, acc)
                        \/ Phase2av(lrn, bal, acc, val)
                        \/ Phase2b(lrn, bal, acc, val)
                 PROVE MsgInv2b(m)'
        BY <2>2 DEF AcceptorSendAction
    <3>1. CASE Phase1b(lrn, bal, acc)
      <4>1. m \in msgs BY <3>1, <2>0a, <2>0e DEF Phase1b, Send, TypeOK
      <4>2. QED BY <1>2b, <3>1, <2>0a, <2>0b, <2>0e, <4>1 DEF Phase1b, MsgInv2b, Send, TypeOK
    <3>2. CASE Phase2av(lrn, bal, acc, val)
      <4>1. m \in msgs BY <3>2, <2>0a, <2>0e DEF Phase2av, Send, TypeOK
      <4>2. QED BY <1>2b, <3>2, <2>0a, <2>0d, <2>0e, <4>1 DEF Phase2av, MsgInv2b, Send, TypeOK
    <3>3. CASE Phase2b(lrn, bal, acc, val)
      <4>1. CASE m \in msgs
        <5>1. ([lr |-> m.lr, bal |-> m.bal, val |-> m.val] \in votesSent[m.acc])'
          BY <1>2b, <2>0e, <4>1, MessageType, VotesSentMonotone DEF MsgInv2b, TypeOK
        <5>2. (\E Q \in ByzQuorum :
                /\ [lr |-> m.lr, q |-> Q] \in TrustLive
                /\ \A ba \in Q :
                    \E m2av \in received[m.acc] :
                        /\ m2av.type = "2av"
                        /\ m2av.lr = m.lr
                        /\ m2av.acc = ba
                        /\ m2av.bal = m.bal
                        /\ m2av.val = m.val)'
              BY <1>2b, <3>3, <2>0a, <2>0b, <2>0d, <2>0e, <4>1 DEF Phase2b, MsgInv2b, Send, TypeOK
        <5>3. QED BY <5>1, <5>2 DEF MsgInv2b
      <4>2. CASE m \notin msgs
        <5> SUFFICES
            ASSUME NEW Q \in ByzQuorum,
                   [lr |-> lrn, q |-> Q] \in TrustLive,
                   \A aa \in Q :
                        \E m_1 \in {mm \in received[acc] :
                                      /\ mm.type = "2av"
                                      /\ mm.lr = lrn
                                      /\ mm.bal = bal} :
                              /\ m_1.val = val
                              /\ m_1.acc = aa,
                   Send([type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]),
                   votesSent' = [votesSent EXCEPT ![acc] =
                                    votesSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> val] }]
                   PROVE MsgInv2b(m)'
              BY <3>3 DEF Phase2b
        <5>1. m = [type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val] BY <4>2 DEF Send
        <5>1e. UNCHANGED received BY <3>3 DEF Phase2b
        <5>2. ([lr |-> m.lr, bal |-> m.bal, val |-> m.val] \in votesSent[m.acc])'
            BY <5>1, <2>0a, <2>0b, <2>0e, MessageType DEF TypeOK
        <5>3. (\E Q_1 \in ByzQuorum :
              /\ [lr |-> m.lr, q |-> Q_1] \in TrustLive
              /\ \A ba \in Q_1 :
                    \E m2av \in received[m.acc] :
                       /\ m2av.type = "2av"
                       /\ m2av.lr = m.lr
                       /\ m2av.acc = ba
                       /\ m2av.bal = m.bal
                       /\ m2av.val = m.val)'
          <6>1. WITNESS Q \in ByzQuorum
          <6>2. QED BY <5>1, <5>1e, <2>0a DEF Send, TypeOK
        <5>4. QED BY <5>2, <5>3 DEF MsgInv2b
      <4>3. QED BY <4>1, <4>2
    <3>5. QED BY <3>1, <3>2, <3>3
  <2>4. CASE AcceptorReceiveAction
    <3>0. SUFFICES ASSUME NEW lrn \in Learner,
                          NEW acc \in Acceptor,
                          NEW m0 \in msgs,
                          received' = [received EXCEPT ![acc] = received[acc] \cup { m0 }],
                          UNCHANGED << msgs, maxBal, 2avSent, votesSent, connected,
                                         receivedByLearner, decision >>
                   PROVE  MsgInv2b(m)'
      BY <2>4, <2>0b DEF AcceptorReceiveAction, Recv, TypeOK
    <3>2. m \in msgs BY <3>0, <1>2b
    <3>2a. m \in Message BY <3>2, <1>2b DEF TypeOK
    <3>2b. TypeOK BY <1>2b DEF Phase2b
    <3>2c. TypeOK' BY <1>2b, <3>2b, TypeOKInvariant
    <3>3. [lr |-> m.lr, bal |-> m.bal, val |-> m.val] \in votesSent'[m.acc] BY <3>0, <1>2b DEF MsgInv2b
    <3>5. PICK Q0 \in ByzQuorum :
           /\ [lr |-> m.lr, q |-> Q0] \in TrustLive
           /\ \A ba \in Q0 :
                 \E m2av \in received[m.acc] :
                    /\ m2av.type = "2av"
                    /\ m2av.lr = m.lr
                    /\ m2av.acc = ba
                    /\ m2av.bal = m.bal
                    /\ m2av.val = m.val BY <1>2b, <2>0e, <3>2 DEF MsgInv2b
    <3>7. (\E Q \in ByzQuorum :
            /\ [lr |-> m.lr, q |-> Q] \in TrustLive
            /\ \A ba \in Q :
                \E m2av \in received[m.acc] :
                    /\ m2av.type = "2av"
                    /\ m2av.lr = m.lr
                    /\ m2av.acc = ba
                    /\ m2av.bal = m.bal
                    /\ m2av.val = m.val)'
        <4>0. WITNESS Q0 \in ByzQuorum
        <4>1. QED BY <1>2b, <3>5, <3>2b, <3>2c, MessageType, ReceivedMonotone DEF TypeOK
    <3>8. QED BY <3>3, <3>7 DEF MsgInv2b
  <2>5. CASE AcceptorDisconnectAction BY <1>2b, <2>5 DEF AcceptorDisconnectAction, Disconnect, MsgInv2b, Next
  <2>6. CASE LearnerAction BY <1>2b, <2>6 DEF LearnerAction, LearnerRecv, LearnerDecide, MsgInv2b, Next
  <2>7. CASE FakeAcceptorAction
        BY <1>2b, <2>7, SafeAcceptorAssumption DEF FakeAcceptorAction, FakeSend, MsgInv2b, Send
  <2>8. QED BY <1>2b, <2>0a, <2>1, <2>2, <2>4, <2>5, <2>6, <2>7 DEF Next
<1>3. QED BY <1>1b, <1>2av, <1>2b

CannotDecide(Q, L, B, V) ==
    \E A \in SafeAcceptor :
        /\ A \in Q
        /\ \E L0 \in Learner : LeftBallot(L0, A, B) \* TODO: check if used
        /\ ~VotedFor(L, A, B, V)

HeterogeneousSpec ==
    \A L1, L2 \in Learner :
    \A B1, B2 \in Ballot :
    \A V1, V2 \in Value :
    \A A2 \in SafeAcceptor :
    \A Q \in ByzQuorum :
    \A M \in msgs :
        /\ <<L1, L2>> \in Ent
        /\ [lr |-> L1, q |-> Q] \in TrustLive
        /\ M.type = "2av" /\ M.lr = L2 /\ M.acc = A2 /\ M.bal = B2 /\ M.val = V2
        /\ B1 < B2
        /\ V1 # V2
        =>
        CannotDecide(Q, L1, B1, V1)

LEMMA HeterogeneousSpecInvariant ==
    TypeOK /\ Next /\ ReceivedSpec /\
    2avSentSpec1 /\
    VotesSentSpec2 /\ VotesSentSpec3 /\ VotesSentSpec4 /\
    ConnectedSpec /\ MsgInv /\
    HeterogeneousSpec => HeterogeneousSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, Next, ReceivedSpec, 2avSentSpec1, VotesSentSpec2, VotesSentSpec3, VotesSentSpec4,
                    ConnectedSpec, MsgInv, HeterogeneousSpec,
                    NEW L1 \in Learner, NEW L2 \in Learner,
                    NEW B1 \in Ballot, NEW B2 \in Ballot,
                    NEW V1 \in Value, NEW V2 \in Value,
                    NEW A2 \in SafeAcceptor,
                    NEW Q1 \in ByzQuorum,
                    NEW m \in msgs',
                    <<L1, L2>> \in Ent,
                    [lr |-> L1, q |-> Q1] \in TrustLive,
                    m.type = "2av", m.lr = L2, m.acc = A2, m.bal = B2, m.val = V2,
                    B1 < B2,
                    V1 # V2
             PROVE CannotDecide(Q1, L1, B1, V1)'
    BY DEF HeterogeneousSpec
<1> USE DEF MsgInv
<1>0a. TypeOK OBVIOUS
<1>0b. TypeOK' BY TypeOKInvariant
<1>0c. m \in Message BY <1>0b DEF TypeOK
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Next, Send, HeterogeneousSpec
<1>2. CASE AcceptorSendAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in SafeAcceptor,
                      NEW val \in Value,
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc, val)
                      \/ Phase2b(lrn, bal, acc, val)
               PROVE CannotDecide(Q1, L1, B1, V1)'
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc)
    <3>1. m \in msgs BY <2>1, <1>0b DEF Phase1b, Send, TypeOK, Message
    <3>2. QED BY <3>1 DEF HeterogeneousSpec
  <2>2. CASE Phase2av(lrn, bal, acc, val)
    <3>0. msgs \subseteq msgs' BY <2>2 DEF Phase2av, Send
    <3>1. CASE m \in msgs BY <3>1 DEF HeterogeneousSpec
    <3>2. CASE m \notin msgs
      <4>0. m = [type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]
             BY <3>2, <2>2 DEF Phase2av, Send
      <4>0a. lrn = L2 /\ acc = A2 /\ bal = B2 /\ val = V2 BY <4>0
      <4>1. maxBal[L2, A2] =< B2 BY <2>2, <4>0a DEF Phase2av
      <4>2. KnowsSafeAt(L2, A2, B2, V2) BY <2>2, <4>0a DEF Phase2av
      <4>3a. CASE KnowsSafeAt1(L2, A2, B2)
        <5>0. USE DEF CannotDecide
        <5>1. PICK Q2 \in ByzQuorum :
            /\ [lr |-> L2, q |-> Q2] \in TrustLive
            /\ \A a \in Q2 :
                \E m1b \in received[A2] :
                    /\ m1b.type = "1b"
                    /\ m1b.lr = L2
                    /\ m1b.bal = B2
                    /\ m1b.acc = a
                    /\ \A p \in {pp \in m1b.votes : <<pp.lr, L2>> \in connected[A2]} :
                            B2 =< p.bal
            BY <4>3a DEF KnowsSafeAt1
        <5>2. PICK S \in SafeAcceptor : S \in Q1 /\ S \in Q2 BY EntanglementTrustLive, <4>0, <5>1
        <5>3. PICK m1b \in received[A2] :
                    /\ m1b.type = "1b"
                    /\ m1b.lr = L2
                    /\ m1b.bal = B2
                    /\ m1b.acc = S
                    /\ \A p \in {pp \in m1b.votes : <<pp.lr, L2>> \in connected[A2]} :
                            B2 =< p.bal
              BY <5>1, <5>2
        <5>4. /\ m1b \in msgs
              /\ m1b.type = "1b"
              /\ m1b.lr = L2
              /\ m1b.bal = B2
              /\ m1b.acc = S
              /\ \A p \in {pp \in m1b.votes : <<pp.lr, L2>> \in connected[A2]} :
                    B2 =< p.bal
              BY <5>3, SafeAcceptorIsAcceptor DEF TypeOK, ReceivedSpec
        <5>5. WITNESS S \in SafeAcceptor
        <5>6. \E L \in Learner : LeftBallot(L, S, B1)' BY <5>4, <3>0 DEF LeftBallot
        <5>7. ~VotedFor(L1, S, B1, V1)'
          <6>1. SUFFICES ASSUME VotedFor(L1, S, B1, V1)' PROVE FALSE OBVIOUS
          <6>1a. VotedFor(L1, S, B1, V1) BY <6>1, <3>2, <2>2 DEF VotedFor, Phase2av, Send
          <6>2. [lr |-> L1, bal |-> B1, val |-> V1] \in votesSent[S] BY <6>1a DEF VotesSentSpec2
          <6>3. m1b.votes = { p \in votesSent[S] : MaxVote(S, B2, p) } BY <5>4 DEF MsgInv1b
          <6>4. PICK P \in votesSent[S] : MaxVote(S, B2, P) /\ P.lr = L1 /\ B1 =< P.bal
            <7>1. SUFFICES ASSUME NEW P0 \in votesSent[S],
                           P0 = [lr |-> L1, bal |-> B1, val |-> V1]
                           PROVE \E P \in votesSent[S] : MaxVote(S, B2, P) /\ P.lr = P0.lr /\ P0.bal =< P.bal
                  BY <6>2
            <7>2. P0.bal < B2 BY <7>1
            <7>3. QED BY <7>1, <7>2 DEF VotesSentSpec3
          <6>5. P \in m1b.votes BY <6>3, <6>4
          <6>6. <<P.lr, L2>> \in connected[A2] BY <6>4 DEF ConnectedSpec
          <6>7. B2 =< P.bal BY <6>5, <6>6, <5>4
          <6>8. P \in [lr : Learner, bal : Ballot, val : Value] BY <6>4, SafeAcceptorIsAcceptor DEF TypeOK
          <6>9. P.bal \in Ballot BY <6>8
          <6>10. QED BY <6>9, <6>7, <6>4, BallotLeNotLeq DEF MaxVote
        <5>8. QED BY <5>2, <5>6, <5>7
      <4>3b. CASE KnowsSafeAt2(L2, A2, B2, V2)
        <5>1. PICK c \in Ballot, BQ \in ByzQuorum, WQ \in ByzQuorum :
                    /\ c < B2
                    /\ [lr |-> L2, q |-> BQ] \in TrustLive
                    /\ \A a \in BQ :
                        \E m1 \in {mm \in received[A2] : mm.type = "1b" /\ mm.lr = L2 /\ mm.bal = B2} :
                            /\ m1.acc = a
                            /\ \A p \in {pp \in m1.votes : <<pp.lr, L2>> \in connected[A2]} :
                                /\ p.bal =< c
                                /\ (p.bal = c) => (p.val = V2)
                    /\ [lr |-> L2, q |-> WQ] \in TrustLive
                    /\ \A a \in WQ :
                        \E m2 \in {mm \in received[A2] : mm.type = "1b" /\ mm.lr = L2 /\ mm.bal = B2} :
                            /\ m2.acc = a
                            /\ \E p \in m2.proposals :
                                /\ p.lr = L2
                                /\ p.bal = c
                                /\ p.val = V2
              BY <4>3b, <4>0a DEF KnowsSafeAt2, Ballot
        <5>2. PICK S1 \in SafeAcceptor : S1 \in Q1 /\ S1 \in BQ BY EntanglementTrustLive, <4>0, <5>1
        <5>4. PICK m1 \in received[A2] :
                    /\ m1.type = "1b"
                    /\ m1.lr = L2
                    /\ m1.bal = B2
                    /\ m1.acc = S1
                    /\ \A p \in {pp \in m1.votes : <<pp.lr, L2>> \in connected[A2]} :
                            /\ p.bal =< c
                            /\ p.bal = c => p.val = V2
              BY <5>1, <5>2
        <5>5. /\ m1 \in msgs
              /\ m1.type = "1b"
              /\ m1.lr = L2
              /\ m1.bal = B2
              /\ m1.acc = S1
              /\ \A p \in {pp \in m1.votes : <<pp.lr, L2>> \in connected[A2]} :
                    /\ p.bal =< c
                    /\ p.bal = c => p.val = V2
              BY <5>4, SafeAcceptorIsAcceptor DEF TypeOK, ReceivedSpec
        <5>6. CASE ~VotedFor(L1, S1, B1, V1)
          <6>1. ~VotedFor(L1, S1, B1, V1)' BY <5>6, <3>2, <2>2 DEF VotedFor, Phase2av, Send
          <6>2. QED BY <6>1, <5>2, <5>5, MsgsMonotone DEF LeftBallot, CannotDecide
        <5>7. CASE VotedFor(L1, S1, B1, V1)
          <6>1. [lr |-> L1, bal |-> B1, val |-> V1] \in votesSent[S1] BY <5>7 DEF VotesSentSpec2
          <6>2. PICK P \in votesSent[S1] : MaxVote(S1, B2, P) /\ P.lr = L1 /\ B1 =< P.bal
            <7>1. SUFFICES ASSUME NEW vote \in votesSent[S1], vote = [lr |-> L1, bal |-> B1, val |-> V1]
                           PROVE \E P \in votesSent[S1] : MaxVote(S1, B2, P) /\ P.lr = L1 /\ vote.bal =< P.bal
                           BY <6>1
            <7>2. QED BY <7>1, SafeAcceptorIsAcceptor DEF VotesSentSpec3, TypeOK
          <6>3. P \in m1.votes BY <6>2, <5>5 DEF MsgInv1b
          <6>4. <<P.lr, L2>> \in connected[A2] BY <5>5, <6>2 DEF ConnectedSpec
          <6>5. P.bal \in Ballot BY <5>5, <6>3, SafeAcceptorIsAcceptor, MessageType DEF TypeOK
          <6>6. B1 < c
            <7>1. CASE P.val = V1
              <8>1. P.bal =< c /\ (P.bal = c => P.val = V2) BY <5>5, <6>3, <6>4
              <8>2. P.bal < c BY <6>5, <8>1, <7>1 DEF Ballot
              <8>10. QED BY <6>2, <6>5, <8>2, BallotLeqLeTrans
            <7>2. CASE P.val # V1
              <8>1. B1 < P.bal
                <9>0. <<L1, L1>> \in Ent BY EntanglementSelf
                <9>1. B1 <= P.bal BY <6>2
                <9>2. B1 # P.bal BY <6>1, <6>2, <6>5, <7>2, <9>0 DEF VotesSentSpec4
                <9>3. QED BY <6>5, <9>1, <9>2 DEF Ballot
              <8>2. P.bal =< c BY <5>5, <6>3, <6>4
              <8>3. QED BY <8>1, <8>2, <6>5, BallotLeLeqTrans
            <7>3. QED BY <7>1, <7>2
          <6>7. PICK S2 \in SafeAcceptor : S2 \in Q1 /\ S2 \in WQ BY EntanglementTrustLive, <4>0, <5>1
          <6>8. PICK m2 \in received[A2] :
                      /\ m2.type = "1b"
                      /\ m2.lr = L2
                      /\ m2.bal = B2
                      /\ m2.acc = S2
                      /\ \E p \in m2.proposals : p.lr = L2 /\ p.bal = c /\ p.val = V2
                BY <5>1, <6>7
          <6>9. PICK p2 \in m2.proposals :
                      /\ m2 \in msgs
                      /\ m2.type = "1b"
                      /\ m2.lr = L2
                      /\ m2.bal = B2
                      /\ m2.acc = S2
                      /\ p2.lr = L2
                      /\ p2.bal = c
                      /\ p2.val = V2
              BY <6>8, SafeAcceptorIsAcceptor DEF TypeOK, ReceivedSpec
          <6>10. Proposed(L2, S2, c, V2)
            <7>1. p2 \in 2avSent[S2] BY <6>9 DEF MsgInv1b
            <7>2. QED BY <7>1, <6>9 DEF 2avSentSpec1
          <6>11. PICK m2av \in msgs :
                    /\ m2av.type = "2av"
                    /\ m2av.lr =  L2
                    /\ m2av.acc = S2
                    /\ m2av.bal = c
                    /\ m2av.val = V2
                 BY <6>10 DEF Proposed
          <6>12. SUFFICES CannotDecide(Q1, L1, B1, V1) BY DEF CannotDecide
          <6>15. QED BY <6>11, <6>6 DEF HeterogeneousSpec
        <5>8. QED BY <5>6, <5>7
      <4>4. QED BY <4>3a, <4>3b, <4>2 DEF KnowsSafeAt
    <3>3. QED BY <3>1, <3>2
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3>1. m \in msgs BY Isa, <2>3, <1>0b, <1>0a DEF Phase2b, Send, TypeOK
    <3>2. QED BY <3>1 DEF HeterogeneousSpec
  <2>4. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Next, Recv, HeterogeneousSpec
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Next, HeterogeneousSpec
<1>5. CASE LearnerAction
  <2> SUFFICES ASSUME NEW lrn \in Learner, NEW bal \in Ballot,
                      \/ LearnerDecide(lrn, bal)
                      \/ LearnerRecv(lrn)
               PROVE CannotDecide(Q1, L1, B1, V1)'
      BY <1>5 DEF LearnerAction
  <2>2. CASE LearnerDecide(lrn, bal) BY <2>2 DEF LearnerDecide, Next, HeterogeneousSpec
  <2>3. CASE LearnerRecv(lrn) BY <2>2 DEF LearnerRecv, Next, HeterogeneousSpec
  <2>4. QED BY <2>2, <2>3
<1>6. CASE FakeAcceptorAction BY <1>6, SafeAcceptorAssumption DEF FakeAcceptorAction, FakeSend, Send, HeterogeneousSpec
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA ChosenSafeCaseEq ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
               NEW B \in Ballot,
               NEW V1 \in Value, NEW V2 \in Value,
               TypeOK, MsgInv,
               ReceivedSpec, ReceivedByLearnerSpec, VotesSentSpec4,
               <<L1, L2>> \in Ent,
               ChosenIn(L1, B, V1), ChosenIn(L2, B, V2)
    PROVE V1 = V2
PROOF
<1> USE DEF MsgInv
<1>1. PICK Q1 \in ByzQuorum :
        /\ [lr |-> L1, q |-> Q1] \in TrustLive
        /\ \A aa \in Q1 :
            \E m \in {mm \in receivedByLearner[L1] : mm.bal = B} :
                /\ m.val = V1
                /\ m.acc = aa
      BY DEF ChosenIn
<1>2. PICK Q2 \in ByzQuorum :
        /\ [lr |-> L2, q |-> Q2] \in TrustLive
        /\ \A aa \in Q2 :
            \E m \in {mm \in receivedByLearner[L2] : mm.bal = B} :
                /\ m.val = V2
                /\ m.acc = aa
      BY DEF ChosenIn
<1>3. PICK A \in SafeAcceptor : A \in Q1 /\ A \in Q2 BY EntanglementTrustLive, <1>1, <1>2
<1>4. PICK m1 \in receivedByLearner[L1] : m1.acc = A /\ m1.bal = B /\ m1.val = V1 BY <1>1, <1>3 DEF ChosenIn
<1>5. PICK m2 \in receivedByLearner[L2] : m2.acc = A /\ m2.bal = B /\ m2.val = V2 BY <1>2, <1>3 DEF ChosenIn
<1>6. /\ m1 \in msgs
      /\ m1.type = "2b"
      /\ m1.lr = L1
      /\ m1.acc = A
      /\ m1.bal = B
      /\ m1.val = V1
      BY <1>4 DEF ReceivedByLearnerSpec, TypeOK
<1>7. /\ m2 \in msgs
      /\ m2.type = "2b"
      /\ m2.lr = L2
      /\ m2.acc = A
      /\ m2.bal = B
      /\ m2.val = V2
      BY <1>5 DEF ReceivedByLearnerSpec, TypeOK
<1>8. [lr |-> L1, bal |-> B, val |-> V1] \in votesSent[A] BY <1>6 DEF MsgInv2b
<1>9. [lr |-> L2, bal |-> B, val |-> V2] \in votesSent[A] BY <1>7 DEF MsgInv2b
<1>100. QED BY <1>8, <1>9 DEF VotesSentSpec4

LEMMA ChosenSafeCaseLt ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
               NEW B1 \in Ballot, NEW B2 \in Ballot,
               NEW V1 \in Value, NEW V2 \in Value,
               TypeOK, ReceivedSpec, ReceivedByLearnerSpec, MsgInv,
               HeterogeneousSpec,
               <<L1, L2>> \in Ent,
               B1 < B2,
               ChosenIn(L1, B1, V1), ChosenIn(L2, B2, V2)
    PROVE V1 = V2
PROOF
<1> USE DEF MsgInv
<1> SUFFICES ASSUME V1 # V2 PROVE FALSE OBVIOUS
<1>1. PICK Q1 \in ByzQuorum :
        /\ [lr |-> L1, q |-> Q1] \in TrustLive
        /\ \A aa \in Q1 :
            \E m \in {mm \in receivedByLearner[L1] : mm.bal = B1} :
                /\ m.val = V1
                /\ m.acc = aa
      BY DEF ChosenIn
<1>2. PICK Q2 \in ByzQuorum :
        /\ [lr |-> L2, q |-> Q2] \in TrustLive
        /\ \A aa \in Q2 :
            \E m \in {mm \in receivedByLearner[L2] : mm.bal = B2} :
                /\ m.val = V2
                /\ m.acc = aa
      BY DEF ChosenIn
<1>3. PICK A \in SafeAcceptor : A \in Q1 /\ A \in Q2 BY EntanglementTrustLive, <1>1, <1>2
<1>4. PICK m1 \in receivedByLearner[L1] : m1.acc = A /\ m1.bal = B1 /\ m1.val = V1 BY <1>1, <1>3 DEF ChosenIn
<1>5. PICK m2 \in receivedByLearner[L2] : m2.acc = A /\ m2.bal = B2 /\ m2.val = V2 BY <1>2, <1>3 DEF ChosenIn
<1>6. /\ m1 \in msgs
      /\ m1.type = "2b"
      /\ m1.lr = L1
      /\ m1.acc = A
      /\ m1.bal = B1
      /\ m1.val = V1
      BY <1>4 DEF ReceivedByLearnerSpec, TypeOK
<1>7. /\ m2 \in msgs
      /\ m2.type = "2b"
      /\ m2.lr = L2
      /\ m2.acc = A
      /\ m2.bal = B2
      /\ m2.val = V2
      BY <1>5 DEF ReceivedByLearnerSpec, TypeOK
<1>10. PICK R1 \in ByzQuorum :
            /\ [lr |-> L1, q |-> R1] \in TrustLive
       BY <1>6 DEF MsgInv2b
<1>11. PICK R2 \in ByzQuorum :
            /\ [lr |-> L2, q |-> R2] \in TrustLive
            /\ \A aa \in R2 :
                \E m2av \in received[A] :
                    /\ m2av.type = "2av"
                    /\ m2av.lr = L2
                    /\ m2av.acc = aa
                    /\ m2av.bal = B2
                    /\ m2av.val = V2
       BY <1>7 DEF MsgInv2b
<1>12. PICK A0 \in SafeAcceptor : A0 \in R1 /\ A0 \in R2 BY EntanglementTrustLive, <1>10, <1>11
<1>14. PICK m2av2 \in received[A] :
            m2av2.type = "2av" /\ m2av2.lr = L2 /\ m2av2.acc = A0 /\ m2av2.bal = B2 /\ m2av2.val = V2
       BY <1>12, <1>11
<1>16. /\ m2av2 \in msgs
       /\ m2av2.type = "2av"
       /\ m2av2.lr = L2
       /\ m2av2.acc = A0
       /\ m2av2.bal = B2
       /\ m2av2.val = V2
       BY <1>14, SafeAcceptorIsAcceptor DEF ReceivedSpec, TypeOK
<1>17. CannotDecide(Q1, L1, B1, V1)
  <2>1. [lr |-> L1, q |-> Q1] \in TrustLive BY <1>1
  <2>5. QED BY <1>16, <2>1 DEF HeterogeneousSpec
<1>18. PICK S \in SafeAcceptor : S \in Q1 /\ ~VotedFor(L1, S, B1, V1) BY <1>17 DEF CannotDecide
<1>19. PICK m \in receivedByLearner[L1] : m.acc = S /\ m.bal = B1 /\ m.val = V1
       BY <1>18, <1>1 DEF CannotDecide
<1>20. /\ m \in {mm \in msgs : mm.type = "2b"}
       /\ m.lr = L1
       /\ m.acc = S
       /\ m.bal = B1
       /\ m.val = V1
       BY <1>19 DEF ReceivedByLearnerSpec, TypeOK
<1>50. QED BY <1>20, <1>18 DEF CannotDecide, VotedFor, ReceivedByLearnerSpec, TypeOK

LEMMA ChosenSafe ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
               NEW B1 \in Ballot, NEW B2 \in Ballot,
               NEW V1 \in Value, NEW V2 \in Value,
               TypeOK, ReceivedSpec, ReceivedByLearnerSpec, VotesSentSpec4, MsgInv,
               HeterogeneousSpec,
               <<L1, L2>> \in Ent,
               ChosenIn(L1, B1, V1), ChosenIn(L2, B2, V2)
    PROVE V1 = V2
PROOF
<1> USE DEF MsgInv
<1>1. PICK Q1 \in ByzQuorum :
        /\ [lr |-> L1, q |-> Q1] \in TrustLive
        /\ \A aa \in Q1 :
            \E m \in {mm \in receivedByLearner[L1] : mm.bal = B1} :
                /\ m.val = V1
                /\ m.acc = aa
      BY DEF ChosenIn
<1>2. PICK Q2 \in ByzQuorum :
        /\ [lr |-> L2, q |-> Q2] \in TrustLive
        /\ \A aa \in Q2 :
            \E m \in {mm \in receivedByLearner[L2] : mm.bal = B2} :
                /\ m.val = V2
                /\ m.acc = aa
      BY DEF ChosenIn
<1>3. PICK A \in SafeAcceptor : A \in Q1 /\ A \in Q2 BY EntanglementTrustLive, <1>1, <1>2
<1>4. PICK m1 \in receivedByLearner[L1] : m1.acc = A /\ m1.bal = B1 /\ m1.val = V1 BY <1>1, <1>3 DEF ChosenIn
<1>5. PICK m2 \in receivedByLearner[L2] : m2.acc = A /\ m2.bal = B2 /\ m2.val = V2 BY <1>2, <1>3 DEF ChosenIn
<1>6. /\ m1 \in msgs
      /\ m1.type = "2b"
      /\ m1.lr = L1
      /\ m1.acc = A
      /\ m1.bal = B1
      /\ m1.val = V1
      BY <1>4 DEF ReceivedByLearnerSpec, TypeOK
<1>7. /\ m2 \in msgs
      /\ m2.type = "2b"
      /\ m2.lr = L2
      /\ m2.acc = A
      /\ m2.bal = B2
      /\ m2.val = V2
      BY <1>5 DEF ReceivedByLearnerSpec, TypeOK
<1>8. [lr |-> L1, bal |-> B1, val |-> V1] \in votesSent[A] BY <1>6 DEF MsgInv2b
<1>9. [lr |-> L2, bal |-> B2, val |-> V2] \in votesSent[A] BY <1>7 DEF MsgInv2b
<1>10. PICK R1 \in ByzQuorum :
            /\ [lr |-> L1, q |-> R1] \in TrustLive
            /\ \A aa \in R1 :
                \E m2av \in received[A] :
                    /\ m2av.type = "2av"
                    /\ m2av.lr = L1
                    /\ m2av.acc = aa
                    /\ m2av.bal = B1
                    /\ m2av.val = V1
       BY <1>6 DEF MsgInv2b
<1>11. PICK R2 \in ByzQuorum :
            /\ [lr |-> L2, q |-> R2] \in TrustLive
            /\ \A aa \in R2 :
                \E m2av \in received[A] :
                    /\ m2av.type = "2av"
                    /\ m2av.lr = L2
                    /\ m2av.acc = aa
                    /\ m2av.bal = B2
                    /\ m2av.val = V2
       BY <1>7 DEF MsgInv2b
<1>12. PICK A0 \in SafeAcceptor : A0 \in R1 /\ A0 \in R2 BY EntanglementTrustLive, <1>10, <1>11
<1>13. PICK m2av1 \in received[A] :
            m2av1.type = "2av" /\ m2av1.lr = L1 /\ m2av1.acc = A0 /\ m2av1.bal = B1 /\ m2av1.val = V1
       BY <1>12, <1>10
<1>14. PICK m2av2 \in received[A] :
            m2av2.type = "2av" /\ m2av2.lr = L2 /\ m2av2.acc = A0 /\ m2av2.bal = B2 /\ m2av2.val = V2
       BY <1>12, <1>11
<1>15. /\ m2av1 \in msgs
       /\ m2av1.type = "2av"
       /\ m2av1.lr = L1
       /\ m2av1.acc = A0
       /\ m2av1.bal = B1
       /\ m2av1.val = V1
       BY <1>13, SafeAcceptorIsAcceptor DEF ReceivedSpec, TypeOK
<1>16. /\ m2av2 \in msgs
       /\ m2av2.type = "2av"
       /\ m2av2.lr = L2
       /\ m2av2.acc = A0
       /\ m2av2.bal = B2
       /\ m2av2.val = V2
       BY <1>14, SafeAcceptorIsAcceptor DEF ReceivedSpec, TypeOK
<1>30. CASE B1 < B2 BY <1>30, ChosenSafeCaseLt
<1>31. CASE B2 < B1 BY <1>31, ChosenSafeCaseLt, EntanglementSym
<1>32. CASE B1 = B2 BY <1>32, ChosenSafeCaseEq
<1>33. QED BY <1>30, <1>31, <1>32, BallotOrderCases

Safety ==
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        <<L1, L2>> \in Ent /\
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] => V1 = V2

LEMMA SafetyStep ==
    TypeOK /\ Next /\ MsgInv /\
    DecisionSpec /\ ReceivedSpec /\ ReceivedByLearnerSpec /\
    2avSentSpec1 /\ 2avSentSpec3 /\ VotesSentSpec4 /\
    HeterogeneousSpec /\ Safety => Safety'
PROOF
<1> SUFFICES
        ASSUME TypeOK, Next, MsgInv, Safety, DecisionSpec, ReceivedSpec, ReceivedByLearnerSpec,
               2avSentSpec1, 2avSentSpec3, VotesSentSpec4,
               HeterogeneousSpec,
               NEW L1 \in Learner, NEW L2 \in Learner,
               NEW B1 \in Ballot, NEW B2 \in Ballot,
               NEW V1 \in Value, NEW V2 \in Value,
               <<L1, L2>> \in Ent,
               V1 \in decision'[L1, B1], V2 \in decision'[L2, B2]
        PROVE V1 = V2
    BY DEF Safety
<1>0a. TypeOK OBVIOUS
<1>0b. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send, Safety
<1>2. CASE AcceptorSendAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in SafeAcceptor,
                      NEW val \in Value,
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc, val)
                      \/ Phase2b(lrn, bal, acc, val)
               PROVE V1 = V2
        BY <1>2 DEF AcceptorSendAction
  <2>2. CASE Phase1b(lrn, bal, acc) BY <2>2, <1>0a, <1>0b DEF AcceptorSendAction, Send, Phase1b, Safety, TypeOK
  <2>3. CASE Phase2av(lrn, bal, acc, val) BY <2>3, <1>0a, <1>0b DEF AcceptorSendAction, Send, Phase2av, Safety, TypeOK
  <2>4. CASE Phase2b(lrn, bal, acc, val) BY <2>4, <1>0a, <1>0b DEF AcceptorSendAction, Send, Phase2b, Safety, TypeOK
  <2>5. QED BY <2>2, <2>3, <2>4
<1>3. CASE AcceptorReceiveAction BY <1>3, <1>0a, <1>0b DEF AcceptorReceiveAction, Recv, TypeOK, Safety
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Safety
<1>5. CASE LearnerAction
  <2> SUFFICES ASSUME NEW lrn \in Learner, NEW bal \in Ballot,
                       \/ LearnerDecide(lrn, bal)
                       \/ LearnerRecv(lrn)
               PROVE V1 = V2 BY <1>5 DEF LearnerAction
  <2>1. CASE LearnerRecv(lrn) BY <2>1 DEF LearnerRecv, Safety
  <2>2. CASE LearnerDecide(lrn, bal)
    <3> SUFFICES ASSUME NEW val \in Value,
                        ChosenIn(lrn, bal, val),
                        decision' = [decision EXCEPT ![<<lrn, bal>>] = decision[lrn, bal] \cup {val}],
                        UNCHANGED <<msgs, maxBal, votesSent, 2avSent, received, connected, receivedByLearner>>
                 PROVE V1 = V2
        BY <2>2 DEF LearnerDecide
    <3>0. CASE V1 = V2 BY <3>0
    <3>1. CASE V1 # V2
      <4>1. CASE val # V1 /\ val # V2 BY <4>1 DEF Safety, TypeOK
      <4>2. CASE val = V1
        <5>0. V2 \in decision[L2, B2] BY <3>1, <4>2 DEF TypeOK
        <5>1. ChosenIn(L2, B2, V2) BY <5>0 DEF DecisionSpec
        <5>2. CASE V1 \in decision[L1, B1] BY <5>0, <5>2 DEF Safety
        <5>3. CASE V1 \notin decision[L1, B1]
          <6>1. lrn = L1 /\ bal = B1 BY <5>3, <4>2 DEF TypeOK
          <6>2. ChosenIn(L1, B1, V1) BY <6>1, <4>2
          <6>3. QED BY <5>1, <6>2, ChosenSafe
        <5>4. QED BY <5>2, <5>3
      <4>3. CASE val = V2
        <5>0. V1 \in decision[L1, B1] BY <3>1, <4>3 DEF TypeOK
        <5>1. ChosenIn(L1, B1, V1) BY <5>0 DEF DecisionSpec
        <5>2. CASE V2 \in decision[L2, B2] BY <5>0, <5>2 DEF Safety
        <5>3. CASE V2 \notin decision[L2, B2]
          <6>1. lrn = L2 /\ bal = B2 BY <5>3, <4>3 DEF TypeOK
          <6>2. ChosenIn(L2, B2, V2) BY <6>1, <4>3
          <6>10. QED BY <5>1, <6>2, ChosenSafe
        <5>4. QED BY <5>2, <5>3
      <4>4. QED BY <4>1, <4>2, <4>3
    <3>2. QED BY <3>0, <3>1
  <2>3. QED BY <2>1, <2>2
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send, Safety
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

FullSafetyInvariant ==
    /\ TypeOK
    /\ MsgInv
    /\ 2avSentSpec1 /\ 2avSentSpec2 /\ 2avSentSpec3
    /\ VotesSentSpec1 /\ VotesSentSpec2 /\ VotesSentSpec3 /\ VotesSentSpec4
    /\ ReceivedSpec
    /\ ReceivedByLearnerSpec
    /\ ConnectedSpec
    /\ DecisionSpec
    /\ HeterogeneousSpec
    /\ Safety

LEMMA TypeOKInit == Init => TypeOK
PROOF BY DEF Init, TypeOK

LEMMA MsgInvInit == Init => MsgInv
PROOF BY DEF Init, MsgInv

LEMMA 2avSentSpec1Init == Init => 2avSentSpec1
PROOF BY DEF Init, 2avSentSpec1

LEMMA 2avSentSpec2Init == Init => 2avSentSpec2
PROOF BY DEF Init, 2avSentSpec2, Proposed

LEMMA 2avSentSpec3Init == Init => 2avSentSpec3
PROOF BY DEF Init, 2avSentSpec3, TypeOK

LEMMA VotesSentSpec1Init == Init => VotesSentSpec1
PROOF BY DEF Init, VotesSentSpec1

LEMMA VotesSentSpec2Init == Init => VotesSentSpec2
PROOF BY DEF Init, VotesSentSpec2, VotedFor

LEMMA VotesSentSpec3Init == Init => VotesSentSpec3
PROOF BY DEF Init, VotesSentSpec3

LEMMA VotesSentSpec4Init == Init => VotesSentSpec4
PROOF BY DEF Init, VotesSentSpec4

LEMMA ReceivedSpecInit == Init => ReceivedSpec
PROOF BY SafeAcceptorIsAcceptor DEF Init, ReceivedSpec

LEMMA ReceivedByLearnerSpecInit == Init => ReceivedByLearnerSpec
PROOF BY DEF Init, ReceivedByLearnerSpec, TypeOK

LEMMA ConnectedSpecInit == Init => ConnectedSpec
PROOF BY DEF Init, ConnectedSpec

LEMMA DecisionSpecInit == Init => DecisionSpec
PROOF BY DEF Init, DecisionSpec

LEMMA HeterogeneousSpecInit == Init => HeterogeneousSpec
PROOF BY DEF Init, HeterogeneousSpec

LEMMA SafetyInit == Init => Safety
PROOF BY DEF Init, Safety

LEMMA FullSafetyInvariantInit == Init => FullSafetyInvariant
PROOF BY TypeOKInit, MsgInvInit,
         2avSentSpec1Init, 2avSentSpec2Init, 2avSentSpec3Init,
         VotesSentSpec1Init, VotesSentSpec2Init, VotesSentSpec3Init, VotesSentSpec4Init,
         ReceivedSpecInit, ReceivedByLearnerSpecInit, ConnectedSpecInit, DecisionSpecInit,
         HeterogeneousSpecInit, SafetyInit
      DEF FullSafetyInvariant

LEMMA FullSafetyInvariantNext == FullSafetyInvariant /\ [Next]_vars => FullSafetyInvariant'
PROOF
<1> SUFFICES ASSUME FullSafetyInvariant, [Next]_vars PROVE FullSafetyInvariant' OBVIOUS
<1>1. CASE Next BY <1>1,
        TypeOKInvariant, MsgInvInvariant,
        2avSentSpec1Invariant, 2avSentSpec2Invariant, 2avSentSpec3Invariant,
        VotesSentSpec1Invariant, VotesSentSpec2Invariant, VotesSentSpec3Invariant, VotesSentSpec4Invariant,
        ReceivedSpecInvariant, ReceivedByLearnerSpecInvariant, ConnectedSpecInvariant, DecisionSpecInvariant,
        HeterogeneousSpecInvariant, SafetyStep
      DEF FullSafetyInvariant
<1>2. CASE vars = vars' BY <1>2 DEF vars, FullSafetyInvariant, TypeOK, MsgInv,
          2avSentSpec1, 2avSentSpec2, 2avSentSpec3,
          VotesSentSpec1, VotesSentSpec2, VotesSentSpec3, VotesSentSpec4,
          ReceivedSpec, ReceivedByLearnerSpec, ConnectedSpec, DecisionSpec,
          MsgInv1b, MsgInv2av, MsgInv2b,
          Safety
<1>3. QED BY <1>1, <1>2

THEOREM SafetyResult == Spec => []Safety
PROOF BY PTL, FullSafetyInvariantInit, FullSafetyInvariantNext DEF Spec, FullSafetyInvariant

=============================================================================
