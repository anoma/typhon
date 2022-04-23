------------------------------- MODULE HPaxos -------------------------------
EXTENDS Integers, FiniteSets, Functions, TLAPS, TLC, SequenceTheorems

-----------------------------------------------------------------------------
Ballot == Nat

LEMMA BallotLeqTrans ==
    ASSUME NEW A \in Ballot, NEW B \in Ballot, NEW C \in Ballot, A =< B, B =< C PROVE A =< C
PROOF BY DEF Ballot

LEMMA BallotLeNotLeq == ASSUME NEW A \in Ballot, NEW B \in Ballot, A < B PROVE \neg B =< A
PROOF BY DEF Ballot

CONSTANT Value
ASSUME ValueNotEmpty == Value # {}

None == CHOOSE v : v \notin Value
-----------------------------------------------------------------------------
CONSTANTS Acceptor,
          SafeAcceptor,
          FakeAcceptor,
          ByzQuorum,
          Learner

ASSUME SafeAcceptorAssumption ==
        /\ SafeAcceptor \cap FakeAcceptor = {}
        /\ SafeAcceptor \cup FakeAcceptor = Acceptor

LEMMA SafeAcceptorIsAcceptor == SafeAcceptor \subseteq Acceptor
PROOF BY SafeAcceptorAssumption

LEMMA FakeAcceptorIsAcceptor == FakeAcceptor \subseteq Acceptor
PROOF BY SafeAcceptorAssumption

ASSUME BQAssumption ==
        /\ \A Q \in ByzQuorum : Q \subseteq Acceptor

ASSUME BallotAssumption ==
        /\ (Ballot \cup {-1}) \cap Acceptor = {}
        /\ (Ballot \cup {-1}) \cap ByzQuorum = {}
        /\ (Ballot \cup {-1}) \cap Learner = {}
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
            E1.q = E2.q =>
            [from |-> E1.from, to |-> E2.to, q |-> E1.q] \in TrustSafe
        (* closure *)
        /\ \A E \in TrustSafe : \A Q \in ByzQuorum :
            E.q \subseteq Q =>
            [from |-> E.from, to |-> E.to, q |-> Q] \in TrustSafe
        (* validity *)
        /\ \A E \in TrustSafe : \A Q1, Q2 \in ByzQuorum :
            ([lr |-> E.from, q |-> Q1] \in TrustLive /\ [lr |-> E.to, q |-> Q2] \in TrustLive) =>
            \E N \in SafeAcceptor : N \in Q1 /\ N \in Q2

CONSTANT Ent
ASSUME EntanglementAssumption ==
        /\ Ent \in SUBSET(Learner \X Learner)
        /\ \A L1, L2 \in Learner :
                <<L1, L2>> \in Ent <=>
                [from |-> L1, to |-> L2, q |-> SafeAcceptor] \in TrustSafe

LEMMA EntanglementTrustLive ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW Q1 \in ByzQuorum, NEW Q2 \in ByzQuorum,
           <<L1, L2>> \in Ent,
           [lr |-> L1, q |-> Q1] \in TrustLive,
           [lr |-> L2, q |-> Q2] \in TrustLive
    PROVE  \E N \in SafeAcceptor : N \in Q1 /\ N \in Q2
PROOF BY EntanglementAssumption, LearnerGraphAssumption


Message ==
    [type : {"1a"}, lr : Learner, bal : Ballot] \cup
    [
        type : {"1b"},
        lr   : Learner,
        acc  : Acceptor,
        bal  : Ballot,
        votes : SUBSET [lr : Learner, bal : Ballot, val : Value],
        proposals : SUBSET [bal : Ballot, val : Value]
    ] \cup
    [type : {"1c"}, lr : Learner, bal : Ballot, val : Value] \cup
    [type : {"2av"}, lr : Learner, acc : Acceptor, bal : Ballot, val : Value] \cup
    [type : {"2b"}, lr : Learner, acc : Acceptor, bal : Ballot, val : Value]

-----------------------------------------------------------------------------
VARIABLES maxBal,
          votesSent,
          2avSent,
          received,
          connected,
          receivedByLearner,
          decision,
          msgs

initializedBallot(lr, bal) ==
    \E m \in msgs : m.type = "1a" /\ m.lr = lr /\ m.bal = bal

announcedValue(lr, bal, val) ==
    \E m \in msgs : m.type = "1c" /\ m.bal = bal /\ m.val = val

ChosenIn(lr, bal, v) ==
    \E Q \in ByzQuorum:
        /\ [lr |-> lr, q |-> Q] \in TrustLive
        /\ \A aa \in Q :
            \E m \in {mm \in receivedByLearner[lr] : mm.bal = bal} :
                /\ m.val = v
                /\ m.acc = aa

Chosen(lr, v) == \E b \in Ballot: ChosenIn(lr, b, v)

KnowsSafeAt1(l, ac, b, v) ==
    LET S == {m \in received[l, ac] : m.type = "1b" /\ m.bal = b}
    IN \E BQ \in ByzQuorum :
        /\ [lr |-> l, q |-> BQ] \in TrustLive
        /\ \A a \in BQ :
            \E m \in S :
                /\ m.acc = a
                /\ \A p \in {pp \in m.votes : <<pp.lr, l>> \in connected[ac]} :
                        b =< p.bal

KnowsSafeAt2(l, ac, b, v) ==
    LET S == {mm \in received[l, ac] : mm.type = "1b" /\ mm.bal = b}
    IN \E c \in Ballot :
        /\ c < b
        /\ \E BQ \in ByzQuorum :
            /\ [lr |-> l, q |-> BQ] \in TrustLive
            /\ \A a \in BQ :
                \E m \in S :
                    /\ m.acc = a
                    /\ \A p \in {pp \in m.votes : <<pp.lr, l>> \in connected[ac]} :
                        /\ p.bal =< c
                        /\ (p.bal = c) => (p.val = v)
        /\ \E WQ \in ByzQuorum :
            /\ [lr |-> l, q |-> WQ] \in TrustLive
            /\ \A a \in WQ :
                \E m \in S :
                    /\ m.acc = a
                    /\ \E p \in m.proposals :
                        /\ p.bal = c
                        /\ p.val = v
\*    LET S == {mm \in received[l, ac] : mm.type = "1b" /\ mm.bal = b}
\*    IN \E c \in Ballot : \E BQ \in ByzQuorum : \E WQ \in ByzQuorum :
\*        /\ c < b
\*        /\ [lr |-> l, q |-> BQ] \in TrustLive
\*        /\ \A a \in BQ :
\*            \E m \in S :
\*                /\ m.acc = a
\*                /\ \A p \in {pp \in m.votes : <<pp.lr, l>> \in connected[ac]} :
\*                    /\ p.bal =< c
\*                    /\ (p.bal = c) => (p.val = v)
\*        /\ [lr |-> l, q |-> WQ] \in TrustLive
\*        /\ \A a \in WQ :
\*            \E m \in S :
\*                /\ m.acc = a
\*                /\ \E p \in m.proposals :
\*                    /\ p.bal = c
\*                    /\ p.val = v

KnowsSafeAt(l, ac, b, v) ==
    \/ KnowsSafeAt1(l, ac, b, v)
    \/ KnowsSafeAt2(l, ac, b, v)

vars == << maxBal, votesSent, 2avSent, received, connected, receivedByLearner, 
           decision, msgs >>

TypeOK ==
    /\ msgs \in SUBSET Message
    /\ maxBal \in [Learner \X Acceptor -> Ballot]
    /\ votesSent \in [Acceptor -> SUBSET [lr : Learner, bal : Ballot, val : Value]]
    /\ 2avSent \in [Acceptor -> SUBSET [bal : Ballot, val : Value]]
    /\ connected \in [Acceptor -> SUBSET (Learner \X Learner)]
    /\ received \in [Learner \X Acceptor -> SUBSET Message]
    /\ receivedByLearner \in [Learner -> SUBSET Message]
    /\ decision \in [Learner \X Ballot -> SUBSET Value]

Init ==
    /\ \A L \in Learner : \A A \in SafeAcceptor : maxBal[L, A] = -1
    /\ \A L \in Learner : \A A \in SafeAcceptor : 2avSent[L, A] = {}
    /\ \A L \in Learner : \A A \in SafeAcceptor : received[L, A] = {}
    /\ \A A \in SafeAcceptor : votesSent[A] = {}
    /\ \A A \in SafeAcceptor : connected[A] = {}
    /\ \A L \in Learner : receivedByLearner[L] = {}
    /\ \A L \in Learner : \A B \in Ballot : decision[L, B] = {}
    /\ msgs = {}
    /\ TypeOK

Send(m) == msgs' = msgs \cup {m}

Phase1a(l, b) ==
    /\ Send([type |-> "1a", lr |-> l, bal |-> b])
    /\ UNCHANGED << maxBal, votesSent, 2avSent, received, connected, receivedByLearner, decision >>

Phase1c(l, b, v) ==
    /\ Send([type |-> "1c", lr |-> l, bal |-> b, val |-> v])
    /\ UNCHANGED << maxBal, votesSent, 2avSent, received, connected, receivedByLearner, decision >>

MaxVote(a, b, vote) ==
    /\ vote.bal < b
    /\ \A other \in votesSent[a] :
        other.lr = vote.lr /\ other.bal < b => other.bal =< vote.bal
        \* TODO: HYPOTHESIS: we can pick max votes per each learner

Phase1b(l, b, a) ==
    /\ maxBal[l, a] =< b
    /\ initializedBallot(l, b)
    /\ maxBal' = [maxBal EXCEPT ![l, a] = b]
    /\ Send([
         type |-> "1b",
         lr |-> l,
         acc |-> a,
         bal |-> b,
         votes |-> { p \in votesSent[a] : MaxVote(a, b, p) },
         \* TODO: should we restrict to instances connected with l?
         proposals |-> { p \in 2avSent[a] : p.bal < b /\ p.lr = l }
       ])
    /\ UNCHANGED << votesSent, 2avSent, received, connected, receivedByLearner, decision >>

Phase2av(l, b, a, v) ==
    /\ maxBal[l, a] =< b
    /\ initializedBallot(l, b)
    /\ announcedValue(l, b, v)
    /\ \A P \in {p \in 2avSent[a] : p.bal = b} : P.val = v
    /\ KnowsSafeAt(l, a, b, v)
    /\ Send([type |-> "2av", lr |-> l, acc |-> a, bal |-> b, val |-> v])
    /\ 2avSent' = [2avSent EXCEPT ![a] = 2avSent[a] \cup { [bal |-> b, val |-> v] }]
    /\ UNCHANGED << maxBal, votesSent, received, connected, receivedByLearner, decision >>

Phase2b(l, b, a, v) ==
    /\ \A L \in Learner : maxBal[L, a] =< b
    /\ \E Q \in ByzQuorum :
        /\ [lr |-> l, q |-> Q] \in TrustLive
        /\ \A aa \in Q :
            \E m \in {mm \in received[l, a] :
                        /\ mm.type = "2av"
                        /\ mm.bal = b} :
                /\ m.val = v
                /\ m.acc = aa
    /\ Send([type |-> "2b", lr |-> l, acc |-> a, bal |-> b, val |-> v])
    /\ votesSent' =
        [votesSent EXCEPT ![a] =
            votesSent[a] \cup { [lr |-> l, bal |-> b, val |-> v] }]
    /\ UNCHANGED << maxBal, 2avSent, received, connected,
                        receivedByLearner, decision >>

Recv(l, a) ==
    /\ \E m \in { mm \in msgs :
                    /\ mm.lr = l
                    /\ mm.type = "1b" \/ mm.type = "2av" } :
        received' = [received EXCEPT ![l, a] = received[l, a] \cup { m }]
    /\ UNCHANGED << msgs, maxBal, 2avSent, votesSent, connected,
                        receivedByLearner, decision >>

Disconnect(a) ==
    /\ \E P \in SUBSET { LL \in Learner \X Learner : LL \notin Ent } :
        connected' = [connected EXCEPT ![a] = connected[a] \ P]
    /\ UNCHANGED << msgs, maxBal, votesSent, 2avSent, received,
                        receivedByLearner, decision >>

FakeSend(a) ==
    /\ \E m \in { mm \in Message :
                   /\ mm.acc = a
                   /\ \/ mm.type = "1b"
                      \/ mm.type = "2av"
                      \/ mm.type = "2b" } :
        Send(m)
   /\ UNCHANGED << maxBal, votesSent, 2avSent, received,
                   connected, receivedByLearner, decision >>

LearnerDecide(l, b) ==
    /\ \E v \in {vv \in Value : ChosenIn(l, b, vv)}:
        decision' = [decision EXCEPT ![l, b] = decision[l, b] \cup {v}]
    /\ UNCHANGED << msgs, maxBal, votesSent, 2avSent, received, 
                        connected, receivedByLearner >>

LearnerRecv(l) ==
    /\ \E m \in {mm \in msgs : mm.type = "2b" /\ mm.lr = l}:
        receivedByLearner' =
            [receivedByLearner EXCEPT ![l] = receivedByLearner[l] \cup {m}]
    /\ UNCHANGED << maxBal, votesSent, 2avSent, received,
                        connected, msgs, decision >>
    
ProposerAction ==
    \E lrn \in Learner : \E proposer \in Ballot :
        \/ Phase1a(lrn, proposer)
        \/ \E v \in Value : Phase1c(lrn, proposer, v)

AcceptorSendAction ==
    \E lrn \in Learner : \E bal \in Ballot : \E acc \in SafeAcceptor : \E val \in Value :
        \/ Phase1b(lrn, bal, acc)
        \/ Phase2av(lrn, bal, acc, val)
        \/ Phase2b(lrn, bal, acc, val)

AcceptorReceiveAction ==
    \E lrn \in Learner : \E acc \in SafeAcceptor : Recv(lrn, acc)
    
AcceptorDisconnectAction ==
    \E acc \in SafeAcceptor : Disconnect(acc)

LearnerAction ==
    \E lrn \in Learner :
        \/ \E bal \in Ballot : LearnerDecide(lrn, bal)
        \/ LearnerRecv(lrn)

FakeAcceptorAction == \E a \in FakeAcceptor : FakeSend(a)

Next ==
    \/ ProposerAction
    \/ AcceptorSendAction
    \/ AcceptorReceiveAction
    \/ AcceptorDisconnectAction
    \/ LearnerAction
    \/ FakeAcceptorAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

VotedForIn(lr, acc, bal, val) ==
    \E m \in msgs : m.type = "2b" /\ m.lr =  lr /\ m.acc = acc /\ m.bal = bal /\ m.val = val

ProposedIn(bal, val) ==
    \E m \in msgs : m.type = "2av" /\ m.bal = bal /\ m.val = val

LeftBallot(lr, acc, bal) ==
    \E m \in msgs : m.type = "1b" /\ m.lr = lr /\ m.acc = acc /\ bal < m.bal

-----------------------------------------------------------------------------


ReceivedSpec ==
    /\ received \in
        [Learner \X Acceptor -> SUBSET {mm \in msgs : mm.type = "1b" \/ mm.type = "2av"}]
    /\ \A L \in Learner : \A A \in SafeAcceptor : \A mm \in Message :
        mm \in received[L, A] => mm.lr = L

ReceivedByLearnerSpec ==
    /\ receivedByLearner \in [Learner -> SUBSET {mm \in msgs : mm.type = "2b"}]
    /\ \A L \in Learner : \A mm \in Message :
        mm \in receivedByLearner[L] => mm.lr = L

VotesSentSpec1 ==
    \A A \in SafeAcceptor : \A vote \in votesSent[A] : VotedForIn(vote.lr, A, vote.bal, vote.val)

VotesSentSpec2 ==
    \A L \in Learner : \A A \in SafeAcceptor : \A B \in Ballot : \A V \in Value :
        VotedForIn(L, A, B, V) => [lr |-> L, bal |-> B, val |-> V] \in votesSent[A]

VotesSentSpec3 ==
    \A A \in SafeAcceptor : \A B \in Ballot : \A vote \in votesSent[A] :
        vote.bal < B => \E P \in votesSent[A] : MaxVote(A, B, P) /\ P.lr = vote.lr

2avSentSpec1 == \A A \in SafeAcceptor : \A p \in 2avSent[A] : ProposedIn(p.bal, p.val)

2avSentSpec2 ==
    \A A \in SafeAcceptor : \A B \in Ballot : \A V1, V2 \in Value :
        [bal |-> B, val |-> V1] \in 2avSent[A] /\ [bal |-> B, val |-> V2] \in 2avSent[A] => V1 = V2

ConnectedSpec ==
    \A A \in SafeAcceptor : \A L1, L2 \in Learner :
        <<L1, L2>> \in Ent => <<L1, L2>> \in connected[A]

DecisionSpec ==
    \A L \in Learner : \A B \in Ballot : \A V \in Value :
        V \in decision[L, B] => ChosenIn(L, B, V)

MsgInv1b(m) ==
    /\ m.bal =< maxBal[m.lr, m.acc]
    /\ \A vote \in m.votes :
            /\ vote.bal < m.bal
            /\ VotedForIn(vote.lr, m.acc, vote.bal, vote.val)
    /\ \A pr \in m.proposals :
            /\ pr.bal < m.bal
            /\ ProposedIn(pr.bal, pr.val)
    /\ m.votes = { p \in votesSent[m.acc] : MaxVote(m.acc, m.bal, p) }
    \*/\ m.votes = {} =>
    \*    \A L \in Learner : \A B \in Ballot : \A V \in Value :
    \*        B < m.bal => ~VotedForIn(L, m.acc, B, V)
    \*/\ m.proposals = {} =>
    \*    \A B \in Ballot : \A V \in Value : (m.bal =< B) => ~ProposedIn(B, V)

\*    [
\*        type : {"1b"},
\*        lr   : Learner,
\*        acc  : Acceptor,
\*        bal  : Ballot,
\*        votes : SUBSET [lr : Learner, bal : Ballot, val : Value],
\*        proposals : SUBSET [bal : Ballot, val : Value]
\*    ]

MsgInv2av(m) ==
    /\ initializedBallot(m.lr, m.bal)
    /\ announcedValue(m.lr, m.bal, m.val)
    /\ KnowsSafeAt(m.lr, m.acc, m.bal, m.val)
    /\ [bal |-> m.bal, val |-> m.val] \in 2avSent[m.acc] \* TODO check if necessary
    /\ \E Q \in ByzQuorum :
        /\ [lr |-> m.lr, q |-> Q] \in TrustLive
        /\ \A ba \in Q :
            \E m1b \in received[m.lr, m.acc] :
                /\ m1b.type = "1b"
                /\ m1b.acc = ba
                /\ m1b.bal = m.bal

MsgInv2b(m) ==
    /\ [lr |-> m.lr, bal |-> m.bal, val |-> m.val] \in votesSent[m.acc]
    /\ \E Q \in ByzQuorum :
        /\ [lr |-> m.lr, q |-> Q] \in TrustLive
        /\ \A ba \in Q :
            \E m2av \in received[m.lr, m.acc] :
                /\ m2av.type = "2av"
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
                /\ m.proposals \in SUBSET [bal : Ballot, val : Value]
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
    <3>2. (2avSent \in [Acceptor -> SUBSET [bal : Ballot, val : Value]])'
            BY <2>1 DEF Phase1b, Phase2av, Phase2b, Send, TypeOK, Message
    <3>3. msgs' \in SUBSET Message
      <4>1. {vote \in votesSent[acc] : MaxVote(acc, bal, vote)}
                \in SUBSET [lr : Learner, bal : Ballot, val : Value]
            BY DEF TypeOK 
      <4>2. {p \in 2avSent[acc] : p.bal < bal /\ p.lr = lrn} \in SUBSET [bal : Ballot, val : Value]
            BY DEF TypeOK
      <4>3. [type |-> "1b", lr |-> lrn, acc |-> acc, bal |-> bal,
             votes |-> {vote \in votesSent[acc] : MaxVote(acc, bal, vote) },
             proposals |-> {p \in 2avSent[acc] : p.bal < bal /\ p.lr = lrn}] \in Message
            BY <4>1, <4>2 DEF Message
      <4>4. QED BY <2>1, <4>1, <4>2, <4>3 DEF Phase1b, Send, TypeOK, Message
    <3>4. QED BY <2>1, <3>1, <3>2, <3>3 DEF Phase1b, TypeOK, Send
  <2>2. CASE Phase2av(lrn, bal, acc, val)
    <3>2. msgs' \in SUBSET Message
        <4>0. [type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val] \in Message
            BY SafeAcceptorIsAcceptor DEF Message
        <4>1. QED BY <2>2, <4>0, SafeAcceptorIsAcceptor DEF Phase2av, Send, TypeOK, Message
    <3>4. (2avSent \in [Acceptor -> SUBSET [bal : Ballot, val : Value]])'
        <4>0. [bal |-> bal, val |-> val] \in [bal : Ballot, val : Value] BY DEF TypeOK
        <4>1. QED BY <2>2, <1>2, <4>0 DEF Phase2av, Send, TypeOK, Message
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
                      NEW m \in { mm \in msgs :
                                    /\ mm.lr = lrn
                                    /\ mm.type = "1b" \/ mm.type = "2av" },
                      received' = [received EXCEPT ![lrn, acc] = received[lrn, acc] \cup { m }],
                      UNCHANGED << msgs, maxBal, 2avSent, votesSent, connected,
                                       receivedByLearner, decision >>
               PROVE  TypeOK'
    BY SafeAcceptorIsAcceptor, <1>3 DEF AcceptorReceiveAction, Recv
  <2>1. received' \in [Learner \X Acceptor -> SUBSET Message] BY DEF TypeOK
  <2>7. QED BY <1>3, <2>1 DEF AcceptorReceiveAction, Recv, TypeOK
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

LEMMA ReceivedSpecInvariant == TypeOK /\ ReceivedSpec /\ Next => ReceivedSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, ReceivedSpec, Next PROVE ReceivedSpec' OBVIOUS
<1>0. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, ReceivedSpec, Send, Next, TypeOK
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
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF TypeOK, ReceivedSpec, Phase1b, Send
  <2>2. CASE Phase2av(lrn, bal, acc, val) BY <2>2 DEF TypeOK, ReceivedSpec, Phase2av, Send
  <2>3. CASE Phase2b(lrn, bal, acc, val) BY <2>3 DEF Phase2b, TypeOK, ReceivedSpec, Send
  <2>4. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW acc \in Acceptor,
                      NEW m \in { mm \in msgs :
                                    /\ mm.lr = lrn
                                    /\ mm.type = "1b" \/ mm.type = "2av" },
                      received' = [received EXCEPT ![lrn, acc] = received[lrn, acc] \cup { m }],
                      UNCHANGED << msgs, maxBal, 2avSent, votesSent, connected,
                                       receivedByLearner, decision >>
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

LEMMA 2avSentMonotone == TypeOK /\ Next => \A A \in Acceptor : 2avSent[A] \subseteq 2avSent'[A]
PROOF
<1>0. SUFFICES ASSUME TypeOK, Next, NEW A \in Acceptor PROVE 2avSent[A] \subseteq 2avSent[A]' OBVIOUS
<1>0a. TypeOK BY <1>0
<1>0b. TypeOK' BY <1>0, TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send
<1>2. CASE AcceptorSendAction BY <1>2, <1>0a, <1>0b DEF AcceptorSendAction, Phase1b, Phase2av, Phase2b, Send, TypeOK
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerDecide, LearnerRecv
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send 
<1>7. QED BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA ReceivedMonotone ==
    TypeOK /\ Next => \A L \in Learner : \A A \in Acceptor : received[L, A] \subseteq received'[L, A]
PROOF
<1> SUFFICES ASSUME TypeOK, Next, NEW L \in Learner, NEW A \in Acceptor
             PROVE received[L, A] \subseteq received'[L, A] OBVIOUS
<1>0a. TypeOK OBVIOUS
<1>0b. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send
<1>2. CASE AcceptorSendAction BY <1>2 DEF AcceptorSendAction, Send, Phase1b, Phase2av, Phase2b
<1>3. CASE AcceptorReceiveAction BY <1>3, <1>0a, <1>0b DEF AcceptorReceiveAction, Recv, TypeOK
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerDecide, LearnerRecv
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send 
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA MaxBalMonotone ==
    TypeOK /\ Next =>
        \A l \in Learner : \A a \in Acceptor : maxBal[l, a] =< maxBal'[l, a]
<1> SUFFICES ASSUME TypeOK, Next,
    NEW CONSTANT l \in Learner, NEW CONSTANT a \in Acceptor
    PROVE maxBal[l, a] =< maxBal'[l, a]
    OBVIOUS
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send, TypeOK, Ballot
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
    <3>2. CASE <<l, a>> # <<lrn, acc>> BY <2>1, <3>2 DEF Phase1b, TypeOK, Ballot
    <3>3. QED BY <3>1, <3>2
  <2>2. CASE Phase2av(lrn, bal, acc, val)
    <3>1. UNCHANGED maxBal BY <2>2 DEF Phase2av
    <3>2. QED BY <3>1 DEF TypeOK, Ballot
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3>1. UNCHANGED maxBal BY <2>3 DEF Phase2b
    <3>2. QED BY <3>1 DEF TypeOK, Ballot
  <2>4. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction
  <2>1. UNCHANGED maxBal BY <1>3 DEF AcceptorReceiveAction, Recv
  <2>2. QED BY <2>1 DEF TypeOK, Ballot
<1>4. CASE AcceptorDisconnectAction
  <2>1. UNCHANGED maxBal BY <1>4 DEF AcceptorDisconnectAction, Disconnect
  <2>2. QED BY <2>1 DEF TypeOK, Ballot
<1>5. CASE LearnerAction
  <2>1. UNCHANGED maxBal BY <1>5 DEF LearnerAction, LearnerDecide, LearnerRecv
  <2>2. QED BY <2>1 DEF TypeOK, Ballot
<1>6. CASE FakeAcceptorAction
  <2>1. UNCHANGED maxBal BY <1>6 DEF FakeAcceptorAction, FakeSend
  <2>2. QED BY <2>1 DEF TypeOK, Ballot
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

\* TODO not used
LEMMA InitializedBallotInvariant ==
    \A L \in Learner : \A B \in Ballot : Next /\ initializedBallot(L, B) => initializedBallot(L, B)'
PROOF
<1> SUFFICES ASSUME NEW L \in Learner, NEW B \in Ballot, Next,
             initializedBallot(L, B)
             PROVE initializedBallot(L, B)'
    OBVIOUS
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Next
<1>2. CASE AcceptorSendAction BY <1>2 DEF Phase1b, Phase2b, Phase2av, Next
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, Next
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Next
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, Next
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA VotesSentSpec1Invariant == Next /\ VotesSentSpec1 => VotesSentSpec1'
PROOF
<1> SUFFICES ASSUME
  Next, VotesSentSpec1, NEW A \in SafeAcceptor, NEW vote \in votesSent'[A]
    PROVE VotedForIn(vote.lr, A, vote.bal, vote.val)'
    BY DEF VotesSentSpec1
<1> USE DEF VotesSentSpec1
<1>1. CASE ProposerAction BY <1>1, SafeAcceptorIsAcceptor DEF ProposerAction, Phase1a, Phase1c, Next, Send
<1>2. CASE AcceptorSendAction
  <2>. SUFFICES ASSUME NEW lrn \in Learner,
                       NEW bal \in Ballot,
                       NEW acc \in SafeAcceptor,
                       NEW val \in Value,
                       \/ Phase1b(lrn, bal, acc)
                       \/ Phase2av(lrn, bal, acc, val)
                       \/ Phase2b(lrn, bal, acc, val)
                PROVE  VotedForIn(vote.lr, A, vote.bal, vote.val)'
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF Phase1b
  <2>2. CASE Phase2av(lrn, bal, acc, val) BY <2>2 DEF Phase2av
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3> SUFFICES ASSUME Send([type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]),
                        votesSent' = [votesSent EXCEPT ![acc] =
                                        votesSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> val] }]
                 PROVE VotedForIn(vote.lr, A, vote.bal, vote.val)'
        BY <2>3 DEF Phase2b
    <3>2. CASE acc = A
      <4>1. USE DEF VotedForIn
      <4>2. CASE vote \in votesSent[acc] BY <3>2, <4>2, MsgsMonotone
      <4>3. CASE vote \notin votesSent[acc]
        <5>1. DEFINE m0 == [type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]
        <5>2. m0 \in msgs' BY DEF Phase2b, Send
        <5>3. WITNESS <5>2
        <5>10 QED BY <3>2, <4>3
      <4>4. QED BY <4>2, <4>3
    <3>3. CASE acc # A BY <3>3
    <3>4 QED BY <3>2, <3>3
  <2>5. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, Next
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Next
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, Next
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA VotesSentSpec2Invariant == TypeOK /\ Next /\ VotesSentSpec2 => VotesSentSpec2'
PROOF
<1> SUFFICES ASSUME TypeOK, Next, VotesSentSpec2,
                    NEW L \in Learner, NEW A \in SafeAcceptor, NEW B \in Ballot, NEW V \in Value
             PROVE (VotedForIn(L, A, B, V) => [lr |-> L, bal |-> B, val |-> V] \in votesSent[A])'
    BY DEF VotesSentSpec2
<1> USE DEF VotesSentSpec2
<1>0a. TypeOK OBVIOUS
<1>0b. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send
<1>2. CASE AcceptorSendAction
  <2>. SUFFICES ASSUME NEW lrn \in Learner,
                       NEW bal \in Ballot,
                       NEW acc \in SafeAcceptor,
                       NEW val \in Value,
                       \/ Phase1b(lrn, bal, acc)
                       \/ Phase2av(lrn, bal, acc, val)
                       \/ Phase2b(lrn, bal, acc, val)
                PROVE (VotedForIn(L, A, B, V) => [lr |-> L, bal |-> B, val |-> V] \in votesSent[A])'
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF Phase1b
  <2>2. CASE Phase2av(lrn, bal, acc, val) BY <2>2 DEF Phase2av
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3> SUFFICES ASSUME Send([type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]),
                        votesSent' = [votesSent EXCEPT ![acc] =
                                        votesSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> val] }]
                 PROVE (VotedForIn(L, A, B, V) => [lr |-> L, bal |-> B, val |-> V] \in votesSent[A])'
        BY <2>3 DEF Phase2b
    <3>1. QED BY <1>0b DEF Send, VotedForIn, TypeOK
  <2>5. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, Next
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Next
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, Next
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA VotesSentSpec3Invariant == TypeOK /\ Next /\ VotesSentSpec3 => VotesSentSpec3'
PROOF
<1> SUFFICES ASSUME TypeOK, Next, VotesSentSpec3,
                    NEW A \in SafeAcceptor, NEW B \in Ballot,
                    NEW V \in votesSent'[A],
                    V.bal < B
             PROVE (\E P \in votesSent[A] : MaxVote(A, B, P) /\ P.lr = V.lr)'
    BY DEF VotesSentSpec3
<1> USE DEF VotesSentSpec3
<1>0a. TypeOK OBVIOUS
<1>0b. TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send
<1>2. CASE AcceptorSendAction
  <2>. SUFFICES ASSUME NEW lrn \in Learner,
                       NEW bal \in Ballot,
                       NEW acc \in SafeAcceptor,
                       NEW val \in Value,
                       \/ Phase1b(lrn, bal, acc)
                       \/ Phase2av(lrn, bal, acc, val)
                       \/ Phase2b(lrn, bal, acc, val)
                PROVE (\E P \in votesSent[A] : MaxVote(A, B, P) /\ P.lr = V.lr)'
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF Phase1b
  <2>2. CASE Phase2av(lrn, bal, acc, val) BY <2>2 DEF Phase2av
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3> SUFFICES ASSUME votesSent' = [votesSent EXCEPT ![acc] =
                                        votesSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> val] }]
                 PROVE (\E P \in votesSent[A] : MaxVote(A, B, P) /\ P.lr = V.lr)'
        BY <2>3 DEF Phase2b
    <3>1. CASE A = acc
      <4>1. CASE \A P \in votesSent[A] : P.lr = V.lr => P.bal >= B
            BY <3>1, <4>1, <1>0b DEF Ballot, TypeOK, MaxVote
      <4>2. CASE \E P \in votesSent[A] : P.lr = V.lr /\ P.bal < B BY <4>2
      <4>3. QED BY <4>1, <4>2 DEF Ballot, TypeOK
    <3>2. CASE A # acc BY <3>2
    <3>3. QED BY <3>1, <3>2
  <2>5. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, Next
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Next
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, Next
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA 2avSentSpec1Invariant == Next /\ 2avSentSpec1 => 2avSentSpec1'
PROOF
<1> SUFFICES ASSUME Next, 2avSentSpec1,
             NEW A \in SafeAcceptor, NEW p \in 2avSent'[A]
             PROVE ProposedIn(p.bal, p.val)'
    BY DEF 2avSentSpec1
<1> USE DEF 2avSentSpec1
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Next, Send
<1>2. CASE AcceptorSendAction
  <2> HIDE DEF Next
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in SafeAcceptor,
                      NEW val \in Value, 
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc, val)
                      \/ Phase2b(lrn, bal, acc, val)
                PROVE  ProposedIn(p.bal, p.val)'
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF Phase1b
  <2>2. CASE Phase2av(lrn, bal, acc, val)
    <3> SUFFICES ASSUME Send([type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]),
                        2avSent' = [2avSent EXCEPT ![acc] = 2avSent[acc] \cup { [bal |-> bal, val |-> val] }]
                 PROVE ProposedIn(p.bal, p.val)'
          BY <2>2 DEF Phase2av
    <3>2. CASE acc = A
        <4>1. USE DEF ProposedIn
        <4>2. CASE p \in 2avSent[acc] BY <3>2, <4>2, MsgsMonotone
        <4>3. CASE p \notin 2avSent[acc]
          <5>1. DEFINE m0 == [type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]
          <5>2. m0 \in msgs' BY DEF Phase2b, Send
          <5>3. WITNESS <5>2
          <5>10. QED BY <3>2, <4>3
        <4>10. QED BY <4>2, <4>3
    <3>3. CASE acc # A BY <3>3
    <3>4. QED BY <3>2, <3>3
  <2>3. CASE Phase2b(lrn, bal, acc, val) BY <2>3 DEF Phase2b
  <2>5. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, Next
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Next
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, Next
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA 2avSentSpec2Invariant == Next /\ 2avSentSpec2 => 2avSentSpec2'
PROOF
<1> SUFFICES ASSUME Next, 2avSentSpec2,
             NEW A \in SafeAcceptor, NEW B \in Ballot,
             NEW V1 \in Value, NEW V2 \in Value,
             [bal |-> B, val |-> V1] \in 2avSent'[A],
             [bal |-> B, val |-> V2] \in 2avSent'[A]
             PROVE V1 = V2
    BY DEF 2avSentSpec2
<1> USE DEF 2avSentSpec2
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
    <3> SUFFICES ASSUME NEW v \in Value,
                        \A P \in {p \in 2avSent[acc] : p.bal = bal} : P.val = v,
                        2avSent' = [2avSent EXCEPT ![acc] = 2avSent[acc] \cup { [bal |-> bal, val |-> v] }]
                 PROVE V1 = V2
          BY <2>2 DEF Phase2av
    <3>2. QED OBVIOUS
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
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Next, Send
<1>2. CASE AcceptorSendAction BY <1>2 DEF AcceptorSendAction, Phase1b, Phase2av, Phase2b, Next, Send
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, Next
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Next
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
    <3>1. QED BY <2>3 DEF LearnerRecv
  <2>4. QED BY <2>2, <2>3 DEF LearnerAction
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send
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
      <4>2. QED BY <1>1b, <4>1, <3>1 DEF Phase1a, MsgInv1b
    <3>2. CASE Phase1c(lrn, proposer, val)
      <4>1. m \in msgs BY <3>2, <2>0e DEF Phase1c, Send, TypeOK
      <4>2. QED BY <1>1b, <4>1, <3>2 DEF Phase1c, MsgInv1b
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
          <6>0. m.bal = bal BY <3>1, <5>7 DEF Next, Phase1b, Send
          <6>1. m.lr = lrn BY <3>1, <5>7 DEF Next, Phase1b, Send
          <6>2. m.acc = acc BY <3>1, <5>7 DEF Next, Phase1b, Send
          <6>3. SUFFICES bal =< maxBal'[lrn, acc] BY <6>0, <6>1, <6>2
          <6>4. maxBal' = [maxBal EXCEPT ![lrn, acc] = bal] BY <3>1 DEF Phase1b, Send
          <6>5. maxBal'[<<lrn, acc>>] = bal BY <6>4, <2>0c, <2>0d
          <6>6. QED BY <6>0, <6>5 DEF Ballot
        <5>8. QED BY <5>6, <5>7
      <4>2. ASSUME NEW vote \in m.votes
            PROVE vote.bal < m.bal /\ VotedForIn(vote.lr, m.acc, vote.bal, vote.val)'
        <5>1. CASE m \in msgs BY <1>1b, <5>1, <2>0e, <4>2 DEF MsgInv1b
        <5>2. CASE m \notin msgs
          <6>0. m.bal = bal BY <3>1, <5>2 DEF Next, Phase1b, Send
          <6>1. <<m.lr, m.acc>> = <<lrn, acc>> BY <3>1, <5>2 DEF Next, Phase1b, Send
          <6>2. m.votes = {p \in votesSent[acc] : MaxVote(acc, bal, p)} BY <5>2, <3>1 DEF Phase1b, Send
          <6>3. QED BY <6>0, <3>1, <1>1b, <6>2, <6>1 DEF VotesSentSpec1, Phase1b, Send, MaxVote
        <5>10. QED BY <5>1, <5>2
      <4>3. ASSUME NEW pr \in m.proposals
            PROVE pr.bal < m.bal /\ ProposedIn(pr.bal, pr.val)'
        <5>1. CASE m \in msgs BY <1>1b, <5>1, <2>0e, <4>2 DEF MsgInv1b
        <5>2. CASE m \notin msgs
          <6>0. m.bal = bal BY <3>1, <5>2 DEF Next, Phase1b, Send
          <6>1. <<m.lr, m.acc>> = <<lrn, acc>> BY <3>1, <5>2 DEF Next, Phase1b, Send
          <6>2. m.proposals = { p \in 2avSent[acc] : p.bal < bal /\ p.lr = lrn } BY <5>2, <3>1 DEF Phase1b, Send
          <6>3. QED BY <6>0, <3>1, <1>1b, <6>2, <6>1 DEF 2avSentSpec1, Phase1b, Send
        <5>3. QED BY <5>1, <5>2
\*      <4>4. ASSUME m.votes = {}, NEW L \in Learner, NEW B \in Ballot, NEW V \in Value, B < m.bal
\*            PROVE ~VotedForIn(L, m.acc, B, V)'
\*        <5>1. CASE m \in msgs
\*          <6>1. SUFFICES ASSUME VotedForIn(L, m.acc, B, V)' PROVE FALSE OBVIOUS
\*          <6>2. PICK m1 \in msgs' : m1.type = "2b" /\ m1.lr =  L /\ m1.acc = m.acc /\ m1.bal = B /\ m1.val = V
\*              BY <6>1 DEF VotedForIn
\*          <6>3. m1 \in msgs BY <3>1, <6>2, <2>0a DEF Phase1b, Send, TypeOK, Message
\*          <6>4. ~VotedForIn(L, m.acc, B, V) BY <1>1b, <4>4, <5>1 DEF MsgInv1b
\*          <6>5. QED BY <6>2, <6>3, <6>4 DEF VotedForIn
\*       <5>2. CASE m \notin msgs
\*         <6>0a. m.bal = bal BY <3>1, <5>2 DEF Next, Phase1b, Send
\*         <6>0b. m.lr =lrn BY <3>1, <5>2 DEF Next, Phase1b, Send
\*         <6>0c. m.acc = acc BY <3>1, <5>2 DEF Next, Phase1b, Send
\*         <6>0d. m.type = "1b" BY <3>1, <5>2 DEF Next, Phase1b, Send
\*         <6>0e. m.votes = {p \in votesSent[acc] : MaxVote(acc, bal, p)} BY <3>1, <5>2 DEF Next, Phase1b, Send
\*         <6>1. \A p \in votesSent[acc] : p.bal >= bal
\*           <7>1. SUFFICES ASSUME NEW P \in votesSent[acc], P.bal < bal PROVE FALSE
\*               BY <1>1b, SafeAcceptorIsAcceptor DEF TypeOK, Ballot
\*           <7>2. QED BY <6>0e, <1>1b, <7>1, <4>4 DEF VotesSentSpec3l
\*         <6>2. SUFFICES ASSUME VotedForIn(L, m.acc, B, V)' PROVE FALSE OBVIOUS
\*         <6>3. VotedForIn(L, m.acc, B, V) BY <6>2, <3>1 DEF Phase1b, Send
\*         <6>4. [lr |-> L, bal |-> B, val |-> V] \in votesSent[acc] BY <6>0c, <6>3, <1>1b DEF VotesSentSpec2
\*         <6>5. QED BY <6>4, <6>0a, <6>1, <4>4 DEF Ballot
\*       <5>3. QED BY <5>1, <5>2
      <4>5. (m.votes = { p \in votesSent[m.acc] : MaxVote(m.acc, m.bal, p) })'
        <5>1. CASE m \in msgs BY <1>1b, <3>1, <5>1 DEF MsgInv1b, Phase1b, Send
        <5>2. CASE m \notin msgs
          <6>1. m.votes = { p \in votesSent[m.acc] : MaxVote(m.acc, m.bal, p) }
            BY <3>1, <5>2 DEF Phase1b, Send
          <6>2. QED BY <6>1, <3>1 DEF Phase1b, Send
        <5>3. QED BY <5>1, <5>2
      <4>10. QED BY <4>1, <4>2, <4>3, <4>5 DEF MsgInv1b
    <3>2. CASE Phase2av(lrn, bal, acc, val)
      <4> SUFFICES
            ASSUME Send([type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]),
                   2avSent' = [2avSent EXCEPT ![acc] = 2avSent[acc] \cup {[bal |-> bal, val |-> val]}]
            PROVE MsgInv1b(m)'
            BY <3>2 DEF Phase2av
      <4>2. m \in msgs BY <2>0e DEF Send
      <4>3. QED BY <4>2, <1>1b, <3>2 DEF Phase2av, MsgInv1b
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
      <4>2. (/\ m.bal =< maxBal[m.lr, m.acc]
             /\ \A vote \in m.votes :
                    /\ vote.bal < m.bal
                    /\ VotedForIn(vote.lr, m.acc, vote.bal, vote.val)
             /\ \A pr \in m.proposals :
                    /\ pr.bal < m.bal
                    /\ ProposedIn(pr.bal, pr.val))' BY <4>1, <1>1b, <3>3 DEF Phase2b, MsgInv1b
      <4>3. (m.votes = { p \in votesSent[m.acc] : MaxVote(m.acc, m.bal, p) })'
          <5>1. CASE m.acc # acc
            <6>1. votesSent'[m.acc] = votesSent[m.acc] BY <3>3, <4>1, <5>1, <2>0, <2>0e, MessageType DEF Phase2b, TypeOK
            <6>2. QED BY <6>1, <4>1, <1>1b, <2>0e DEF MsgInv1b
          <5>2. CASE m.acc = acc
            <6>1. m.bal =< maxBal[m.lr, m.acc] BY <1>1b, <4>1 DEF MsgInv1b
            <6>2. maxBal[m.lr, m.acc] =< bal BY <2>0a, <2>0e, <5>2, MessageType DEF Ballot, TypeOK
            <6>3. m.bal \in Ballot BY <2>0a, MessageType DEF TypeOK
            <6>4. m.bal =< bal BY <6>1, <6>2, <6>3, <2>0g, BallotLeqTrans
            <6>5. SUFFICES {p \in votesSent[m.acc] : MaxVote(m.acc, m.bal, p)} =
                           {p \in votesSent'[m.acc] : MaxVote(m.acc, m.bal, p)'}
                  BY <4>1, <2>0e, <1>1b DEF MsgInv1b
            <6>6. {p \in votesSent[m.acc] : MaxVote(m.acc, m.bal, p)} \subseteq
                  {p \in votesSent'[m.acc] : MaxVote(m.acc, m.bal, p)'}
               BY <4>1a, <2>0, VotesSentMonotone, <6>4 DEF TypeOK
            <6>7. {p \in votesSent'[m.acc] : MaxVote(m.acc, m.bal, p)'} \subseteq
                  {p \in votesSent[m.acc] : MaxVote(m.acc, m.bal, p)}
               <7>1. SUFFICES ASSUME NEW p \in votesSent'[m.acc],
                                     MaxVote(m.acc, m.bal, p)',
                                     p \notin votesSent[m.acc]
                              PROVE FALSE
                     OBVIOUS
               <7>2. p = [lr |-> lrn, bal |-> bal, val |-> val] BY <7>1, <5>2, <2>0 DEF TypeOK
               <7>3. QED BY <7>2, <7>1, <6>4, <6>3, BallotLeNotLeq DEF MaxVote
            <6>8. QED BY <6>6, <6>7
          <5>3. QED BY <5>1, <5>2
      <4>4. QED BY <4>2, <4>3 DEF MsgInv1b
    <3>4. QED BY <3>1, <3>2, <3>3
  <2>4. CASE AcceptorReceiveAction BY <1>1b, <2>4 DEF AcceptorReceiveAction, Recv, MsgInv1b, Next
  <2>5. CASE AcceptorDisconnectAction BY <1>1b, <2>5 DEF AcceptorDisconnectAction, Disconnect, MsgInv1b, Next
  <2>6. CASE LearnerAction BY <1>1b, <2>6 DEF LearnerAction, LearnerRecv, LearnerDecide, MsgInv1b, Next
  <2>7. CASE FakeAcceptorAction BY <1>1b, <2>7, SafeAcceptorAssumption DEF FakeAcceptorAction, FakeSend, MsgInv1b, Send
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
      <4>1. m \in msgs BY <3>1, <2>0e DEF Phase1b, Send
      <4>2. QED BY <1>2av, <4>1, <3>1 DEF Phase1b, MsgInv2av, Send
    <3>2. CASE Phase2av(lrn, bal, acc, val)
      <4> SUFFICES
            ASSUME \*initializedBallot(lrn, bal),
                   announcedValue(lrn, bal, val),
                   KnowsSafeAt(lrn, acc, bal, val),
                   Send([type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val]),
                   2avSent' = [2avSent EXCEPT ![acc] = 2avSent[acc] \cup { [bal |-> bal, val |-> val] }],
                   UNCHANGED received
                PROVE MsgInv2av(m)'
            BY <3>2 DEF Phase2av
      <4>1. CASE m \in msgs
        <5>1. initializedBallot(m.lr, m.bal)' BY <4>1, <2>0e, <1>2av, MsgsMonotone DEF MsgInv2av, initializedBallot
        <5>2. announcedValue(m.lr, m.bal, m.val)' BY <4>1, <2>0e, <1>2av, MsgsMonotone DEF MsgInv2av, announcedValue
        <5>3. KnowsSafeAt(m.lr, m.acc, m.bal, m.val)' BY <4>1, <1>2av DEF Phase2av, MsgInv2av
        <5>4. [bal |-> m.bal, val |-> m.val] \in 2avSent'[m.acc]
            BY <4>1, <2>0e, <1>2av, 2avSentMonotone, MessageType DEF MsgInv2av, TypeOK
        <5>5. (\E Q \in ByzQuorum :
              /\ [lr |-> m.lr, q |-> Q] \in TrustLive
              /\ \A ba \in Q :
                    \E m1b \in received[m.lr, m.acc] :
                       /\ m1b.type = "1b"
                       /\ m1b.acc = ba
                       /\ m1b.bal = m.bal)'
              BY <4>1, <2>0e, <1>2av, 2avSentMonotone, MessageType DEF MsgInv2av, TypeOK
        <5>6. QED BY <5>1, <5>2, <5>3, <5>4, <5>5 DEF MsgInv2av
      <4>2. CASE m \notin msgs
        <5>1. m = [type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> val] BY <4>2 DEF Send
        <5>3. initializedBallot(m.lr, m.bal)' BY <5>1, <3>2 DEF Phase2av
        <5>4. announcedValue(m.lr, m.bal, m.val)' BY <5>1
        <5>5. KnowsSafeAt(m.lr, m.acc, m.bal, m.val)' BY <5>1
        <5>6. [bal |-> m.bal, val |-> m.val] \in 2avSent'[m.acc] BY <5>1, <2>0b DEF TypeOK
        <5>7. (\E Q \in ByzQuorum :
              /\ [lr |-> m.lr, q |-> Q] \in TrustLive
              /\ \A ba \in Q :
                    \E m1b \in received[m.lr, m.acc] :
                       /\ m1b.type = "1b"
                       /\ m1b.acc = ba
                       /\ m1b.bal = m.bal)'
          <6>1. CASE KnowsSafeAt1(lrn, acc, bal, val)
            <7>1. PICK Q1 \in ByzQuorum :
                        /\ [lr |-> lrn, q |-> Q1] \in TrustLive
                        /\ \A a \in Q1 :
                            \E m1b \in received[lrn, acc] :
                                /\ m1b.type = "1b"
                                /\ m1b.bal = bal
                                /\ m1b.acc = a
                  BY <6>1 DEF KnowsSafeAt1
            <7>2. WITNESS Q1 \in ByzQuorum
            <7>3. QED BY <7>1, <5>1
          <6>2. CASE KnowsSafeAt2(lrn, acc, bal, val)
            <7>1. PICK Q2 \in ByzQuorum :
                        /\ [lr |-> lrn, q |-> Q2] \in TrustLive
                        /\ \A a \in Q2 :
                            \E m1b \in received[lrn, acc] :
                                /\ m1b.type = "1b"
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
                    \E m1b \in received[m.lr, m.acc] :
                       /\ m1b.type = "1b"
                       /\ m1b.acc = ba
                       /\ m1b.bal = m.bal)'                      
      <7>1. PICK Q0 \in ByzQuorum :
              /\ [lr |-> m.lr, q |-> Q0] \in TrustLive
              /\ \A ba \in Q0 :
                     \E m1b \in received[m.lr, m.acc] :
                        /\ m1b.type = "1b"
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
                    \E m2av \in received[m.lr, m.acc] :
                        /\ m2av.type = "2av"
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
                        \E m_1 \in {mm \in received[lrn, acc] :
                                      /\ mm.type = "2av"
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
                    \E m2av \in received[m.lr, m.acc] :
                       /\ m2av.type = "2av"
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
                          NEW acc \in SafeAcceptor,
                          NEW m0 \in msgs,
                          m0.lr = lrn,
                          m0.type = "1b" \/ m0.type = "2av",
                          received' = [received EXCEPT ![lrn, acc] = received[lrn, acc] \cup { m0 }],
                          UNCHANGED << msgs, maxBal, 2avSent, votesSent, connected,
                                         receivedByLearner, decision >>
                   PROVE  MsgInv2b(m)'
      BY <2>4 DEF AcceptorReceiveAction, Recv
    <3>1. m # m0 BY <3>0, <1>2b
    <3>2. m \in msgs BY <3>0, <1>2b
    <3>2a. m \in Message BY <3>2, <1>2b DEF TypeOK
    <3>2b. TypeOK BY <1>2b DEF Phase2b
    <3>2c. TypeOK' BY <1>2b, <3>2b, TypeOKInvariant
    <3>3. [lr |-> m.lr, bal |-> m.bal, val |-> m.val] \in votesSent'[m.acc] BY <3>0, <1>2b DEF MsgInv2b
    <3>4. \E Q \in ByzQuorum :
           /\ [lr |-> m.lr, q |-> Q] \in TrustLive
           /\ \A ba \in Q :
                 \E m2av \in received[m.lr, m.acc] :
                    /\ m2av.type = "2av"
                    /\ m2av.acc = ba
                    /\ m2av.bal = m.bal
                    /\ m2av.val = m.val
          BY <1>2b, <2>0e, <3>2 DEF MsgInv2b
    <3>5. PICK Q0 \in ByzQuorum : /\ [lr |-> m.lr, q |-> Q0] \in TrustLive
           /\ \A ba \in Q0 :
                 \E m2av \in received[m.lr, m.acc] :
                    /\ m2av.type = "2av"
                    /\ m2av.acc = ba
                    /\ m2av.bal = m.bal
                    /\ m2av.val = m.val BY <3>4
    <3>7. (\E Q \in ByzQuorum :
            /\ [lr |-> m.lr, q |-> Q] \in TrustLive
            /\ \A ba \in Q :
                \E m2av \in received[m.lr, m.acc] :
                    /\ m2av.type = "2av"
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
        \E A1 \in SafeAcceptor :
            /\ A1 \in Q
            /\ \E L \in Learner : LeftBallot(L, A1, B1)
            /\ \neg VotedForIn(L1, A1, B1, V1)

LEMMA HeterogeneousSpecInvariant ==
    TypeOK /\ Next /\ ReceivedSpec /\ VotesSentSpec2 /\ VotesSentSpec3 /\ ConnectedSpec /\ MsgInv /\
    HeterogeneousSpec => HeterogeneousSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, Next, ReceivedSpec, VotesSentSpec2, VotesSentSpec3,
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
             PROVE \E A1 \in SafeAcceptor :
                    /\ A1 \in Q1
                    /\ \E L \in Learner : LeftBallot(L, A1, B1)
                    /\ \neg VotedForIn(L1, A1, B1, V1)
    BY DEF HeterogeneousSpec
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
               PROVE (\E A1 \in SafeAcceptor :
                        /\ A1 \in Q1
                        /\ \E L \in Learner : LeftBallot(L, A1, B1)
                        /\ \neg VotedForIn(L1, A1, B1, V1))'
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
      <4>1. maxBal[lrn, acc] =< bal BY <2>2 DEF Phase2av
      <4>2. KnowsSafeAt(lrn, acc, bal, val) BY <2>2 DEF Phase2av
      <4>3a. CASE KnowsSafeAt1(lrn, acc, bal, val)
        <5>1. PICK Q2 \in ByzQuorum :
            /\ [lr |-> lrn, q |-> Q2] \in TrustLive
            /\ \A a \in Q2 :
                \E m1b \in received[lrn, acc] :
                    /\ m1b.type = "1b"
                    /\ m1b.bal = bal
                    /\ m1b.acc = a
                    /\ \A p \in {pp \in m1b.votes : <<pp.lr, lrn>> \in connected[acc]} :
                            bal =< p.bal
            BY <4>3a DEF KnowsSafeAt1
        <5>2. PICK S \in SafeAcceptor : S \in Q1 /\ S \in Q2 BY EntanglementTrustLive, <4>0, <5>1
        <5>3. PICK m1b \in received[lrn, acc] :
                    /\ m1b.type = "1b"
                    /\ m1b.bal = bal
                    /\ m1b.acc = S
                    /\ \A p \in {pp \in m1b.votes : <<pp.lr, lrn>> \in connected[acc]} :
                            bal =< p.bal
              BY <5>1, <5>2
        <5>4. /\ m1b \in msgs
              /\ m1b.type = "1b"
              /\ m1b.lr = lrn
              /\ m1b.bal = bal
              /\ m1b.acc = S
              /\ \A p \in {pp \in m1b.votes : <<pp.lr, lrn>> \in connected[acc]} :
                    bal =< p.bal
              BY <5>3, SafeAcceptorIsAcceptor DEF TypeOK, ReceivedSpec
        <5>5. WITNESS S \in SafeAcceptor
        <5>6. \E L \in Learner : LeftBallot(L, S, B1)' BY <4>0, <5>4, <3>0 DEF LeftBallot
        <5>7. \neg VotedForIn(L1, S, B1, V1)'
          <6>1. SUFFICES ASSUME VotedForIn(L1, S, B1, V1) PROVE FALSE OBVIOUS
          <6>2. [lr |-> L1, bal |-> B1, val |-> V1] \in votesSent[S] BY <6>1 DEF VotesSentSpec2
          <6>3. m1b.votes = { p \in votesSent[S] : MaxVote(S, B2, p) } BY <4>0, <5>4 DEF MsgInv, MsgInv1b
          <6>4. PICK P \in votesSent[S] : MaxVote(S, B2, P) /\ P.lr = L1
            <7>1. SUFFICES ASSUME NEW P0 \in votesSent[S],
                           P0 = [lr |-> L1, bal |-> B1, val |-> V1]
                           PROVE \E P \in votesSent[S] : MaxVote(S, B2, P) /\ P.lr = P0.lr
                  BY <6>2
            <7>2. SUFFICES P0.bal < B2 BY DEF VotesSentSpec3
            <7>3. QED BY <7>1
          <6>5. P \in m1b.votes BY <6>3, <6>4
          <6>6. <<P.lr, lrn>> \in connected[acc] BY <6>4, <4>0 DEF ConnectedSpec
          <6>7. B2 =< P.bal BY <6>5, <6>6, <5>4, <4>0
          <6>8. P \in [lr : Learner, bal : Ballot, val : Value] BY <6>4, SafeAcceptorIsAcceptor DEF TypeOK
          <6>9. P.bal \in Ballot BY <6>8
          <6>10. QED BY <6>9, <6>7, <6>4, BallotLeNotLeq DEF MaxVote
        <5>100. QED BY <5>2, <5>6, <5>7 \*DEF LeftBallot
      <4>3b. CASE KnowsSafeAt2(lrn, acc, bal, val) OMITTED
      <4>4. QED BY <4>3a, <4>3b, <4>2 DEF KnowsSafeAt
      \*<4>50. PICK A0 \in SafeAcceptor : A0 \in Q /\ A0 \in  BY EntanglementTrustLive, <1>10, <1>11
      \*<4>100. QED BY <3>2, <4>1a, <4>1b, <4>1c, <4>1d
    <3>3. QED BY <3>1, <3>2
  <2>3. CASE Phase2b(lrn, bal, acc, val)
    <3>1. m \in msgs BY <2>3, <1>0b, <1>0c, MessageType DEF Phase2b, Send
    <3>2. QED BY <3>1 DEF HeterogeneousSpec
  <2>4. QED BY <2>1, <2>2, <2>3
\*BY <1>2 DEF AcceptorSendAction, Phase1b, Phase2av, Phase2b, Next, Send
<1>3. CASE AcceptorReceiveAction
      BY <1>3, <1>0b, <1>0c\*, MessageType
      DEF AcceptorReceiveAction, Next, Recv, HeterogeneousSpec, LeftBallot, VotedForIn\*, TypeOK
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Next, HeterogeneousSpec
<1>5. CASE LearnerAction BY <1>5 \*, <1>0b, <1>0c, MessageType
          DEF LearnerAction, LearnerRecv, LearnerDecide, Next, HeterogeneousSpec, TypeOK
<1>6. CASE FakeAcceptorAction BY <1>6, SafeAcceptorAssumption DEF FakeAcceptorAction, FakeSend, Send, HeterogeneousSpec
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA ChosenSafe ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
               NEW B1 \in Ballot, NEW B2 \in Ballot,
               NEW V1 \in Value, NEW V2 \in Value,
               TypeOK, ReceivedSpec, ReceivedByLearnerSpec, MsgInv,
               2avSentSpec1, 2avSentSpec2, \* TODO remove if not needed
               <<L1, L2>> \in Ent,
               ChosenIn(L1, B1, V1), ChosenIn(L2, B2, V2)
    PROVE V1 = V2
PROOF
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
<1>6. m1 \in msgs /\ m1.type = "2b" /\ m1.lr = L1 /\ m1.acc = A /\ m1.bal = B1 /\ m1.val = V1
        BY <1>4 DEF ReceivedByLearnerSpec, TypeOK
<1>7. m2 \in msgs /\ m2.type = "2b" /\ m2.lr = L2 /\ m2.acc = A /\ m2.bal = B2 /\ m2.val = V2
        BY <1>5 DEF ReceivedByLearnerSpec, TypeOK
<1>8. [lr |-> L1, bal |-> B1, val |-> V1] \in votesSent[A] BY <1>6 DEF MsgInv, MsgInv2b
<1>9. [lr |-> L2, bal |-> B2, val |-> V2] \in votesSent[A] BY <1>7 DEF MsgInv, MsgInv2b
<1>10. PICK R1 \in ByzQuorum :
            /\ [lr |-> L1, q |-> R1] \in TrustLive
            /\ \A aa \in R1 :
                \E m2av \in received[L1, A] :
                    /\ m2av.type = "2av"
                    /\ m2av.acc = aa
                    /\ m2av.bal = B1
                    /\ m2av.val = V1
       BY <1>6 DEF MsgInv, MsgInv2b
<1>11. PICK R2 \in ByzQuorum :
            /\ [lr |-> L2, q |-> R2] \in TrustLive
            /\ \A aa \in R2 :
                \E m2av \in received[L2, A] :
                    /\ m2av.type = "2av"
                    /\ m2av.acc = aa
                    /\ m2av.bal = B2
                    /\ m2av.val = V2
       BY <1>7 DEF MsgInv, MsgInv2b
<1>12. PICK A0 \in SafeAcceptor : A0 \in R1 /\ A0 \in R2 BY EntanglementTrustLive, <1>10, <1>11
<1>13. PICK m2av1 \in received[L1, A] :
            m2av1.type = "2av" /\ m2av1.acc = A0 /\ m2av1.bal = B1 /\ m2av1.val = V1
       BY <1>12, <1>10
<1>14. PICK m2av2 \in received[L2, A] :
            m2av2.type = "2av" /\ m2av2.acc = A0 /\ m2av2.bal = B2 /\ m2av2.val = V2
       BY <1>12, <1>11
<1>15. m2av1 \in msgs /\ m2av1.type = "2av" /\
       m2av1.lr = L1 /\ m2av1.acc = A0 /\ m2av1.bal = B1 /\ m2av1.val = V1
       BY <1>13, SafeAcceptorIsAcceptor DEF ReceivedSpec, TypeOK
<1>16. m2av2 \in msgs /\ m2av2.type = "2av" /\
       m2av2.lr = L2 /\ m2av2.acc = A0 /\ m2av2.bal = B2 /\ m2av2.val = V2
       BY <1>14, SafeAcceptorIsAcceptor DEF ReceivedSpec, TypeOK
<1>17a. initializedBallot(L1, B1) BY <1>15 DEF MsgInv, MsgInv2av
<1>17b. announcedValue(L1, B1, V1) BY <1>15 DEF MsgInv, MsgInv2av
<1>17c. KnowsSafeAt(L1, A0, B1, V1) BY <1>15 DEF MsgInv, MsgInv2av
<1>17d. [bal |-> B1, val |-> V1] \in 2avSent[A0] BY <1>15 DEF MsgInv, MsgInv2av
<1>17e. PICK S1 \in ByzQuorum :
             /\ [lr |-> L1, q |-> S1] \in TrustLive
             /\ \A ba \in S1 :
                 \E m1b \in received[L1, A0] :
                     /\ m1b.type = "1b"
                     /\ m1b.acc = ba
                     /\ m1b.bal = B1
        BY <1>15 DEF MsgInv, MsgInv2av
<1>18a. initializedBallot(L2, B2) BY <1>16 DEF MsgInv, MsgInv2av
<1>18b. announcedValue(L2, B2, V2) BY <1>16 DEF MsgInv, MsgInv2av
<1>18c. KnowsSafeAt(L2, A0, B2, V2) BY <1>16 DEF MsgInv, MsgInv2av
<1>18d. [bal |-> B2, val |-> V2] \in 2avSent[A0] BY <1>16 DEF MsgInv, MsgInv2av
<1>18e. PICK S2 \in ByzQuorum :
             /\ [lr |-> L2, q |-> S2] \in TrustLive
             /\ \A ba \in S2 :
                 \E m1b \in received[L2, A0] :
                     /\ m1b.type = "1b"
                     /\ m1b.acc = ba
                     /\ m1b.bal = B2
        BY <1>16 DEF MsgInv, MsgInv2av
<1>19. PICK A1 \in SafeAcceptor : A1 \in S1 /\ A1 \in S2 BY EntanglementTrustLive, <1>17e, <1>18e
<1>20. PICK m1b1 \in received[L1, A0] : m1b1.type = "1b" /\ m1b1.acc = A1 /\ m1b1.bal = B1 BY <1>17e, <1>19
<1>21. PICK m1b2 \in received[L2, A0] : m1b2.type = "1b" /\ m1b2.acc = A1 /\ m1b2.bal = B2 BY <1>18e, <1>19
<1>22. m1b1 \in msgs /\ m1b1.type = "1b" /\ m1b1.lr = L1 /\ m1b1.acc = A1 /\ m1b1.bal = B1
       BY <1>20, SafeAcceptorIsAcceptor DEF ReceivedSpec, TypeOK
<1>23. m1b2 \in msgs /\ m1b2.type = "1b" /\ m1b2.lr = L2 /\ m1b2.acc = A1 /\ m1b2.bal = B2
       BY <1>21, SafeAcceptorIsAcceptor DEF ReceivedSpec, TypeOK
<1>100. QED OBVIOUS

Safety == (* safety *)
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        <<L1, L2>> \in Ent /\
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] => V1 = V2

LEMMA SafetyInit == Init => Safety
PROOF BY DEF Init, Safety

LEMMA SafetyStep ==
    TypeOK /\ Next /\
    DecisionSpec /\ ReceivedSpec /\ ReceivedByLearnerSpec /\ MsgInv /\
    2avSentSpec1 /\ 2avSentSpec2 /\ Safety => Safety'
PROOF
<1> SUFFICES
        ASSUME TypeOK, Next, Safety, DecisionSpec, ReceivedSpec, ReceivedByLearnerSpec, MsgInv,
               2avSentSpec1, 2avSentSpec2,
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
          <6>1a. lrn = L1 BY <5>3, <4>2 DEF TypeOK
          <6>1b. bal = B1 BY <5>3, <4>2 DEF TypeOK
          <6>2. ChosenIn(L1, B1, V1) BY <6>1a, <6>1b, <4>2
          <6>10. QED BY <5>1, <6>2, ChosenSafe
        <5>4. QED BY <5>2, <5>3
      <4>3. CASE val = V2
        <5>0. V1 \in decision[L1, B1] BY <3>1, <4>3 DEF TypeOK
        <5>1. ChosenIn(L1, B1, V1) BY <5>0 DEF DecisionSpec
        <5>2. CASE V2 \in decision[L2, B2] BY <5>0, <5>2 DEF Safety
        <5>3. CASE V2 \notin decision[L2, B2]
          <6>1a. lrn = L2 BY <5>3, <4>3 DEF TypeOK
          <6>1b. bal = B2 BY <5>3, <4>3 DEF TypeOK
          <6>2. ChosenIn(L2, B2, V2) BY <6>1a, <6>1b, <4>3
          <6>10. QED BY <5>1, <6>2, ChosenSafe
        <5>4. QED BY <5>2, <5>3
      <4>4. QED BY <4>1, <4>2, <4>3
    <3>2. QED BY <3>0, <3>1
  <2>3. QED BY <2>1, <2>2
<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send, Safety
<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next


THEOREM SafetyResult == Spec => []Safety
OMITTED

==============================================================================
