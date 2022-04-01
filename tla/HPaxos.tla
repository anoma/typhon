------------------------------- MODULE HPaxos -------------------------------
EXTENDS Integers, FiniteSets, Functions, TLAPS, TLC, SequenceTheorems

-----------------------------------------------------------------------------
Ballot == Nat

LEMMA BallotLeqTrans ==
    ASSUME NEW A \in Ballot, NEW B \in Ballot, NEW C \in Ballot, A =< B, B =< C PROVE A =< C
PROOF BY DEF Ballot

CONSTANT Value
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
        
ASSUME BQAssumption ==
        /\ \A Q \in ByzQuorum : Q \subseteq Acceptor

ASSUME BallotAssumption ==
        /\ (Ballot \cup {-1}) \cap Acceptor = {}
        /\ (Ballot \cup {-1}) \cap ByzQuorum = {}
        /\ (Ballot \cup {-1}) \cap Learner = {}
-----------------------------------------------------------------------------
(* Learner graph *)

CONSTANT TrustLive
ASSUME TrustLive \in SUBSET [lr : Learner, q : ByzQuorum]

CONSTANT TrustSafe
ASSUME TrustSafe \in SUBSET [from : Learner, to : Learner, q : ByzQuorum]

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
            \E N \in Acceptor :
                N \in Q1 /\ N \in Q2 /\ N \in SafeAcceptor

CONSTANT Ent
ASSUME EntanglementAssumption ==
        /\ Ent \in SUBSET(Learner \X Learner)
        /\ \A L1, L2 \in Learner :
                <<L1, L2>> \in Ent <=>
                [from |-> L1, to |-> L2, q |-> SafeAcceptor] \in TrustSafe

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

KnowsSafeAt(l, ac, b, v) ==
    LET S == {m \in received[ac] : m.type = "1b" /\ m.lr = l /\ m.bal = b}
    IN  \/ \E BQ \in ByzQuorum :
            /\ [lr |-> l, q |-> BQ] \in TrustLive
            /\ \A a \in BQ :
                \E m \in S :
                    /\ m.acc = a
                    /\ \A p \in {pp \in m.votes : <<pp.lr, l>> \in connected[ac]} :
                            b <= p.bal
        \/ \E c \in 0..(b-1):
            /\ \E BQ \in ByzQuorum :
                /\ [lr |-> l, q |-> BQ] \in TrustLive
                /\ \A a \in BQ :
                    \E m \in S :
                        /\ m.acc = a
                        /\ \A p \in {pp \in m.votes : <<pp.lr, l>> \in connected[ac]} :
                            /\ p.bal <= c
                            /\ (p.bal = c) => (p.val = v)
            /\ \E WQ \in ByzQuorum :
                /\ [lr |-> l, q |-> WQ] \in TrustLive
                /\ \A a \in WQ :
                    \E m \in S :
                        /\ m.acc = a
                        /\ \E p \in m.proposals :
                            /\ p.bal = c
                            /\ p.val = v


vars == << maxBal, votesSent, 2avSent, received, connected, receivedByLearner, 
           decision, msgs >>

Init == 
    /\ maxBal = [l \in Learner, a \in Acceptor |-> -1]
    /\ votesSent = [a \in Acceptor |-> {}]
    /\ 2avSent = [l \in Learner, a \in Acceptor |-> {}]
    /\ received = [l \in Learner, a \in Acceptor |-> {}]
    /\ connected = [a \in Acceptor |-> {}]
    /\ receivedByLearner = [l \in Learner |-> {}]
    /\ decision = [l \in Learner, b \in Ballot |-> {}]
    /\ msgs = {}

Send(m) == msgs' = msgs \cup {m}

Phase1a(l, b) ==
    /\ Send([type |-> "1a", lr |-> l, bal |-> b])
    /\ UNCHANGED << maxBal, votesSent, 2avSent, received, connected, receivedByLearner, decision >>

Phase1c(l, b, v) ==
    /\ Send([type |-> "1c", lr |-> l, bal |-> b, val |-> v])
    /\ UNCHANGED << maxBal, votesSent, 2avSent, received, connected, receivedByLearner, decision >>

MaxVote(a, b, vote) ==
    /\ vote.bal < b
    /\ \A other \in votesSent[a] : other.bal < b => other.bal <= vote.bal

Phase1b(l, b, a) ==
    /\ maxBal[l, a] <= b
    /\ initializedBallot(l, b)
    /\ maxBal' = [maxBal EXCEPT ![l, a] = b]
    /\ Send([
         type |-> "1b",
         lr |-> l,
         acc |-> a,
         bal |-> b,
         votes |-> { p \in votesSent[a] : MaxVote(a, b, p) },
         proposals |-> { p \in 2avSent[a] : p.bal < b /\ p.lr = l }
       ])
    /\ UNCHANGED << votesSent, 2avSent, received, connected, receivedByLearner, decision >>

Phase2av(l, b, a) ==
    /\ maxBal[l, a] <= b
    /\ initializedBallot(l, b)
    /\ \E v \in {vv \in Value :
                    /\ announcedValue(l, b, vv)
                    /\ \A P \in {p \in 2avSent[a] : p.bal = b} : P.val = vv } :
        /\ KnowsSafeAt(l, a, b, v)
        /\ Send([type |-> "2av", lr |-> l, acc |-> a, bal |-> b, val |-> v])
        /\ 2avSent' = [2avSent EXCEPT ![a] = 2avSent[a] \cup { [bal |-> b, val |-> v] }]
    /\ UNCHANGED << maxBal, votesSent, received, connected, receivedByLearner, decision >>

Phase2b(l, b, a) ==
    /\ \A L \in Learner : maxBal[L][a] <= b
    /\ \E v \in {vv \in Value :
                    \E Q \in ByzQuorum :
                        /\ [lr |-> l, q |-> Q] \in TrustLive
                        /\ \A aa \in Q :
                            \E m \in {mm \in received[l, a] :
                                        /\ mm.type = "2av"
                                        /\ mm.bal = b} :
                                /\ m.val = vv
                                /\ m.acc = aa} :
         /\ Send([type |-> "2b", lr |-> l, acc |-> a, bal |-> b, val |-> v])
         /\ votesSent' =
                [votesSent EXCEPT ![a] =
                    votesSent[a] \cup { [lr |-> l, bal |-> b, val |-> v] }]
    /\ UNCHANGED << maxBal, 2avSent, received, connected,
                        receivedByLearner, decision >>

Recv(l, a) ==
    /\ \E m \in { mm \in msgs :
                    /\ mm.lrn = l
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
    /\ \E m \in {mm \in msgs : mm.type = "2b" /\ mm.lrn = l}:
        receivedByLearner' =
            [receivedByLearner EXCEPT ![l] = receivedByLearner[l] \cup {m}]
    /\ UNCHANGED << maxBal, votesSent, 2avSent, received,
                        connected, msgs, decision >>
    
ProposerAction ==
    \E lrn \in Learner : \E proposer \in Ballot :
        \/ Phase1a(lrn, proposer)
        \/ \E v \in Value : Phase1c(lrn, proposer, v)

AcceptorSendAction ==
    \E lrn \in Learner : \E bal \in Ballot : \E acc \in Acceptor :
        \/ Phase1b(lrn, bal, acc)
        \/ Phase2av(lrn, bal, acc)
        \/ Phase2b(lrn, bal, acc)

AcceptorReceiveAction ==
    \E lrn \in Learner : \E acc \in Acceptor : Recv(lrn, acc)
    
AcceptorDisconnectAction ==
    \E acc \in Acceptor : Disconnect(acc)

LearnerAction ==
    \E lrn \in Learner :
        \/ \E bal \in Ballot : LearnerDecide(lrn, bal)
        \/ LearnerRecv(lrn)

Next ==
    \/ ProposerAction
    \/ AcceptorSendAction
    \/ AcceptorReceiveAction
    \/ AcceptorDisconnectAction
    \/ LearnerAction

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

VotedForIn(lr, acc, bal, val) ==
    \E m \in msgs : m.type = "2b" /\ m.lr =  lr /\ m.acc = acc /\ m.bal = bal /\ m.val = val

ProposedIn(bal, val) ==
    \E m \in msgs : m.type = "2av" /\ m.bal = bal /\ m.val = val

-----------------------------------------------------------------------------

TypeOK ==
    /\ msgs \in SUBSET Message
    /\ maxBal \in [Learner \X Acceptor -> Ballot]
    /\ votesSent \in [Acceptor -> SUBSET [lr : Learner, bal : Ballot, val : Value]]
    /\ 2avSent \in [Acceptor -> SUBSET [bal : Ballot, val : Value]]
    /\ connected \in [Acceptor -> SUBSET (Learner \X Learner)]
    /\ received \in [Learner \X Acceptor -> SUBSET Message]
    /\ receivedByLearner \in [Learner -> SUBSET Message]
    /\ decision \in [Learner \X Ballot -> SUBSET Value]

ReceivedSpec ==
    /\ received \in
        [Learner \X Acceptor -> SUBSET {mm \in msgs : mm.type = "1b" \/ mm.type = "2av"}]
    /\ \A L \in Learner : \A A \in Acceptor : \A mm \in Message :
        mm \in received[<<L, A>>] => mm.lrn = L

ReceivedByLearnerSpec ==
    /\ receivedByLearner \in [Learner -> SUBSET {mm \in msgs : mm.type = "2b"}]
    /\ \A L \in Learner : \A mm \in Message :
        mm \in receivedByLearner[L] => mm.lrn = L

VotesSentSpec == \A A \in Acceptor : \A vote \in votesSent[A] : VotedForIn(vote.lr, A, vote.bal, vote.val)

2avSentSpec == \A A \in Acceptor : \A p \in 2avSent[A] : ProposedIn(p.bal, p.val)

VarInv3 == \A L \in Learner : \A B \in Ballot : \A V \in Value :
            V \in decision[<<L, B>>] => ChosenIn(L, B, V)

MsgInv1b(m) ==
    /\ m.bal \leq maxBal[<<m.lr, m.acc>>]
    /\ \A vote \in m.votes : VotedForIn(vote.lr, m.acc, vote.bal, vote.val)
    /\ \A pr \in m.proposals : ProposedIn(pr.bal, pr.val)

MsgInv2av(m) ==
    /\ initializedBallot(m.lr, m.bal)
    /\ announcedValue(m.lr, m.bal, m.val)
    /\ KnowsSafeAt(m.lr, m.acc, m.bal, m.val)
    /\ [bal |-> m.bal, val |-> m.val] \in 2avSent[m.acc]
    /\ \A V \in Value : [bal |-> m.bal, val |-> V] \in 2avSent[m.acc] => V = m.val
    
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

MsgInv == \A m \in msgs: /\ (m.type = "1b") => MsgInv1b(m)
                         /\ (m.type = "2av") => MsgInv2av(m)
                         /\ (m.type = "2b") => MsgInv2b(m)
                         
-----------------------------------------------------------------------------

LEMMA TypeOKInvariant == TypeOK /\ Next => TypeOK'
PROOF
<1> SUFFICES ASSUME TypeOK, Next PROVE TypeOK' OBVIOUS
<1> USE DEF Next
<1>1. CASE ProposerAction
    BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send, TypeOK, Message
<1>2. CASE AcceptorSendAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in Acceptor,
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc)
                      \/ Phase2b(lrn, bal, acc)
               PROVE  TypeOK'
    BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc)
    <3>1.(votesSent \in [Acceptor -> SUBSET [lr : Learner, bal : Ballot, val : Value]])'
            BY <1>2, <2>1 DEF AcceptorSendAction, Phase1b, Phase2av, Phase2b, Send, TypeOK, Message
    <3>2. (2avSent \in [Acceptor -> SUBSET [bal : Ballot, val : Value]])'
            BY <1>2, <2>1 DEF AcceptorSendAction, Phase1b, Phase2av, Phase2b, Send, TypeOK, Message
    <3>3. msgs' \in SUBSET Message
      <4>1. {vote \in votesSent[acc] : MaxVote(acc, bal, vote)}
                \in SUBSET [lr : Learner, bal : Ballot, val : Value] BY DEF TypeOK 
      <4>2. {p \in 2avSent[acc] : p.bal < bal /\ p.lr = lrn} \in SUBSET [bal : Ballot, val : Value]
            BY DEF TypeOK
      <4>3. [type |-> "1b", lr |-> lrn, acc |-> acc, bal |-> bal,
                   votes |-> {vote \in votesSent[acc] : MaxVote(acc, bal, vote) },
                   proposals |-> {p \in 2avSent[acc] : p.bal < bal /\ p.lr = lrn}] \in Message
            BY <4>1, <4>2 DEF Message
      <4>4. QED BY <2>1, <4>1, <4>2, <4>3 DEF Phase1b, Send, TypeOK, Message
    <3>4. QED BY <2>1, <3>1, <3>2, <3>3 DEF Phase1b, TypeOK, Send
  <2>2. CASE Phase2av(lrn, bal, acc)
    <3> SUFFICES ASSUME NEW v \in Value,
                        Send([type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> v]),
                        2avSent' = [2avSent EXCEPT ![acc] =
                                        2avSent[acc] \cup { [bal |-> bal, val |-> v] }]
                 PROVE  TypeOK'
      BY <2>2 DEF Phase2av
    <3>2. msgs' \in SUBSET Message
        <4>0. [type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal,
                   val |-> v] \in Message BY DEF Message
        <4>1. QED BY <4>0 DEF Message, Send, TypeOK
    <3>4. (2avSent \in [Acceptor -> SUBSET [bal : Ballot, val : Value]])'
        <4>0. [bal |-> bal, val |-> v] \in [bal : Ballot, val : Value]
            BY DEF TypeOK
        <4>1. QED BY <2>2, <1>2, <4>0 DEF Send, TypeOK, Message
    <3>5. QED
      BY <2>2, <3>2, <3>4 DEF Phase2av, Send, TypeOK
  <2>3. CASE Phase2b(lrn, bal, acc)
    <3> SUFFICES ASSUME NEW v \in Value,
                        Send([type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> v]),
                        votesSent' =
                               [votesSent EXCEPT ![acc] =
                                   votesSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> v] }]
                 PROVE  TypeOK'
      BY <2>3 DEF Phase2b
    <3>1. v \in Value OBVIOUS
    <3>2. msgs' \in SUBSET Message
        <4>0. [type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal,
                   val |-> v] \in Message BY DEF Message
        <4>1. QED BY <4>0 DEF Message, Send, TypeOK
    <3>3. votesSent'
           \in [Acceptor -> SUBSET [lr : Learner, bal : Ballot, val : Value]]
        <4>0. [lr |-> lrn, bal |-> bal, val |-> v]
            \in [lr : Learner, bal : Ballot, val : Value] BY <3>1
        <4>1 QED BY <2>2, <1>2, <4>0 DEF TypeOK
    <3>5. QED
      BY <2>3, <1>2, <3>1, <3>2, <3>3 DEF Phase2b, Send, TypeOK
  <2>4. QED
    BY <1>2, <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW acc \in Acceptor,
                      NEW m \in { mm \in msgs :
                                    /\ mm.lrn = lrn
                                    /\ mm.type = "1b" \/ mm.type = "2av" },
                      received' = [received EXCEPT ![lrn, acc] = received[lrn, acc] \cup { m }],
                      UNCHANGED << msgs, maxBal, 2avSent, votesSent, connected,
                                       receivedByLearner, decision >>
               PROVE  TypeOK'
    BY <1>3 DEF AcceptorReceiveAction, Recv
  <2>1. received' \in [Learner \X Acceptor -> SUBSET Message] BY DEF TypeOK
  <2>7. QED
    BY <1>3, <2>1 DEF AcceptorReceiveAction, Recv, TypeOK  
<1>4. CASE AcceptorDisconnectAction
    BY <1>4 DEF AcceptorDisconnectAction, Disconnect, TypeOK, Message    
<1>5. CASE LearnerAction
  <2>1. ASSUME NEW lrn \in Learner, NEW bal \in Ballot,
                   LearnerDecide(lrn, bal)
               PROVE  TypeOK'
    BY <2>1 DEF LearnerDecide, TypeOK
  <2>2. ASSUME NEW lrn \in Learner, LearnerRecv(lrn)
               PROVE  TypeOK'
    BY <2>2 DEF LearnerRecv, TypeOK
  <2>3. QED BY <1>5, <2>1, <2>2 DEF LearnerAction
<1>6. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

LEMMA ReceivedSpecInvariant ==
    TypeOK /\ ReceivedSpec /\ Next => ReceivedSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, ReceivedSpec, Next PROVE ReceivedSpec' OBVIOUS
<1>1. CASE ProposerAction
  BY <1>1 DEF ProposerAction, Phase1a, Phase1c, ReceivedSpec, Send, Next, TypeOK
<1>2. CASE AcceptorSendAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in Acceptor,
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc)
                      \/ Phase2b(lrn, bal, acc)
               PROVE  ReceivedSpec'
    BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc)
    BY <2>1 DEF TypeOK, ReceivedSpec, Phase1b, Send
  <2>2. CASE Phase2av(lrn, bal, acc)
    BY <2>2 DEF TypeOK, ReceivedSpec, Phase2av, Send
  <2>3. CASE Phase2b(lrn, bal, acc)
    <3> SUFFICES ASSUME NEW v \in Value,
                        Send([type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> v])
                 PROVE  ReceivedSpec'
      BY <2>3 DEF Phase2b
    <3>2. UNCHANGED << received >> BY <2>3 DEF Phase2b
    <3>5. QED
      BY <3>2 DEF TypeOK, ReceivedSpec, Send
  <2>4. QED
    BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW acc \in Acceptor,
                      NEW m \in { mm \in msgs :
                                    /\ mm.lrn = lrn
                                    /\ mm.type = "1b" \/ mm.type = "2av" },
                      received' = [received EXCEPT ![lrn, acc] = received[lrn, acc] \cup { m }],
                      UNCHANGED << msgs, maxBal, 2avSent, votesSent, connected,
                                       receivedByLearner, decision >>
               PROVE  ReceivedSpec'
    BY <1>3 DEF AcceptorReceiveAction, Recv
  <2> QED
    BY DEF ReceivedSpec, TypeOK, Next
<1>4. CASE AcceptorDisconnectAction
  BY <1>4 DEF AcceptorDisconnectAction, Disconnect, ReceivedSpec, TypeOK, Next
<1>5. CASE LearnerAction
  BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, ReceivedSpec, TypeOK, Next
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

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
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc)
                      \/ Phase2b(lrn, bal, acc)
               PROVE  ReceivedByLearnerSpec'
    BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc)
    BY <2>1 DEF TypeOK, ReceivedByLearnerSpec, Phase1b, Send
  <2>2. CASE Phase2av(lrn, bal, acc)
    BY <2>2 DEF TypeOK, ReceivedByLearnerSpec, Phase2av, Send
  <2>3. CASE Phase2b(lrn, bal, acc)
    <3> SUFFICES ASSUME NEW v \in Value,
                        Send([type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> v])
                 PROVE  ReceivedByLearnerSpec'
      BY <2>3 DEF Phase2b
    <3>1. UNCHANGED <<receivedByLearner>> BY <2>3 DEF Phase2b
    <3>3. (\A L \in Learner : \A mm \in Message : mm \in receivedByLearner[L] => mm.lrn = L)'
          BY <3>1 DEF ReceivedByLearnerSpec, TypeOK
    <3>4. (receivedByLearner \in [Learner -> SUBSET {mm \in msgs : mm.type = "2b"}])'
           BY <3>1 DEF ReceivedByLearnerSpec, Send
    <3>5. QED
      BY <3>3, <3>4 DEF ReceivedByLearnerSpec
  <2>4. QED
    BY <2>1, <2>2, <2>3
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
    <3> SUFFICES ASSUME NEW m \in {mm \in msgs : mm.type = "2b" /\ mm.lrn = lrn},
                        receivedByLearner' =
                            [receivedByLearner EXCEPT ![lrn] = receivedByLearner[lrn] \cup {m}]
                 PROVE  ReceivedByLearnerSpec'
      BY <2>2 DEF LearnerRecv
    <3>1. UNCHANGED << msgs >> BY <2>2 DEF LearnerAction, LearnerRecv
    <3>5. QED BY <2>2, <3>1 DEF ReceivedByLearnerSpec
  <2>3. QED BY <1>5, <2>1, <2>2 DEF LearnerAction
<1>6. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

LEMMA MsgsMonotone == Next => msgs \subseteq msgs'
PROOF
<1> SUFFICES ASSUME Next PROVE msgs \subseteq msgs' OBVIOUS
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send
<1>2. CASE AcceptorSendAction BY <1>2 DEF AcceptorSendAction, Phase1b, Phase2av, Phase2b, Send
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerDecide, LearnerRecv
<1>6. QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

LEMMA MaxBalMonotone ==
    TypeOK /\ Next =>
        \A l \in Learner : \A a \in Acceptor : maxBal[<<l, a>>] =< maxBal'[<<l, a>>]
<1> SUFFICES ASSUME TypeOK, Next,
    NEW CONSTANT l \in Learner, NEW CONSTANT a \in Acceptor
    PROVE maxBal[<<l, a>>] =< maxBal'[<<l, a>>]
    OBVIOUS
<1> USE DEF Next
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send, TypeOK, Ballot
<1>2. CASE AcceptorSendAction
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                      NEW bal \in Ballot,
                      NEW acc \in Acceptor,
                      \/ Phase1b(lrn, bal, acc)
                      \/ Phase2av(lrn, bal, acc)
                      \/ Phase2b(lrn, bal, acc)
               PROVE  maxBal[<<l, a>>] =< (maxBal')[<<l, a>>]
    BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc)
    <3>1. CASE <<l, a>> = <<lrn, acc>> BY <2>1, <3>1 DEF Phase1b, TypeOK, Ballot
    <3>2. CASE <<l, a>> # <<lrn, acc>> BY <2>1, <3>2 DEF Phase1b, TypeOK, Ballot
    <3>3. QED BY <3>1, <3>2
  <2>2. CASE Phase2av(lrn, bal, acc)
    <3>1. UNCHANGED maxBal BY <2>2 DEF Phase2av
    <3>2. QED BY <3>1 DEF TypeOK, Ballot
  <2>3. CASE Phase2b(lrn, bal, acc)
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
<1>6. QED BY <1>1, <1>2, <1>3, <1>4, <1>5

LEMMA VotesSentSpecInvariant == Next /\ VotesSentSpec => VotesSentSpec'
PROOF
<1> SUFFICES ASSUME
  Next, VotesSentSpec, NEW A \in Acceptor, NEW vote \in votesSent'[A]
    PROVE VotedForIn(vote.lr, A, vote.bal, vote.val)'
    BY DEF VotesSentSpec
<1> USE DEF VotesSentSpec
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Next, Send
<1>2. CASE AcceptorSendAction
  <2>. SUFFICES ASSUME NEW lrn \in Learner,
                       NEW bal \in Ballot,
                       NEW acc \in Acceptor,
                       \/ Phase1b(lrn, bal, acc)
                       \/ Phase2av(lrn, bal, acc)
                       \/ Phase2b(lrn, bal, acc)
                PROVE  VotedForIn(vote.lr, A, vote.bal, vote.val)'
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF Phase1b
  <2>2. CASE Phase2av(lrn, bal, acc) BY <2>2 DEF Phase2av
  <2>3. CASE Phase2b(lrn, bal, acc)
    <3>1. SUFFICES ASSUME NEW v \in Value,
                          Send([type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> v]),
                          votesSent' =
                                 [votesSent EXCEPT ![acc] =
                                     votesSent[acc] \cup { [lr |-> lrn, bal |-> bal, val |-> v] }]
                   PROVE  VotedForIn(vote.lr, A, vote.bal, vote.val)'
        BY <2>3 DEF Phase2b
    <3>2. CASE acc = A
      <4>1. USE DEF VotedForIn
      <4>2. CASE vote \in votesSent[acc] BY <3>2, <4>2, MsgsMonotone
      <4>3. CASE vote \notin votesSent[acc]
        <5>1. DEFINE m0 == [type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> v]
        <5>2. m0 \in msgs' BY <3>1 DEF Phase2b, Send
        <5>3. WITNESS <5>2
        <5>10 QED BY <3>1, <3>2, <4>3
      <4>4. QED BY <4>2, <4>3
    <3>3. CASE acc # A BY <3>1, <3>3
    <3>4 QED BY <3>2, <3>3
  <2>5. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, Next
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Next
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, Next
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

LEMMA 2avSentSpecInvariant == Next /\ 2avSentSpec => 2avSentSpec'
PROOF
<1> SUFFICES ASSUME
  Next, 2avSentSpec, NEW A \in Acceptor, NEW p \in 2avSent'[A]
    PROVE ProposedIn(p.bal, p.val)'
    BY DEF 2avSentSpec
<1> USE DEF 2avSentSpec
<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Next, Send
<1>2. CASE AcceptorSendAction
  <2> HIDE DEF Next
  <2> SUFFICES ASSUME NEW lrn \in Learner,
                       NEW bal \in Ballot,
                       NEW acc \in Acceptor,
                       \/ Phase1b(lrn, bal, acc)
                       \/ Phase2av(lrn, bal, acc)
                       \/ Phase2b(lrn, bal, acc)
                PROVE  ProposedIn(p.bal, p.val)'
      BY <1>2 DEF AcceptorSendAction
  <2>1. CASE Phase1b(lrn, bal, acc) BY <2>1 DEF Phase1b
  <2>2. CASE Phase2av(lrn, bal, acc)
    <3>1. SUFFICES ASSUME NEW v \in Value,
                          Send([type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> v]),
                          2avSent' = [2avSent EXCEPT ![acc] = 2avSent[acc] \cup { [bal |-> bal, val |-> v] }]
                   PROVE ProposedIn(p.bal, p.val)'
          BY <2>2 DEF Phase2av
    <3>2. CASE acc = A
        <4>1. USE DEF ProposedIn
        <4>2. CASE p \in 2avSent[acc] BY <3>2, <4>2, MsgsMonotone
        <4>3. CASE p \notin 2avSent[acc]
          <5>1. DEFINE m0 == [type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> v]
          <5>2. m0 \in msgs' BY <3>1 DEF Phase2b, Send
          <5>3. WITNESS <5>2
          <5>10. QED BY <3>1, <3>2, <4>3
        <4>10. QED BY <4>2, <4>3
    <3>3. CASE acc # A BY <3>1, <3>3
    <3>4. QED BY <3>2, <3>3
  <2>3. CASE Phase2b(lrn, bal, acc) BY <2>3 DEF Phase2b
  <2>5. QED BY <2>1, <2>2, <2>3
<1>3. CASE AcceptorReceiveAction BY <1>3 DEF AcceptorReceiveAction, Recv, Next
<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Next
<1>5. CASE LearnerAction BY <1>5 DEF LearnerAction, LearnerRecv, LearnerDecide, Next
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

LEMMA MsgInvInvariant == TypeOK /\ MsgInv /\ VotesSentSpec /\ 2avSentSpec /\ Next => MsgInv'
PROOF
<1> USE DEF MsgInv
<1>1b. ASSUME TypeOK, VotesSentSpec, 2avSentSpec, Next, \A m \in msgs : m.type = "1b" => MsgInv1b(m),
        NEW CONSTANT m \in msgs', m.type = "1b"
        PROVE MsgInv1b(m)'
  <2>0a. TypeOK' BY <1>1b, TypeOKInvariant
  <2>0b. m \in Message BY <2>0a DEF TypeOK
  <2>0c. maxBal \in [Learner \X Acceptor -> Ballot] BY <1>1b DEF TypeOK
  <2>0d. maxBal' \in [Learner \X Acceptor -> Ballot] BY <2>0a DEF TypeOK
  <2>0e. m.type = "1b" BY <1>1b
  <2>0f. m.bal \in Ballot BY <2>0b, <2>0e DEF Message, Ballot
  <2>0g. maxBal[<<m.lr, m.acc>>] \in Ballot BY <2>0b, <2>0c, <2>0e DEF Message
  <2>0h. maxBal'[<<m.lr, m.acc>>] \in Ballot BY <2>0b, <2>0d, <2>0e DEF Message
  <2>0i. (maxBal[<<m.lr, m.acc>>] =< maxBal'[<<m.lr, m.acc>>])
            BY <1>1b, <2>0b, MaxBalMonotone DEF TypeOK, Message
  <2>1. CASE ProposerAction
    BY <1>1b, <2>1 DEF ProposerAction, Phase1a, Phase1c, MsgInv1b, Next, Send
  <2>2. CASE AcceptorSendAction
    <3> SUFFICES ASSUME NEW lrn \in Learner,
                        NEW bal \in Ballot,
                        NEW acc \in Acceptor,
                        \/ Phase1b(lrn, bal, acc)
                        \/ Phase2av(lrn, bal, acc)
                        \/ Phase2b(lrn, bal, acc)
                 PROVE  MsgInv1b(m)'
      BY <2>2 DEF AcceptorSendAction
    <3>1. CASE Phase1b(lrn, bal, acc)
      <4>1. m.bal =< maxBal'[<<m.lr, m.acc>>]
        <5>6. CASE m \in msgs
          <6>0. m.bal =< maxBal[<<m.lr, m.acc>>] BY <1>1b, <5>6 DEF MsgInv1b
          <6>1. QED BY <6>0, <2>0i, <2>0g, <2>0h, <2>0b, BallotLeqTrans DEF Message
        <5>7. CASE m \notin msgs
          <6>0. m.bal = bal BY <3>1, <5>7 DEF Next, Phase1b, Send
          <6>1. <<m.lr, m.acc>> = <<lrn, acc>> BY <3>1, <5>7 DEF Next, Phase1b, Send
          <6>3. SUFFICES bal =< (maxBal')[<<lrn, acc>>] BY <6>0, <6>1
          <6>4. maxBal' = [maxBal EXCEPT ![<<lrn, acc>>] = bal] BY <3>1 DEF Phase1b, Send
          <6>5. maxBal'[<<lrn, acc>>] = bal BY <6>4, <2>0c, <2>0d
          <6>6. QED BY <6>0, <6>5 DEF Ballot
        <5>8. QED BY <5>6, <5>7
         \*BY <1>1b, <2>0e, <2>0i, <3>1, <5>6, <2>0g, <2>0h, BallotLeqTrans DEF Phase1b, Send , MsgInv1b
        \*<5>7. CASE <<m.lr, m.acc>> = <<lrn, acc>> BY <2>0a, <3>1 DEF Phase1b, TypeOK, Ballot
        \*<5>8. CASE <<m.lr, m.acc>> # <<lrn, acc>> BY <2>0a, <3>1 DEF Phase1b, TypeOK, Ballot
\*        <5>0. SUFFICES m.bal =< maxBal[<<m.lr, m.acc>>]
\*            BY <2>0i, \*<2>1b, <2>1e,
\*            <2>0f, <2>0g, <2>0h,
\*            BallotLeqTrans
\*            \*DEF Phase1b, MsgInv1b, Message \*, Ballot
\*             \*BY <2>1e, <2>0i, <3>1, <2>1b, <2>1c, <2>1d, <2>0f, <2>0g, <2>0h, BallotLeqTrans DEF Phase1b, MsgInv1b, Message
\*        <5>1. CASE m \in msgs BY <1>1b, <3>1 , <5>1 DEF Phase1b, Send , MsgInv1b
        \*<5>2. CASE m \in [lr |-> lrn, acc |-> acc, bal |-> bal]
\*        <5>3. QED BY <5>1 \*, <5>2
\*          DEF Phase1b, Send, MsgInv1b
      <4>2. ASSUME NEW vote \in m.votes PROVE VotedForIn(vote.lr, m.acc, vote.bal, vote.val)'
        <5>1. CASE m \in msgs BY <1>1b, <5>1, <2>0e, <4>2 DEF MsgInv1b
        <5>2. CASE m \notin msgs
          <6>0. m.bal = bal BY <3>1, <5>2 DEF Next, Phase1b, Send
          <6>1. <<m.lr, m.acc>> = <<lrn, acc>> BY <3>1, <5>2 DEF Next, Phase1b, Send
          <6>2. m.votes = {p \in votesSent[acc] : MaxVote(acc, bal, p)} BY <5>2, <3>1 DEF Phase1b, Send
          <6>3. QED BY <6>0, <3>1, <1>1b, <6>2, <6>1 DEF VotesSentSpec, Phase1b, Send
        <5>10. QED BY <5>1, <5>2
      <4>3. ASSUME NEW pr \in m.proposals PROVE ProposedIn(pr.bal, pr.val)'
        <5>1. CASE m \in msgs BY <1>1b, <5>1, <2>0e, <4>2 DEF MsgInv1b
        <5>2. CASE m \notin msgs
          <6>0. m.bal = bal BY <3>1, <5>2 DEF Next, Phase1b, Send
          <6>1. <<m.lr, m.acc>> = <<lrn, acc>> BY <3>1, <5>2 DEF Next, Phase1b, Send
          <6>2. m.proposals = { p \in 2avSent[acc] : p.bal < bal /\ p.lr = lrn } BY <5>2, <3>1 DEF Phase1b, Send
          <6>3. QED BY <6>0, <3>1, <1>1b, <6>2, <6>1 DEF 2avSentSpec, Phase1b, Send
        <5>3. QED BY <5>1, <5>2   
      <4>10. QED BY <4>1, <4>2, <4>3 DEF MsgInv1b
    <3>2. CASE Phase2av(lrn, bal, acc)
      <4>1. SUFFICES ASSUME NEW v \in Value,
                            Send([type |-> "2av", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> v]),
                            2avSent' = [2avSent EXCEPT
                                            ![acc] = 2avSent[acc] \cup {[bal |-> bal, val |-> v]}]
                     PROVE MsgInv1b(m)'
            BY <3>2 DEF Phase2av
      <4>2. m \in msgs BY <4>1, <2>0e DEF Send
      <4>3. QED BY <4>2, <1>1b, <3>2 DEF Phase2av, MsgInv1b
    <3>3. CASE Phase2b(lrn, bal, acc)
      <4>1. SUFFICES ASSUME NEW v \in Value,
                            Send([type |-> "2b", lr |-> lrn, acc |-> acc, bal |-> bal, val |-> v]),
                            votesSent' = [votesSent EXCEPT
                                            ![acc] = votesSent[acc] \cup {[lr |-> lrn, bal |-> bal, val |-> v]}]
                     PROVE MsgInv1b(m)'
            BY <3>3 DEF Phase2b
      <4>2. m \in msgs BY <4>1, <2>0e DEF Send
      <4>3. QED BY <4>2, <1>1b, <3>3 DEF Phase2b, MsgInv1b
    <3>4. QED BY <3>1, <3>2, <3>3
  <2>4. CASE AcceptorReceiveAction BY <1>1b, <2>4 DEF AcceptorReceiveAction, Recv, MsgInv1b, Next
  <2>5. CASE AcceptorDisconnectAction BY <1>1b, <2>5 DEF AcceptorDisconnectAction, Disconnect, MsgInv1b, Next
  <2>6. CASE LearnerAction BY <1>1b, <2>6 DEF LearnerAction, LearnerRecv, LearnerDecide, MsgInv1b, Next
  <2>7. QED BY <1>1b, <2>0a, <2>1, <2>2, <2>4, <2>5, <2>6 DEF Next
<1>2av. ASSUME TypeOK, Next, \A m \in msgs : m.type = "2av" => MsgInv2av(m),
        NEW m \in msgs', m.type = "2av"
        PROVE MsgInv2av(m)'
        OMITTED
<1>2b. ASSUME TypeOK, Next, \A m \in msgs : m.type = "2b" => MsgInv2b(m),
        NEW m \in msgs', m.type = "2b"
        PROVE MsgInv2b(m)'
        OMITTED
<1>3. QED BY <1>1b, <1>2av, <1>2b


Safety == (* safety *)
    \A L1, L2 \in Learner: \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        <<L1, L2>> \in Ent /\
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] => V1 = V2

THEOREM SafetyResult == Spec => []Safety
    OBVIOUS

==============================================================================
