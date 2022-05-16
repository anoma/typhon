------------------------------- MODULE HPaxos -------------------------------
EXTENDS Integers

-----------------------------------------------------------------------------
Ballot == Nat

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

ASSUME BQAssumption == \A Q \in ByzQuorum : Q \subseteq Acceptor

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

CONSTANT Ent
ASSUME EntanglementAssumption ==
        /\ Ent \in SUBSET(Learner \X Learner)
        /\ \A L1, L2 \in Learner :
              <<L1, L2>> \in Ent <=>
              [from |-> L1, to |-> L2, q |-> SafeAcceptor] \in TrustSafe

-----------------------------------------------------------------------------
(* Messages *)

Message ==
    [type : {"1a"}, lr : Learner, bal : Ballot] \cup
    [
        type : {"1b"},
        lr   : Learner,
        acc  : Acceptor,
        bal  : Ballot,
        votes : SUBSET [lr : Learner, bal : Ballot, val : Value],
        proposals : SUBSET [lr : Learner, bal : Ballot, val : Value]
    ] \cup
    [type : {"1c"}, lr : Learner, bal : Ballot, val : Value] \cup
    [type : {"2av"}, lr : Learner, acc : Acceptor, bal : Ballot, val : Value] \cup
    [type : {"2b"}, lr : Learner, acc : Acceptor, bal : Ballot, val : Value]

-----------------------------------------------------------------------------
(* Algorithm specification *)

VARIABLES maxBal,
          votesSent,
          2avSent,
          received,
          connected,
          receivedByLearner,
          decision,
          msgs

InitializedBallot(lr, bal) ==
    \E m \in msgs : m.type = "1a" /\ m.lr = lr /\ m.bal = bal

AnnouncedValue(lr, bal, val) ==
    \E m \in msgs : m.type = "1c" /\ m.bal = bal /\ m.val = val \* TODO fix it

ChosenIn(lr, bal, v) ==
    \E Q \in ByzQuorum:
        /\ [lr |-> lr, q |-> Q] \in TrustLive
        /\ \A aa \in Q :
            \E m \in { mm \in receivedByLearner[lr] : mm.bal = bal } :
                /\ m.val = v
                /\ m.acc = aa

KnowsSafeAt1(l, ac, b, v) ==
    LET S == { mm \in received[ac] : mm.type = "1b" /\ mm.lr = l /\ mm.bal = b }
    IN \E BQ \in ByzQuorum :
        /\ [lr |-> l, q |-> BQ] \in TrustLive
        /\ \A a \in BQ :
            \E m \in S :
                /\ m.acc = a
                /\ \A p \in { pp \in m.votes : <<pp.lr, l>> \in connected[ac] } :
                        b =< p.bal

KnowsSafeAt2(l, ac, b, v) ==
    LET S == { mm \in received[ac] : mm.type = "1b" /\ mm.lr = l /\ mm.bal = b }
    IN \E c \in Ballot :
        /\ c < b
        /\ \E BQ \in ByzQuorum :
            /\ [lr |-> l, q |-> BQ] \in TrustLive
            /\ \A a \in BQ :
                \E m \in S :
                    /\ m.acc = a
                    /\ \A p \in { pp \in m.votes : <<pp.lr, l>> \in connected[ac] } :
                        /\ p.bal =< c
                        /\ (p.bal = c) => (p.val = v)
        /\ \E WQ \in ByzQuorum :
            /\ [lr |-> l, q |-> WQ] \in TrustLive
            /\ \A a \in WQ :
                \E m \in S :
                    /\ m.acc = a
                    /\ \E p \in m.proposals :
                        /\ p.lr = l
                        /\ p.bal = c
                        /\ p.val = v

KnowsSafeAt(l, ac, b, v) ==
    \/ KnowsSafeAt1(l, ac, b, v) \* TODO remove v
    \/ KnowsSafeAt2(l, ac, b, v)

vars == << maxBal, votesSent, 2avSent, received, connected, receivedByLearner, decision, msgs >>

TypeOK ==
    /\ msgs \in SUBSET Message
    /\ maxBal \in [Learner \X Acceptor -> Ballot]
    /\ votesSent \in [Acceptor -> SUBSET [lr : Learner, bal : Ballot, val : Value]]
    /\ 2avSent   \in [Acceptor -> SUBSET [lr : Learner, bal : Ballot, val : Value]]
    /\ connected \in [Acceptor -> SUBSET (Learner \X Learner)]
    /\ received  \in [Acceptor -> SUBSET Message]
    /\ receivedByLearner \in [Learner -> SUBSET Message]
    /\ decision \in [Learner \X Ballot -> SUBSET Value]

Init ==
    /\ msgs = {}
    /\ \A L \in Learner : \A A \in SafeAcceptor : maxBal[L, A] = 0
    /\ \A A \in SafeAcceptor : 2avSent[A] = {}
    /\ \A A \in SafeAcceptor : votesSent[A] = {}
    /\ \A A \in SafeAcceptor : connected[A] = Learner \X Learner
    /\ \A A \in Acceptor : received[A] = {}
    /\ \A L \in Learner : receivedByLearner[L] = {}
    /\ \A L \in Learner : \A B \in Ballot : decision[L, B] = {}
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
          other.lr = vote.lr /\ other.bal < b =>
          other.bal =< vote.bal

Phase1b(l, b, a) ==
    /\ maxBal[l, a] =< b
    /\ InitializedBallot(l, b)
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

Phase2av(l, b, a, v) ==
    /\ maxBal[l, a] =< b
    /\ InitializedBallot(l, b)
    /\ AnnouncedValue(l, b, v)
    /\ \A P \in { p \in 2avSent[a] : p.bal = b /\ <<p.lr, l>> \in connected[a] } : P.val = v
    /\ KnowsSafeAt(l, a, b, v)
    /\ Send([type |-> "2av", lr |-> l, acc |-> a, bal |-> b, val |-> v])
    /\ 2avSent' = [2avSent EXCEPT ![a] = 2avSent[a] \cup { [lr |-> l, bal |-> b, val |-> v] }]
    /\ UNCHANGED << maxBal, votesSent, received, connected, receivedByLearner, decision >>

Phase2b(l, b, a, v) ==
    /\ \A L \in Learner : maxBal[L, a] =< b
    /\ \E Q \in ByzQuorum :
        /\ [lr |-> l, q |-> Q] \in TrustLive
        /\ \A aa \in Q :
            \E m \in { mm \in received[a] :
                        /\ mm.type = "2av"
                        /\ mm.lr = l
                        /\ mm.bal = b } :
                /\ m.val = v
                /\ m.acc = aa
    /\ Send([type |-> "2b", lr |-> l, acc |-> a, bal |-> b, val |-> v])
    /\ votesSent' = [votesSent EXCEPT ![a] =
                        votesSent[a] \cup { [lr |-> l, bal |-> b, val |-> v] }]
    /\ UNCHANGED << maxBal, 2avSent, received, connected, receivedByLearner, decision >>

Recv(l, a) ==
    /\ \E m \in msgs : received' = [received EXCEPT ![a] = received[a] \cup { m }]
    /\ UNCHANGED << msgs, maxBal, 2avSent, votesSent, connected, receivedByLearner, decision >>

Disconnect(a) ==
    /\ \E P \in SUBSET { LL \in Learner \X Learner : LL \notin Ent } :
        connected' = [connected EXCEPT ![a] = connected[a] \ P]
    /\ UNCHANGED << msgs, maxBal, votesSent, 2avSent, received, receivedByLearner, decision >>

FakeSend(a) ==
    /\ \E m \in { mm \in Message :
                   /\ mm.acc = a
                   /\ \/ mm.type = "1b"
                      \/ mm.type = "2av"
                      \/ mm.type = "2b" } :
        Send(m)
    /\ UNCHANGED << maxBal, votesSent, 2avSent, received, connected, receivedByLearner, decision >>

LearnerDecide(l, b) ==
    /\ \E v \in {vv \in Value : ChosenIn(l, b, vv)}:
        decision' = [decision EXCEPT ![l, b] = decision[l, b] \cup {v}]
    /\ UNCHANGED << msgs, maxBal, votesSent, 2avSent, received, connected, receivedByLearner >>

LearnerRecv(l) ==
    /\ \E m \in {mm \in msgs : mm.type = "2b" /\ mm.lr = l}:
        receivedByLearner' =
            [receivedByLearner EXCEPT ![l] = receivedByLearner[l] \cup {m}]
    /\ UNCHANGED << msgs, maxBal, votesSent, 2avSent, received, connected, decision >>

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
    \E lrn \in Learner : \E acc \in Acceptor : Recv(lrn, acc)

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

=============================================================================
