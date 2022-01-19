---------------------------- MODULE HPaxosProof -----------------------------
EXTENDS Integers, FiniteSets

-----------------------------------------------------------------------------
Ballot == Nat

CONSTANT Value
None == CHOOSE v : v \notin Value
-----------------------------------------------------------------------------
CONSTANTS Acceptor,
          SafeAcceptor,
          FakeAcceptor,
          ByzQuorum,
          Learner

ASSUME SafeAccAssumption ==
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
        /\ Ent \in SUBSET (Learner \X Learner)
        /\ \A L1, L2 \in Learner :
            <<L1, L2>> \in Ent <=>
                [from |-> L1, to |-> L2, q |-> SafeAcceptor] \in TrustSafe

1aMessage == [type : {"1a"}, lr : Learner, bal : Ballot]

1bMessage ==
    [
        type : {"1b"},
        lr   : Learner,
        acc  : Acceptor,
        bal  : Ballot,
        votes : SUBSET [bal : Ballot, val : Value],
        proposals : SUBSET [bal : Ballot, val : Value]
    ]

1cMessage ==
    [type : {"1c"}, lr : Learner, bal : Ballot, val : Value]

2avMessage ==
    [type : {"2av"}, lr : Learner, acc : Acceptor, bal : Ballot, val : Value]

2bMessage ==
    [type : {"2b"}, lr : Learner, acc : Acceptor, bal : Ballot, val : Value]

BMessage ==
    1aMessage \cup 1bMessage \cup 1cMessage \cup 2avMessage \cup 2bMessage
-----------------------------------------------------------------------------

(****************************************************************************
(* TODO description *)

--algorithm HPaxos {

    variables
        maxBal  = [l \in Learner, a \in Acceptor |-> -1],
        votesSent = [a \in Acceptor |-> {}],
        2avSent = [l \in Learner, a \in Acceptor |-> {}],
        received = [l \in Learner, a \in Acceptor |-> {}],
        connected = [a \in Acceptor |-> {}],
        receivedByLearner = [l \in Learner |-> {}],
        decision = [l \in Learner, b \in Ballot |-> {}],
        msgs = {}

    define {
        sentMsgs(type, lr, bal) ==
            {m \in msgs: m.type = type /\ m.lr = lr /\ m.bal = bal}

        sentMsgsAnywhere(type, bal) ==
            { m \in msgs: m.type = type /\ m.bal = bal }

        initializedBallot(lr, bal) == sentMsgs("1a", lr, bal) # {}
        (*announcements(lr, bal) == sentMsgs("1c", lr, bal)*)
        announcedValues(lr, bal) == { m.val : m \in sentMsgs("1c", lr, bal) }

        KnowsSafeAt(l, ac, b, v) ==
            LET S == {m \in received[ac] : m.type = "1b" /\ m.lr = l /\ m.bal = b}
            IN  \/ \E BQ \in ByzQuorum :
                    /\ [lr |-> l, q |-> BQ] \in TrustLive
                    /\ \A a \in BQ :
                        \E m \in S :
                            /\ m.acc = a
                            /\ \A p \in m.votes :
                                    b <= p.bal
                \/ \E c \in 0..(b-1):
                    /\ \E BQ \in ByzQuorum :
                        /\ [lr |-> l, q |-> BQ] \in TrustLive
                        /\ \A a \in BQ :
                            \E m \in S :
                                /\ m.acc = a
                                /\ \A p \in m.votes :
                                    /\ p.bal =< c
                                    /\ (p.bal = c) => (p.val = v)
                    /\ \E WQ \in ByzQuorum :
                        /\ [lr |-> l, q |-> WQ] \in TrustLive
                        /\ \A a \in WQ :
                            \E m \in S :
                                    /\ m.acc = a
                                    /\ \E p \in m.proposals :
                                        /\ p.bal = c (* TODO *)
                                        /\ p.val = v
    }

    macro SendMessage(m) { msgs := msgs \cup { m } }

    macro Phase1a(l) { SendMessage([type |-> "1a", lr |-> l, bal |-> self]) }

    macro Phase1b(l, b)
    {
        when /\ maxBal[l, self] <= b
             /\ initializedBallot(l, b) ;
        maxBal[l, self] := b ;
        SendMessage(
            [
                type |-> "1b",
                lr |-> l,
                acc |-> self,
                bal |-> b,
                votes |-> {p \in votesSent[self] : p.bal < b},
                proposals |-> {p \in 2avSent[l, self] : p.bal < b}
            ]
        )
    }

    macro Phase1c(l)
    {
        with (m \in [type : {"1c"}, lr : {l}, bal : {self}, val : Value])
        {
            SendMessage(m)
        }
    }

    macro Phase2av(l, b)
    {
        when /\ maxBal[l, self] =< b
             /\ initializedBallot(l, b) ;
        with (
            v \in { va \in announcedValues(l, b) :
                /\ \A L \in Learner :
                   \A P \in {p \in 2avSent[L, self] : p.bal = b} :
                        P.val = va
                /\ KnowsSafeAt(l, self, b, va) }
        )
        {
            SendMessage(
                [type |-> "2av", lr |-> l, acc |-> self, bal |-> b, val |-> v]
            ) ;
            2avSent[l, self] :=
                2avSent[l, self] \cup { [bal |-> b, val |-> v] }
        }
    }

    macro Phase2b(l, b)
    {
        when \A L \in Learner : maxBal[L, self] <= b ;
        with (
            v \in {vv \in Value :
                    \E Q \in ByzQuorum :
                        /\ [lr |-> l, q |-> Q] \in TrustLive
                        /\ \A aa \in Q :
                            \E m \in {mm \in received[l, self] :
                                        /\ mm.type = "2av"
                                        /\ mm.bal = b} :
                                /\ m.val = vv
                                /\ m.acc = aa}
        )
        {
            SendMessage(
                [type |-> "2b", lr |-> l, acc |-> self, bal |-> b, val |-> v]
            ) ;
            votesSent[self] := votesSent[self] \cup {[bal |-> b, val |-> v]}
        }
    }

    macro Receive(l, b)
    {
        with (m \in sentMsgs("1b", l, b) \cup sentMsgs("2av", l, b))
        {
            received[l, self] := received[l, self] \cup { m }
        }
    }

    macro LearnerReceive(b)
    {
        with (m \in sentMsgs("2b", self, b))
        {
            receivedByLearner[self] := receivedByLearner[self] \cup {m}
        }
    }

    macro FakingAcceptor()
    {
        with (m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage : mm.acc = self })
        {
            SendMessage(m)
        }
    }

    macro Decide(b)
    {
        with (
            v \in {vv \in Value :
                    \E Q \in ByzQuorum :
                        /\ [lr |-> self, q |-> Q] \in TrustLive
                        /\ \A aa \in Q :
                            \E m \in {mm \in receivedByLearner[self] : mm.bal = b} :
                                /\ m.val = vv
                                /\ m.acc = aa}
        )
        {
            decision[self, b] := decision[self, b] \cup {v}
        }
    }

    process (leader \in Ballot)
    {
        ldr: while (TRUE)
        {
            with (l \in Learner) { either Phase1a(l) or Phase1c(l) }
        }
    }

    process (acceptor \in SafeAcceptor)
    {
        acc: while (TRUE)
        {
            with (b \in Ballot, l \in Learner)
            {
                either Phase1b(l, b)
                    or Phase2av(l, b)
                    or Phase2b(l, b)
                    or Receive(l, b)
            }
        }
    }

    process (facceptor \in FakeAcceptor)
    {
        facc : while (TRUE) { FakingAcceptor() }
    }

    process (learner \in Learner)
    {
        lrn : while (TRUE) { with (b \in Ballot) { Decide(b) } }
    }
}
****************************************************************************)

\* BEGIN TRANSLATION (chksum(pcal) = "2c60bdbe" /\ chksum(tla) = "e7f49c68")
VARIABLES maxBal, votesSent, 2avSent, received, connected, receivedByLearner, 
          decision, msgs

(* define statement *)
sentMsgs(type, lr, bal) ==
    {m \in msgs: m.type = type /\ m.lr = lr /\ m.bal = bal}

sentMsgsAnywhere(type, bal) ==
    { m \in msgs: m.type = type /\ m.bal = bal }

initializedBallot(lr, bal) == sentMsgs("1a", lr, bal) # {}

announcedValues(lr, bal) == { m.val : m \in sentMsgs("1c", lr, bal) }

KnowsSafeAt(l, ac, b, v) ==
    LET S == {m \in received[ac] : m.type = "1b" /\ m.lr = l /\ m.bal = b}
    IN  \/ \E BQ \in ByzQuorum :
            /\ [lr |-> l, q |-> BQ] \in TrustLive
            /\ \A a \in BQ :
                \E m \in S :
                    /\ m.acc = a
                    /\ \A p \in m.votes :
                            b <= p.bal
        \/ \E c \in 0..(b-1):
            /\ \E BQ \in ByzQuorum :
                /\ [lr |-> l, q |-> BQ] \in TrustLive
                /\ \A a \in BQ :
                    \E m \in S :
                        /\ m.acc = a
                        /\ \A p \in m.votes :
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


vars == << maxBal, votesSent, 2avSent, received, connected, receivedByLearner, 
           decision, msgs >>

ProcSet == (Ballot) \cup (SafeAcceptor) \cup (FakeAcceptor) \cup (Learner)

Init == (* Global variables *)
        /\ maxBal = [l \in Learner, a \in Acceptor |-> -1]
        /\ votesSent = [a \in Acceptor |-> {}]
        /\ 2avSent = [l \in Learner, a \in Acceptor |-> {}]
        /\ received = [l \in Learner, a \in Acceptor |-> {}]
        /\ connected = [a \in Acceptor |-> {}]
        /\ receivedByLearner = [l \in Learner |-> {}]
        /\ decision = [l \in Learner, b \in Ballot |-> {}]
        /\ msgs = {}

leader(self) == /\ \E l \in Learner:
                     \/ /\ msgs' = (msgs \cup { ([type |-> "1a", lr |-> l, bal |-> self]) })
                     \/ /\ \E m \in [type : {"1c"}, lr : {l}, bal : {self}, val : Value]:
                             msgs' = (msgs \cup { m })
                /\ UNCHANGED << maxBal, votesSent, 2avSent, received, 
                                connected, receivedByLearner, decision >>

acceptor(self) == /\ \E b \in Ballot:
                       \E l \in Learner:
                         \/ /\ /\ maxBal[l, self] <= b
                               /\ initializedBallot(l, b)
                            /\ maxBal' = [maxBal EXCEPT ![l, self] = b]
                            /\ msgs' = (msgs \cup { ([
                                                         type |-> "1b",
                                                         lr |-> l,
                                                         acc |-> self,
                                                         bal |-> b,
                                                         votes |-> {p \in votesSent[self] : p.bal < b},
                                                         proposals |-> {p \in 2avSent[l, self] : p.bal < b}
                                                     ]) })
                            /\ UNCHANGED <<votesSent, 2avSent, received>>
                         \/ /\ /\ maxBal[l, self] =< b
                               /\ initializedBallot(l, b)
                            /\ \E v \in   { va \in announcedValues(l, b) :
                                        /\ \A L \in Learner :
                                           \A P \in {p \in 2avSent[L, self] : p.bal = b} :
                                                P.val = va
                                        /\ KnowsSafeAt(l, self, b, va) }:
                                 /\ msgs' = (msgs \cup { ([type |-> "2av", lr |-> l, acc |-> self, bal |-> b, val |-> v]) })
                                 /\ 2avSent' = [2avSent EXCEPT ![l, self] = 2avSent[l, self] \cup { [bal |-> b, val |-> v] }]
                            /\ UNCHANGED <<maxBal, votesSent, received>>
                         \/ /\ \A L \in Learner : maxBal[L, self] <= b
                            /\ \E v \in {vv \in Value :
                                          \E Q \in ByzQuorum :
                                              /\ [lr |-> l, q |-> Q] \in TrustLive
                                              /\ \A aa \in Q :
                                                  \E m \in {mm \in received[l, self] :
                                                              /\ mm.type = "2av"
                                                              /\ mm.bal = b} :
                                                      /\ m.val = vv
                                                      /\ m.acc = aa}:
                                 /\ msgs' = (msgs \cup { ([type |-> "2b", lr |-> l, acc |-> self, bal |-> b, val |-> v]) })
                                 /\ votesSent' = [votesSent EXCEPT ![self] = votesSent[self] \cup {[bal |-> b, val |-> v]}]
                            /\ UNCHANGED <<maxBal, 2avSent, received>>
                         \/ /\ \E m \in sentMsgs("1b", l, b) \cup sentMsgs("2av", l, b):
                                 received' = [received EXCEPT ![l, self] = received[l, self] \cup { m }]
                            /\ UNCHANGED <<maxBal, votesSent, 2avSent, msgs>>
                  /\ UNCHANGED << connected, receivedByLearner, decision >>

facceptor(self) == /\ \E m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage : mm.acc = self }:
                        msgs' = (msgs \cup { m })
                   /\ UNCHANGED << maxBal, votesSent, 2avSent, received, 
                                   connected, receivedByLearner, decision >>

learner(self) == /\ \E b \in Ballot:
                      \E v \in {vv \in Value :
                                 \E Q \in ByzQuorum :
                                     /\ [lr |-> self, q |-> Q] \in TrustLive
                                     /\ \A aa \in Q :
                                         \E m \in {mm \in receivedByLearner[self] : mm.bal = b} :
                                             /\ m.val = vv
                                             /\ m.acc = aa}:
                        decision' = [decision EXCEPT ![self, b] = decision[self, b] \cup {v}]
                 /\ UNCHANGED << maxBal, votesSent, 2avSent, received, 
                                 connected, receivedByLearner, msgs >>

Next == (\E self \in Ballot: leader(self))
           \/ (\E self \in SafeAcceptor: acceptor(self))
           \/ (\E self \in FakeAcceptor: facceptor(self))
           \/ (\E self \in Learner: learner(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
-----------------------------------------------------------------------------

Safety ==
    \A <<L1, L2>> \in Ent : \A B1, B2 \in Ballot : \A V1, V2 \in Value :
        V1 \in decision[L1, B1] /\ V2 \in decision[L2, B2] => V1 = V2

THEOREM Spec => []Safety

==============================================================================
