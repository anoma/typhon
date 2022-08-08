------------------------------ MODULE HPaxosTR ------------------------------
EXTENDS Naturals, Integers, NaturalsInduction, WellFoundedInduction, TLAPS

-----------------------------------------------------------------------------
CONSTANT LastBallot
ASSUME LastBallot \in Int

Ballot == 0..LastBallot
\*Ballot == Int

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

CONSTANT Ent
\*ASSUME EntanglementAssumption1 ==
\*        Ent \in SUBSET(Learner \X Learner)
\*ASSUME EntanglementAssumption2 ==
\*        \A L1, L2 \in Learner :
\*              <<L1, L2>> \in Ent =>
\*              [from |-> L1, to |-> L2, q |-> SafeAcceptor] \in TrustSafe
\*ASSUME EntanglementAssumption3 ==
\*        \A L1, L2 \in Learner :
\*              [from |-> L1, to |-> L2, q |-> SafeAcceptor] \in TrustSafe =>
\*              <<L1, L2>> \in Ent

ASSUME EntanglementAssumption ==
        /\ Ent \in SUBSET(Learner \X Learner)
        /\ \A L1, L2 \in Learner :
              <<L1, L2>> \in Ent <=>
              [from |-> L1, to |-> L2, q |-> SafeAcceptor] \in TrustSafe

-----------------------------------------------------------------------------
(* Messages *)

MessageRec0 ==
    [ type : {"1a"}, lr : Learner, bal : Ballot, val : Value, ref : {} ] \cup
    [ type : {"1b"}, lr : Learner, ref : {} ] \cup
    [ type : {"2a"}, lr : Learner, ref : {} ]

MessageRec1(M, n) ==
    M \cup
    [ type : {"1a"}, lr : Learner, bal : Ballot, val : Value, ref : SUBSET M ] \cup
    [ type : {"1b"}, lr : Learner, ref : SUBSET M ] \cup
    [ type : {"2a"}, lr : Learner, ref : SUBSET M ]

MessageRec ==
    CHOOSE MessageRec :
    MessageRec = [n \in Nat |->
                    IF n = 0
                    THEN MessageRec0
                    ELSE MessageRec1(MessageRec[n-1], n)]

Message == UNION { MessageRec[n] : n \in Nat }

LEMMA MessageRec_def ==
    MessageRec = [n \in Nat |->
                    IF n = 0
                    THEN MessageRec0
                    ELSE MessageRec1(MessageRec[n-1], n)]
PROOF BY NatInductiveDef
      DEF NatInductiveDefHypothesis, NatInductiveDefConclusion, MessageRec

LEMMA Message_spec ==
    /\ \A n \in Nat : MessageRec[n] \subseteq Message
    /\ \A m \in Message : \E n \in Nat : m \in MessageRec[n]
PROOF BY DEF Message

LEMMA MessageRec_eq0 == MessageRec[0] = MessageRec0
PROOF BY MessageRec_def

LEMMA MessageRec_eq1 ==
    ASSUME NEW n \in Nat, n # 0
    PROVE MessageRec[n] = MessageRec1(MessageRec[n-1], n)
PROOF BY MessageRec_def DEF MessageRec1

LEMMA MessageRec_monotone_1 ==
    ASSUME NEW n \in Nat
    PROVE MessageRec[n] \subseteq MessageRec[n+1]
PROOF BY MessageRec_eq1 DEF MessageRec1

LEMMA MessageRec_monotone ==
    \A n, m \in Nat : n <= m => MessageRec[n] \subseteq MessageRec[m]
PROOF
<1> DEFINE P(m) == \A n \in Nat : n < m => MessageRec[n] \subseteq MessageRec[m]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0) OBVIOUS
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1) BY <1>1, MessageRec_monotone_1
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA MessageRec_ref0 ==
    ASSUME NEW m \in MessageRec[0]
    PROVE m.ref = {}
PROOF BY MessageRec_def DEF MessageRec0

LEMMA MessageRec_ref1 ==
    ASSUME NEW n \in Nat, n # 0
    PROVE \A m \in MessageRec[n] : m.ref \subseteq MessageRec[n-1]
PROOF
<1> DEFINE P(j) == j # 0 =>
                \A mm \in MessageRec[j] : mm.ref \subseteq MessageRec[j-1]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0) OBVIOUS
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1)
  <2> SUFFICES ASSUME NEW mm \in MessageRec[m+1]
               PROVE mm.ref \subseteq MessageRec[m]
      OBVIOUS
  <2>1. CASE m = 0
        BY <2>1, MessageRec_eq1, MessageRec_ref0 DEF MessageRec1
  <2>2. CASE m # 0
        BY <1>1, <2>2, MessageRec_eq1, MessageRec_monotone DEF MessageRec1
  <2>3. QED BY <2>1, <2>2
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA Message_ref ==
    ASSUME NEW m \in Message
    PROVE m.ref \subseteq Message
PROOF BY MessageRec_ref0, MessageRec_ref1, Message_spec

LEMMA MessageRec_min ==
    ASSUME NEW m \in Message
    PROVE \E n \in Nat :
            /\ m \in MessageRec[n]
            /\ \A k \in 0 .. n - 1 : m \notin MessageRec[k]
PROOF
<1>1. DEFINE P(k) == m \in MessageRec[k]
<1>2. SUFFICES \E n \in Nat :
                /\ P(n)
                /\ \A k \in 0 .. n - 1 : ~P(k)
      OBVIOUS
<1>3. PICK n1 \in Nat : P(n1) BY Message_spec
<1>4. HIDE DEF P
<1>5. QED BY <1>3, SmallestNatural

LEMMA Message_ref_acyclic ==
    ASSUME NEW m \in Message
    PROVE m \notin m.ref
PROOF
<1>0. PICK n \in Nat :
        /\ m \in MessageRec[n]
        /\ \A k \in 0 .. n-1 : m \notin MessageRec[k]
      BY MessageRec_min
<1>1. CASE n = 0 BY <1>0, <1>1, MessageRec_eq0 DEF MessageRec0
<1>2. CASE n # 0 /\ m \in m.ref
  <2>1. m.ref \in SUBSET MessageRec[n-1]
        BY <1>0, <1>2, MessageRec_eq1 DEF MessageRec1
  <2>10. QED BY <2>1, <1>0, <1>2
<1>10. QED BY <1>1, <1>2

\*LEMMA Message_ref_acyclic_2 ==
\*    ASSUME NEW m1 \in Message, NEW m2 \in m1.ref
\*    PROVE m1 \notin m2.ref
\*PROOF
\*<1> SUFFICES ASSUME NEW x \in Message,
\*                    NEW y \in x.ref,
\*                    x \in y.ref
\*             PROVE FALSE
\*    OBVIOUS
\*<1>0. PICK n \in Nat :
\*        /\ x \in MessageRec[n]
\*        /\ \A k \in 0 .. n-1 : x \notin MessageRec[k]
\*      BY MessageRec_min
\*<1>1. n # 0 BY <1>0, MessageRec_eq0 DEF MessageRec0
\*<1>2. y \in MessageRec[n - 1] BY MessageRec_ref1, <1>0, <1>1
\*<1>3. n - 1 # 0 BY <1>2, MessageRec_eq0 DEF MessageRec0
\*<1>4. n - 1 \in Nat BY <1>1, <1>3
\*<1>5. x \in MessageRec[n - 1 - 1] BY <1>2, <1>3, <1>4, MessageRec_ref1
\*<1>6. QED BY <1>5, <1>0, <1>3, <1>4

-----------------------------------------------------------------------------
(* Transitive references *)

\* Bounded transitive references
TranBound0 == [m \in Message |-> {m}]
TranBound1(tr, n) ==
    [m \in Message |-> {m} \cup UNION {tr[r] : r \in m.ref}]

TranBound ==
    CHOOSE TranBound :
    TranBound = [n \in Nat |->
                    IF n = 0
                    THEN TranBound0
                    ELSE TranBound1(TranBound[n-1], n)]

\* Countable transitive references
Tran(m) == UNION {TranBound[n][m] : n \in Nat}

LEMMA TranBound_def ==
    TranBound = [n \in Nat |->
                    IF n = 0
                    THEN TranBound0
                    ELSE TranBound1(TranBound[n-1], n)]
PROOF BY NatInductiveDef
DEF NatInductiveDefHypothesis, NatInductiveDefConclusion, TranBound

LEMMA Tran_spec ==
    ASSUME NEW m \in Message
    PROVE
    /\ \A n \in Nat : TranBound[n][m] \subseteq Tran(m)
    /\ \A r \in Tran(m) : \E n \in Nat : r \in TranBound[n][m]
PROOF BY DEF Tran

LEMMA TranBound_eq0 ==
    TranBound[0] = [m \in Message |-> {m}]
PROOF BY TranBound_def DEF TranBound0

LEMMA TranBound_eq1 ==
    ASSUME NEW n \in Nat, n # 0
    PROVE TranBound[n] =
            [m \in Message |-> {m} \cup UNION {TranBound[n-1][r] : r \in m.ref}]
PROOF BY TranBound_def DEF TranBound1

LEMMA TranBound_Message ==
    ASSUME NEW m1 \in Message,
           NEW n \in Nat, NEW m2 \in TranBound[n][m1]
    PROVE m2 \in Message
PROOF
<1> DEFINE P(j) == \A x \in Message : \A y \in TranBound[j][x] : y \in Message
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) BY DEF Tran
<1>0. P(0) BY TranBound_eq0
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k+1)
  <2> SUFFICES ASSUME NEW x \in Message, NEW y \in TranBound[k + 1][x]
               PROVE y \in Message
      OBVIOUS
  <2> SUFFICES ASSUME NEW r \in x.ref, y \in TranBound[k][r]
               PROVE y \in Message
      BY TranBound_eq1, Isa
  <2>2. r \in Message BY Message_ref
  <2>3. QED BY <1>1, <2>2
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA Tran_Message ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1)
    PROVE m2 \in Message
PROOF BY TranBound_Message DEF Tran

LEMMA TranBound_monotone_1 ==
    ASSUME NEW n \in Nat, NEW m \in Message
    PROVE TranBound[n][m] \subseteq TranBound[n+1][m]
PROOF
<1> DEFINE P(j) == \A mm \in Message :
                    TranBound[j][mm] \subseteq TranBound[j+1][mm]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0) BY TranBound_eq0, TranBound_eq1
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k+1)
  <2> SUFFICES ASSUME NEW mm \in Message
               PROVE TranBound[k+1][mm] \subseteq TranBound[(k+1)+1][mm]
      OBVIOUS
  <2>1. SUFFICES
        UNION {TranBound[k][r] : r \in mm.ref} \subseteq
        UNION {TranBound[k+1][r] : r \in mm.ref}
        BY TranBound_eq1, Isa
  <2>6. QED BY <1>1, Message_ref
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA TranBound_monotone ==
    \A n, m \in Nat : n <= m =>
        \A mm \in Message :
            TranBound[n][mm] \subseteq TranBound[m][mm]
PROOF
<1> DEFINE P(m) == \A n \in Nat : n < m =>
                    \A mm \in Message : TranBound[n][mm] \subseteq TranBound[m][mm]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0) OBVIOUS
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1) BY <1>1, TranBound_monotone_1
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA Message_ref_TranBound1 ==
    ASSUME NEW m1 \in Message, NEW m2 \in m1.ref
    PROVE m2 \in TranBound[1][m1]
PROOF
<1> m2 \in Message BY Message_ref
<1>1. QED BY TranBound_eq0, TranBound_eq1, Isa

LEMMA TranBound_trans ==
    ASSUME NEW n1 \in Nat, NEW n2 \in Nat,
           NEW m1 \in Message,
           NEW m2 \in TranBound[n1][m1],
           NEW m3 \in TranBound[n2][m2]
    PROVE  m3 \in TranBound[n1 + n2][m1]
PROOF
<1>0. DEFINE P(n) ==
        \A k \in Nat :
        \A x \in Message :
        \A y \in TranBound[n][x] :
        \A z \in TranBound[k][y] :
            z \in TranBound[n + k][x]
<1>1. SUFFICES \A n \in Nat : P(n) OBVIOUS
<1>2. P(0) BY TranBound_eq0
<1>3. ASSUME NEW n \in Nat, P(n) PROVE P(n+1)
  <2>1. SUFFICES ASSUME NEW k \in Nat, NEW x \in Message,
                            NEW y \in TranBound[n + 1][x], NEW z \in TranBound[k][y]
                 PROVE z \in TranBound[n + 1 + k][x]
        OBVIOUS
  <2>2. CASE y = x BY <2>2, TranBound_monotone
  <2>3. CASE y \in UNION {TranBound[n][r] : r \in x.ref}
    <3>0. PICK r \in x.ref : y \in TranBound[n][r] BY <2>3
    <3>1. r \in Message BY Message_ref
    <3>2. z \in TranBound[n + k][r] BY <3>0, <3>1, <1>3
    <3>5. QED BY <3>0, <3>2, TranBound_eq1, Isa
  <2>10. QED BY <2>2, <2>3, TranBound_eq1, Isa
<1>4. HIDE DEF P
<1>5. QED BY <1>2, <1>3, NatInduction, Isa

LEMMA Tran_trans ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1), NEW m3 \in Tran(m2)
    PROVE  m3 \in Tran(m1)
PROOF
<1>0. PICK n1 \in Nat : m2 \in TranBound[n1][m1] BY DEF Tran
<1>1. PICK n2 \in Nat : m3 \in TranBound[n2][m2] BY DEF Tran
<1>2. m3 \in TranBound[n2 + n1][m1] BY TranBound_trans, <1>0, <1>1
<1>3. QED BY <1>2 DEF Tran

LEMMA Message_ref_Tran ==
    ASSUME NEW m1 \in Message, NEW m2 \in m1.ref
    PROVE m2 \in Tran(m1)
PROOF BY Message_ref_TranBound1 DEF Tran

LEMMA MessageRec0_Tran ==
    ASSUME NEW m1 \in MessageRec[0], NEW m2 \in Tran(m1)
    PROVE m1 = m2
PROOF
<1> PICK k \in Nat : m2 \in TranBound[k][m1] BY DEF Tran
<1> m1 \in Message BY DEF Message
<1> m2 \in Message BY Tran_Message
<1>1. CASE k = 0 BY TranBound_eq0, <1>1
<1>2. CASE k # 0
  <2>1. CASE m2 \in UNION { TranBound[k - 1][r] : r \in m1.ref }
        BY MessageRec_eq0 DEF MessageRec0
  <2>2. QED BY Isa, TranBound_eq1, <1>2, <2>1
<1>3. QED BY <1>1, <1>2

LEMMA MessageRec_Tran_bound ==
    ASSUME NEW n \in Nat, NEW m1 \in MessageRec[n], NEW m2 \in Tran(m1)
    PROVE m2 \in MessageRec[n]
PROOF
<1> DEFINE P(l) == \A k \in Nat :
                   \A x \in MessageRec[k] :
                   \A y \in TranBound[l][x] :
                        y \in MessageRec[k]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) BY DEF Tran
<1>0. P(0) BY TranBound_eq0, Message_spec DEF Tran
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1)
  <2> SUFFICES ASSUME NEW k \in Nat,
                      NEW x \in MessageRec[k],
                      NEW y \in TranBound[m + 1][x]
               PROVE y \in MessageRec[k]
      OBVIOUS
  <2> SUFFICES ASSUME k # 0 PROVE y \in MessageRec[k]
      BY MessageRec0_Tran DEF Tran
  <2> x \in Message BY DEF Message
  <2>1. CASE y = x BY <2>1
  <2>2. CASE y \in UNION { TranBound[m][r] : r \in x.ref }
    <3>1. PICK r \in x.ref : y \in TranBound[m][r] BY <2>2
    <3>3. r \in MessageRec[k - 1] BY MessageRec_ref1
    <3>4. y \in MessageRec[k - 1] BY <3>3, <3>1, <1>1
    <3>5. QED BY <3>4, MessageRec_monotone
  <2>3. QED BY <2>1, <2>2, TranBound_eq1, Isa
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

\*LEMMA MessageRec_TranBound ==
\*    ASSUME NEW n \in Nat, NEW m1 \in MessageRec[n], NEW m2 \in Tran(m1)
\*    PROVE \E k \in Nat : k <= n /\ m2 \in TranBound[k][m1]
\*PROOF
\*<1> DEFINE P(l) == \A k \in Nat :
\*                   \A x \in MessageRec[k] :
\*                   \A y \in TranBound[l][x] :
\*                    \E k1 \in Nat : k1 <= k /\ y \in TranBound[k1][x]
\*<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) BY DEF Tran
\*<1>0. P(0) BY TranBound_eq1, TranBound_eq1, MessageRec_eq0 DEF MessageRec0
\*<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1)
\*  <2> DEFINE E(k, x, y) == \E k1 \in Nat : k1 <= k /\ y \in TranBound[k1][x]
\*  <2> SUFFICES ASSUME NEW k \in Nat,
\*                      NEW x \in MessageRec[k],
\*                      NEW y \in TranBound[m + 1][x]
\*               PROVE E(k, x, y)
\*      BY MessageRec0_Tran DEF Tran
\*  <2> x \in Message BY Tran_Message DEF Message, Tran
\*  <2> y \in Tran(x) BY DEF Tran
\*  <2> SUFFICES ASSUME k # 0 PROVE E(k, x, y)
\*    <3>1. CASE k = 0
\*      <4>1. x = y BY <3>1, MessageRec0_Tran
\*      <4>2. WITNESS 0 \in Nat
\*      <4>3. QED BY TranBound_eq0, <4>1
\*    <3>2. QED BY <3>1
\*  <2>1. CASE y = x BY <2>1, TranBound_eq0
\*  <2>2. CASE y \in UNION { TranBound[m][r] : r \in x.ref }
\*    <3>1. PICK r \in x.ref : y \in TranBound[m][r] BY <2>2
\*    <3>3. r \in MessageRec[k - 1] BY MessageRec_ref1
\*    <3>4. PICK k2 \in Nat : k2 <= k - 1 /\ y \in TranBound[k2][r]
\*          BY <1>1, <3>1, <3>3
\*    <3>5. WITNESS k2 + 1 \in Nat
\*    <3>6. r \in TranBound[1][x] BY Message_ref_TranBound1, <3>1
\*    <3>10. QED BY <3>4, <3>6, TranBound_trans
\*  <2>4. HIDE DEF E
\*  <2>5. QED BY <2>1, <2>2, TranBound_eq1, Isa
\*<1>2. HIDE DEF P
\*<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA Tran_ref_acyclic ==
    ASSUME NEW m \in Message, NEW r \in m.ref
    PROVE m \notin Tran(r)
PROOF
<1> r \in Message BY Message_ref
<1> SUFFICES ASSUME NEW n \in Nat,
                    NEW x \in Message,
                    NEW y \in x.ref, x \in Tran(y)
             PROVE x \in MessageRec[n] => FALSE
    BY DEF Message
<1>0. PICK k \in Nat : /\ x \in MessageRec[k]
                       /\ \A k1 \in 0 .. k - 1 : x \notin MessageRec[k1]
      BY MessageRec_min
<1> SUFFICES ASSUME k # 0 PROVE FALSE
  <2>1. CASE k = 0 BY <1>0, <2>1, MessageRec_eq0 DEF MessageRec0
  <2>2. QED BY <2>1
<1>2. y \in MessageRec[k - 1] BY <1>0, MessageRec_ref1
<1>3. x \in MessageRec[k - 1] BY <1>2, MessageRec_Tran_bound
<1>4. QED BY <1>0, <1>3

LEMMA Tran_acyclic ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1),
           m1 \in Tran(m2)
    PROVE m1 = m2
PROOF
<1> PICK n \in Nat : m2 \in TranBound[n][m1] BY DEF Tran
<1> SUFFICES ASSUME n # 0 PROVE m1 = m2 BY TranBound_eq0
<1>1. CASE m1 = m2 BY <1>1
<1>2. CASE m2 \in UNION { TranBound[n - 1][r] : r \in m1.ref }
  <2> PICK r \in m1.ref : m2 \in TranBound[n - 1][r] BY <1>2
  <2> r \in Message BY Message_ref
  <2> m2 \in Tran(r) BY DEF Tran
  <2>1. m1 \in Tran(r) BY Tran_trans
  <2>2. QED BY <2>1, Tran_ref_acyclic
<1>3. QED BY <1>1, <1>2, TranBound_eq1, Isa

\*-----------------------------------------------------------------------------
(* Algorithm specification *)

VARIABLES msgs,
          \*maxBal,
          received,
          known_msgs,
          recent_msgs,
          known_msgs_by_learner,
          decision
          \*connected

\*InitializedBallot(lr, bal) ==
\*    \E m \in msgs : m.type = "1a" /\ m.lr = lr /\ m.bal = bal
\*
\*AnnouncedValue(lr, bal, val) ==
\*    \E m \in msgs : m.type = "1c" /\ m.lr = lr /\ m.bal = bal /\ m.val = val
\*
\*ChosenIn(lr, bal, v) ==
\*    \E Q \in ByzQuorum:
\*        /\ [lr |-> lr, q |-> Q] \in TrustLive
\*        /\ \A aa \in Q :
\*            \E m \in { mm \in receivedByLearner[lr] : mm.bal = bal } :
\*                /\ m.val = v
\*                /\ m.acc = aa
\*
\*KnowsSafeAt1(l, ac, b) ==
\*    LET S == { mm \in received[ac] : mm.type = "1b" /\ mm.lr = l /\ mm.bal = b }
\*    IN \E BQ \in ByzQuorum :
\*        /\ [lr |-> l, q |-> BQ] \in TrustLive
\*        /\ \A a \in BQ :
\*            \E m \in S :
\*                /\ m.acc = a
\*                /\ \A p \in { pp \in m.votes : <<pp.lr, l>> \in connected[ac] } :
\*                        b =< p.bal
\*
\*KnowsSafeAt2(l, ac, b, v) ==
\*    LET S == { mm \in received[ac] : mm.type = "1b" /\ mm.lr = l /\ mm.bal = b }
\*    IN \E c \in Ballot :
\*        /\ c < b
\*        /\ \E BQ \in ByzQuorum :
\*            /\ [lr |-> l, q |-> BQ] \in TrustLive
\*            /\ \A a \in BQ :
\*                \E m \in S :
\*                    /\ m.acc = a
\*                    /\ \A p \in { pp \in m.votes : <<pp.lr, l>> \in connected[ac] } :
\*                        /\ p.bal =< c
\*                        /\ (p.bal = c) => (p.val = v)
\*        /\ \E WQ \in ByzQuorum :
\*            /\ [lr |-> l, q |-> WQ] \in TrustLive
\*            /\ \A a \in WQ :
\*                \E m \in S :
\*                    /\ m.acc = a
\*                    /\ \E p \in m.proposals :
\*                        /\ p.lr = l
\*                        /\ p.bal = c
\*                        /\ p.val = v
\*
\*KnowsSafeAt(l, ac, b, v) ==
\*    \/ KnowsSafeAt1(l, ac, b)
\*    \/ KnowsSafeAt2(l, ac, b, v)

Proper(a, m) ==
    /\ \A r \in m.refs : r \in known_msgs[a]

ProperForLearner(l, m) ==
    /\ \A r \in m.refs : r \in known_msgs_by_learner[l]

WellFormed(m) ==
    /\ m \in Message
    \* No 1b message should reference any message with the same ballot number
    \* besides a 1a message
    \* TODO : check if we need the uniqueness assumption
    /\ m.type = "1b" =>
        /\ \A r \in m.ref : r.bal = m.bal => r.type = "1a"
        /\ \A r1, r2 \in m.ref :
            m.bal = r1.bal /\ r1.type = "1a" /\
            m.bal = r2.bal /\ r2.type = "1a" => r1 = r2
    /\ m.type = "2a" => m.acc \in m.q

vars == << msgs, known_msgs, recent_msgs, known_msgs_by_learner, decision >>
\*votesSent, 2avSent, received, connected, receivedByLearner, decision, msgs >>

\*
\*Init ==
\*    /\ msgs = {}
\*    /\ maxBal = [la \in Learner \X Acceptor |-> 0]
\*    /\ 2avSent = [a \in Acceptor |-> {}]
\*    /\ votesSent = [a \in Acceptor |-> {}]
\*    /\ connected = [a \in Acceptor |-> Learner \X Learner]
\*    /\ received = [a \in Acceptor |-> {}]
\*    /\ receivedByLearner = [l \in Learner |-> {}]
\*    /\ decision = [lb \in Learner \X Ballot |-> {}]
\*
\*TypeOK ==
\*    /\ msgs \in SUBSET Message
\*    /\ maxBal \in [Learner \X Acceptor -> Ballot]
\*    /\ votesSent \in [Acceptor -> SUBSET [lr : Learner, bal : Ballot, val : Value]]
\*    /\ 2avSent   \in [Acceptor -> SUBSET [lr : Learner, bal : Ballot, val : Value]]
\*    /\ connected \in [Acceptor -> SUBSET (Learner \X Learner)]
\*    /\ received  \in [Acceptor -> SUBSET Message]
\*    /\ receivedByLearner \in [Learner -> SUBSET Message]
\*    /\ decision \in [Learner \X Ballot -> SUBSET Value]
\*
\*Send(m) == msgs' = msgs \cup {m}
\*
\*Phase1a(l, b) ==
\*    /\ Send([type |-> "1a", lr |-> l, bal |-> b])
\*    /\ UNCHANGED << maxBal, votesSent, 2avSent, received, connected, receivedByLearner, decision >>
\*
\*Phase1c(l, b, v) ==
\*    /\ Send([type |-> "1c", lr |-> l, bal |-> b, val |-> v])
\*    /\ UNCHANGED << maxBal, votesSent, 2avSent, received, connected, receivedByLearner, decision >>
\*
\*MaxVote(a, b, vote) ==
\*    /\ vote.bal < b
\*    /\ \A other \in votesSent[a] :
\*          other.lr = vote.lr /\ other.bal < b =>
\*          other.bal =< vote.bal
\*
\*Phase1b(l, b, a) ==
\*    /\ maxBal[<<l, a>>] =< b
\*    /\ InitializedBallot(l, b)
\*    /\ maxBal' = [maxBal EXCEPT ![<<l, a>>] = b]
\*    /\ Send([
\*         type |-> "1b",
\*         lr |-> l,
\*         acc |-> a,
\*         bal |-> b,
\*         votes |-> { p \in votesSent[a] : MaxVote(a, b, p) },
\*         proposals |-> { p \in 2avSent[a] : p.bal < b }
\*       ])
\*    /\ UNCHANGED << votesSent, 2avSent, received, connected, receivedByLearner, decision >>
\*
\*Phase2av(l, b, a, v) ==
\*    /\ maxBal[l, a] =< b
\*    /\ InitializedBallot(l, b)
\*    /\ AnnouncedValue(l, b, v)
\*    /\ \A P \in { p \in 2avSent[a] : p.bal = b /\ <<p.lr, l>> \in connected[a] } : P.val = v
\*    /\ KnowsSafeAt(l, a, b, v)
\*    /\ Send([type |-> "2av", lr |-> l, acc |-> a, bal |-> b, val |-> v])
\*    /\ 2avSent' = [2avSent EXCEPT ![a] = 2avSent[a] \cup { [lr |-> l, bal |-> b, val |-> v] }]
\*    /\ UNCHANGED << maxBal, votesSent, received, connected, receivedByLearner, decision >>
\*
\*Phase2b(l, b, a, v) ==
\*    /\ \A L \in Learner : maxBal[L, a] =< b
\*    /\ \E Q \in ByzQuorum :
\*        /\ [lr |-> l, q |-> Q] \in TrustLive
\*        /\ \A aa \in Q :
\*            \E m \in { mm \in received[a] :
\*                        /\ mm.type = "2av"
\*                        /\ mm.lr = l
\*                        /\ mm.bal = b } :
\*                /\ m.val = v
\*                /\ m.acc = aa
\*    /\ Send([type |-> "2b", lr |-> l, acc |-> a, bal |-> b, val |-> v])
\*    /\ votesSent' = [votesSent EXCEPT ![a] =
\*                        votesSent[a] \cup { [lr |-> l, bal |-> b, val |-> v] }]
\*    /\ UNCHANGED << maxBal, 2avSent, received, connected, receivedByLearner, decision >>

Recv(a) ==
    /\ \E m \in msgs :
        received' = [received EXCEPT ![a] = received[a] \cup { m }]
    /\ UNCHANGED << msgs, known_msgs, recent_msgs, known_msgs_by_learner, decision >>

\*Disconnect(a) ==
\*    /\ \E P \in SUBSET { LL \in Learner \X Learner : LL \notin Ent } :
\*        connected' = [connected EXCEPT ![a] = connected[a] \ P]
\*    /\ UNCHANGED << msgs, maxBal, votesSent, 2avSent, received, known_msgs_by_learner, decision >>
\*
\*FakeSend(a) ==
\*    /\ \E m \in { mm \in Message :
\*                   /\ mm.acc = a
\*                   /\ \/ mm.type = "1b"
\*                      \/ mm.type = "2av"
\*                      \/ mm.type = "2b" } :
\*        Send(m)
\*    /\ UNCHANGED << maxBal, votesSent, 2avSent, received, connected, known_msgs_by_learner, decision >>
\*

LearnerRecv(l) ==
    /\ \E m \in { mm \in msgs : mm.type = "2a" }:
        /\ ProperForLearner(l, m)
        /\ known_msgs_by_learner' =
            [known_msgs_by_learner EXCEPT ![l] = known_msgs_by_learner[l] \cup {m}]
    /\ UNCHANGED << msgs, known_msgs, recent_msgs, decision >>

\*LearnerDecide(l, b) ==
\*    /\ \E v \in {vv \in Value : ChosenIn(l, b, vv)}:
\*        decision' = [decision EXCEPT ![<<l, b>>] = decision[l, b] \cup {v}]
\*    /\ UNCHANGED << msgs, received, known_msgs_by_learner >>

\*ProposerAction ==
\*    \E lrn \in Learner : \E proposer \in Ballot :
\*        \/ Phase1a(lrn, proposer)
\*        \/ \E v \in Value : Phase1c(lrn, proposer, v)
\*
\*AcceptorSendAction ==
\*    \E lrn \in Learner : \E bal \in Ballot : \E acc \in SafeAcceptor : \E val \in Value :
\*        \/ Phase1b(lrn, bal, acc)
\*        \/ Phase2av(lrn, bal, acc, val)
\*        \/ Phase2b(lrn, bal, acc, val)
\*
\*AcceptorReceiveAction ==
\*    \E lrn \in Learner : \E acc \in Acceptor : Recv(lrn, acc)
\*
\*AcceptorDisconnectAction ==
\*    \E acc \in SafeAcceptor : Disconnect(acc)
\*
\*LearnerAction ==
\*    \E lrn \in Learner :
\*        \/ \E bal \in Ballot : LearnerDecide(lrn, bal)
\*        \/ LearnerRecv(lrn)
\*
\*FakeAcceptorAction == \E a \in FakeAcceptor : FakeSend(a)
\*
\*Next ==
\*    \/ ProposerAction
\*    \/ AcceptorSendAction
\*    \/ AcceptorReceiveAction
\*    \/ AcceptorDisconnectAction
\*    \/ LearnerAction
\*    \/ FakeAcceptorAction
\*
\*Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Mon Aug 08 15:02:23 CEST 2022 by aleph
\* Created Mon Jul 25 14:24:03 CEST 2022 by aleph
