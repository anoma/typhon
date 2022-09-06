--------------------------- MODULE HPaxosTR_proof ---------------------------
EXTENDS HPaxosTR, Sequences, NaturalsInduction, WellFoundedInduction, TLAPS

-----------------------------------------------------------------------------

LEMMA FinSubset_sub ==
    ASSUME NEW S, NEW K \in Nat, NEW F \in FINSUBSET(S, K)
    PROVE F \subseteq S
PROOF BY DEF Range, FINSUBSET

LEMMA FinSubset_finite ==
    ASSUME NEW S, NEW K \in Nat, NEW F \in FINSUBSET(S, K)
    PROVE IsFiniteSet(F)
PROOF BY DEF FINSUBSET, IsFiniteSet, Range

LEMMA IsFiniteSet_add ==
    ASSUME NEW S, IsFiniteSet(S), NEW x
    PROVE IsFiniteSet(S \cup {x})
PROOF
<1> PICK seq \in Seq(S) : \A s \in S : \E n \in 1..Len(seq) : seq[n] = s
    BY DEF IsFiniteSet
<1> DEFINE f == [i \in 1..(Len(seq) + 1) |->
                    IF i < Len(seq) + 1 THEN seq[i] ELSE x]
<1> f \in Seq(S \cup {x}) BY DEF Seq
<1> Len(f) = Len(seq) + 1 OBVIOUS
<1>1. SUFFICES ASSUME NEW s \in S \cup {x} PROVE \E i \in 1..Len(f) : f[i] = s
      BY Zenon DEF IsFiniteSet
<1>9. QED BY <1>1


-----------------------------------------------------------------------------
(* Messages *)

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
PROOF BY DEF Message, MessageDepthRange

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
        BY <2>1, MessageRec_eq1, MessageRec_ref0, FinSubset_sub DEF MessageRec1
  <2>2. CASE m # 0
        BY <1>1, <2>2, MessageRec_eq1, MessageRec_monotone, FinSubset_sub DEF MessageRec1
  <2>3. QED BY <2>1, <2>2
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA Message_ref ==
    ASSUME NEW m \in Message
    PROVE m.ref \subseteq Message
PROOF BY MessageRec_ref0, MessageRec_ref1, Message_spec DEF MessageDepthRange

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
        BY <1>0, <1>2, MessageRec_eq1, FinSubset_sub DEF MessageRec1
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

\*LEMMA XXX1 ==
\*    ASSUME NEW M \in SUBSET Message, IsFiniteSet(M),
\*           NEW A \in Acceptor 
\*    PROVE [type |-> "1b", acc |-> A, ref |-> M] \in Message
\*PROOF
\*<1> PICK n \in Nat : \A m \in M : m \in MessageRec[n] BY Message_finite_1
\*<1> [type |-> "1b", acc |-> A, ref |-> M] \in MessageRec[n + 1]
\*    BY MessageRec_eq1 DEF MessageRec1
\*<1>10. QED

-----------------------------------------------------------------------------
(* Transitive references *)

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
PROOF BY DEF Tran, TranDepthRange, MessageDepthRange

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
PROOF BY Tran_spec, TranBound_Message

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
<1>0. PICK n1 \in Nat : m2 \in TranBound[n1][m1] BY Tran_spec
<1>1. PICK n2 \in Nat : m3 \in TranBound[n2][m2] BY TranBound_Message, Tran_spec
<1>2. m3 \in TranBound[n2 + n1][m1] BY TranBound_trans, <1>0, <1>1
<1>3. QED BY <1>2, Tran_spec

LEMMA Message_ref_Tran ==
    ASSUME NEW m1 \in Message, NEW m2 \in m1.ref
    PROVE m2 \in Tran(m1)
PROOF BY Message_ref_TranBound1 DEF Tran, TranDepthRange, MessageDepthRange

LEMMA MessageRec0_Tran ==
    ASSUME NEW m1 \in MessageRec[0], NEW m2 \in Tran(m1)
    PROVE m1 = m2
PROOF
<1> m1 \in Message BY Message_spec DEF MessageDepthRange
<1> PICK k \in Nat : m2 \in TranBound[k][m1] BY Tran_spec
<1> m2 \in Message BY Tran_Message
<1>1. CASE k = 0 BY TranBound_eq0, <1>1
<1>2. CASE k # 0
  <2>1. CASE m2 \in UNION { TranBound[k - 1][r] : r \in m1.ref }
        BY <2>1, MessageRec_eq0 DEF MessageRec0
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
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j)
    BY Tran_spec, Message_spec DEF MessageDepthRange
<1>0. P(0) BY TranBound_eq0, Message_spec
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1)
  <2> SUFFICES ASSUME NEW k \in Nat,
                      NEW x \in MessageRec[k],
                      NEW y \in TranBound[m + 1][x]
               PROVE y \in MessageRec[k]
      OBVIOUS
  <2> SUFFICES ASSUME k # 0 PROVE y \in MessageRec[k]
      BY MessageRec0_Tran DEF Tran, TranDepthRange, MessageDepthRange
  <2> x \in Message BY Message_spec
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
    BY DEF Message, MessageDepthRange
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
<1> PICK n \in Nat : m2 \in TranBound[n][m1] BY Tran_spec
<1> SUFFICES ASSUME n # 0 PROVE m1 = m2 BY TranBound_eq0
<1>1. CASE m1 = m2 BY <1>1
<1>2. CASE m2 \in UNION { TranBound[n - 1][r] : r \in m1.ref }
  <2> PICK r \in m1.ref : m2 \in TranBound[n - 1][r] BY <1>2
  <2> r \in Message BY Message_ref
  <2> m2 \in Tran(r) BY Tran_spec
  <2>1. m1 \in Tran(r) BY Tran_trans
  <2>2. QED BY <2>1, Tran_ref_acyclic
<1>3. QED BY <1>1, <1>2, TranBound_eq1, Isa

-----------------------------------------------------------------------------
LEMMA MessageTypeOK ==
    ASSUME NEW m \in Message 
    PROVE /\ m.type = "1a" => /\ m.bal \in Ballot
                              /\ m.val \in Value
                              /\ m.ref = {}
          /\ m.type = "1b" => /\ m.acc \in Acceptor
                              /\ m.ref \in SUBSET Message
          /\ m.type = "2a" => /\ m.lrn \in Learner
                              /\ m.acc \in Acceptor
                              /\ m.ref \in SUBSET Message 
PROOF
<1> DEFINE P(n) ==
        \A x \in MessageRec[n] :
            /\ x.type = "1a" => /\ x.bal \in Ballot
                                /\ x.val \in Value
                                /\ x.ref = {}
            /\ x.type = "1b" => /\ x.acc \in Acceptor
                                /\ x.ref \in SUBSET Message
            /\ x.type = "2a" => /\ x.lrn \in Learner
                                /\ x.acc \in Acceptor
                                /\ x.ref \in SUBSET Message
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) BY Message_spec
<1>0. P(0) BY MessageRec_eq0 DEF MessageRec0
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
      BY <1>1, MessageRec_eq1, Message_spec, FinSubset_sub DEF MessageRec1, Message
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa


LEMMA B_func ==
    ASSUME NEW m \in Message,
           NEW b1 \in Ballot, B(m, b1),
           NEW b2 \in Ballot, B(m, b2)
    PROVE b1 = b2
PROOF BY DEF B, Get1a, Ballot

-----------------------------------------------------------------------------
DecisionSpec ==
    \A L \in Learner : \A BAL \in Ballot : \A VAL \in Value :
        VAL \in decision[L, BAL] => ChosenIn(L, BAL, VAL)



\* vars == << msgs, known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns, decision >>
TypeOK ==
    /\ msgs \in SUBSET Message
    /\ known_msgs \in [Acceptor \cup Learner -> SUBSET Message]
    /\ recent_msgs \in [Acceptor \cup Learner -> SUBSET Message]
    /\ 2a_lrn_loop \in [Acceptor -> BOOLEAN]
    /\ processed_lrns \in [Acceptor -> SUBSET Learner]
    /\ decision \in [Learner \X Ballot -> SUBSET Value]

LEMMA WellFormedMessage ==
    ASSUME NEW M, WellFormed(M)
    PROVE M \in Message
BY DEF WellFormed

LEMMA TypeOKInvariant == TypeOK /\ Next => TypeOK'
PROOF
<1> SUFFICES ASSUME TypeOK, Next PROVE TypeOK' OBVIOUS
<1> USE DEF Next
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot, val \in Value : Send1a(bal, val) BY <1>1 DEF ProposerSendAction
  <2> [type |-> "1a", bal |-> bal, val |-> val, ref |-> {}] \in Message
        BY Message_spec, MessageRec_eq0 DEF MessageRec0
  <2> QED BY Zenon DEF Send1a, Send, TypeOK            
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1a(acc, msg)
      BY <1>2
  <2> msg \in Message BY DEF TypeOK
  <2> msgs' \in SUBSET Message
        BY WellFormedMessage, Zenon DEF Process1a, Send, TypeOK
  <2> known_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
        BY Zenon DEF Process1a, Recv, TypeOK
  <2> QED BY DEF Process1a, TypeOK
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>3
  <2> acc \in Acceptor BY AcceptorAssumption
  <2> known_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY DEF Process1b, Recv, TypeOK
  <2> QED BY Zenon DEF Process1b, TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner : Process1bLearnerLoopStep(acc, lrn)
      BY <1>4
  <2> acc \in Acceptor BY AcceptorAssumption
  <2> msgs' \in SUBSET Message
      BY WellFormedMessage, Zenon DEF Process1bLearnerLoopStep, Send, TypeOK
  <2> 2a_lrn_loop' \in [Acceptor -> BOOLEAN]
      BY Zenon DEF Process1bLearnerLoopStep, TypeOK
  <2> recent_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY AllProvers, WellFormedMessage, AcceptorAssumption DEF Process1bLearnerLoopStep, TypeOK
  <2> processed_lrns' \in [Acceptor -> SUBSET Learner]
      BY Isa DEF Process1bLearnerLoopStep, TypeOK
  <2>1. QED BY DEF Process1bLearnerLoopStep, TypeOK
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5, Zenon DEF Process1bLearnerLoopDone, TypeOK
<1>6. CASE LearnerAction
      BY <1>6, Isa DEF LearnerAction, LearnerRecv, LearnerDecide, Recv, TypeOK
<1>7. CASE FakeAcceptorAction
      BY <1>7 DEF FakeAcceptorAction, FakeSend, Send, TypeOK
<1>8. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7
          DEF AcceptorProcessAction, Process1bLearnerLoop 

LEMMA DecisionSpecInvariant == TypeOK /\ Next /\ DecisionSpec => DecisionSpec'
PROOF OMITTED

LEMMA ChosenSafe ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
               NEW B1 \in Ballot, NEW B2 \in Ballot,
               NEW V1 \in Value, NEW V2 \in Value,
               TypeOK, \*ReceivedSpec, ReceivedByLearnerSpec, VotesSentSpec4, MsgInv,
               \*HeterogeneousSpec,
               <<L1, L2>> \in Ent,
               ChosenIn(L1, B1, V1), ChosenIn(L2, B2, V2)
    PROVE V1 = V2

LEMMA SafetyStep ==
    TypeOK /\ Next /\
    DecisionSpec /\
    Safety => Safety'
PROOF
<1> SUFFICES
        ASSUME TypeOK, Next,
               DecisionSpec,
               Safety,
               NEW L1 \in Learner, NEW L2 \in Learner,
               NEW B1 \in Ballot, NEW B2 \in Ballot,
               NEW V1 \in Value, NEW V2 \in Value,
               <<L1, L2>> \in Ent,
               V1 \in decision'[L1, B1], V2 \in decision'[L2, B2]
        PROVE V1 = V2
    BY DEF Safety
<1>1. CASE ProposerSendAction
      BY <1>1 DEF ProposerSendAction, Send1a, Safety
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
      BY <1>2 DEF Process1a, Safety
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
      BY <1>3 DEF Process1b, Safety
<1>4. CASE \E a \in SafeAcceptor : \E l \in Learner : Process1bLearnerLoopStep(a, l)
      BY <1>4 DEF Process1bLearnerLoopStep, Safety
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5 DEF Process1bLearnerLoopDone, Safety
<1>6. CASE \E lrn \in Learner : LearnerRecv(lrn)
      BY <1>6 DEF LearnerRecv, Safety
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
        /\ ChosenIn(lrn, bal, val)
        /\ decision' = [decision EXCEPT ![<<lrn, bal>>] = decision[lrn, bal] \cup {val}]
        /\ UNCHANGED << msgs, known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns >>
      BY <1>7 DEF LearnerDecide
  <2> CASE V1 # V2
    <3>1. CASE val # V1 /\ val # V2 BY <3>1 DEF Safety, TypeOK
    <3>2. CASE val = V1
      <4> V2 \in decision[L2, B2] BY <3>2 DEF TypeOK
      <4>1. ChosenIn(L2, B2, V2) BY DEF DecisionSpec
      <4>2. CASE V1 \in decision[L1, B1] BY <4>2 DEF Safety
      <4>3. CASE V1 \notin decision[L1, B1]
        <5> lrn = L1 /\ bal = B1 BY <4>3, <3>2 DEF TypeOK
        <5>2. ChosenIn(L1, B1, V1) BY <3>2
        <5>3. QED BY <4>1, <5>2, ChosenSafe
      <4>4. QED BY <4>2, <4>3
    <3>3. CASE val = V2
      <4> V1 \in decision[L1, B1] BY <3>3 DEF TypeOK
      <4>1. ChosenIn(L1, B1, V1) BY DEF DecisionSpec
      <4>2. CASE V2 \in decision[L2, B2] BY <4>2 DEF Safety
      <4>3. CASE V2 \notin decision[L2, B2]
        <5> lrn = L2 /\ bal = B2 BY <4>3, <3>2 DEF TypeOK
        <5>2. ChosenIn(L2, B2, V2) BY <3>3
        <5>3. QED BY <4>1, <5>2, ChosenSafe
      <4>4. QED BY <4>2, <4>3
    <3>10. QED BY <3>1, <3>2, <3>3
  <2>10. QED OBVIOUS
<1>8. CASE FakeAcceptorAction
      BY <1>8 DEF FakeAcceptorAction, FakeSend, Safety
<1>9. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8
          DEF Next, AcceptorProcessAction, Process1bLearnerLoop, LearnerAction 

-----------------------------------------------------------------------------
\*LEMMA SafetyStep ==
\*    TypeOK /\ Next /\ MsgInv /\
\*    DecisionSpec /\ ReceivedSpec /\ ReceivedByLearnerSpec /\
\*    2avSentSpec1 /\ 2avSentSpec3 /\ VotesSentSpec4 /\
\*    HeterogeneousSpec /\ Safety => Safety'
\*PROOF
\*<1> SUFFICES
\*        ASSUME TypeOK, Next, MsgInv, Safety, DecisionSpec, ReceivedSpec, ReceivedByLearnerSpec,
\*               2avSentSpec1, 2avSentSpec3, VotesSentSpec4,
\*               HeterogeneousSpec,
\*               NEW L1 \in Learner, NEW L2 \in Learner,
\*               NEW B1 \in Ballot, NEW B2 \in Ballot,
\*               NEW V1 \in Value, NEW V2 \in Value,
\*               <<L1, L2>> \in Ent,
\*               V1 \in decision'[L1, B1], V2 \in decision'[L2, B2]
\*        PROVE V1 = V2
\*    BY DEF Safety
\*<1>0a. TypeOK OBVIOUS
\*<1>0b. TypeOK' BY TypeOKInvariant
\*<1>1. CASE ProposerAction BY <1>1 DEF ProposerAction, Phase1a, Phase1c, Send, Safety
\*<1>2. CASE AcceptorSendAction
\*  <2>0. SUFFICES ASSUME NEW lrn \in Learner,
\*                      NEW bal \in Ballot,
\*                      NEW acc \in SafeAcceptor,
\*                      NEW val \in Value,
\*                      \/ Phase1b(lrn, bal, acc)
\*                      \/ Phase2av(lrn, bal, acc, val)
\*                      \/ Phase2b(lrn, bal, acc, val)
\*               PROVE V1 = V2
\*        BY <1>2 DEF AcceptorSendAction
\*  <2>2. CASE Phase1b(lrn, bal, acc) BY <2>2, <1>0a, <1>0b DEF AcceptorSendAction, Send, Phase1b, Safety, TypeOK
\*  <2>3. CASE Phase2av(lrn, bal, acc, val) BY <2>3, <1>0a, <1>0b DEF AcceptorSendAction, Send, Phase2av, Safety, TypeOK
\*  <2>4. CASE Phase2b(lrn, bal, acc, val) BY <2>4, <1>0a, <1>0b DEF AcceptorSendAction, Send, Phase2b, Safety, TypeOK
\*  <2>5. QED BY <2>0, <2>2, <2>3, <2>4
\*<1>3. CASE AcceptorReceiveAction BY <1>3, <1>0a, <1>0b DEF AcceptorReceiveAction, Recv, TypeOK, Safety
\*<1>4. CASE AcceptorDisconnectAction BY <1>4 DEF AcceptorDisconnectAction, Disconnect, Safety
\*<1>5. CASE LearnerAction
\*  <2> SUFFICES ASSUME NEW lrn \in Learner, NEW bal \in Ballot,
\*                       \/ LearnerDecide(lrn, bal)
\*                       \/ LearnerRecv(lrn)
\*               PROVE V1 = V2 BY <1>5 DEF LearnerAction
\*  <2>1. CASE LearnerRecv(lrn) BY <2>1 DEF LearnerRecv, Safety
\*  <2>2. CASE LearnerDecide(lrn, bal)
\*    <3> SUFFICES ASSUME NEW val \in Value,
\*                        ChosenIn(lrn, bal, val),
\*                        decision' = [decision EXCEPT ![<<lrn, bal>>] = decision[lrn, bal] \cup {val}],
\*                        UNCHANGED <<msgs, maxBal, votesSent, 2avSent, received, connected, receivedByLearner>>
\*                 PROVE V1 = V2
\*        BY <2>2 DEF LearnerDecide
\*    <3>0. CASE V1 = V2 BY <3>0
\*    <3>1. CASE V1 # V2
\*      <4>1. CASE val # V1 /\ val # V2 BY <4>1 DEF Safety, TypeOK
\*      <4>2. CASE val = V1
\*        <5>0. V2 \in decision[L2, B2] BY <3>1, <4>2 DEF TypeOK
\*        <5>1. ChosenIn(L2, B2, V2) BY <5>0 DEF DecisionSpec
\*        <5>2. CASE V1 \in decision[L1, B1] BY <5>0, <5>2 DEF Safety
\*        <5>3. CASE V1 \notin decision[L1, B1]
\*          <6>1. lrn = L1 /\ bal = B1 BY <5>3, <4>2 DEF TypeOK
\*          <6>2. ChosenIn(L1, B1, V1) BY <6>1, <4>2
\*          <6>3. QED BY <5>1, <6>2, ChosenSafe
\*        <5>4. QED BY <5>2, <5>3
\*      <4>3. CASE val = V2
\*        <5>0. V1 \in decision[L1, B1] BY <3>1, <4>3 DEF TypeOK
\*        <5>1. ChosenIn(L1, B1, V1) BY <5>0 DEF DecisionSpec
\*        <5>2. CASE V2 \in decision[L2, B2] BY <5>0, <5>2 DEF Safety
\*        <5>3. CASE V2 \notin decision[L2, B2]
\*          <6>1. lrn = L2 /\ bal = B2 BY <5>3, <4>3 DEF TypeOK
\*          <6>2. ChosenIn(L2, B2, V2) BY <6>1, <4>3
\*          <6>10. QED BY <5>1, <6>2, ChosenSafe
\*        <5>4. QED BY <5>2, <5>3
\*      <4>4. QED BY <4>1, <4>2, <4>3
\*    <3>2. QED BY <3>0, <3>1
\*  <2>3. QED BY <2>1, <2>2
\*<1>6. CASE FakeAcceptorAction BY <1>6 DEF FakeAcceptorAction, FakeSend, Send, Safety
\*<1>7. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

=============================================================================
\* Modification History
\* Last modified Tue Sep 06 19:55:15 CEST 2022 by aleph
\* Created Thu Aug 25 10:12:00 CEST 2022 by aleph
