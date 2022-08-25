--------------------------- MODULE HPaxosTR_proof ---------------------------
EXTENDS HPaxosTR, NaturalsInduction, WellFoundedInduction, TLAPS

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
    /\ \A n \in MessageDepth : MessageRec[n] \subseteq Message
    /\ \A m \in Message : \E n \in Nat : m \in MessageRec[n]
PROOF BY DEF Message, MessageDepth

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
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) BY DEF Message
<1>0. P(0) BY MessageRec_eq0 DEF MessageRec0
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
   BY <1>1, MessageRec_eq1 DEF MessageRec1, Message
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa


LEMMA B_func ==
    ASSUME NEW m \in Message,
           NEW b1 \in Ballot, B(m, b1),
           NEW b2 \in Ballot, B(m, b2)
    PROVE b1 = b2
PROOF BY DEF B, Get1a, Ballot
=============================================================================
\* Modification History
\* Last modified Thu Aug 25 10:22:00 CEST 2022 by aleph
\* Created Thu Aug 25 10:12:00 CEST 2022 by aleph
