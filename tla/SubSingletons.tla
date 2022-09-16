---------------------------- MODULE SubSingletons ---------------------------

\* safe
\* @type: (Set(a)) => Bool;
IsNone(X) == X={}

\* safe
\* @type: (Set(a)) => Bool;
IsSome(X) == X # {}

\* safe
\* @type: (a) => Set(a);
makeSome(x) == {x}

\* unsafe
\* @type: (Set(a)) => a;
extract(X) == 
  IF X # {} /\ \A x \in X : \A y \in X : x = y 
  THEN CHOOSE x \in X: TRUE
  ELSE CHOOSE x \in X: FALSE

(* 
In the above "extract(X)", we can replace CHOOSE with Apalache's Guess;
i.o.w., this implementation can cope with Apalache's CHOOSE semantics. 
*)

=============================================================================
