---------------------------- MODULE SubSingletons ---------------------------

\* safe
\* @type: (Set(a)) => Bool;
IsEmpty(X) == X={}

\* @type: (Set(a)) => a;
Extract(X) == CHOOSE x \in X: TRUE

=============================================================================
