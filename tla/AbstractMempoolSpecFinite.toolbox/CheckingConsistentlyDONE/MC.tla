---- MODULE MC ----
EXTENDS AbstractMempoolSpecFinite, TLC

\* CONSTANT definitions @modelParameterConstants:0Payload
const_165960459924420000 == 
{1,2,3,4}
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_165960459924421000 ==
mempool \subseteq Payload
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_165960459924422000 ==
<>(ENABLED DONE)
----
=============================================================================
\* Modification History
\* Created Thu Aug 04 11:16:39 CEST 2022 by tobias
