---- MODULE MC ----
EXTENDS MempoolSpecFinite, TLC

\* CONSTANT definitions @modelParameterConstants:0WorkerIndex
const_1659617191388129000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:1Payload
const_1659617191388130000 == 
{1,2,3,4}
----

\* CONSTANT definitions @modelParameterConstants:2FakeValidator
const_1659617191388131000 == 
{"4"}
----

\* CONSTANT definitions @modelParameterConstants:3Validator
const_1659617191388132000 == 
{"1","2","3"}
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1659617191388133000 ==
UNION { chosenSet[n] : n \in NN } \subseteq Payload
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1659617191388134000 ==
<>(ENABLED DONE)
----
=============================================================================
\* Modification History
\* Created Thu Aug 04 14:46:31 CEST 2022 by tobias
