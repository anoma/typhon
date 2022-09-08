---- MODULE MC ----
EXTENDS MempoolSpecFinite, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
U_1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
B_4
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
B_1, B_2, B_3
----

\* MV CONSTANT definitions WorkerIndex
const_166263633794569000 == 
{U_1}
----

\* MV CONSTANT definitions FakeValidator
const_166263633794570000 == 
{B_4}
----

\* MV CONSTANT definitions Validator
const_166263633794571000 == 
{B_1, B_2, B_3}
----

\* CONSTANT definitions @modelParameterConstants:1Payload
const_166263633794572000 == 
{1,2,3,4}
----

\* CONSTANT definitions @modelParameterConstants:4WeakQuorum
const_166263633794573000 == 
{{B_1, B_2}, {B_1, B_3}, {B_1, B_4}, {B_2, B_3}, {B_2, B_4}, {B_3, B_4}}
----

\* CONSTANT definitions @modelParameterConstants:5ByzQuorum
const_166263633794574000 == 
{{B_1, B_2, B_3}, {B_1, B_2, B_4}, {B_1, B_3, B_4}, {B_2, B_3, B_4}}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_166263633794575000 ==
{CHOOSE x \in ValidRequests: TRUE}
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_166263633794676000 ==
UNION { chosenSet[n] : n \in NN } \subseteq Payload
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_166263633794677000 ==
<>(ENABLED DONE)
----
=============================================================================
\* Modification History
\* Created Thu Sep 08 13:25:37 CEST 2022 by tobias
