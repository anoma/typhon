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
const_166263581275060000 == 
{U_1}
----

\* MV CONSTANT definitions FakeValidator
const_166263581275061000 == 
{B_4}
----

\* MV CONSTANT definitions Validator
const_166263581275062000 == 
{B_1, B_2, B_3}
----

\* CONSTANT definitions @modelParameterConstants:1Payload
const_166263581275063000 == 
{1,2,3,4}
----

\* CONSTANT definitions @modelParameterConstants:4WeakQuorum
const_166263581275064000 == 
{{B_1, B_2}, {B_1, B_3}, {B_1, B_4}, {B_2, B_3}, {B_2, B_4}, {B_3, B_4}}
----

\* CONSTANT definitions @modelParameterConstants:5ByzQuorum
const_166263581275065000 == 
{{B_1, B_2, B_3}, {B_1, B_2, B_4}, {B_1, B_3, B_4}, {B_2, B_3, B_4}}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_166263581275066000 ==
{CHOOSE x \in ValidRequests: TRUE}
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_166263581275167000 ==
UNION { chosenSet[n] : n \in NN } \subseteq Payload
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_166263581275168000 ==
<>(ENABLED DONE)
----
=============================================================================
\* Modification History
\* Created Thu Sep 08 13:16:52 CEST 2022 by tobias
