---- MODULE MC ----
EXTENDS DAGpool, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
B_4
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
B_1, B_2, B_3
----

\* MV CONSTANT definitions FakeValidator
const_166239242572326000 == 
{B_4}
----

\* MV CONSTANT definitions Validator
const_166239242572327000 == 
{B_1, B_2, B_3}
----

\* CONSTANT definitions @modelParameterConstants:0WorkerIndex
const_166239242572328000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:1Payload
const_166239242572329000 == 
{"a"}
----

\* CONSTANT definitions @modelParameterConstants:2noValidator
const_166239242572330000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4WeakQuorum
const_166239242572331000 == 
{{B_1, B_2}, {B_1, B_3}, {B_1, B_4}, {B_2, B_3}, {B_2, B_4}, {B_3, B_4}}
----

\* CONSTANT definitions @modelParameterConstants:6ByzQuorum
const_166239242572332000 == 
{{B_1, B_2, B_3}, {B_1, B_2, B_4}, {B_1, B_3, B_4}, {B_2, B_3, B_4}}
----

\* CONSTANT definitions @modelParameterConstants:7emptyLayer
const_166239242572333000 == 
[x \in {} |-> x]
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_166239242572334000 ==
{1,2,3}
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_166239242572335000 ==
/\ \A i \in 1..Len(dag) : \E Q \in ByzQuorum : DOMAIN dag[i] \subseteq Q
/\ Len(dag) < 5
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_166239242572336000 ==
[]<><<NewBlock>>_vars
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_166239242572337000 ==
[]<><<ChooseSupportedLeaderBlock>>_vars
----
=============================================================================
\* Modification History
\* Created Mon Sep 05 17:40:25 CEST 2022 by tobias
