---- MODULE MC ----
EXTENDS DAGpool, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A_1
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
B_4
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
B_1, B_2, B_3
----

\* MV CONSTANT definitions Payload
const_1662364180762142000 == 
{A_1}
----

\* MV CONSTANT definitions FakeValidator
const_1662364180762143000 == 
{B_4}
----

\* MV CONSTANT definitions Validator
const_1662364180762144000 == 
{B_1, B_2, B_3}
----

\* CONSTANT definitions @modelParameterConstants:0WorkerIndex
const_1662364180762145000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:2noValidator
const_1662364180762146000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4WeakQuorum
const_1662364180762147000 == 
{{B_1, B_2}, {B_1, B_3}, {B_1, B_4}, {B_2, B_3}, {B_2, B_4}, {B_3, B_4}}
----

\* CONSTANT definitions @modelParameterConstants:6ByzQuorum
const_1662364180762148000 == 
{{B_1, B_2, B_3}, {B_1, B_2, B_4}, {B_1, B_3, B_4}, {B_2, B_3, B_4}}
----

\* CONSTANT definitions @modelParameterConstants:7emptyLayer
const_1662364180762149000 == 
[x\in{}|->x]
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1662364180762150000 ==
{1,2,3}
----
=============================================================================
\* Modification History
\* Created Mon Sep 05 09:49:40 CEST 2022 by tobias
