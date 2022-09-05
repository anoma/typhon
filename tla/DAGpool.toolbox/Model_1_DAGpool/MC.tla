---- MODULE MC ----
EXTENDS DAGpool, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A_1, A_2, A_3, A_4
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
const_1662041497972128000 == 
{A_1, A_2, A_3, A_4}
----

\* MV CONSTANT definitions FakeValidator
const_1662041497972129000 == 
{B_4}
----

\* MV CONSTANT definitions Validator
const_1662041497972130000 == 
{B_1, B_2, B_3}
----

\* SYMMETRY definition
symm_1662041497972131000 == 
Permutations(const_1662041497972128000)
----

\* CONSTANT definitions @modelParameterConstants:0WorkerIndex
const_1662041497972132000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:2noValidator
const_1662041497972133000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4WeakQuorum
const_1662041497972134000 == 
{{B_1, B_2}, {B_1, B_3}, {B_1, B_4}, {B_2, B_3}, {B_2, B_4}, {B_3, B_4}}
----

\* CONSTANT definitions @modelParameterConstants:6ByzQuorum
const_1662041497972135000 == 
{{B_1, B_2, B_3}, {B_1, B_2, B_4}, {B_1, B_3, B_4}, {B_2, B_3, B_4}}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1662041497972136000 ==
{1,2}
----
=============================================================================
\* Modification History
\* Created Thu Sep 01 16:11:37 CEST 2022 by tobias
