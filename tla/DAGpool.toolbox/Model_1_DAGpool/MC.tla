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
const_1662373733688690000 == 
{B_4}
----

\* MV CONSTANT definitions Validator
const_1662373733688691000 == 
{B_1, B_2, B_3}
----

\* CONSTANT definitions @modelParameterConstants:0WorkerIndex
const_1662373733688692000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:1Payload
const_1662373733688693000 == 
{"a"}
----

\* CONSTANT definitions @modelParameterConstants:2noValidator
const_1662373733688694000 == 
5
----

\* CONSTANT definitions @modelParameterConstants:4WeakQuorum
const_1662373733688695000 == 
{{B_1, B_2}, {B_1, B_3}, {B_1, B_4}, {B_2, B_3}, {B_2, B_4}, {B_3, B_4}}
----

\* CONSTANT definitions @modelParameterConstants:6ByzQuorum
const_1662373733688696000 == 
{{B_1, B_2, B_3}, {B_1, B_2, B_4}, {B_1, B_3, B_4}, {B_2, B_3, B_4}}
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1662373733688697000 ==
{1,2,3}
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1662373733688698000 ==
Len(dag) < 4
----
\* Constant expression definition @modelExpressionEval
const_expr_1662373733688699000 == 
Block

----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1662373733688699000>>)
----

=============================================================================
\* Modification History
\* Created Mon Sep 05 12:28:53 CEST 2022 by tobias
