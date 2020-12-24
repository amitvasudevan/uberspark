---- MODULE MC ----
EXTENDS toy, TLC

\* CONSTANT definitions @modelParameterConstants:0MAXUOBJCOLLECTIONS
const_1608145729980146000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:1MAXCPUS
const_1608145729980147000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:3MAXUOBJSWITHINCOLLECTION
const_1608145729980148000 == 
16
----

\* CONSTANT definitions @modelParameterConstants:4MAXUOBJCOLLECTIONSTACKSIZE
const_1608145729980149000 == 
16
----

\* CONSTANT definitions @modelParameterConstants:5MAXUOBJDEVMMIO
const_1608145729980150000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:6func_set
const_1608145729980151000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:7maxvars
const_1608145729980152000 == 
2
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1608145729981153000 ==
Cpu[2].id = 2
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1608145729982154000 ==
cpu /= 0
----
=============================================================================
\* Modification History
\* Created Wed Dec 16 11:08:49 PST 2020 by mjmccall
