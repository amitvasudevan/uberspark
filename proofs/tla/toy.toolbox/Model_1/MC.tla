---- MODULE MC ----
EXTENDS toy, TLC

\* CONSTANT definitions @modelParameterConstants:0MAXUOBJDEVMMIO
const_159837327988679000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:1MAXCPUS
const_159837327988680000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:2MAXUOBJCOLLECTIONS
const_159837327988681000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:3MAXUOBJCOLLECTIONSTACKSIZE
const_159837327988682000 == 
4096
----

\* CONSTANT definitions @modelParameterConstants:4MAXUOBJSWITHINCOLLECTION
const_159837327988683000 == 
8
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_159837327988784000 ==
cpus # 0
----
=============================================================================
\* Modification History
\* Created Tue Aug 25 09:34:39 PDT 2020 by mjmccall
