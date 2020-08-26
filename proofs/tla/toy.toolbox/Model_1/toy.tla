-------------------------------- MODULE toy --------------------------------
EXTENDS TLC, Sequences, Integers
CONSTANTS MAXCPUS, MAXUOBJCOLLECTIONS, MAXUOBJSWITHINCOLLECTION, MAXUOBJCOLLECTIONSTACKSIZE, MAXUOBJDEVMMIO 
E(n) == IF n \in MAXCPUS THEN TRUE ELSE FALSE
R(n) == 1..n

(* --algorithm execution
variables cpus = MAXCPUS,
    (**)cpu = [x \in 1..MAXCPUS |->
              [id |-> x,
               Pc |-> 1,
               Sp |-> 1,
               Shared_cpustate |-> <<1,2,3>>,
               Legacy_cpustate |-> <<4,5,6>>,
               uobjcoll_cpustate |-> [y \in 1..MAXUOBJCOLLECTIONS |->
                 [z \in 1..MAXUOBJSWITHINCOLLECTION |-> <<3,4>>
          ]]]],(**)
    \*cpu = [x \in 1..MAXCPUS |-> [id : 0, pop : [y \in R(5) |-> z]]];
    memory = [memuobjs \in 1..MAXUOBJSWITHINCOLLECTION |->
                [Uobj_ssa : 1..MAXCPUS,
                 Uobj_code : {},
                 Uobj_data : {},
                 Uobj_dmadata : {},
                 Uobj_devmmio : 1..MAXUOBJDEVMMIO]]

begin
while cpus > 0 do
    cpus := cpus - 1;
end while;
end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b52011fd1ad54c9008607ffbc1487929
VARIABLES cpus, cpu, memory, pc

vars == << cpus, cpu, memory, pc >>

Init == (* Global variables *)
        /\ cpus = MAXCPUS
        /\ cpu =     [x \in 1..MAXCPUS |->
                     [id |-> x,
                      Pc |-> 1,
                      Sp |-> 1,
                      Shared_cpustate |-> <<1,2,3>>,
                      Legacy_cpustate |-> <<4,5,6>>,
                      uobjcoll_cpustate |-> [y \in 1..MAXUOBJCOLLECTIONS |->
                        [z \in 1..MAXUOBJSWITHINCOLLECTION |-> <<3,4>>
                 ]]]]
        /\ memory = [memuobjs \in 1..MAXUOBJSWITHINCOLLECTION |->
                       [Uobj_ssa : 1..MAXCPUS,
                        Uobj_code : {},
                        Uobj_data : {},
                        Uobj_dmadata : {},
                        Uobj_devmmio : 1..MAXUOBJDEVMMIO]]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF cpus > 0
               THEN /\ cpus' = cpus - 1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ cpus' = cpus
         /\ UNCHANGED << cpu, memory >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-27fbeccdec609cc2141842d3f16f66f8

=============================================================================
\* Modification History
\* Last modified Tue Aug 25 09:34:18 PDT 2020 by mjmccall
\* Created Thu Aug 20 05:23:36 PDT 2020 by mjmccall
