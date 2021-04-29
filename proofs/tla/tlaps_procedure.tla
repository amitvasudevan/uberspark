-------------------------- MODULE tlaps_procedure --------------------------
EXTENDS Sequences, Integers, TLAPS, SequenceTheorems
CONSTANTS MAXCPUS, MAXUOBJCOLLECTIONS, MAXUOBJSWITHINCOLLECTION

LEGACY == 1
UBER == 2

(* --algorithm execution
variables (*Cpu = [cp \in 1..MAXCPUS |->
            [Id |-> cp,                             \* unique CPU identifier
             Pc |-> 0,                              \* program counter (currently abstracted to object control)
             Pr |-> 0,                              \* privelege level
             Shared_cpustate |-> 0,
             Legacy_cpustate |-> 0,
             Res_cpustate |-> [m \in 1..MAXUOBJCOLLECTIONS |->
                 [n \in 1..MAXUOBJSWITHINCOLLECTION |-> 0]
             ]
            ]
          ],*)
             
    (*memory = [Mem_legacy |-> 0,
              Mem_global |-> 0, 
              Mem_uobjcollection |-> [co \in 1..MAXUOBJCOLLECTIONS |->
                [memuobj |-> [ob \in 1..MAXUOBJSWITHINCOLLECTION |->
                   [
                    uobj_local_data |-> 0 (* Section 1.6: memory safety: invariant 1 *)
                   ]
                  ]
                ]
              ]
             ]*)
    priority = 0;

(***************************************************************************)
(* Cpu_process(p) runs legacy code or an uObject collection on processor   *)
(* p.                                                                      *)
(***************************************************************************)
procedure Cpu_process(p) begin
Start:
    either
        \*Cpu[p].Pr := LEGACY;
Legacy:
        priority := LEGACY;
        return;
    or
Uber:
        priority := UBER;
        return;
    end either;
end procedure;

begin
Call:
    call Cpu_process(2);

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "28a4c2cb" /\ chksum(tla) = "8adf01d9")
CONSTANT defaultInitValue
VARIABLES priority, pc, stack, p

vars == << priority, pc, stack, p >>

Init == (* Global variables *)
        /\ priority = 0
        (* Procedure Cpu_process *)
        /\ p = defaultInitValue
        /\ stack = << >>
        /\ pc = "Call"

Start == /\ pc = "Start"
         /\ \/ /\ pc' = "Legacy"
            \/ /\ pc' = "Uber"
         /\ UNCHANGED << priority, stack, p >>

Legacy == /\ pc = "Legacy"
          /\ priority' = LEGACY
          /\ pc' = Head(stack).pc
          /\ p' = Head(stack).p
          /\ stack' = Tail(stack)

Uber == /\ pc = "Uber"
        /\ priority' = UBER
        /\ pc' = Head(stack).pc
        /\ p' = Head(stack).p
        /\ stack' = Tail(stack)

Cpu_process == Start \/ Legacy \/ Uber

Call == /\ pc = "Call"
        /\ /\ p' = 2
           /\ stack' = << [ procedure |->  "Cpu_process",
                            pc        |->  "Done",
                            p         |->  p ] >>
                        \o stack
        /\ pc' = "Start"
        /\ UNCHANGED priority

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Cpu_process \/ Call
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

property == priority < 3

StackEntry == [procedure : {"Cpu_process"},
   pc : {"Done"},
   p : 1..2 \cup {defaultInitValue}
]


TypeOK == /\ priority \in 0..2
          /\ p \in 1..2 \cup {defaultInitValue}
          /\ stack \in Seq(StackEntry)
          /\ \/ stack = << >>
             \/ /\ Len(stack) = 1
                /\ stack[1].pc = "Done"
                /\ stack[1].procedure = "Cpu_process"
                /\ stack[1].p \in 1..2 \cup {defaultInitValue}\*"defaultInitValue"
          /\ \/ pc \in {"Call", "Done"} /\ stack = << >>
             \/ pc \in {"Start", "Legacy", "Uber"} /\ stack # << >>
          /\ pc \in {"Call", "Start", "Done", "Legacy", "Uber"}

Inv == property /\ TypeOK

empty == << >>
THEOREM empty \in Seq(StackEntry)
<1>1. QED BY DEF empty, StackEntry

THEOREM Spec => []property
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, property, StackEntry
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. SUFFICES ASSUME Inv, Next PROVE Inv'
    BY DEFS Inv, TypeOK, property, vars
  <2>2.TypeOK'
    <3>1. CASE Cpu_process
      <4>1. CASE Start
        BY <2>1, <3>1, <4>1 DEF Cpu_process, Start, TypeOK, StackEntry, Inv
      <4>2. CASE Legacy \/ Uber
        <5>1. (priority \in 0..2)'
          BY <2>1, <3>1, <4>2 DEF Cpu_process, Legacy, Uber, Inv, TypeOK, LEGACY, UBER
        <5>2. (p \in 1..2 \cup {defaultInitValue})'
          <6>1. Head(stack) \in StackEntry
            BY <2>1, <3>1, <4>2, HeadTailProperties DEF Cpu_process, Uber, Legacy, Inv, TypeOK, StackEntry
          <6>2. QED BY <6>1, <2>1, <3>1, <4>2 DEF Inv, TypeOK, StackEntry, Cpu_process, Uber, Legacy
        <5>3. (stack \in Seq(StackEntry))'
          BY <2>1, <3>1, <4>2 DEF Cpu_process, Uber, Legacy, TypeOK, Inv
        <5>4. (\/ stack = << >>
               \/ /\ Len(stack) = 1
                  /\ stack[1].pc = "Done"
                  /\ stack[1].procedure = "Cpu_process"
                  /\ stack[1].p \in 1..2 \cup {defaultInitValue})'
          BY <2>1, <3>1, <4>2 DEF Cpu_process, Uber, Legacy, TypeOK, Inv
        <5>5. (\/ pc \in {"Call", "Done"} /\ stack = << >>
               \/ pc \in {"Start", "Legacy", "Uber"} /\ stack # << >>)'
            <6>1. pc' = "Done"
              BY <2>1, <3>1, <4>2 DEF Cpu_process, Uber, Legacy, TypeOK, Inv
            <6>2. Tail(stack) = << >>
              BY <2>1, <3>1, <4>2 DEF Cpu_process, Uber, Legacy, TypeOK, Inv
            <6>3. QED BY <6>1, <6>2, <4>2 DEF Cpu_process, Uber, Legacy, TypeOK, Inv       
        <5>6. (pc \in {"Call", "Start", "Done", "Legacy", "Uber"})'
          BY <2>1, <3>1, <4>2 DEF Cpu_process, Uber, Legacy, TypeOK, Inv
        <5>7. QED BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6 DEF TypeOK
      <4>4 QED BY <3>1, <4>1, <4>2 DEF TypeOK, Cpu_process
    <3>2. CASE Call
      <4>1. (priority \in 0..2)'
        BY <2>1, <3>2 DEF Call, Inv, TypeOK
      <4>2. (p \in 1..2 \cup {defaultInitValue})'
        BY <3>2 DEF Call
      <4>3. (stack \in Seq(StackEntry))'
        BY <2>1, <3>2 DEF Call, StackEntry, Inv, TypeOK
      <4>4. (\/ stack = << >>
             \/ /\ Len(stack) = 1
                /\ stack[1].pc = "Done"
                /\ stack[1].procedure = "Cpu_process"
                /\ stack[1].p \in 1..2 \cup {defaultInitValue})'
        <5>1. Len(stack) = 0
          BY <2>1, <3>2 DEF Call, Inv, TypeOK
        <5>3. QED BY <5>1, (*<5>2,*) <2>1, <3>2 DEF Call, Inv, TypeOK
      <4>5. (\/ pc \in {"Call", "Done"} /\ stack = << >>
             \/ pc \in {"Start", "Legacy", "Uber"} /\ stack # << >>)'
        BY <2>1, <3>2 DEF Call, Inv, TypeOK
      <4>6. (pc \in {"Call", "Start", "Done", "Legacy", "Uber"})'
        BY <3>2 DEF Call
      <4>7. QED BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF TypeOK
    <3>3. CASE Terminating
      BY <2>1, <3>3 DEF Terminating, TypeOK, StackEntry, Inv, vars
    <3>4. QED BY <2>1, <3>1, <3>2, <3>3 DEF Next, TypeOK, StackEntry
  <2>3. property'
      BY <2>1 DEF property, Inv, vars, Cpu_process, Start, Legacy, Uber,
                  Call, Terminating, LEGACY, UBER, Next
    (*<3>1. CASE Cpu_process
      BY <2>1, <3>1 DEF Cpu_process, property, Inv, vars, Start, Legacy, Uber, LEGACY, UBER
    <3>2. CASE Call
      BY <2>1, <3>2 DEF Call, property, Inv, vars
    <3>3. CASE Terminating
      BY <2>1, <3>3 DEF Terminating, property, Inv, vars
    <3>4. QED BY <2>1, <3>1, <3>2, <3>3 DEF Next, property*)
  <2>4. QED
        BY <2>2, <2>3 DEF Inv
<1>3. Inv => property
  BY DEF Inv, property
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================
\* Modification History
\* Last modified Thu Apr 29 08:35:40 PDT 2021 by uber
\* Created Mon Apr 26 08:52:40 PDT 2021 by uber
