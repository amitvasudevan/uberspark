---------------------- MODULE tlaps_procedure_process ----------------------
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

process one = 1
begin
Call:
    call Cpu_process(1);
end process;

process two = 2
begin
Call:
    call Cpu_process(2);
end process;

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "44c32885" /\ chksum(tla) = "783600b9")
\* Label Call of process one at line 55 col 5 changed to Call_
CONSTANT defaultInitValue
VARIABLES priority, pc, stack, p

vars == << priority, pc, stack, p >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ priority = 0
        (* Procedure Cpu_process *)
        /\ p = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "Call_"
                                        [] self = 2 -> "Call"]

Start(self) == /\ pc[self] = "Start"
               /\ \/ /\ pc' = [pc EXCEPT ![self] = "Legacy"]
                  \/ /\ pc' = [pc EXCEPT ![self] = "Uber"]
               /\ UNCHANGED << priority, stack, p >>

Legacy(self) == /\ pc[self] = "Legacy"
                /\ priority' = LEGACY
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]

Uber(self) == /\ pc[self] = "Uber"
              /\ priority' = UBER
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]

Cpu_process(self) == Start(self) \/ Legacy(self) \/ Uber(self)

Call_ == /\ pc[1] = "Call_"
         /\ /\ p' = [p EXCEPT ![1] = 1]
            /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "Cpu_process",
                                                  pc        |->  "Done",
                                                  p         |->  p[1] ] >>
                                              \o stack[1]]
         /\ pc' = [pc EXCEPT ![1] = "Start"]
         /\ UNCHANGED priority

one == Call_

Call == /\ pc[2] = "Call"
        /\ /\ p' = [p EXCEPT ![2] = 2]
           /\ stack' = [stack EXCEPT ![2] = << [ procedure |->  "Cpu_process",
                                                 pc        |->  "Done",
                                                 p         |->  p[2] ] >>
                                             \o stack[2]]
        /\ pc' = [pc EXCEPT ![2] = "Start"]
        /\ UNCHANGED priority

two == Call

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two
           \/ (\E self \in ProcSet: Cpu_process(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

property == priority < 3

StackEntry == [procedure : {"Cpu_process"},
   pc : {"Done"},
   p : 1..2 \cup {defaultInitValue}
]

TypeOK == /\ priority \in 0..2
          /\ p \in [ProcSet -> 1..2 \cup {defaultInitValue}]
          /\ stack \in [ProcSet -> Seq(StackEntry)]
          /\ \A i \in ProcSet :
             \/ stack[i] = << >>
             \/ /\ Len(stack[i]) = 1
                /\ stack[i][1].pc = "Done"
                /\ stack[i][1].procedure = "Cpu_process"
                /\ stack[i][1].p \in 1..2 \cup {defaultInitValue}   
          /\ \A i \in ProcSet :
             \/ pc[i] \in {"Call", "Call_", "Done"} /\ stack[i] = << >>
             \/ pc[i] \in {"Start", "Legacy", "Uber"} /\ stack[i] # << >>
          /\ pc \in [ProcSet -> {"Call", "Call_", "Start", "Done", "Legacy", "Uber"}]

Inv == property /\ TypeOK


THEOREM obv == (/\ pc[1] = "Call_"
         /\ /\ p' = [p EXCEPT ![1] = 1]
            /\ stack'
                 = [stack EXCEPT
                      ![1] = <<[procedure |-> "Cpu_process", pc |-> "Done",
                                p |-> p[1]]>>
                             \o stack[1]]
         /\ pc' = [pc EXCEPT ![1] = "Start"]
         /\ UNCHANGED priority) =>
        stack'
        = [stack EXCEPT
            ![1] = <<[procedure |-> "Cpu_process", pc |-> "Done", p |-> p[1]]>>
                   \o stack[1]]
<1> QED OBVIOUS



THEOREM Spec => []property
<1>1. Init => Inv
  <2>1. SUFFICES ASSUME Init PROVE Inv
    BY DEF Init, Inv, TypeOK, property
  <2>2. property
    BY <2>1 DEF Init, Inv, property
  <2>3. TypeOK
    \*BY <2>1 DEF Init, ProcSet
    <3>1. priority \in 0..2
      BY <2>1 DEF Init
    <3>2. p \in [ProcSet -> 1..2 \cup {defaultInitValue}]
      BY <2>1 DEF Init
    <3>3. stack \in [ProcSet -> Seq(StackEntry)]
      BY <2>1 DEF Init
    <3>4. \A i \in ProcSet :
             \/ stack[i] = <<>>
             \/ /\ Len(stack[i]) = 1
                /\ stack[i][1].pc = "Done"
                /\ stack[i][1].procedure = "Cpu_process"
                /\ stack[i][1].p \in 1..2 \cup {defaultInitValue}
      BY <2>1 DEF Init
    <3>5. \A i \in ProcSet :
             \/ pc[i] \in {"Call", "Call_", "Done"} /\ stack[i] = <<>>
             \/ pc[i] \in {"Start", "Legacy", "Uber"} /\ stack[i] # <<>>
      BY <2>1 DEF Init, ProcSet
      (*<4>1. pc[1] = "Call_" /\ stack[1] = << >>
        BY <2>1 DEF Init, ProcSet
      <4>2. pc[2] = "Call" /\ stack[2] = << >>
        BY <2>1 DEF Init, ProcSet
      <4> QED BY <4>1, <4>2 DEF Init, ProcSet*)
    <3>6. pc \in [ProcSet -> {"Call", "Call_", "Start", "Done", "Legacy", "Uber"}]
      BY <2>1 DEF Init, ProcSet
    <3>7. QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF TypeOK
  <2>4. QED BY <2>2, <2>3 DEF Init, Inv, TypeOK, property
<1>2. Inv /\ [Next]_vars => Inv'
  <2>1. SUFFICES ASSUME Inv, Next PROVE Inv'
    BY DEFS Inv, TypeOK, property, vars
  <2>2.TypeOK'
    <3> DEFINE self == CHOOSE self \in ProcSet : TRUE
    \*<3>1. CASE Cpu_process(self)
    <3>1. CASE \E i \in ProcSet : Cpu_process(i)
      \*<4>1. CASE Start(self)
      <4>1. CASE \E i \in ProcSet : Start(i) (* ALSO WORKS FOR ALL *)
        BY <2>1, <3>1, <4>1 DEF Cpu_process, Start, TypeOK, StackEntry, Inv
      \*<4>2. CASE Legacy(self) \/ Uber(self)
      <4>2. CASE \E i \in ProcSet :  Legacy(i) \/ Uber(i) (* WAS FOR ALL *)
        <5>1. (priority \in 0..2)'
          (*<6>1. CASE \A i \in ProcSet : pc[i] = "Legacy"
            BY <2>1, <3>1, <4>2 DEF Cpu_process, Legacy, Uber, Inv, TypeOK, LEGACY, UBER
          <6>2. CASE \A i \in ProcSet : pc[i] = "Uber"*)
            BY <2>1, <3>1, <4>2 DEF Cpu_process, Legacy, Uber, Inv, TypeOK, LEGACY, UBER
          (*<6> QED BY <2>1, <4>2, <6>1, <6>2 DEF Legacy, Uber*)
        <5>2. (p \in [ProcSet -> 1..2 \cup {defaultInitValue}])'
          <6>1. \E i \in ProcSet : Head(stack[i]) \in StackEntry (* WAS FOR ALL *)
            BY <2>1, <3>1, <4>2, HeadTailProperties DEF Cpu_process, Uber, Legacy, Inv, TypeOK, StackEntry
          <6>. QED BY <2>1, <4>2, <6>1
            \*\A i \in ProcSet : Head(stack[i]).p \in 1..2 \cup {defaultInitValue},
            \*\A i \in ProcSet : p' = [p EXCEPT ![i] = Head(stack[i]).p]
            DEF Inv, TypeOK, StackEntry, Uber, Legacy, ProcSet
          
          \*<6>1. (p[1] \in 1..2 \cup {defaultInitValue})'
          \*<6>2. (p[2] \in 1..2 \cup {defaultInitValue})'
          \*<6>1. (p \in [1..2 -> 1..2 \cup {defaultInitValue}])'
            \*<7>1. p[1]' \in 1..2 \cup {defaultInitValue}
            \*<7>2. p[2]' \in 1..2 \cup {defaultInitValue}
            \*<7>1. \A i \in ProcSet : p[i] \in 1..2 \cup {defaultInitValue}
            \*<7>. QED BY <7>1(*, <7>2*) DEF ProcSet
          \*<6> QED BY <6>1(*, <6>2*) DEF ProcSet
        
          \*<6>1. \A i \in ProcSet : Head(stack[i]) \in StackEntry
          \*  BY <2>1, <3>1, <4>2, HeadTailProperties DEF Cpu_process, Uber, Legacy, Inv, TypeOK, StackEntry
          (*<6>1. Head(stack[1]) \in StackEntry
            <7>1. CASE pc[1] = "Legacy"
              BY <2>1, <3>1, <4>2, <7>1, HeadTailProperties DEF Cpu_process, Uber, Legacy, Inv, TypeOK, StackEntry
            <7>2. CASE pc[1] = "Uber"
              BY <2>1, <3>1, <4>2, <7>2, HeadTailProperties DEF Cpu_process, Uber, Legacy, Inv, TypeOK, StackEntry
            <7> QED BY <7>1, <7>2
          <6>2. Head(stack[2]) \in StackEntry
            BY <2>1, <3>1, <4>2, HeadTailProperties DEF Cpu_process, Uber, Legacy, Inv, TypeOK, StackEntry
          <6>. QED BY <4>2, <6>1, <6>2 DEF (*Inv, TypeOK,*) StackEntry, (*Cpu_process,*) Uber, Legacy, ProcSet*)
        <5>3. (stack \in [ProcSet -> Seq(StackEntry)])'
          BY <2>1, <3>1, <4>2 DEF Cpu_process, Uber, Legacy, TypeOK, Inv
        <5>4. (\A i \in ProcSet :
                 \/ stack[i] = << >>
                 \/ /\ Len(stack[i]) = 1
                    /\ stack[i][1].pc = "Done"
                    /\ stack[i][1].procedure = "Cpu_process"
                    /\ stack[i][1].p \in 1..2 \cup {defaultInitValue} )'
          BY <2>1, <3>1, <4>2 DEF Cpu_process, Uber, Legacy, TypeOK, Inv
        <5>5. (\A i \in ProcSet :
                 \/ pc[i] \in {"Call", "Call_", "Done"} /\ stack[i] = << >>
                 \/ pc[i] \in {"Start", "Legacy", "Uber"} /\ stack[i] # << >>)'
            <6>1. \E i \in ProcSet : pc[i]' = "Done" (* WAS FOR ALL *)
              BY <2>1, <3>1, <4>2 DEF Cpu_process, Uber, Legacy, TypeOK, Inv
            <6>2. \A i \in ProcSet : Tail(stack[i]) = << >>
              BY <2>1, <3>1, <4>2 DEF Cpu_process, Uber, Legacy, TypeOK, Inv
            <6>3. QED BY <2>1, <4>2, <6>1, <6>2 DEF Cpu_process, Uber, Legacy, TypeOK, Inv       
        <5>6. (pc \in [ProcSet -> {"Call", "Call_", "Start", "Done", "Legacy", "Uber"}])'
          BY <2>1, <3>1, <4>2 DEF Cpu_process, Uber, Legacy, TypeOK, Inv
        <5>7. QED BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6 DEF TypeOK
      <4>4 QED BY <3>1, <4>1, <4>2 DEF TypeOK, Cpu_process
    <3>2. CASE Call \/ Call_
      <4>1. (priority \in 0..2)'
        BY <2>1, <3>2 DEF Call, Call_, Inv, TypeOK
      <4>2. (p \in [ProcSet -> 1..2 \cup {defaultInitValue}])'
        BY <2>1, <3>2 DEF Call, Call_, ProcSet, Inv, TypeOK
      <4>3. (stack \in [ProcSet -> Seq(StackEntry)])'
        BY <2>1, <3>2, 
        (*[procedure |-> "Cpu_process", pc |-> "Done", p |-> p[1]] \in StackEntry,
        [procedure |-> "Cpu_process", pc |-> "Done", p |-> p[2]] \in StackEntry,*)
        stack' = [stack EXCEPT
                      ![1] = <<[procedure |-> "Cpu_process", pc |-> "Done",
                                p |-> p[1]]>>
                             \o stack[1]]
        \/ stack'
              = [stack EXCEPT
                   ![2] = <<[procedure |-> "Cpu_process", pc |-> "Done",
                             p |-> p[2]]>>
                          \o stack[2]],
        \*(p \in [{1} \cup {2} -> 1..2 \cup {defaultInitValue}]),
        \*stack[1] \in Seq(StackEntry),
        <<[procedure |-> "Cpu_process", pc |-> "Done", p |-> p[1]]>> \o stack[1] \in Seq(StackEntry),
        <<[procedure |-> "Cpu_process", pc |-> "Done", p |-> p[2]]>> \o stack[2] \in Seq(StackEntry)
        DEF Call, Call_, StackEntry, Inv, TypeOK, ProcSet
      <4>4. (\A i \in ProcSet :
                 \/ stack[i] = << >>
                 \/ /\ Len(stack[i]) = 1
                    /\ stack[i][1].pc = "Done"
                    /\ stack[i][1].procedure = "Cpu_process"
                    /\ stack[i][1].p \in 1..2 \cup {defaultInitValue})'
        <5>1. CASE Call_\*pc[1] = "Call_" \*/\ pc[2] # "Call"
          <6>1. Len(stack[1]) = 0 /\ stack[1] = <<>>
            BY <2>1, <5>1 DEF Inv, TypeOK, ProcSet, Call_
          <6>a. Len(<<[procedure |-> "Cpu_process", pc |-> "Done",
                                p |-> p[1]]>>
                             \o stack[1]) = 1
            BY <6>1
          (*<6>b. (stack[1] = <<[procedure |-> "Cpu_process", pc |-> "Done",
                                p |-> p[1]]>>
                             \o stack[1])'
            BY <2>1, <3>2, <5>1, <6>1 DEF Call_, Inv, TypeOK, ProcSet*) 
          <6>c. stack'
                 = [stack EXCEPT
                      ![1] = <<[procedure |-> "Cpu_process", pc |-> "Done",
                                p |-> p[1]]>>
                             \o stack[1]]
            BY <2>1, <3>2, <5>1, <6>1, obv DEF Call_, Inv, TypeOK, ProcSet      
          <6>d. (/\ pc[1] = "Call_"
                 /\ /\ p' = [p EXCEPT ![1] = 1]
                    /\ stack'
                       = [stack EXCEPT
                            ![1] = <<[procedure |-> "Cpu_process", pc |-> "Done",
                                      p |-> p[1]]>>
                                   \o stack[1]]
                 /\ pc' = [pc EXCEPT ![1] = "Start"]
                 /\ UNCHANGED priority)
            BY <2>1, <3>2, <5>1 DEF Call_, Call
          <6>2. (Len(stack[1]))' = 1
            BY <2>1, <3>2, <5>1, <6>1, <6>a DEF Call_, Inv, TypeOK, ProcSet
          <6>3. (stack[1][1].pc)' = "Done"
            BY <2>1, <3>2, <5>1, <6>1 DEF Call_, Inv, TypeOK, ProcSet
          <6>4. stack[1][1].procedure' = "Cpu_process"
            BY <2>1, <3>2, <5>1, <6>1 DEF Call_, Inv, TypeOK, ProcSet
          <6>5. stack[1][1].p' \in 1..2 \cup {defaultInitValue}
            BY <2>1, <3>2, <5>1, <6>1 DEF Call_, Inv, TypeOK, ProcSet
          <6> QED BY <2>1, <3>2, <5>1, <6>1, <6>2, <6>3, <6>4, <6>5\*,
          \*p[1] \in 1..2 \cup {defaultInitValue},
          \*(Len(stack[1]))' = 1
           DEF Call_, Inv, TypeOK, ProcSet
        <5>2. CASE Call\*pc[2] = "Call" \*/\ pc[1] # "Call_"
          <6>1. Len(stack[2]) = 0 /\ stack[2] = <<>>
            BY <2>1, <5>2 DEF Inv, TypeOK, ProcSet, Call
          <6>2. (Len(stack[2]))' = 1
            BY <2>1, <3>2, <5>2, <6>1 DEF Call, Inv, TypeOK, ProcSet
          <6> QED BY <2>1, <3>2, <5>2, <6>1 DEF Call, Inv, TypeOK, ProcSet
        <5>3. QED BY <2>1, <3>2, <5>1, <5>2 DEF Call, Call_, Inv, TypeOK
      <4>5. (\A i \in ProcSet :
                 \/ pc[i] \in {"Call", "Call_", "Done"} /\ stack[i] = << >>
                 \/ pc[i] \in {"Start", "Legacy", "Uber"} /\ stack[i] # << >>)'
        BY <2>1, <3>2 DEF Call, Call_, Inv, TypeOK
      <4>6. (pc \in [ProcSet -> {"Call", "Call_", "Start", "Done", "Legacy", "Uber"}])'
        BY <2>1, <3>2 DEF Call, Call_, ProcSet, Inv, TypeOK
      <4>7. QED BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6 DEF TypeOK
    <3>3. CASE Terminating
      BY <2>1, <3>3 DEF Terminating, TypeOK, StackEntry, Inv, vars
    <3>4. QED BY <2>1, <3>1, <3>2, <3>3 DEF Inv, Next, TypeOK, StackEntry, one, two
    (*<3>1. (priority \in 0..2)'
      BY <2>1 DEF Inv, TypeOK, StackEntry
    <3>2. (p \in [ProcSet -> 1..2 \cup {defaultInitValue}])'
      BY <2>1 DEF Inv, TypeOK, StackEntry
    <3>3. (stack \in [ProcSet -> Seq(StackEntry)])'
      BY <2>1 DEF Inv, TypeOK, StackEntry
    <3>4. (\A i \in ProcSet :
             \/ stack[i] = <<>>
             \/ /\ Len(stack[i]) = 1
                /\ stack[i][1].pc = "Done"
                /\ stack[i][1].procedure = "Cpu_process"
                /\ stack[i][1].p \in 1..2 \cup {defaultInitValue})'
      BY <2>1 DEF Inv, TypeOK, StackEntry
    <3>5. (\A i \in ProcSet :
             \/ pc[i] \in {"Call", "Call_", "Done"} /\ stack[i] = <<>>
             \/ pc[i] \in {"Start", "Legacy", "Uber"} /\ stack[i] # <<>>)'
      BY <2>1 DEF Inv, TypeOK, StackEntry
    <3>6. (pc \in [ProcSet -> {"Call", "Call_", "Start", "Done", "Legacy", "Uber"}])'
      BY <2>1 DEF Inv, TypeOK, StackEntry
    <3>7. QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF TypeOK*)
  <2>3. property'
    \*BY <2>1 DEF Init, Inv, property, Next
    BY <2>1 DEF property, Inv, vars, Cpu_process, Start, Legacy, Uber,
                  Call, Call_, Terminating, LEGACY, UBER, Next, one, two
  <2>4. QED BY <2>2, <2>3 DEF Inv
<1>3. Inv => property
  BY DEF Inv, property
<1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

THEOREM p = [self \in ProcSet |-> defaultInitValue] => p \in [ProcSet -> 1..2 \cup {defaultInitValue}]
OBVIOUS

empty == << >>
THEOREM empty \in Seq(StackEntry)
<1>1. QED BY DEF empty, StackEntry

(*THEOREM Spec => []property
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
  BY <1>1, <1>2, <1>3, PTL DEF Spec*)
  
  
THEOREM (p \in [{1} \cup {2} -> 1..2 \cup {defaultInitValue}])
          /\(\A i \in ProcSet : Head(stack[i]).p \in 1..2 \cup {defaultInitValue})
          /\ (\A i \in ProcSet : p' = [p EXCEPT ![i] = Head(stack[i]).p]) =>
          (p \in [{1} \cup {2} -> 1..2 \cup {defaultInitValue}])'
  <1> QED BY DEF ProcSet


THEOREM (\A i \in ProcSet : p' = [p EXCEPT ![i] = 0]) =>
          (p \in [{1} \cup {2} -> {0}])'
  <1> QED BY DEF ProcSet
  
THEOREM p' = 0 => (p = 0)'
OBVIOUS

THEOREM p[1]' = 0 => (p[1] = 0)'
OBVIOUS

THEOREM /\ p = [ i \in ProcSet |-> 0]
        /\ p' = [p EXCEPT ![1] = 1]
        =>
        (p[1] = 1)'
<1> QED BY DEF ProcSet

THEOREM /\ p \in [ ProcSet -> 0..2]
        /\ p' = [p EXCEPT ![1] = 1]
        =>
        (p[1] = 1)'
<1> QED BY DEF ProcSet

THEOREM /\ p \in [{1} \cup {2} -> 1..2]
        /\ p' = [p EXCEPT ![2] = 1]
        =>
        (p \in [{1} \cup {2} -> 1..2])'
OBVIOUS


A == [a : {1,2} \cup {defaultInitValue}, b : {1,2}]
B == [a |-> 1, b |-> 2]
\*C == [self \in ProcSet |-> B \o << >>]
C == [self \in ProcSet |->  << >>]
THEOREM <<[a |-> 1, b |-> 2]>> \o << >> \in Seq(A)
<1> QED BY DEF A

THEOREM C' = [stack EXCEPT ![1] = <<[a |-> 2, b |-> 1]>> \o C[1]] /\
        C \in [{1} \cup {2} -> Seq([a : {1,2} \cup {defaultInitValue}, b : {1,2}])]
        => (C \in [{1} \cup {2} -> Seq([a : {1,2} \cup {defaultInitValue}, b : {1,2}])])'
<1> QED OBVIOUS

THEOREM <<[a |-> 5]>> \in Seq(A)
<1> QED BY DEF A


THEOREM stack \in [{1} \cup {2} ->
                        Seq([procedure : {"Cpu_process"}, pc : {"Done"},
                             p : 1..2 \cup {defaultInitValue}])] /\
       (p \in [{1} \cup {2} -> 1..2 \cup {defaultInitValue}]) /\
       (*[procedure |-> "Cpu_process", pc |-> "Done", p |-> p[1]]
       \in [procedure : {"Cpu_process"}, pc : {"Done"},
       p : 1..2 \cup {defaultInitValue}] /\
       [procedure |-> "Cpu_process", pc |-> "Done", p |-> p[2]]
       \in [procedure : {"Cpu_process"}, pc : {"Done"},
       p : 1..2 \cup {defaultInitValue}] /\*)
       \*(stack' = [stack EXCEPT
       \*     ![1] = <<[procedure |-> "Cpu_process", pc |-> "Done", p |-> p[1]]>>
       \*            \o stack[1]])
       \*stack' = [stack EXCEPT ![1] = <<[procedure |-> "Cpu_process", pc |-> "Done", p |-> 1]>> \o stack[1]]
       stack' = [stack EXCEPT ![1] = <<[procedure |-> "Cpu_process", pc |-> "Done", p |-> 1]>> \o stack[1]] \*/\
       \*[procedure |-> "Cpu_process", pc |-> "Done", p |-> 1] \in StackEntry
       \*\/ stack' = [stack EXCEPT
       \*        ![2] = <<[procedure |-> "Cpu_process", pc |-> "Done",
       \*                  p |-> p[2]]>>
       \*               \o stack[2]]) 
       =>  (stack
        \in [{1} \cup {2} ->
               Seq([procedure : {"Cpu_process"}, pc : {"Done"},
                    p : 1..2 \cup {defaultInitValue}])])'
<1> QED OBVIOUS
  
 THEOREM stack \in [{1} \cup {2} -> Seq(StackEntry)] /\
         \*stack' = stack
         stack' = [stack EXCEPT ![1] = <<[procedure |-> "Cpu_process", pc |-> "Done", p |-> 1]>> \o stack[1]] /\
         <<[procedure |-> "Cpu_process", pc |-> "Done", p |-> 1]>> \o stack[1] \in Seq(StackEntry)
         \*[procedure |-> "Cpu_process", pc |-> "Done", p |-> 1] \in StackEntry
         =>  (stack \in [{1} \cup {2} -> Seq(StackEntry)])'
 <1> QED BY DEF StackEntry
 
  
 VARIABLE X, Y
 THEOREM X \in [{1} \cup {2} -> Seq(StackEntry)] /\
         Y \in [{1} \cup {2} -> Seq(StackEntry)] /\
         X[1] \o <<>> \in Seq(StackEntry) /\
         X' = [X EXCEPT ![1] = X[1] \o <<>>(*Y[1]*)] =>
         (X \in [{1} \cup {2} -> Seq(StackEntry)])'
<1> QED BY DEF StackEntry



=============================================================================
\* Modification History
\* Last modified Mon Jun 14 12:33:11 PDT 2021 by uber
\* Created Mon Apr 26 07:25:44 PDT 2021 by uber
