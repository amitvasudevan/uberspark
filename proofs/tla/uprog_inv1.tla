----------------------------- MODULE uprog_inv1 -----------------------------
EXTENDS Sequences, Integers, TLAPS
CONSTANTS (*MAXCPUS,*) MAXUOBJCOLLECTIONS, MAXUOBJSWITHINCOLLECTION

MAXCPUS == 2

LEGACY == 1
UBER == 3

(* --algorithm execution
variables Cpu = [cp \in 1..MAXCPUS |->
            [Id |-> cp,                             \* unique CPU identifier
             Pc |-> 0,                              \* program counter (currently abstracted to object control)
             Pr |-> 0,                              \* privelege level
             Collection |-> 0,
             Object |-> 0,
             Shared_cpustate |-> 0,
             Legacy_cpustate |-> 0,
             Res_cpustate |-> [m \in 1..MAXUOBJCOLLECTIONS |->
                 [n \in 1..MAXUOBJSWITHINCOLLECTION |-> 0]
             ]
            ]
          ],
             
    memory = [Mem_legacy |-> 0,
              Mem_global |-> 0, 
              Mem_uobjcollection |-> [co \in 1..MAXUOBJCOLLECTIONS |->
                [memuobj |-> [ob \in 1..MAXUOBJSWITHINCOLLECTION |->
                   [
                    uobj_local_data |-> 0, (* Section 1.6: memory safety: invariant 1 *)
                    lock |-> 0
                   ]
                  ]
                ]
              ]
             ],
    call_stack = 3;
    
(***************************************************************************)
(* Cpu_process(p) runs legacy code or an uObject collection on processor   *)
(* p.                                                                      *)
(***************************************************************************)
procedure Cpu_process(p) begin
Start:
    either
        Cpu[p].Pr := LEGACY;
Call:
        call Legacy_code(p, 0);
        return;
    or
        with col \in 1..MAXUOBJCOLLECTIONS do
            Cpu[p].Pr := UBER;      
            call Uobjcollection_code(p, col, 0);
        end with;
After_branching:
        return;
    end either;
end procedure;

(***************************************************************************)
(* Legacy_code(p, saved_pc) accesses cpu state or legacy memory; or calls  *)
(* uObject collection code.                                                *)
(***************************************************************************)
procedure Legacy_code(p, saved_pc) begin
Start:
    Cpu[p].Pc := LEGACY;
Loop:
    while TRUE do
        either
            if call_stack > 0 then
                call_stack := call_stack - 1;
                with col \in 1..MAXUOBJCOLLECTIONS do
                    call Uobjcollection_code(p, col, LEGACY) \* Sentinel will not allow this to happen if legacy called from uObject code
                end with;
            end if;
        or 
            memory.Mem_legacy := LEGACY;        \* Read/write to memory.mem_legacy[]
        or  
            Cpu[p].Shared_cpustate := LEGACY;   \* Read/write to cpu[x].shared_cpustate[]
        or  
            Cpu[p].Legacy_cpustate := LEGACY;   \* Read/write to cpu[x].legacy_cpustate[]
        or
            Cpu[p].Pc := saved_pc;
            return; 
        end either;
    end while;
end procedure;
 
(***************************************************************************)
(* Uobjcollection_code(p, c, saved_pc) calls code for each uObject o in the*)
(* collection c on processor p.                                            *)
(***************************************************************************)
procedure Uobjcollection_code(p, c, saved_pc) begin
Start:
    Cpu[p].Pc := UBER;
Call:
    with object \in 1..MAXUOBJCOLLECTIONS do
        call Uobject_code(p, c, object, saved_pc);
    end with;
Return:
    Cpu[p].Pc := saved_pc;
    return;
end procedure;

(***************************************************************************)
(* Uobject_code(p, c, o, saved_pc) calls uObject functions or legacy       *)
(* functions, or accesses its allocated CPU state or memory.               *)
(***************************************************************************)
procedure Uobject_code(p, c, o, saved_pc)
    variables In_uobj = FALSE,
        Uobj_finished = FALSE; 
        
        (* Section 1.6: memory safety: invariant 1 *)
        \* char tmp_local_data;
        \* declared in memory above
        
    begin
Start:
    await memory.Mem_uobjcollection[c].memuobj[o].lock = 0;
    if ~In_uobj then
        Cpu[p].Pc := UBER;
Loop:
        while ~Uobj_finished do
            either
                if call_stack > 0 then
                    call_stack := call_stack - 1;
                    \*
                    call Uobject_code_legacy_func(p, UBER);
                    
                end if;
            or 
                (* Section 1.6: memory safety: invariant 1 *)
                \*memory.Mem_uobjcollection[c].memuobj[o].uobj_local_data := 0;   \* access uobjects local_data for write
                memory.Mem_uobjcollection[c].memuobj[o].uobj_local_data := 100*c + o; \* read and write currently represented the same
            or
                (* Section 1.6: memory safety: invariant 1 *)
                \*tmp_local_data = memory.Mem_uobjcollection[c].memuobj[o].uobj_local_data;   \* access uobjects local_data for read
                skip;
            or
                Uobj_finished := TRUE;
            end either;
        end while;
    end if;
Uobj_finished_assign:
    Uobj_finished := FALSE;
    In_uobj := FALSE;
    Cpu[p].Pc := saved_pc;
End:
    return;
end procedure;

procedure Uobject_code_legacy_func(p, saved_pc) begin
Start:
    Cpu[p].Pc := LEGACY;
End:
    Cpu[p].Pc := saved_pc;
    return;
end procedure;

process one = 1
begin
  A:
    call Cpu_process(1);
end process;

process two = 2
begin
  A:
    call Cpu_process(2);
end process;

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "52368506" /\ chksum(tla) = "cbf376ff")
\* Label Start of procedure Cpu_process at line 45 col 5 changed to Start_
\* Label Call of procedure Cpu_process at line 48 col 9 changed to Call_
\* Label Start of procedure Legacy_code at line 66 col 5 changed to Start_L
\* Label Loop of procedure Legacy_code at line 68 col 5 changed to Loop_
\* Label Start of procedure Uobjcollection_code at line 95 col 5 changed to Start_U
\* Label Start of procedure Uobject_code at line 119 col 5 changed to Start_Uo
\* Label End of procedure Uobject_code at line 149 col 5 changed to End_
\* Label A of process one at line 163 col 5 changed to A_
\* Parameter p of procedure Cpu_process at line 43 col 23 changed to p_
\* Parameter p of procedure Legacy_code at line 64 col 23 changed to p_L
\* Parameter saved_pc of procedure Legacy_code at line 64 col 26 changed to saved_pc_
\* Parameter p of procedure Uobjcollection_code at line 93 col 31 changed to p_U
\* Parameter c of procedure Uobjcollection_code at line 93 col 34 changed to c_
\* Parameter saved_pc of procedure Uobjcollection_code at line 93 col 37 changed to saved_pc_U
\* Parameter p of procedure Uobject_code at line 109 col 24 changed to p_Uo
\* Parameter saved_pc of procedure Uobject_code at line 109 col 33 changed to saved_pc_Uo
CONSTANT defaultInitValue
VARIABLES Cpu, memory, call_stack, pc, stack, p_, p_L, saved_pc_, p_U, c_, 
          saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, Uobj_finished, p, 
          saved_pc

vars == << Cpu, memory, call_stack, pc, stack, p_, p_L, saved_pc_, p_U, c_, 
           saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, Uobj_finished, p, 
           saved_pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ Cpu =       [cp \in 1..MAXCPUS |->
                   [Id |-> cp,
                    Pc |-> 0,
                    Pr |-> 0,
                    Collection |-> 0,
                    Object |-> 0,
                    Shared_cpustate |-> 0,
                    Legacy_cpustate |-> 0,
                    Res_cpustate |-> [m \in 1..MAXUOBJCOLLECTIONS |->
                        [n \in 1..MAXUOBJSWITHINCOLLECTION |-> 0]
                    ]
                   ]
                 ]
        /\ memory = [Mem_legacy |-> 0,
                     Mem_global |-> 0,
                     Mem_uobjcollection |-> [co \in 1..MAXUOBJCOLLECTIONS |->
                       [memuobj |-> [ob \in 1..MAXUOBJSWITHINCOLLECTION |->
                          [
                           uobj_local_data |-> 0,
                           lock |-> 0
                          ]
                         ]
                       ]
                     ]
                    ]
        /\ call_stack = 3
        (* Procedure Cpu_process *)
        /\ p_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Legacy_code *)
        /\ p_L = [ self \in ProcSet |-> defaultInitValue]
        /\ saved_pc_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Uobjcollection_code *)
        /\ p_U = [ self \in ProcSet |-> defaultInitValue]
        /\ c_ = [ self \in ProcSet |-> defaultInitValue]
        /\ saved_pc_U = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Uobject_code *)
        /\ p_Uo = [ self \in ProcSet |-> defaultInitValue]
        /\ c = [ self \in ProcSet |-> defaultInitValue]
        /\ o = [ self \in ProcSet |-> defaultInitValue]
        /\ saved_pc_Uo = [ self \in ProcSet |-> defaultInitValue]
        /\ In_uobj = [ self \in ProcSet |-> FALSE]
        /\ Uobj_finished = [ self \in ProcSet |-> FALSE]
        (* Procedure Uobject_code_legacy_func *)
        /\ p = [ self \in ProcSet |-> defaultInitValue]
        /\ saved_pc = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "A_"
                                        [] self = 2 -> "A"]

Start_(self) == /\ pc[self] = "Start_"
                /\ \/ /\ Cpu' = [Cpu EXCEPT ![p_[self]].Pr = LEGACY]
                      /\ pc' = [pc EXCEPT ![self] = "Call_"]
                      /\ UNCHANGED <<stack, p_U, c_, saved_pc_U>>
                   \/ /\ \E col \in 1..MAXUOBJCOLLECTIONS:
                           /\ Cpu' = [Cpu EXCEPT ![p_[self]].Pr = UBER]
                           /\ /\ c_' = [c_ EXCEPT ![self] = col]
                              /\ p_U' = [p_U EXCEPT ![self] = p_[self]]
                              /\ saved_pc_U' = [saved_pc_U EXCEPT ![self] = 0]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobjcollection_code",
                                                                       pc        |->  "After_branching",
                                                                       p_U       |->  p_U[self],
                                                                       c_        |->  c_[self],
                                                                       saved_pc_U |->  saved_pc_U[self] ] >>
                                                                   \o stack[self]]
                           /\ pc' = [pc EXCEPT ![self] = "Start_U"]
                /\ UNCHANGED << memory, call_stack, p_, p_L, saved_pc_, p_Uo, 
                                c, o, saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                saved_pc >>

Call_(self) == /\ pc[self] = "Call_"
               /\ /\ p_L' = [p_L EXCEPT ![self] = p_[self]]
                  /\ saved_pc_' = [saved_pc_ EXCEPT ![self] = 0]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Legacy_code",
                                                           pc        |->  Head(stack[self]).pc,
                                                           p_L       |->  p_L[self],
                                                           saved_pc_ |->  saved_pc_[self] ] >>
                                                       \o Tail(stack[self])]
               /\ pc' = [pc EXCEPT ![self] = "Start_L"]
               /\ UNCHANGED << Cpu, memory, call_stack, p_, p_U, c_, 
                               saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, 
                               Uobj_finished, p, saved_pc >>

After_branching(self) == /\ pc[self] = "After_branching"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ p_' = [p_ EXCEPT ![self] = Head(stack[self]).p_]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << Cpu, memory, call_stack, p_L, 
                                         saved_pc_, p_U, c_, saved_pc_U, p_Uo, 
                                         c, o, saved_pc_Uo, In_uobj, 
                                         Uobj_finished, p, saved_pc >>

Cpu_process(self) == Start_(self) \/ Call_(self) \/ After_branching(self)

Start_L(self) == /\ pc[self] = "Start_L"
                 /\ Cpu' = [Cpu EXCEPT ![p_L[self]].Pc = LEGACY]
                 /\ pc' = [pc EXCEPT ![self] = "Loop_"]
                 /\ UNCHANGED << memory, call_stack, stack, p_, p_L, saved_pc_, 
                                 p_U, c_, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                 In_uobj, Uobj_finished, p, saved_pc >>

Loop_(self) == /\ pc[self] = "Loop_"
               /\ \/ /\ IF call_stack > 0
                           THEN /\ call_stack' = call_stack - 1
                                /\ \E col \in 1..MAXUOBJCOLLECTIONS:
                                     /\ /\ c_' = [c_ EXCEPT ![self] = col]
                                        /\ p_U' = [p_U EXCEPT ![self] = p_L[self]]
                                        /\ saved_pc_U' = [saved_pc_U EXCEPT ![self] = LEGACY]
                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobjcollection_code",
                                                                                 pc        |->  "Loop_",
                                                                                 p_U       |->  p_U[self],
                                                                                 c_        |->  c_[self],
                                                                                 saved_pc_U |->  saved_pc_U[self] ] >>
                                                                             \o stack[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "Start_U"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Loop_"]
                                /\ UNCHANGED << call_stack, stack, p_U, c_, 
                                                saved_pc_U >>
                     /\ UNCHANGED <<Cpu, memory, p_L, saved_pc_>>
                  \/ /\ memory' = [memory EXCEPT !.Mem_legacy = LEGACY]
                     /\ pc' = [pc EXCEPT ![self] = "Loop_"]
                     /\ UNCHANGED <<Cpu, call_stack, stack, p_L, saved_pc_, p_U, c_, saved_pc_U>>
                  \/ /\ Cpu' = [Cpu EXCEPT ![p_L[self]].Shared_cpustate = LEGACY]
                     /\ pc' = [pc EXCEPT ![self] = "Loop_"]
                     /\ UNCHANGED <<memory, call_stack, stack, p_L, saved_pc_, p_U, c_, saved_pc_U>>
                  \/ /\ Cpu' = [Cpu EXCEPT ![p_L[self]].Legacy_cpustate = LEGACY]
                     /\ pc' = [pc EXCEPT ![self] = "Loop_"]
                     /\ UNCHANGED <<memory, call_stack, stack, p_L, saved_pc_, p_U, c_, saved_pc_U>>
                  \/ /\ Cpu' = [Cpu EXCEPT ![p_L[self]].Pc = saved_pc_[self]]
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ p_L' = [p_L EXCEPT ![self] = Head(stack[self]).p_L]
                     /\ saved_pc_' = [saved_pc_ EXCEPT ![self] = Head(stack[self]).saved_pc_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED <<memory, call_stack, p_U, c_, saved_pc_U>>
               /\ UNCHANGED << p_, p_Uo, c, o, saved_pc_Uo, In_uobj, 
                               Uobj_finished, p, saved_pc >>

Legacy_code(self) == Start_L(self) \/ Loop_(self)

Start_U(self) == /\ pc[self] = "Start_U"
                 /\ Cpu' = [Cpu EXCEPT ![p_U[self]].Pc = UBER]
                 /\ pc' = [pc EXCEPT ![self] = "Call"]
                 /\ UNCHANGED << memory, call_stack, stack, p_, p_L, saved_pc_, 
                                 p_U, c_, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                 In_uobj, Uobj_finished, p, saved_pc >>

Call(self) == /\ pc[self] = "Call"
              /\ \E object \in 1..MAXUOBJCOLLECTIONS:
                   /\ /\ c' = [c EXCEPT ![self] = c_[self]]
                      /\ o' = [o EXCEPT ![self] = object]
                      /\ p_Uo' = [p_Uo EXCEPT ![self] = p_U[self]]
                      /\ saved_pc_Uo' = [saved_pc_Uo EXCEPT ![self] = saved_pc_U[self]]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobject_code",
                                                               pc        |->  "Return",
                                                               In_uobj   |->  In_uobj[self],
                                                               Uobj_finished |->  Uobj_finished[self],
                                                               p_Uo      |->  p_Uo[self],
                                                               c         |->  c[self],
                                                               o         |->  o[self],
                                                               saved_pc_Uo |->  saved_pc_Uo[self] ] >>
                                                           \o stack[self]]
                   /\ In_uobj' = [In_uobj EXCEPT ![self] = FALSE]
                   /\ Uobj_finished' = [Uobj_finished EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "Start_Uo"]
              /\ UNCHANGED << Cpu, memory, call_stack, p_, p_L, saved_pc_, p_U, 
                              c_, saved_pc_U, p, saved_pc >>

Return(self) == /\ pc[self] = "Return"
                /\ Cpu' = [Cpu EXCEPT ![p_U[self]].Pc = saved_pc_U[self]]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ p_U' = [p_U EXCEPT ![self] = Head(stack[self]).p_U]
                /\ c_' = [c_ EXCEPT ![self] = Head(stack[self]).c_]
                /\ saved_pc_U' = [saved_pc_U EXCEPT ![self] = Head(stack[self]).saved_pc_U]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << memory, call_stack, p_, p_L, saved_pc_, p_Uo, 
                                c, o, saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                saved_pc >>

Uobjcollection_code(self) == Start_U(self) \/ Call(self) \/ Return(self)

Start_Uo(self) == /\ pc[self] = "Start_Uo"
                  /\ memory.Mem_uobjcollection[c[self]].memuobj[o[self]].lock = 0
                  /\ IF ~In_uobj[self]
                        THEN /\ Cpu' = [Cpu EXCEPT ![p_Uo[self]].Pc = UBER]
                             /\ pc' = [pc EXCEPT ![self] = "Loop"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Uobj_finished_assign"]
                             /\ Cpu' = Cpu
                  /\ UNCHANGED << memory, call_stack, stack, p_, p_L, 
                                  saved_pc_, p_U, c_, saved_pc_U, p_Uo, c, o, 
                                  saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                  saved_pc >>

Loop(self) == /\ pc[self] = "Loop"
              /\ IF ~Uobj_finished[self]
                    THEN /\ \/ /\ IF call_stack > 0
                                     THEN /\ call_stack' = call_stack - 1
                                          /\ /\ p' = [p EXCEPT ![self] = p_Uo[self]]
                                             /\ saved_pc' = [saved_pc EXCEPT ![self] = UBER]
                                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobject_code_legacy_func",
                                                                                      pc        |->  "Loop",
                                                                                      p         |->  p[self],
                                                                                      saved_pc  |->  saved_pc[self] ] >>
                                                                                  \o stack[self]]
                                          /\ pc' = [pc EXCEPT ![self] = "Start"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "Loop"]
                                          /\ UNCHANGED << call_stack, stack, p, 
                                                          saved_pc >>
                               /\ UNCHANGED <<memory, Uobj_finished>>
                            \/ /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c[self]].memuobj[o[self]].uobj_local_data = 100*c[self] + o[self]]
                               /\ pc' = [pc EXCEPT ![self] = "Loop"]
                               /\ UNCHANGED <<call_stack, stack, Uobj_finished, p, saved_pc>>
                            \/ /\ TRUE
                               /\ pc' = [pc EXCEPT ![self] = "Loop"]
                               /\ UNCHANGED <<memory, call_stack, stack, Uobj_finished, p, saved_pc>>
                            \/ /\ Uobj_finished' = [Uobj_finished EXCEPT ![self] = TRUE]
                               /\ pc' = [pc EXCEPT ![self] = "Loop"]
                               /\ UNCHANGED <<memory, call_stack, stack, p, saved_pc>>
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Uobj_finished_assign"]
                         /\ UNCHANGED << memory, call_stack, stack, 
                                         Uobj_finished, p, saved_pc >>
              /\ UNCHANGED << Cpu, p_, p_L, saved_pc_, p_U, c_, saved_pc_U, 
                              p_Uo, c, o, saved_pc_Uo, In_uobj >>

Uobj_finished_assign(self) == /\ pc[self] = "Uobj_finished_assign"
                              /\ Uobj_finished' = [Uobj_finished EXCEPT ![self] = FALSE]
                              /\ In_uobj' = [In_uobj EXCEPT ![self] = FALSE]
                              /\ Cpu' = [Cpu EXCEPT ![p_Uo[self]].Pc = saved_pc_Uo[self]]
                              /\ pc' = [pc EXCEPT ![self] = "End_"]
                              /\ UNCHANGED << memory, call_stack, stack, p_, 
                                              p_L, saved_pc_, p_U, c_, 
                                              saved_pc_U, p_Uo, c, o, 
                                              saved_pc_Uo, p, saved_pc >>

End_(self) == /\ pc[self] = "End_"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ In_uobj' = [In_uobj EXCEPT ![self] = Head(stack[self]).In_uobj]
              /\ Uobj_finished' = [Uobj_finished EXCEPT ![self] = Head(stack[self]).Uobj_finished]
              /\ p_Uo' = [p_Uo EXCEPT ![self] = Head(stack[self]).p_Uo]
              /\ c' = [c EXCEPT ![self] = Head(stack[self]).c]
              /\ o' = [o EXCEPT ![self] = Head(stack[self]).o]
              /\ saved_pc_Uo' = [saved_pc_Uo EXCEPT ![self] = Head(stack[self]).saved_pc_Uo]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Cpu, memory, call_stack, p_, p_L, saved_pc_, p_U, 
                              c_, saved_pc_U, p, saved_pc >>

Uobject_code(self) == Start_Uo(self) \/ Loop(self)
                         \/ Uobj_finished_assign(self) \/ End_(self)

Start(self) == /\ pc[self] = "Start"
               /\ Cpu' = [Cpu EXCEPT ![p[self]].Pc = LEGACY]
               /\ pc' = [pc EXCEPT ![self] = "End"]
               /\ UNCHANGED << memory, call_stack, stack, p_, p_L, saved_pc_, 
                               p_U, c_, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

End(self) == /\ pc[self] = "End"
             /\ Cpu' = [Cpu EXCEPT ![p[self]].Pc = saved_pc[self]]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
             /\ saved_pc' = [saved_pc EXCEPT ![self] = Head(stack[self]).saved_pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << memory, call_stack, p_, p_L, saved_pc_, p_U, c_, 
                             saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, 
                             Uobj_finished >>

Uobject_code_legacy_func(self) == Start(self) \/ End(self)

A_ == /\ pc[1] = "A_"
      /\ /\ p_' = [p_ EXCEPT ![1] = 1]
         /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "Cpu_process",
                                               pc        |->  "Done",
                                               p_        |->  p_[1] ] >>
                                           \o stack[1]]
      /\ pc' = [pc EXCEPT ![1] = "Start_"]
      /\ UNCHANGED << Cpu, memory, call_stack, p_L, saved_pc_, p_U, c_, 
                      saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, 
                      Uobj_finished, p, saved_pc >>

one == A_

A == /\ pc[2] = "A"
     /\ /\ p_' = [p_ EXCEPT ![2] = 2]
        /\ stack' = [stack EXCEPT ![2] = << [ procedure |->  "Cpu_process",
                                              pc        |->  "Done",
                                              p_        |->  p_[2] ] >>
                                          \o stack[2]]
     /\ pc' = [pc EXCEPT ![2] = "Start_"]
     /\ UNCHANGED << Cpu, memory, call_stack, p_L, saved_pc_, p_U, c_, 
                     saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, 
                     Uobj_finished, p, saved_pc >>

two == A

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two
           \/ (\E self \in ProcSet:  \/ Cpu_process(self) \/ Legacy_code(self)
                                     \/ Uobjcollection_code(self)
                                     \/ Uobject_code(self)
                                     \/ Uobject_code_legacy_func(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


(***********************************************************************************)
(* uObject only writes to its uobj_local_data                                      *)
(* Need to check 100*c+o (or pc version) not in any uObject memory outside of this *)
(***********************************************************************************)
uprog_inv1 == \A col \in 1..MAXUOBJCOLLECTIONS: \A obj \in 1..MAXUOBJSWITHINCOLLECTION: 
                    memory.Mem_uobjcollection[col].memuobj[obj].uobj_local_data = 100*col + obj \/
                    memory.Mem_uobjcollection[col].memuobj[obj].uobj_local_data = 0
                    
StackEntry == [procedure : {"Cpu_process", "Legacy_code", "Uobjcollection_code",
                "Uobject_code", "Uobject_code_legacy_func"},
   pc : {"A_", "A", "After_branching", "Loop_", "Return", "Loop", "Done"},
   p_ : 1..MAXCPUS \cup {defaultInitValue},
   p : 1..MAXCPUS \cup {defaultInitValue},
   saved_pc : 0..3 \cup {defaultInitValue},
   c : 1..MAXCPUS \cup {defaultInitValue},
   o : 1..MAXCPUS \cup {defaultInitValue},
   p_Uo : 1..MAXCPUS \cup {defaultInitValue},
   In_uobj : BOOLEAN \cup {defaultInitValue},
   Uobj_finished : BOOLEAN \cup {defaultInitValue},
   p_U : 1..MAXCPUS \cup {defaultInitValue},
   c_ : 1..MAXCPUS \cup {defaultInitValue},
   saved_pc_U : 0..3 \cup {defaultInitValue},
   p_L : 1..MAXCPUS \cup {defaultInitValue},
   saved_pc_ : 0..3 \cup {defaultInitValue}
]


TypeOK == /\ Cpu \in [1..MAXCPUS ->
                   [Id : 1..MAXCPUS,
                    Pc : 0..3,
                    Pr : 0..3,
                    Shared_cpustate : 0..3,
                    Legacy_cpustate : 0..3,
                    Res_cpustate : [1..MAXUOBJCOLLECTIONS ->
                        [1..MAXUOBJSWITHINCOLLECTION -> 0..3]
                    ]
                   ]
                 ]
          /\ memory \in [Mem_legacy : 0..3,
                         Mem_global : 0..3, 
                         Mem_uobjcollection : [1..MAXUOBJCOLLECTIONS ->
                           [memuobj : [1..MAXUOBJSWITHINCOLLECTION ->
                              [uobj_local_data : 0..3]
                             ]
                           ]
                         ]
                        ]
          /\ call_stack \in {3}
        (* Procedure Cpu_process *)
          /\ p_ \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}]
        (* Procedure Legacy_code *)
          /\ p_L \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}]
          /\ saved_pc_ \in [ ProcSet -> 0..3 \cup {defaultInitValue}]
        (* Procedure Uobjcollection_code *)
          /\ p_U \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}]
          /\ c_ \in [ ProcSet -> 1..MAXUOBJCOLLECTIONS \cup {defaultInitValue}]
          /\ saved_pc_U \in [ ProcSet -> 0..3 \cup {defaultInitValue}]
        (* Procedure Uobject_code *)
          /\ p_Uo \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}]
          /\ c \in [ ProcSet -> 1..MAXUOBJCOLLECTIONS \cup {defaultInitValue}]
          /\ o \in [ ProcSet -> 1..MAXUOBJSWITHINCOLLECTION \cup {defaultInitValue}]
          /\ saved_pc_Uo \in [ ProcSet -> 0..3 \cup {defaultInitValue}]
          /\ In_uobj \in [ ProcSet -> BOOLEAN \cup {defaultInitValue}]
          /\ Uobj_finished \in [ ProcSet -> BOOLEAN \cup {defaultInitValue}]
        (* Procedure Uobject_code_legacy_func *)
          /\ p \in [ ProcSet -> 1..MAXCPUS (*\cup {defaultInitValue}*)]
          /\ saved_pc \in [ ProcSet -> 0..3 \cup {defaultInitValue}]
          /\ stack \in [ ProcSet -> Seq(StackEntry)]
          /\ pc \in [ProcSet -> {"one", "A_", "two", "A", "Start_", "Cpu_process", "Call_", "After_branching",
            "Legacy_code", "Start_L", "Loop_", "End_",
            "Uobjcollection_code", "Start_U", "Call", "Return",
            "Uobject_code", "Start_Uo", "Uobj_finished_assign",
            "Uobject_code_legacy_func", "Start", "End", "Loop"}]
          /\ TRUE
            
      (*                                  
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
          *)


Inv == TypeOK /\ uprog_inv1

\* Proof outline      
THEOREM Spec => []uprog_inv1
<1>1. Init => Inv
  BY DEF Init, Inv\*, TypeOK, uprog_inv1
<1>2. Inv /\ [Next]_vars => Inv'
  BY DEFS Inv, TypeOK, uprog_inv1, vars, Next,
            one, A_, two, A, Start_, Cpu_process, Call_, After_branching,
            Legacy_code, Start_L, Loop_, End_,
            Uobjcollection_code, Start_U, Call, Return,
            Uobject_code, Start_Uo, Uobj_finished_assign,
            Uobject_code_legacy_func, Start, End, Loop
<1>3. Inv => uprog_inv1
  BY DEFS Inv, uprog_inv1
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
THEOREM Spec => []uprog_inv1
<1>1 Init => uprog_inv1
  <2>1 SUFFICES ASSUME Init PROVE uprog_inv1
    BY DEF Init, uprog_inv1
  <2>2 uprog_inv1
    BY <2>1 DEF Init, uprog_inv1
  <2> QED BY <2>2 DEF Init, Inv, TypeOK, uprog_inv1
<1>2 uprog_inv1 /\ [Next]_vars => uprog_inv1'
  <2>1 SUFFICES ASSUME uprog_inv1, Next PROVE uprog_inv1'
    BY DEFS uprog_inv1, vars
  <2>2 uprog_inv1'
    <3>1 CASE A \/ A_
      BY <2>1, <3>1 DEF A, A_, Inv, uprog_inv1
    <3>2 CASE \E i \in ProcSet : Cpu_process(i)
      BY <2>1, <3>2 DEF Cpu_process, Inv, uprog_inv1, Start_, Call_, After_branching
    <3>3 CASE \E i \in ProcSet : Legacy_code(i)
      <4>1 CASE \E i \in ProcSet : Start_L(i)
        BY <2>1, <3>3, <4>1 DEF Legacy_code, Inv, uprog_inv1, Start_L
      <4>2 CASE \E i \in ProcSet : Loop_(i)
        <5>1 CASE memory' = [memory EXCEPT !.Mem_legacy = LEGACY]
          BY <2>1, <3>3, <4>2, <5>1 DEF Legacy_code, Inv, uprog_inv1, Loop_
        <5>2 CASE UNCHANGED memory
          BY <2>1, <3>3, <4>2, <5>2 DEF Legacy_code, Inv, uprog_inv1, Loop_
        <5> QED BY <2>1, <3>3, <4>2, <5>1, <5>2 DEF Legacy_code, Inv, uprog_inv1, Loop_
      <4> QED BY <2>1, <3>3, <4>1, <4>2 DEF uprog_inv1, Legacy_code
    <3>4 CASE \E i \in ProcSet : Uobjcollection_code(i)
      BY <2>1, <3>4 DEF Uobjcollection_code, uprog_inv1, Inv, Start_U, Call, Return
    <3>5 CASE \E i \in ProcSet : Uobject_code(i)
      <4>1 CASE (\E i \in ProcSet : memory' = [memory EXCEPT !.Mem_uobjcollection[c[i]].memuobj[o[i]].uobj_local_data = 100*c[i] + o[i]])
        BY <2>1, <3>5, <4>1 DEF Inv, uprog_inv1
      <4>2 CASE UNCHANGED memory
        BY <2>1, <3>5, <4>2 DEF Uobject_code, TypeOK, StackEntry, Inv, uprog_inv1,
                        Start_Uo, Loop, Uobj_finished_assign, End_
      <4> QED BY <2>1, <3>5, <4>1, <4>2 DEF Uobject_code, TypeOK, StackEntry, Inv, uprog_inv1,
                        Start_Uo, Loop, Uobj_finished_assign, End_
    <3>6 CASE \E i \in ProcSet : Uobject_code_legacy_func(i)
      BY <2>1, <3>6 DEF Uobject_code_legacy_func, TypeOK, StackEntry, Inv, uprog_inv1, Start, End
    <3>7 CASE Terminating
      BY <2>1, <3>7 DEF Terminating, TypeOK, StackEntry, Inv, vars, uprog_inv1
    <3> QED BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7
          DEF Inv, Next, uprog_inv1, one, two
  <2> QED BY <2>2 DEF uprog_inv1
<1> QED
  BY <1>1, <1>2, PTL DEF Spec
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
THEOREM Spec => []uprog_inv1
<1>1 Init => Inv
  <2>1 SUFFICES ASSUME Init PROVE Inv
    BY DEF Init, Inv, TypeOK, uprog_inv1
  <2>2 uprog_inv1
    BY <2>1 DEF Init, uprog_inv1
  <2>3 TypeOK
    \*BY <2>1 DEF Init, TypeOK, MAXCPUS
    <3>1 pc \in [ProcSet -> {"one", "A_", "two", "A", "Start_", "Cpu_process", "Call_", "After_branching",
            "Legacy_code", "Start_L", "Loop_", "End_",
            "Uobjcollection_code", "Start_U", "Call", "Return",
            "Uobject_code", "Start_Uo", "Uobj_finished_assign",
            "Uobject_code_legacy_func", "Start", "End", "Loop"}]
      BY <2>1 DEF Init, ProcSet
    <3>2 stack \in [ ProcSet -> Seq(StackEntry)]
      BY <2>1 DEF Init, ProcSet
    <3>3 saved_pc \in [ ProcSet -> 0..3 \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet
    <3>4 p \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet
    <3>5 Uobj_finished \in [ ProcSet -> BOOLEAN \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet
    <3>6 In_uobj \in [ ProcSet -> BOOLEAN \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet
    <3>7 saved_pc_Uo \in [ ProcSet -> 0..3 \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet
    <3>8 o \in [ ProcSet -> 1..MAXUOBJSWITHINCOLLECTION \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet
    <3>9 c \in [ ProcSet -> 1..MAXUOBJCOLLECTIONS \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet
    <3>10 p_Uo \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet
    <3>11 saved_pc_U \in [ ProcSet -> 0..3 \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet
    <3>12 c_ \in [ ProcSet -> 1..MAXUOBJCOLLECTIONS \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet
    <3>13 p_U \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet
    <3>14 saved_pc_ \in [ ProcSet -> 0..3 \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet
    <3>15 p_L \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet
    <3>16 p_ \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}]
      BY <2>1 DEF Init, ProcSet      
    <3>17 call_stack \in {3}
      BY <2>1 DEF Init, ProcSet
    <3>18 memory \in [Mem_legacy : 0..3,
                         Mem_global : 0..3, 
                         Mem_uobjcollection : [1..MAXUOBJCOLLECTIONS ->
                           [memuobj : [1..MAXUOBJSWITHINCOLLECTION ->
                              [uobj_local_data : 0..3]
                             ]
                           ]
                         ]
                        ]
      BY <2>1 DEF Init, ProcSet
    <3>19 Cpu \in [1..MAXCPUS ->
                   [Id : 1..MAXCPUS,
                    Pc : 0..3,
                    Pr : 0..3,
                    Shared_cpustate : 0..3,
                    Legacy_cpustate : 0..3,
                    Res_cpustate : [1..MAXUOBJCOLLECTIONS ->
                        [1..MAXUOBJSWITHINCOLLECTION -> 0..3]
                    ]
                   ]
                 ]
      BY <2>1 DEF Init, ProcSet, MAXCPUS
    <3> QED BY <3>1, <3>2, <3>3, <3>4,
               <3>5, <3>6, <3>7, <3>8,
               <3>9, <3>10, <3>11, <3>12,
               <3>13, <3>14, <3>15, <3>16,
               <3>17, <3>18, <3>19 DEF Init, TypeOK
  <2> QED BY <2>2, <2>3 DEF Init, Inv, TypeOK, uprog_inv1
<1>2 Inv /\ [Next]_vars => Inv'
  <2>1 SUFFICES ASSUME Inv, Next PROVE Inv'
    BY DEFS Inv, TypeOK, uprog_inv1, vars
  <2>2 TypeOK'
    <3>1 CASE A \/ A_
      <4>1 (pc \in [ProcSet -> {"one", "A_", "two", "A", "Start_", "Cpu_process", "Call_", "After_branching",
            "Legacy_code", "Start_L", "Loop_", "End_",
            "Uobjcollection_code", "Start_U", "Call", "Return",
            "Uobject_code", "Start_Uo", "Uobj_finished_assign",
            "Uobject_code_legacy_func", "Start", "End", "Loop"}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>2 (stack \in [ ProcSet -> Seq(StackEntry)])'
        BY <2>1, <3>1,
          p_[1] \in 1..MAXCPUS \cup {defaultInitValue},
          <<[procedure |-> "Cpu_process", pc |-> "Done",
                             p_ |-> p_[2], p |-> defaultInitValue,
                             saved_pc |-> defaultInitValue,
                             c |-> defaultInitValue, o |-> defaultInitValue,
                             p_Uo |-> defaultInitValue,
                             In_uobj |-> defaultInitValue,
                             Uobj_finished |-> defaultInitValue,
                             p_U |-> defaultInitValue,
                             c_ |-> defaultInitValue,
                             saved_pc_U |-> defaultInitValue,
                             p_L |-> defaultInitValue,
                             saved_pc_ |-> defaultInitValue]>>
                          \o stack[2] \in Seq(StackEntry),
          <<[procedure |-> "Cpu_process", pc |-> "Done",
                                p_ |-> p_[1], p |-> defaultInitValue,
                                saved_pc |-> defaultInitValue,
                                c |-> defaultInitValue,
                                o |-> defaultInitValue,
                                p_Uo |-> defaultInitValue,
                                In_uobj |-> defaultInitValue,
                                Uobj_finished |-> defaultInitValue,
                                p_U |-> defaultInitValue,
                                c_ |-> defaultInitValue,
                                saved_pc_U |-> defaultInitValue,
                                p_L |-> defaultInitValue,
                                saved_pc_ |-> defaultInitValue]>>
                             \o stack[1] \in Seq(StackEntry)
          DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>3 (saved_pc \in [ ProcSet -> 0..3 \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>4 (p \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>5 (Uobj_finished \in [ ProcSet -> BOOLEAN \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>6 (In_uobj \in [ ProcSet -> BOOLEAN \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>7 (saved_pc_Uo \in [ ProcSet -> 0..3 \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>8 (o \in [ ProcSet -> 1..MAXUOBJSWITHINCOLLECTION \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>9 (c \in [ ProcSet -> 1..MAXUOBJCOLLECTIONS \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>10 (p_Uo \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>11 (saved_pc_U \in [ ProcSet -> 0..3 \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>12 (c_ \in [ ProcSet -> 1..MAXUOBJCOLLECTIONS \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>13 (p_U \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>14 (saved_pc_ \in [ ProcSet -> 0..3 \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>15 (p_L \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>16 (p_ \in [ ProcSet -> 1..MAXCPUS \cup {defaultInitValue}])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet, MAXCPUS \* Needed MAXCPUS to compare to 2 / 1
      <4>17 (call_stack \in {3})'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>18 (memory \in [Mem_legacy : 0..3,
                         Mem_global : 0..3, 
                         Mem_uobjcollection : [1..MAXUOBJCOLLECTIONS ->
                           [memuobj : [1..MAXUOBJSWITHINCOLLECTION ->
                              [uobj_local_data : 0..3]
                             ]
                           ]
                         ]
                        ])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4>19 (Cpu \in [1..MAXCPUS ->
                   [Id : 1..MAXCPUS,
                    Pc : 0..3,
                    Pr : 0..3,
                    Shared_cpustate : 0..3,
                    Legacy_cpustate : 0..3,
                    Res_cpustate : [1..MAXUOBJCOLLECTIONS ->
                        [1..MAXUOBJSWITHINCOLLECTION -> 0..3]
                    ]
                   ]
                 ])'
        BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv, ProcSet
      <4> QED BY <4>1, <4>2, <4>3, <4>4,
                 <4>5, <4>6, <4>7, <4>8,
                 <4>9, <4>10, <4>11, <4>12,
                 <4>13, <4>14, <4>15, <4>16,
                 <4>17, <4>18, <4>19 DEF TypeOK
      \*BY <2>1, <3>1 DEF A, A_, TypeOK, StackEntry, Inv
    <3>2 CASE \E i \in ProcSet : Cpu_process(i) \* Fill out stack
      BY <2>1, <3>2 DEF Cpu_process, TypeOK, StackEntry, Inv, Start_, Call_, After_branching, ProcSet, MAXCPUS
    <3>3 CASE \E i \in ProcSet : Legacy_code(i) \* Fill out stack, split between pc?
      BY <2>1, <3>3 DEF Legacy_code, TypeOK, StackEntry, Inv, Start_L, Loop_, ProcSet, MAXCPUS
    <3>4 CASE \E i \in ProcSet : Uobjcollection_code(i) \* Stack in Call
      BY <2>1, <3>4 DEF Uobjcollection_code, TypeOK, StackEntry, Inv, Start_U, Call, Return, ProcSet, MAXCPUS
    <3>5 CASE \E i \in ProcSet : Uobject_code(i) \* Stack and memory in loop
      BY <2>1, <3>5 DEF Uobject_code, TypeOK, StackEntry, Inv, Start_Uo, Loop, Uobj_finished_assign, End_, ProcSet, MAXCPUS
    <3>6 CASE \E i \in ProcSet : Uobject_code_legacy_func(i) \* Cpu in start and End
      <4>1 CASE \E i \in ProcSet : Start(i)
        <5>1 (Cpu \in [1..2 ->
                     [Id : 1..2, Pc : 0..3, Pr : 0..3,
                      Shared_cpustate : 0..3, Legacy_cpustate : 0..3,
                      Res_cpustate : [1..MAXUOBJCOLLECTIONS ->
                                        [1..MAXUOBJSWITHINCOLLECTION -> 0..3]]]])'
          BY <2>1, <3>6, <4>1,
           (\E i \in ProcSet : [Cpu EXCEPT ![p[i]] = [Cpu[p[i]] EXCEPT !.Pc = 1]] \in [1..2 ->
                     [Id : 1..2, Pc : 0..3, Pr : 0..3,
                      Shared_cpustate : 0..3, Legacy_cpustate : 0..3,
                      Res_cpustate : [1..MAXUOBJCOLLECTIONS ->
                                        [1..MAXUOBJSWITHINCOLLECTION -> 0..3]]]]) \* set p to start at 1, and changed TypeOK, now this is a fact
           DEF Uobject_code_legacy_func, TypeOK, StackEntry, Inv, Start, ProcSet, MAXCPUS, LEGACY     
        <5>2 (pc \in [{1} \cup {2} ->
                  {"one", "A_", "two", "A", "Start_", "Cpu_process", "Call_",
                   "After_branching", "Legacy_code", "Start_L", "Loop_",
                   "End_", "Uobjcollection_code", "Start_U", "Call",
                   "Return", "Uobject_code", "Start_Uo",
                   "Uobj_finished_assign", "Uobject_code_legacy_func",
                   "Start", "End", "Loop"}])'
          BY <2>1, <3>6, <4>1 DEF Uobject_code_legacy_func, TypeOK, StackEntry, Inv, Start, ProcSet, MAXCPUS
        <5> QED BY <2>1, <3>6, <5>1, <5>2 DEF Uobject_code_legacy_func, TypeOK, StackEntry, Inv, Start, ProcSet, MAXCPUS
      <4>2 CASE \E i \in ProcSet : End(i)
        BY <2>1, <3>6 DEF Uobject_code_legacy_func, TypeOK, StackEntry, Inv, End, ProcSet, MAXCPUS
      <4> QED BY <2>1, <3>6, <4>1, <4>2 DEF Inv, TypeOK, Uobject_code_legacy_func
    <3>7 CASE Terminating
      BY <2>1, <3>7 DEF Terminating, TypeOK, StackEntry, Inv, vars
    <3> QED BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7
          DEF Inv, Next, TypeOK, StackEntry, one, two
    (*BY <2>1 DEF Inv, TypeOK, uprog_inv1, vars, Next,
            one, A_, two, A, Start_, Cpu_process, After_branching,
            Legacy_code, Start_L, Loop_, End_,
            Uobjcollection_code, Start_U, Call, Return,
            Uobject_code, Start_Uo, Uobj_finished_assign,
            Uobject_code_legacy_func, Start, End, Loop*)
  <2>3 uprog_inv1'
    <3>1 CASE A \/ A_
      BY <2>1, <3>1 DEF A, A_, Inv, uprog_inv1
    <3>2 CASE \E i \in ProcSet : Cpu_process(i)
      BY <2>1, <3>2 DEF Cpu_process, Inv, uprog_inv1, Start_, Call_, After_branching
    <3>3 CASE \E i \in ProcSet : Legacy_code(i)
      <4>1 CASE \E i \in ProcSet : Start_L(i)
        BY <2>1, <3>3, <4>1 DEF Legacy_code, Inv, uprog_inv1, Start_L
      <4>2 CASE \E i \in ProcSet : Loop_(i)
        <5>1 CASE memory' = [memory EXCEPT !.Mem_legacy = LEGACY]
          BY <2>1, <3>3, <4>2, <5>1 DEF Legacy_code, Inv, uprog_inv1, Loop_
        <5>2 CASE UNCHANGED memory
          BY <2>1, <3>3, <4>2, <5>2 DEF Legacy_code, Inv, uprog_inv1, Loop_
        <5> QED BY <2>1, <3>3, <4>2, <5>1, <5>2 DEF Legacy_code, Inv, uprog_inv1, Loop_
      <4> QED BY <2>1, <3>3, <4>1, <4>2 DEF uprog_inv1, Legacy_code
    <3>4 CASE \E i \in ProcSet : Uobjcollection_code(i)
      (*<4>1 CASE \E i \in ProcSet : Start_U(i)
        BY <2>1, <3>4, <4>1 DEF Uobjcollection_code, Inv, uprog_inv1, Start_U
      <4>2 CASE \E i \in ProcSet : Call(i)
        BY <2>1, <3>4, <4>2 DEF Uobjcollection_code, Inv, uprog_inv1, Call
      <4>3 CASE \E i \in ProcSet : Return(i)
        BY <2>1, <3>4, <4>3 DEF Uobjcollection_code, Inv, uprog_inv1, Return
      <4> QED BY <2>1, <3>4, <4>1, <4>2, <4>3 DEF Uobjcollection_code, uprog_inv1, Inv*)
      BY <2>1, <3>4 DEF Uobjcollection_code, uprog_inv1, Inv, Start_U, Call, Return
    <3>5 CASE \E i \in ProcSet : Uobject_code(i)
      <4>1 CASE (\E i \in ProcSet : memory' = [memory EXCEPT !.Mem_uobjcollection[c[i]].memuobj[o[i]].uobj_local_data = 100*c[i] + o[i]])
        BY <2>1, <3>5, <4>1 DEF Inv, uprog_inv1(*, <3>5, <4>1 DEF Uobject_code, Inv, uprog_inv1,
                        Start_Uo, Loop, Uobj_finished_assign, End_, ProcSet*) (*(((Sometimes you need less facts*)
      <4>2 CASE UNCHANGED memory
        BY <2>1, <3>5, <4>2 DEF Uobject_code, TypeOK, StackEntry, Inv, uprog_inv1,
                        Start_Uo, Loop, Uobj_finished_assign, End_
      <4> QED BY <2>1, <3>5, <4>1, <4>2 DEF Uobject_code, TypeOK, StackEntry, Inv, uprog_inv1,
                        Start_Uo, Loop, Uobj_finished_assign, End_
    <3>6 CASE \E i \in ProcSet : Uobject_code_legacy_func(i)
      BY <2>1, <3>6 DEF Uobject_code_legacy_func, TypeOK, StackEntry, Inv, uprog_inv1, Start, End
    <3>7 CASE Terminating
      BY <2>1, <3>7 DEF Terminating, TypeOK, StackEntry, Inv, vars, uprog_inv1
    <3> QED BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7
          DEF Inv, Next, uprog_inv1, one, two
    (*BY <2>1 DEF Inv, TypeOK, uprog_inv1, (*vars,*) Next,
            one, A_, two, A, Cpu_process, Start_, Call_, After_branching,
            Legacy_code, Start_L, Terminating(*, Loop_*), Uobjcollection_code, End_,
             (*Start_U, Call, Return,*)
            Uobject_code,(* Start_Uo, Uobj_finished_assign,*)
            Uobject_code_legacy_func(*, Start, End, Loop*)*)
  <2> QED BY <2>2, <2>3 DEF Inv
<1>3 Inv => uprog_inv1
  BY DEFS Inv, uprog_inv1
<1> QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
  
(*THEOREM Spec => []property
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
<1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec*)


(*THEOREM memtest
          = [Mem_legacy |-> 0, Mem_global |-> 0,
             Mem_uobjcollection |-> [co \in 1..MAXUOBJCOLLECTIONS |->
                                       [memuobj |-> [ob
                                                     \in 1..MAXUOBJSWITHINCOLLECTION |->
                                                       [Mem |-> 0]]]]]
       => 
       memtest
       \in [Mem_legacy : 0..3, Mem_global : 0..3,
            Mem_uobjcollection : [1..MAXUOBJCOLLECTIONS ->
                                    [memuobj : [1..MAXUOBJSWITHINCOLLECTION ->
                                                  [Mem : 0..3]]]]]
<1> QED OBVIOUS*)
                                                  
THEOREM memory
          = [Mem_legacy |-> 0, Mem_global |-> 0,
             Mem_uobjcollection |-> [co \in 1..MAXUOBJCOLLECTIONS |->
                                       [memuobj |-> [ob
                                                     \in 1..MAXUOBJSWITHINCOLLECTION |->
                                                       [uobj_local_data |-> 0]]]]]
       =>
       memory
       \in [Mem_legacy : 0..3, Mem_global : 0..3,
            Mem_uobjcollection : [1..MAXUOBJCOLLECTIONS ->
                                    [memuobj : [1..MAXUOBJSWITHINCOLLECTION ->
                                                  [uobj_local_data : 0..3]]]]]
<1> QED OBVIOUS


THEOREM Cpu
          = [cp \in 1..MAXCPUS |->
               [Id |-> 1(*, Pc |-> 0, Pr |-> 0, Shared_cpustate |-> 0,
                Legacy_cpustate |-> 0,
                Res_cpustate |-> [m \in 1..MAXUOBJCOLLECTIONS |->
                                    [n \in 1..MAXUOBJSWITHINCOLLECTION |-> 0]]*)]]
                                    =>
        Cpu
       \in [1..MAXCPUS ->
              [Id : 1..MAXCPUS(*, Pc : 0..3, Pr : 0..3, Shared_cpustate : 0..3,
               Legacy_cpustate : 0..3,
               Res_cpustate : [1..MAXUOBJCOLLECTIONS ->
                                 [1..MAXUOBJSWITHINCOLLECTION -> 0..3]]*)]]
<1> QED BY DEF MAXCPUS

THEOREM (\A col \in 1..MAXUOBJCOLLECTIONS :
                 \A obj \in 1..MAXUOBJSWITHINCOLLECTION :
                    ((memory.Mem_uobjcollection)[col].memuobj)[obj].uobj_local_data
                    = 100 * col + obj
                    \/ ((memory.Mem_uobjcollection)[col].memuobj)[obj].uobj_local_data
                       = 0) /\
        \*\E i \in ProcSet : UNCHANGED vars
        (\/ /\ memory' = [memory EXCEPT !.Mem_legacy = LEGACY]
            /\ pc' = [pc EXCEPT ![1] = "Loop_"]
            /\ UNCHANGED <<Cpu, call_stack, stack, p_L, saved_pc_,
                                   p_U, c_, saved_pc_U>>
         \/ UNCHANGED vars)
        =>
        (\A col \in 1..MAXUOBJCOLLECTIONS :
           \A obj \in 1..MAXUOBJSWITHINCOLLECTION :
              ((memory.Mem_uobjcollection)[col].memuobj)[obj].uobj_local_data
              = 100 * col + obj
              \/ ((memory.Mem_uobjcollection)[col].memuobj)[obj].uobj_local_data
                 = 0)'
<1> QED BY DEF vars, ProcSet
(*
THEOREM memtest.a = 1 /\
        ( \/ UNCHANGED memtest)
        =>
        (memtest.a = 1)'
<1> QED OBVIOUS

THEOREM memtest.a = 1 /\
        ( \/ memtest' = [memtest EXCEPT !.b = 2])
        =>
        (memtest.a = 1)'
<1> QED OBVIOUS

THEOREM memtest.a = 1 /\
        ( \/ memtest' = [memtest EXCEPT !.b = 2]
          \/ UNCHANGED memtest)
        =>
        (memtest.a = 1)'
<1>1 CASE memtest' = [memtest EXCEPT !.b = 2]
  BY <1>1
<1>2 CASE UNCHANGED memtest
  BY <1>2
<1> QED BY <1>1, <1>2

THEOREM (\A col \in 1..MAXUOBJCOLLECTIONS :
                 \A obj \in 1..MAXUOBJSWITHINCOLLECTION :
                    ((memory.Mem_uobjcollection)[col].memuobj)[obj].uobj_local_data
                    = 100 * col + obj
                    \/ ((memory.Mem_uobjcollection)[col].memuobj)[obj].uobj_local_data
                       = 0) /\
         (\E i \in ProcSet : memory' = [memory EXCEPT !.Mem_uobjcollection[c[i]].memuobj[o[i]].uobj_local_data = 100*c[i] + o[i]])
        =>
        (\A col \in 1..MAXUOBJCOLLECTIONS :
                 \A obj \in 1..MAXUOBJSWITHINCOLLECTION :
                    ((memory.Mem_uobjcollection)[col].memuobj)[obj].uobj_local_data
                    = 100 * col + obj
                    \/ ((memory.Mem_uobjcollection)[col].memuobj)[obj].uobj_local_data
                       = 0)'
<1> QED BY DEF ProcSet


THEOREM [a |-> 1, b |-> 2] \in [a : {1}, b : {2}(*, c : {3}*)]
<1> QED OBVIOUS \* might have to set the rest to default initial values

THEOREM Cpu \in [1..2 ->
                     [Id : 1..2, Pc : 0..3, Pr : 0..3,
                      Shared_cpustate : 0..3, Legacy_cpustate : 0..3,
                      Res_cpustate : [1..MAXUOBJCOLLECTIONS ->
                                        [1..MAXUOBJSWITHINCOLLECTION -> 0..3]]]] =>
        (\E i \in ProcSet : [Cpu EXCEPT ![i] = [Cpu[i] EXCEPT !.Pc = 1]] \in [1..2 ->
                     [Id : 1..2, Pc : 0..3, Pr : 0..3,
                      Shared_cpustate : 0..3, Legacy_cpustate : 0..3,
                      Res_cpustate : [1..MAXUOBJCOLLECTIONS ->
                                        [1..MAXUOBJSWITHINCOLLECTION -> 0..3]]]])
<1> QED BY DEF ProcSet

THEOREM Cpu \in [1..2 ->
                     [Id : 1..2, Pc : 0..3, Pr : 0..3,
                      Shared_cpustate : 0..3, Legacy_cpustate : 0..3,
                      Res_cpustate : [1..MAXUOBJCOLLECTIONS ->
                                        [1..MAXUOBJSWITHINCOLLECTION -> 0..3]]]] /\
        (\E i \in ProcSet : p[i] \in 1..2) /\
        (\E i \in ProcSet : [Cpu EXCEPT ![(*p[i]*)i] = [Cpu[(*p[i]*)i] EXCEPT !.Pc = 1]] \in [1..2 ->
                     [Id : 1..2, Pc : 0..3, Pr : 0..3,
                      Shared_cpustate : 0..3, Legacy_cpustate : 0..3,
                      Res_cpustate : [1..MAXUOBJCOLLECTIONS ->
                                        [1..MAXUOBJSWITHINCOLLECTION -> 0..3]]]]) /\
        (\E i \in ProcSet : Cpu' = [Cpu EXCEPT ![i(*p[i]*)] = [Cpu[i(*p[i]*)] EXCEPT !.Pc = 1]])
        =>
        (Cpu \in [1..2 ->
                     [Id : 1..2, Pc : 0..3, Pr : 0..3,
                      Shared_cpustate : 0..3, Legacy_cpustate : 0..3,
                      Res_cpustate : [1..MAXUOBJCOLLECTIONS ->
                                        [1..MAXUOBJSWITHINCOLLECTION -> 0..3]]]])' \* switching from p[i] to i for index fixes
<1> QED BY DEF ProcSet*)
=============================================================================
\* Modification History
\* Last modified Wed Jun 02 17:49:23 PDT 2021 by uber
\* Created Tue Apr 20 10:54:04 PDT 2021 by uber
