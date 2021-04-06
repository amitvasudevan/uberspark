------------------------------- MODULE uSpark -------------------------------
EXTENDS TLC, Sequences, Integers
CONSTANTS MAXCPUS, MAXUOBJCOLLECTIONS, MAXUOBJSWITHINCOLLECTION

LEGACY == 1
SENTINEL == 2
UBER == 3

(* --algorithm execution
variables cpu = MAXCPUS, \* for test iterating through CPUs

    (* TODO: Add CPU memory to invariants *)
    Cpu = [cp \in 1..MAXCPUS |->
            [Id |-> cp,                             \* unique CPU identifier
             Pc |-> 0,                              \* program counter (currently abstracted to object control)
             Pc_prev |-> 0,                         (* meta variable for tracking control flow *)
             Pr |-> 0,                              \* privelege level
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
                   [Mem |-> 0,
                    (* Section 1.6: memory safety: invariant 1 *)
                    uobj_local_data |-> 0]
                  ]
                ]
              ]
             ],
             
    \*line = 0;   \* for debugging traces       
    cfi = TRUE, \* for tracking CFI, any time CF is altered, check src/dest
    call_stack = 3;
    
(***************************************************************************)
(* CFI_observer(p) is called any time a Cpu[p].Pc is altered.  After       *)
(* checking that control does not flow directly between an uObject and     *)
(* legacy code, the Cpu[p].Pc_prev is updated.                             *)
(***************************************************************************)
procedure CFI_observer(p) begin
Start:
    if (Cpu[p].Pc_prev = LEGACY /\ Cpu[p].Pc = UBER) \/ (Cpu[p].Pc_prev = UBER /\ Cpu[p].Pc = LEGACY) then
        cfi := FALSE;
    end if;
    Cpu[p].Pc_prev := Cpu[p].Pc;
    return;
end procedure;

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
    call CFI_observer(p);
Loop:
    while TRUE do
        either
            if call_stack > 0 then
                call_stack := call_stack - 1;
                with col \in 1..MAXUOBJCOLLECTIONS do
                    call Entry_sentinel(p, col, LEGACY, FALSE);
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
            call CFI_observer(p);
            return; 
        end either;
    end while;
end procedure;

(***************************************************************************)
(* Entry_sentinel(p, c, saved_pc, func) is an interface for calling        *)
(* uObject code from legacy code.                                          *)
(***************************************************************************)
procedure Entry_sentinel(p, c, saved_pc, func) begin
Start:
    Cpu[p].Pc := SENTINEL;
    call CFI_observer(p);
Privilege_up:
    Cpu[p].Pr := UBER;
    if func then
        \* not reachable right now
        \* call Uobject_code_c_func(x, y, z);
    else
        call Uobjcollection_code(p, c, SENTINEL);
    end if;
End:
    Cpu[p].Pc := saved_pc;
    call CFI_observer(p);
    return;
end procedure;

(***************************************************************************)
(* Exit_sentinel(p, saved_pc, func) controls calls to legacy code from an  *)
(* uObject.                                                                *)
(***************************************************************************)
procedure Exit_sentinel(p, saved_pc, func) begin
Start:
    Cpu[p].Pc := SENTINEL;
    call CFI_observer(p);
Privilege_down:
    Cpu[p].Pr := LEGACY;
    if func then
        call Uobject_code_legacy_func(p, SENTINEL);
    else
        call Legacy_code(p, SENTINEL);
    end if;
End:
    Cpu[p].Pc := saved_pc;
    call CFI_observer(p);
    return;
end procedure;
 
(***************************************************************************)
(* Uobjcollection_code(p, c, saved_pc) calls code for each uObject o in the*)
(* collection c on processor p.                                            *)
(***************************************************************************)
procedure Uobjcollection_code(p, c, saved_pc) begin
Start:
    Cpu[p].Pc := UBER;
    call CFI_observer(p);
Call:
    with object \in 1..MAXUOBJCOLLECTIONS do
        call Uobject_code(p, c, object, saved_pc);
    end with;
Return:
    Cpu[p].Pc := saved_pc;
    call CFI_observer(p);
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
    if ~In_uobj then
        Cpu[p].Pc := UBER;
        call CFI_observer(p);
Loop:
        while ~Uobj_finished do
            either
                if call_stack > 0 then
                    call_stack := call_stack - 1;
                    call Uobject_code_c_func(p, c, o, UBER);
                end if;
            or 
                if call_stack > 0 then
                    call_stack := call_stack - 1;
                    call Uobject_code_casm_func(p, c, o, UBER);
                end if;
            or  
                if call_stack > 0 then
                    call_stack := call_stack - 1;
                    call Exit_sentinel(p, UBER, TRUE);                          \* Call legacy function
                end if;
            or 
                Cpu[p].Res_cpustate[c][o] := 100*c + o;                     \* Access the CPU state reserved to this object
            or 
                memory.Mem_uobjcollection[c].memuobj[o].Mem := 100*c + o;   \* Access this object's allocated memory
            
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
    call CFI_observer(p);
End:
    return;
end procedure;

procedure Uobject_code_c_func(p, c, o, saved_pc)
    variables cfunc_finished = FALSE, in_cfunc = FALSE;
    begin
Start:
    if ~in_cfunc then
        Cpu[p].Pc := UBER;
        call CFI_observer(p);
Loop:
        while ~cfunc_finished do 
            either
                if call_stack > 0 then
                    call_stack := call_stack - 1;
                    call Uobject_code_c_func(p, c, o, UBER);
                end if;
            or 
                if call_stack > 0 then
                    call_stack := call_stack - 1;
                    call Uobject_code_casm_func(p, c, o, UBER);
                end if;
            or  

                if call_stack > 0 then
                    call_stack := call_stack - 1;
                    call Exit_sentinel(p, UBER, TRUE);
                end if;
            or 
                Cpu[p].Res_cpustate[c][o] := 100*c + o;
            or 
                memory.Mem_uobjcollection[c].memuobj[o].Mem := 100*c + o;

            or 
                cfunc_finished := TRUE;
            end either;
        end while;
    end if;
Cfunc_finished_assign:
    cfunc_finished := FALSE; 
    in_cfunc := FALSE; (* Where assigned to? *)
    Cpu[p].Pc := saved_pc;
    call CFI_observer(p);
End:    
    return;
end procedure;

procedure Uobject_code_casm_func(p, c, o, saved_pc)
    variable casmfunc_finished = FALSE, in_casmfunc = FALSE;
    begin
Start: 
    if ~in_casmfunc then
        Cpu[p].Pc := UBER;
        call CFI_observer(p);
Loop:
        while ~casmfunc_finished do
            either
                if call_stack > 0 then
                    call_stack := call_stack - 1;
                    call Uobject_code_c_func(p, c, o, UBER);
                end if;
            or 
                if call_stack > 0 then
                    call_stack := call_stack - 1;
                    call Uobject_code_casm_func(p, c, o, UBER);
                end if;
            or  
                if call_stack > 0 then
                    call_stack := call_stack - 1;
                    call Exit_sentinel(p, UBER, TRUE);
                end if;
            or
                Cpu[p].Res_cpustate[c][o] := 100*c + o;
            or
                memory.Mem_uobjcollection[c].memuobj[o].Mem := 100*c + o;
            or
                casmfunc_finished := TRUE; 
            end either;
        end while;
        casmfunc_finished := FALSE;
        in_casmfunc := FALSE;
        Cpu[p].Pc := saved_pc;
        call CFI_observer(p);
    end if;
End:
    return;
end procedure;

procedure Uobject_code_legacy_func(p, saved_pc) begin
Start:
    Cpu[p].Pc := LEGACY;
    call CFI_observer(p);
End:
    Cpu[p].Pc := saved_pc;
    call CFI_observer(p);
    return;
end procedure;

(* Unused for now *)
procedure device_process(p) begin
Loop:
    while TRUE do
        either
            skip; \*read from memory.memuobjcollection[(1..MAXUOBJCOLLECTIONS)].memuobj[(1..MAXUOBJSWITHINCOLLECTION)].uobj_dmadata[];
        or
            skip; \*write to memory.memuobjcollection[(1..MAXUOBJCOLLECTIONS)].memuobj[(1..MAXUOBJSWITHINCOLLECTION)].uobj_dmadata[];
        or
            return;
        end either;
    end while;
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7c5b65bfe537008e0cf5632193526bb0
\* Label Start of procedure CFI_observer at line 49 col 5 changed to Start_
\* Label Start of procedure Cpu_process at line 62 col 5 changed to Start_C
\* Label Call of procedure Cpu_process at line 65 col 9 changed to Call_
\* Label Start of procedure Legacy_code at line 83 col 5 changed to Start_L
\* Label Loop of procedure Legacy_code at line 86 col 5 changed to Loop_
\* Label Start of procedure Entry_sentinel at line 114 col 5 changed to Start_E
\* Label End of procedure Entry_sentinel at line 125 col 5 changed to End_
\* Label Start of procedure Exit_sentinel at line 136 col 5 changed to Start_Ex
\* Label End of procedure Exit_sentinel at line 146 col 5 changed to End_E
\* Label Start of procedure Uobjcollection_code at line 157 col 5 changed to Start_U
\* Label Start of procedure Uobject_code at line 183 col 5 changed to Start_Uo
\* Label Loop of procedure Uobject_code at line 187 col 9 changed to Loop_U
\* Label End of procedure Uobject_code at line 229 col 5 changed to End_U
\* Label Start of procedure Uobject_code_c_func at line 236 col 5 changed to Start_Uob
\* Label Loop of procedure Uobject_code_c_func at line 240 col 9 changed to Loop_Uo
\* Label End of procedure Uobject_code_c_func at line 273 col 5 changed to End_Uo
\* Label Start of procedure Uobject_code_casm_func at line 280 col 5 changed to Start_Uobj
\* Label Loop of procedure Uobject_code_casm_func at line 284 col 9 changed to Loop_Uob
\* Label End of procedure Uobject_code_casm_func at line 314 col 5 changed to End_Uob
\* Label A of process one at line 345 col 5 changed to A_
\* Parameter p of procedure CFI_observer at line 47 col 24 changed to p_
\* Parameter p of procedure Cpu_process at line 60 col 23 changed to p_C
\* Parameter p of procedure Legacy_code at line 81 col 23 changed to p_L
\* Parameter saved_pc of procedure Legacy_code at line 81 col 26 changed to saved_pc_
\* Parameter p of procedure Entry_sentinel at line 112 col 26 changed to p_E
\* Parameter c of procedure Entry_sentinel at line 112 col 29 changed to c_
\* Parameter saved_pc of procedure Entry_sentinel at line 112 col 32 changed to saved_pc_E
\* Parameter func of procedure Entry_sentinel at line 112 col 42 changed to func_
\* Parameter p of procedure Exit_sentinel at line 134 col 25 changed to p_Ex
\* Parameter saved_pc of procedure Exit_sentinel at line 134 col 28 changed to saved_pc_Ex
\* Parameter p of procedure Uobjcollection_code at line 155 col 31 changed to p_U
\* Parameter c of procedure Uobjcollection_code at line 155 col 34 changed to c_U
\* Parameter saved_pc of procedure Uobjcollection_code at line 155 col 37 changed to saved_pc_U
\* Parameter p of procedure Uobject_code at line 173 col 24 changed to p_Uo
\* Parameter c of procedure Uobject_code at line 173 col 27 changed to c_Uo
\* Parameter o of procedure Uobject_code at line 173 col 30 changed to o_
\* Parameter saved_pc of procedure Uobject_code at line 173 col 33 changed to saved_pc_Uo
\* Parameter p of procedure Uobject_code_c_func at line 232 col 31 changed to p_Uob
\* Parameter c of procedure Uobject_code_c_func at line 232 col 34 changed to c_Uob
\* Parameter o of procedure Uobject_code_c_func at line 232 col 37 changed to o_U
\* Parameter saved_pc of procedure Uobject_code_c_func at line 232 col 40 changed to saved_pc_Uob
\* Parameter p of procedure Uobject_code_casm_func at line 276 col 34 changed to p_Uobj
\* Parameter saved_pc of procedure Uobject_code_casm_func at line 276 col 43 changed to saved_pc_Uobj
\* Parameter p of procedure Uobject_code_legacy_func at line 317 col 36 changed to p_Uobje
CONSTANT defaultInitValue
VARIABLES cpu, Cpu, memory, cfi, call_stack, pc, stack, p_, p_C, p_L, 
          saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
          c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
          Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
          in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, 
          in_casmfunc, p_Uobje, saved_pc, p

vars == << cpu, Cpu, memory, cfi, call_stack, pc, stack, p_, p_C, p_L, 
           saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, func, 
           p_U, c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
           Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
           in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, 
           in_casmfunc, p_Uobje, saved_pc, p >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ cpu = MAXCPUS
        /\ Cpu = [cp \in 1..MAXCPUS |->
                   [Id |-> cp,
                    Pc |-> 0,
                    Pc_prev |-> 0,
                    Pr |-> 0,
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
                          [Mem |-> 0,
                    
                           uobj_local_data |-> 0]
                         ]
                       ]
                     ]
                    ]
        /\ cfi = TRUE
        /\ call_stack = 3
        (* Procedure CFI_observer *)
        /\ p_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Cpu_process *)
        /\ p_C = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Legacy_code *)
        /\ p_L = [ self \in ProcSet |-> defaultInitValue]
        /\ saved_pc_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Entry_sentinel *)
        /\ p_E = [ self \in ProcSet |-> defaultInitValue]
        /\ c_ = [ self \in ProcSet |-> defaultInitValue]
        /\ saved_pc_E = [ self \in ProcSet |-> defaultInitValue]
        /\ func_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Exit_sentinel *)
        /\ p_Ex = [ self \in ProcSet |-> defaultInitValue]
        /\ saved_pc_Ex = [ self \in ProcSet |-> defaultInitValue]
        /\ func = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Uobjcollection_code *)
        /\ p_U = [ self \in ProcSet |-> defaultInitValue]
        /\ c_U = [ self \in ProcSet |-> defaultInitValue]
        /\ saved_pc_U = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Uobject_code *)
        /\ p_Uo = [ self \in ProcSet |-> defaultInitValue]
        /\ c_Uo = [ self \in ProcSet |-> defaultInitValue]
        /\ o_ = [ self \in ProcSet |-> defaultInitValue]
        /\ saved_pc_Uo = [ self \in ProcSet |-> defaultInitValue]
        /\ In_uobj = [ self \in ProcSet |-> FALSE]
        /\ Uobj_finished = [ self \in ProcSet |-> FALSE]
        (* Procedure Uobject_code_c_func *)
        /\ p_Uob = [ self \in ProcSet |-> defaultInitValue]
        /\ c_Uob = [ self \in ProcSet |-> defaultInitValue]
        /\ o_U = [ self \in ProcSet |-> defaultInitValue]
        /\ saved_pc_Uob = [ self \in ProcSet |-> defaultInitValue]
        /\ cfunc_finished = [ self \in ProcSet |-> FALSE]
        /\ in_cfunc = [ self \in ProcSet |-> FALSE]
        (* Procedure Uobject_code_casm_func *)
        /\ p_Uobj = [ self \in ProcSet |-> defaultInitValue]
        /\ c = [ self \in ProcSet |-> defaultInitValue]
        /\ o = [ self \in ProcSet |-> defaultInitValue]
        /\ saved_pc_Uobj = [ self \in ProcSet |-> defaultInitValue]
        /\ casmfunc_finished = [ self \in ProcSet |-> FALSE]
        /\ in_casmfunc = [ self \in ProcSet |-> FALSE]
        (* Procedure Uobject_code_legacy_func *)
        /\ p_Uobje = [ self \in ProcSet |-> defaultInitValue]
        /\ saved_pc = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure device_process *)
        /\ p = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "A_"
                                        [] self = 2 -> "A"]

Start_(self) == /\ pc[self] = "Start_"
                /\ IF (Cpu[p_[self]].Pc_prev = LEGACY /\ Cpu[p_[self]].Pc = UBER) \/ (Cpu[p_[self]].Pc_prev = UBER /\ Cpu[p_[self]].Pc = LEGACY)
                      THEN /\ cfi' = FALSE
                      ELSE /\ TRUE
                           /\ cfi' = cfi
                /\ Cpu' = [Cpu EXCEPT ![p_[self]].Pc_prev = Cpu[p_[self]].Pc]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ p_' = [p_ EXCEPT ![self] = Head(stack[self]).p_]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << cpu, memory, call_stack, p_C, p_L, saved_pc_, 
                                p_E, c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, 
                                func, p_U, c_U, saved_pc_U, p_Uo, c_Uo, o_, 
                                saved_pc_Uo, In_uobj, Uobj_finished, p_Uob, 
                                c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
                                in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                                casmfunc_finished, in_casmfunc, p_Uobje, 
                                saved_pc, p >>

CFI_observer(self) == Start_(self)

Start_C(self) == /\ pc[self] = "Start_C"
                 /\ \/ /\ Cpu' = [Cpu EXCEPT ![p_C[self]].Pr = LEGACY]
                       /\ pc' = [pc EXCEPT ![self] = "Call_"]
                       /\ UNCHANGED <<stack, p_U, c_U, saved_pc_U>>
                    \/ /\ \E col \in 1..MAXUOBJCOLLECTIONS:
                            /\ Cpu' = [Cpu EXCEPT ![p_C[self]].Pr = UBER]
                            /\ /\ c_U' = [c_U EXCEPT ![self] = col]
                               /\ p_U' = [p_U EXCEPT ![self] = p_C[self]]
                               /\ saved_pc_U' = [saved_pc_U EXCEPT ![self] = 0]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobjcollection_code",
                                                                        pc        |->  "After_branching",
                                                                        p_U       |->  p_U[self],
                                                                        c_U       |->  c_U[self],
                                                                        saved_pc_U |->  saved_pc_U[self] ] >>
                                                                    \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "Start_U"]
                 /\ UNCHANGED << cpu, memory, cfi, call_stack, p_, p_C, p_L, 
                                 saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                                 saved_pc_Ex, func, p_Uo, c_Uo, o_, 
                                 saved_pc_Uo, In_uobj, Uobj_finished, p_Uob, 
                                 c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
                                 in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                                 casmfunc_finished, in_casmfunc, p_Uobje, 
                                 saved_pc, p >>

Call_(self) == /\ pc[self] = "Call_"
               /\ /\ p_L' = [p_L EXCEPT ![self] = p_C[self]]
                  /\ saved_pc_' = [saved_pc_ EXCEPT ![self] = 0]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Legacy_code",
                                                           pc        |->  Head(stack[self]).pc,
                                                           p_L       |->  p_L[self],
                                                           saved_pc_ |->  saved_pc_[self] ] >>
                                                       \o Tail(stack[self])]
               /\ pc' = [pc EXCEPT ![self] = "Start_L"]
               /\ UNCHANGED << cpu, Cpu, memory, cfi, call_stack, p_, p_C, p_E, 
                               c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, func, 
                               p_U, c_U, saved_pc_U, p_Uo, c_Uo, o_, 
                               saved_pc_Uo, In_uobj, Uobj_finished, p_Uob, 
                               c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
                               in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                               casmfunc_finished, in_casmfunc, p_Uobje, 
                               saved_pc, p >>

After_branching(self) == /\ pc[self] = "After_branching"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ p_C' = [p_C EXCEPT ![self] = Head(stack[self]).p_C]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << cpu, Cpu, memory, cfi, call_stack, p_, 
                                         p_L, saved_pc_, p_E, c_, saved_pc_E, 
                                         func_, p_Ex, saved_pc_Ex, func, p_U, 
                                         c_U, saved_pc_U, p_Uo, c_Uo, o_, 
                                         saved_pc_Uo, In_uobj, Uobj_finished, 
                                         p_Uob, c_Uob, o_U, saved_pc_Uob, 
                                         cfunc_finished, in_cfunc, p_Uobj, c, 
                                         o, saved_pc_Uobj, casmfunc_finished, 
                                         in_casmfunc, p_Uobje, saved_pc, p >>

Cpu_process(self) == Start_C(self) \/ Call_(self) \/ After_branching(self)

Start_L(self) == /\ pc[self] = "Start_L"
                 /\ Cpu' = [Cpu EXCEPT ![p_L[self]].Pc = LEGACY]
                 /\ /\ p_' = [p_ EXCEPT ![self] = p_L[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                             pc        |->  "Loop_",
                                                             p_        |->  p_[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Start_"]
                 /\ UNCHANGED << cpu, memory, cfi, call_stack, p_C, p_L, 
                                 saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                                 saved_pc_Ex, func, p_U, c_U, saved_pc_U, p_Uo, 
                                 c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, 
                                 p_Uob, c_Uob, o_U, saved_pc_Uob, 
                                 cfunc_finished, in_cfunc, p_Uobj, c, o, 
                                 saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                                 p_Uobje, saved_pc, p >>

Loop_(self) == /\ pc[self] = "Loop_"
               /\ \/ /\ IF call_stack > 0
                           THEN /\ call_stack' = call_stack - 1
                                /\ \E col \in 1..MAXUOBJCOLLECTIONS:
                                     /\ /\ c_' = [c_ EXCEPT ![self] = col]
                                        /\ func_' = [func_ EXCEPT ![self] = FALSE]
                                        /\ p_E' = [p_E EXCEPT ![self] = p_L[self]]
                                        /\ saved_pc_E' = [saved_pc_E EXCEPT ![self] = LEGACY]
                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Entry_sentinel",
                                                                                 pc        |->  "Loop_",
                                                                                 p_E       |->  p_E[self],
                                                                                 c_        |->  c_[self],
                                                                                 saved_pc_E |->  saved_pc_E[self],
                                                                                 func_     |->  func_[self] ] >>
                                                                             \o stack[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "Start_E"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Loop_"]
                                /\ UNCHANGED << call_stack, stack, p_E, c_, 
                                                saved_pc_E, func_ >>
                     /\ UNCHANGED <<Cpu, memory, p_>>
                  \/ /\ memory' = [memory EXCEPT !.Mem_legacy = LEGACY]
                     /\ pc' = [pc EXCEPT ![self] = "Loop_"]
                     /\ UNCHANGED <<Cpu, call_stack, stack, p_, p_E, c_, saved_pc_E, func_>>
                  \/ /\ Cpu' = [Cpu EXCEPT ![p_L[self]].Shared_cpustate = LEGACY]
                     /\ pc' = [pc EXCEPT ![self] = "Loop_"]
                     /\ UNCHANGED <<memory, call_stack, stack, p_, p_E, c_, saved_pc_E, func_>>
                  \/ /\ Cpu' = [Cpu EXCEPT ![p_L[self]].Legacy_cpustate = LEGACY]
                     /\ pc' = [pc EXCEPT ![self] = "Loop_"]
                     /\ UNCHANGED <<memory, call_stack, stack, p_, p_E, c_, saved_pc_E, func_>>
                  \/ /\ Cpu' = [Cpu EXCEPT ![p_L[self]].Pc = saved_pc_[self]]
                     /\ /\ p_' = [p_ EXCEPT ![self] = p_L[self]]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                                 pc        |->  Head(stack[self]).pc,
                                                                 p_        |->  p_[self] ] >>
                                                             \o Tail(stack[self])]
                     /\ pc' = [pc EXCEPT ![self] = "Start_"]
                     /\ UNCHANGED <<memory, call_stack, p_E, c_, saved_pc_E, func_>>
               /\ UNCHANGED << cpu, cfi, p_C, p_L, saved_pc_, p_Ex, 
                               saved_pc_Ex, func, p_U, c_U, saved_pc_U, p_Uo, 
                               c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, 
                               p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
                               in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                               casmfunc_finished, in_casmfunc, p_Uobje, 
                               saved_pc, p >>

Legacy_code(self) == Start_L(self) \/ Loop_(self)

Start_E(self) == /\ pc[self] = "Start_E"
                 /\ Cpu' = [Cpu EXCEPT ![p_E[self]].Pc = SENTINEL]
                 /\ /\ p_' = [p_ EXCEPT ![self] = p_E[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                             pc        |->  "Privilege_up",
                                                             p_        |->  p_[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Start_"]
                 /\ UNCHANGED << cpu, memory, cfi, call_stack, p_C, p_L, 
                                 saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                                 saved_pc_Ex, func, p_U, c_U, saved_pc_U, p_Uo, 
                                 c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, 
                                 p_Uob, c_Uob, o_U, saved_pc_Uob, 
                                 cfunc_finished, in_cfunc, p_Uobj, c, o, 
                                 saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                                 p_Uobje, saved_pc, p >>

Privilege_up(self) == /\ pc[self] = "Privilege_up"
                      /\ Cpu' = [Cpu EXCEPT ![p_E[self]].Pr = UBER]
                      /\ IF func_[self]
                            THEN /\ pc' = [pc EXCEPT ![self] = "End_"]
                                 /\ UNCHANGED << stack, p_U, c_U, saved_pc_U >>
                            ELSE /\ /\ c_U' = [c_U EXCEPT ![self] = c_[self]]
                                    /\ p_U' = [p_U EXCEPT ![self] = p_E[self]]
                                    /\ saved_pc_U' = [saved_pc_U EXCEPT ![self] = SENTINEL]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobjcollection_code",
                                                                             pc        |->  "End_",
                                                                             p_U       |->  p_U[self],
                                                                             c_U       |->  c_U[self],
                                                                             saved_pc_U |->  saved_pc_U[self] ] >>
                                                                         \o stack[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "Start_U"]
                      /\ UNCHANGED << cpu, memory, cfi, call_stack, p_, p_C, 
                                      p_L, saved_pc_, p_E, c_, saved_pc_E, 
                                      func_, p_Ex, saved_pc_Ex, func, p_Uo, 
                                      c_Uo, o_, saved_pc_Uo, In_uobj, 
                                      Uobj_finished, p_Uob, c_Uob, o_U, 
                                      saved_pc_Uob, cfunc_finished, in_cfunc, 
                                      p_Uobj, c, o, saved_pc_Uobj, 
                                      casmfunc_finished, in_casmfunc, p_Uobje, 
                                      saved_pc, p >>

End_(self) == /\ pc[self] = "End_"
              /\ Cpu' = [Cpu EXCEPT ![p_E[self]].Pc = saved_pc_E[self]]
              /\ /\ p_' = [p_ EXCEPT ![self] = p_E[self]]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                          pc        |->  Head(stack[self]).pc,
                                                          p_        |->  p_[self] ] >>
                                                      \o Tail(stack[self])]
              /\ pc' = [pc EXCEPT ![self] = "Start_"]
              /\ UNCHANGED << cpu, memory, cfi, call_stack, p_C, p_L, 
                              saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                              saved_pc_Ex, func, p_U, c_U, saved_pc_U, p_Uo, 
                              c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, 
                              p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
                              in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                              casmfunc_finished, in_casmfunc, p_Uobje, 
                              saved_pc, p >>

Entry_sentinel(self) == Start_E(self) \/ Privilege_up(self) \/ End_(self)

Start_Ex(self) == /\ pc[self] = "Start_Ex"
                  /\ Cpu' = [Cpu EXCEPT ![p_Ex[self]].Pc = SENTINEL]
                  /\ /\ p_' = [p_ EXCEPT ![self] = p_Ex[self]]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                              pc        |->  "Privilege_down",
                                                              p_        |->  p_[self] ] >>
                                                          \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "Start_"]
                  /\ UNCHANGED << cpu, memory, cfi, call_stack, p_C, p_L, 
                                  saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                                  saved_pc_Ex, func, p_U, c_U, saved_pc_U, 
                                  p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                                  Uobj_finished, p_Uob, c_Uob, o_U, 
                                  saved_pc_Uob, cfunc_finished, in_cfunc, 
                                  p_Uobj, c, o, saved_pc_Uobj, 
                                  casmfunc_finished, in_casmfunc, p_Uobje, 
                                  saved_pc, p >>

Privilege_down(self) == /\ pc[self] = "Privilege_down"
                        /\ Cpu' = [Cpu EXCEPT ![p_Ex[self]].Pr = LEGACY]
                        /\ IF func[self]
                              THEN /\ /\ p_Uobje' = [p_Uobje EXCEPT ![self] = p_Ex[self]]
                                      /\ saved_pc' = [saved_pc EXCEPT ![self] = SENTINEL]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobject_code_legacy_func",
                                                                               pc        |->  "End_E",
                                                                               p_Uobje   |->  p_Uobje[self],
                                                                               saved_pc  |->  saved_pc[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "Start"]
                                   /\ UNCHANGED << p_L, saved_pc_ >>
                              ELSE /\ /\ p_L' = [p_L EXCEPT ![self] = p_Ex[self]]
                                      /\ saved_pc_' = [saved_pc_ EXCEPT ![self] = SENTINEL]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Legacy_code",
                                                                               pc        |->  "End_E",
                                                                               p_L       |->  p_L[self],
                                                                               saved_pc_ |->  saved_pc_[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "Start_L"]
                                   /\ UNCHANGED << p_Uobje, saved_pc >>
                        /\ UNCHANGED << cpu, memory, cfi, call_stack, p_, p_C, 
                                        p_E, c_, saved_pc_E, func_, p_Ex, 
                                        saved_pc_Ex, func, p_U, c_U, 
                                        saved_pc_U, p_Uo, c_Uo, o_, 
                                        saved_pc_Uo, In_uobj, Uobj_finished, 
                                        p_Uob, c_Uob, o_U, saved_pc_Uob, 
                                        cfunc_finished, in_cfunc, p_Uobj, c, o, 
                                        saved_pc_Uobj, casmfunc_finished, 
                                        in_casmfunc, p >>

End_E(self) == /\ pc[self] = "End_E"
               /\ Cpu' = [Cpu EXCEPT ![p_Ex[self]].Pc = saved_pc_Ex[self]]
               /\ /\ p_' = [p_ EXCEPT ![self] = p_Ex[self]]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                           pc        |->  Head(stack[self]).pc,
                                                           p_        |->  p_[self] ] >>
                                                       \o Tail(stack[self])]
               /\ pc' = [pc EXCEPT ![self] = "Start_"]
               /\ UNCHANGED << cpu, memory, cfi, call_stack, p_C, p_L, 
                               saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                               saved_pc_Ex, func, p_U, c_U, saved_pc_U, p_Uo, 
                               c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, 
                               p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
                               in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                               casmfunc_finished, in_casmfunc, p_Uobje, 
                               saved_pc, p >>

Exit_sentinel(self) == Start_Ex(self) \/ Privilege_down(self)
                          \/ End_E(self)

Start_U(self) == /\ pc[self] = "Start_U"
                 /\ Cpu' = [Cpu EXCEPT ![p_U[self]].Pc = UBER]
                 /\ /\ p_' = [p_ EXCEPT ![self] = p_U[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                             pc        |->  "Call",
                                                             p_        |->  p_[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Start_"]
                 /\ UNCHANGED << cpu, memory, cfi, call_stack, p_C, p_L, 
                                 saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                                 saved_pc_Ex, func, p_U, c_U, saved_pc_U, p_Uo, 
                                 c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, 
                                 p_Uob, c_Uob, o_U, saved_pc_Uob, 
                                 cfunc_finished, in_cfunc, p_Uobj, c, o, 
                                 saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                                 p_Uobje, saved_pc, p >>

Call(self) == /\ pc[self] = "Call"
              /\ \E object \in 1..MAXUOBJCOLLECTIONS:
                   /\ /\ c_Uo' = [c_Uo EXCEPT ![self] = c_U[self]]
                      /\ o_' = [o_ EXCEPT ![self] = object]
                      /\ p_Uo' = [p_Uo EXCEPT ![self] = p_U[self]]
                      /\ saved_pc_Uo' = [saved_pc_Uo EXCEPT ![self] = saved_pc_U[self]]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobject_code",
                                                               pc        |->  "Return",
                                                               In_uobj   |->  In_uobj[self],
                                                               Uobj_finished |->  Uobj_finished[self],
                                                               p_Uo      |->  p_Uo[self],
                                                               c_Uo      |->  c_Uo[self],
                                                               o_        |->  o_[self],
                                                               saved_pc_Uo |->  saved_pc_Uo[self] ] >>
                                                           \o stack[self]]
                   /\ In_uobj' = [In_uobj EXCEPT ![self] = FALSE]
                   /\ Uobj_finished' = [Uobj_finished EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "Start_Uo"]
              /\ UNCHANGED << cpu, Cpu, memory, cfi, call_stack, p_, p_C, p_L, 
                              saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                              saved_pc_Ex, func, p_U, c_U, saved_pc_U, p_Uob, 
                              c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
                              in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                              casmfunc_finished, in_casmfunc, p_Uobje, 
                              saved_pc, p >>

Return(self) == /\ pc[self] = "Return"
                /\ Cpu' = [Cpu EXCEPT ![p_U[self]].Pc = saved_pc_U[self]]
                /\ /\ p_' = [p_ EXCEPT ![self] = p_U[self]]
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                            pc        |->  Head(stack[self]).pc,
                                                            p_        |->  p_[self] ] >>
                                                        \o Tail(stack[self])]
                /\ pc' = [pc EXCEPT ![self] = "Start_"]
                /\ UNCHANGED << cpu, memory, cfi, call_stack, p_C, p_L, 
                                saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                                saved_pc_Ex, func, p_U, c_U, saved_pc_U, p_Uo, 
                                c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, 
                                p_Uob, c_Uob, o_U, saved_pc_Uob, 
                                cfunc_finished, in_cfunc, p_Uobj, c, o, 
                                saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                                p_Uobje, saved_pc, p >>

Uobjcollection_code(self) == Start_U(self) \/ Call(self) \/ Return(self)

Start_Uo(self) == /\ pc[self] = "Start_Uo"
                  /\ IF ~In_uobj[self]
                        THEN /\ Cpu' = [Cpu EXCEPT ![p_Uo[self]].Pc = UBER]
                             /\ /\ p_' = [p_ EXCEPT ![self] = p_Uo[self]]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                                         pc        |->  "Loop_U",
                                                                         p_        |->  p_[self] ] >>
                                                                     \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "Start_"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Uobj_finished_assign"]
                             /\ UNCHANGED << Cpu, stack, p_ >>
                  /\ UNCHANGED << cpu, memory, cfi, call_stack, p_C, p_L, 
                                  saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                                  saved_pc_Ex, func, p_U, c_U, saved_pc_U, 
                                  p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                                  Uobj_finished, p_Uob, c_Uob, o_U, 
                                  saved_pc_Uob, cfunc_finished, in_cfunc, 
                                  p_Uobj, c, o, saved_pc_Uobj, 
                                  casmfunc_finished, in_casmfunc, p_Uobje, 
                                  saved_pc, p >>

Loop_U(self) == /\ pc[self] = "Loop_U"
                /\ IF ~Uobj_finished[self]
                      THEN /\ \/ /\ IF call_stack > 0
                                       THEN /\ call_stack' = call_stack - 1
                                            /\ /\ c_Uob' = [c_Uob EXCEPT ![self] = c_Uo[self]]
                                               /\ o_U' = [o_U EXCEPT ![self] = o_[self]]
                                               /\ p_Uob' = [p_Uob EXCEPT ![self] = p_Uo[self]]
                                               /\ saved_pc_Uob' = [saved_pc_Uob EXCEPT ![self] = UBER]
                                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobject_code_c_func",
                                                                                        pc        |->  "Loop_U",
                                                                                        cfunc_finished |->  cfunc_finished[self],
                                                                                        in_cfunc  |->  in_cfunc[self],
                                                                                        p_Uob     |->  p_Uob[self],
                                                                                        c_Uob     |->  c_Uob[self],
                                                                                        o_U       |->  o_U[self],
                                                                                        saved_pc_Uob |->  saved_pc_Uob[self] ] >>
                                                                                    \o stack[self]]
                                            /\ cfunc_finished' = [cfunc_finished EXCEPT ![self] = FALSE]
                                            /\ in_cfunc' = [in_cfunc EXCEPT ![self] = FALSE]
                                            /\ pc' = [pc EXCEPT ![self] = "Start_Uob"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "Loop_U"]
                                            /\ UNCHANGED << call_stack, stack, 
                                                            p_Uob, c_Uob, o_U, 
                                                            saved_pc_Uob, 
                                                            cfunc_finished, 
                                                            in_cfunc >>
                                 /\ UNCHANGED <<Cpu, memory, p_Ex, saved_pc_Ex, func, Uobj_finished, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                              \/ /\ IF call_stack > 0
                                       THEN /\ call_stack' = call_stack - 1
                                            /\ /\ c' = [c EXCEPT ![self] = c_Uo[self]]
                                               /\ o' = [o EXCEPT ![self] = o_[self]]
                                               /\ p_Uobj' = [p_Uobj EXCEPT ![self] = p_Uo[self]]
                                               /\ saved_pc_Uobj' = [saved_pc_Uobj EXCEPT ![self] = UBER]
                                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobject_code_casm_func",
                                                                                        pc        |->  "Loop_U",
                                                                                        casmfunc_finished |->  casmfunc_finished[self],
                                                                                        in_casmfunc |->  in_casmfunc[self],
                                                                                        p_Uobj    |->  p_Uobj[self],
                                                                                        c         |->  c[self],
                                                                                        o         |->  o[self],
                                                                                        saved_pc_Uobj |->  saved_pc_Uobj[self] ] >>
                                                                                    \o stack[self]]
                                            /\ casmfunc_finished' = [casmfunc_finished EXCEPT ![self] = FALSE]
                                            /\ in_casmfunc' = [in_casmfunc EXCEPT ![self] = FALSE]
                                            /\ pc' = [pc EXCEPT ![self] = "Start_Uobj"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "Loop_U"]
                                            /\ UNCHANGED << call_stack, stack, 
                                                            p_Uobj, c, o, 
                                                            saved_pc_Uobj, 
                                                            casmfunc_finished, 
                                                            in_casmfunc >>
                                 /\ UNCHANGED <<Cpu, memory, p_Ex, saved_pc_Ex, func, Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc>>
                              \/ /\ IF call_stack > 0
                                       THEN /\ call_stack' = call_stack - 1
                                            /\ /\ func' = [func EXCEPT ![self] = TRUE]
                                               /\ p_Ex' = [p_Ex EXCEPT ![self] = p_Uo[self]]
                                               /\ saved_pc_Ex' = [saved_pc_Ex EXCEPT ![self] = UBER]
                                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Exit_sentinel",
                                                                                        pc        |->  "Loop_U",
                                                                                        p_Ex      |->  p_Ex[self],
                                                                                        saved_pc_Ex |->  saved_pc_Ex[self],
                                                                                        func      |->  func[self] ] >>
                                                                                    \o stack[self]]
                                            /\ pc' = [pc EXCEPT ![self] = "Start_Ex"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "Loop_U"]
                                            /\ UNCHANGED << call_stack, stack, 
                                                            p_Ex, saved_pc_Ex, 
                                                            func >>
                                 /\ UNCHANGED <<Cpu, memory, Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                              \/ /\ Cpu' = [Cpu EXCEPT ![p_Uo[self]].Res_cpustate[c_Uo[self]][o_[self]] = 100*c_Uo[self] + o_[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "Loop_U"]
                                 /\ UNCHANGED <<memory, call_stack, stack, p_Ex, saved_pc_Ex, func, Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                              \/ /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c_Uo[self]].memuobj[o_[self]].Mem = 100*c_Uo[self] + o_[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "Loop_U"]
                                 /\ UNCHANGED <<Cpu, call_stack, stack, p_Ex, saved_pc_Ex, func, Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                              \/ /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c_Uo[self]].memuobj[o_[self]].uobj_local_data = 100*c_Uo[self] + o_[self]]
                                 /\ pc' = [pc EXCEPT ![self] = "Loop_U"]
                                 /\ UNCHANGED <<Cpu, call_stack, stack, p_Ex, saved_pc_Ex, func, Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                              \/ /\ TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "Loop_U"]
                                 /\ UNCHANGED <<Cpu, memory, call_stack, stack, p_Ex, saved_pc_Ex, func, Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                              \/ /\ Uobj_finished' = [Uobj_finished EXCEPT ![self] = TRUE]
                                 /\ pc' = [pc EXCEPT ![self] = "Loop_U"]
                                 /\ UNCHANGED <<Cpu, memory, call_stack, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Uobj_finished_assign"]
                           /\ UNCHANGED << Cpu, memory, call_stack, stack, 
                                           p_Ex, saved_pc_Ex, func, 
                                           Uobj_finished, p_Uob, c_Uob, o_U, 
                                           saved_pc_Uob, cfunc_finished, 
                                           in_cfunc, p_Uobj, c, o, 
                                           saved_pc_Uobj, casmfunc_finished, 
                                           in_casmfunc >>
                /\ UNCHANGED << cpu, cfi, p_, p_C, p_L, saved_pc_, p_E, c_, 
                                saved_pc_E, func_, p_U, c_U, saved_pc_U, p_Uo, 
                                c_Uo, o_, saved_pc_Uo, In_uobj, p_Uobje, 
                                saved_pc, p >>

Uobj_finished_assign(self) == /\ pc[self] = "Uobj_finished_assign"
                              /\ Uobj_finished' = [Uobj_finished EXCEPT ![self] = FALSE]
                              /\ In_uobj' = [In_uobj EXCEPT ![self] = FALSE]
                              /\ Cpu' = [Cpu EXCEPT ![p_Uo[self]].Pc = saved_pc_Uo[self]]
                              /\ /\ p_' = [p_ EXCEPT ![self] = p_Uo[self]]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                                          pc        |->  "End_U",
                                                                          p_        |->  p_[self] ] >>
                                                                      \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "Start_"]
                              /\ UNCHANGED << cpu, memory, cfi, call_stack, 
                                              p_C, p_L, saved_pc_, p_E, c_, 
                                              saved_pc_E, func_, p_Ex, 
                                              saved_pc_Ex, func, p_U, c_U, 
                                              saved_pc_U, p_Uo, c_Uo, o_, 
                                              saved_pc_Uo, p_Uob, c_Uob, o_U, 
                                              saved_pc_Uob, cfunc_finished, 
                                              in_cfunc, p_Uobj, c, o, 
                                              saved_pc_Uobj, casmfunc_finished, 
                                              in_casmfunc, p_Uobje, saved_pc, 
                                              p >>

End_U(self) == /\ pc[self] = "End_U"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ In_uobj' = [In_uobj EXCEPT ![self] = Head(stack[self]).In_uobj]
               /\ Uobj_finished' = [Uobj_finished EXCEPT ![self] = Head(stack[self]).Uobj_finished]
               /\ p_Uo' = [p_Uo EXCEPT ![self] = Head(stack[self]).p_Uo]
               /\ c_Uo' = [c_Uo EXCEPT ![self] = Head(stack[self]).c_Uo]
               /\ o_' = [o_ EXCEPT ![self] = Head(stack[self]).o_]
               /\ saved_pc_Uo' = [saved_pc_Uo EXCEPT ![self] = Head(stack[self]).saved_pc_Uo]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << cpu, Cpu, memory, cfi, call_stack, p_, p_C, p_L, 
                               saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                               saved_pc_Ex, func, p_U, c_U, saved_pc_U, p_Uob, 
                               c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
                               in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                               casmfunc_finished, in_casmfunc, p_Uobje, 
                               saved_pc, p >>

Uobject_code(self) == Start_Uo(self) \/ Loop_U(self)
                         \/ Uobj_finished_assign(self) \/ End_U(self)

Start_Uob(self) == /\ pc[self] = "Start_Uob"
                   /\ IF ~in_cfunc[self]
                         THEN /\ Cpu' = [Cpu EXCEPT ![p_Uob[self]].Pc = UBER]
                              /\ /\ p_' = [p_ EXCEPT ![self] = p_Uob[self]]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                                          pc        |->  "Loop_Uo",
                                                                          p_        |->  p_[self] ] >>
                                                                      \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "Start_"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "Cfunc_finished_assign"]
                              /\ UNCHANGED << Cpu, stack, p_ >>
                   /\ UNCHANGED << cpu, memory, cfi, call_stack, p_C, p_L, 
                                   saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                                   saved_pc_Ex, func, p_U, c_U, saved_pc_U, 
                                   p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                                   Uobj_finished, p_Uob, c_Uob, o_U, 
                                   saved_pc_Uob, cfunc_finished, in_cfunc, 
                                   p_Uobj, c, o, saved_pc_Uobj, 
                                   casmfunc_finished, in_casmfunc, p_Uobje, 
                                   saved_pc, p >>

Loop_Uo(self) == /\ pc[self] = "Loop_Uo"
                 /\ IF ~cfunc_finished[self]
                       THEN /\ \/ /\ IF call_stack > 0
                                        THEN /\ call_stack' = call_stack - 1
                                             /\ /\ c_Uob' = [c_Uob EXCEPT ![self] = c_Uob[self]]
                                                /\ o_U' = [o_U EXCEPT ![self] = o_U[self]]
                                                /\ p_Uob' = [p_Uob EXCEPT ![self] = p_Uob[self]]
                                                /\ saved_pc_Uob' = [saved_pc_Uob EXCEPT ![self] = UBER]
                                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobject_code_c_func",
                                                                                         pc        |->  "Loop_Uo",
                                                                                         cfunc_finished |->  cfunc_finished[self],
                                                                                         in_cfunc  |->  in_cfunc[self],
                                                                                         p_Uob     |->  p_Uob[self],
                                                                                         c_Uob     |->  c_Uob[self],
                                                                                         o_U       |->  o_U[self],
                                                                                         saved_pc_Uob |->  saved_pc_Uob[self] ] >>
                                                                                     \o stack[self]]
                                             /\ cfunc_finished' = [cfunc_finished EXCEPT ![self] = FALSE]
                                             /\ in_cfunc' = [in_cfunc EXCEPT ![self] = FALSE]
                                             /\ pc' = [pc EXCEPT ![self] = "Start_Uob"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "Loop_Uo"]
                                             /\ UNCHANGED << call_stack, stack, 
                                                             p_Uob, c_Uob, o_U, 
                                                             saved_pc_Uob, 
                                                             cfunc_finished, 
                                                             in_cfunc >>
                                  /\ UNCHANGED <<Cpu, memory, p_Ex, saved_pc_Ex, func, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                               \/ /\ IF call_stack > 0
                                        THEN /\ call_stack' = call_stack - 1
                                             /\ /\ c' = [c EXCEPT ![self] = c_Uob[self]]
                                                /\ o' = [o EXCEPT ![self] = o_U[self]]
                                                /\ p_Uobj' = [p_Uobj EXCEPT ![self] = p_Uob[self]]
                                                /\ saved_pc_Uobj' = [saved_pc_Uobj EXCEPT ![self] = UBER]
                                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobject_code_casm_func",
                                                                                         pc        |->  "Loop_Uo",
                                                                                         casmfunc_finished |->  casmfunc_finished[self],
                                                                                         in_casmfunc |->  in_casmfunc[self],
                                                                                         p_Uobj    |->  p_Uobj[self],
                                                                                         c         |->  c[self],
                                                                                         o         |->  o[self],
                                                                                         saved_pc_Uobj |->  saved_pc_Uobj[self] ] >>
                                                                                     \o stack[self]]
                                             /\ casmfunc_finished' = [casmfunc_finished EXCEPT ![self] = FALSE]
                                             /\ in_casmfunc' = [in_casmfunc EXCEPT ![self] = FALSE]
                                             /\ pc' = [pc EXCEPT ![self] = "Start_Uobj"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "Loop_Uo"]
                                             /\ UNCHANGED << call_stack, stack, 
                                                             p_Uobj, c, o, 
                                                             saved_pc_Uobj, 
                                                             casmfunc_finished, 
                                                             in_casmfunc >>
                                  /\ UNCHANGED <<Cpu, memory, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc>>
                               \/ /\ IF call_stack > 0
                                        THEN /\ call_stack' = call_stack - 1
                                             /\ /\ func' = [func EXCEPT ![self] = TRUE]
                                                /\ p_Ex' = [p_Ex EXCEPT ![self] = p_Uob[self]]
                                                /\ saved_pc_Ex' = [saved_pc_Ex EXCEPT ![self] = UBER]
                                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Exit_sentinel",
                                                                                         pc        |->  "Loop_Uo",
                                                                                         p_Ex      |->  p_Ex[self],
                                                                                         saved_pc_Ex |->  saved_pc_Ex[self],
                                                                                         func      |->  func[self] ] >>
                                                                                     \o stack[self]]
                                             /\ pc' = [pc EXCEPT ![self] = "Start_Ex"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "Loop_Uo"]
                                             /\ UNCHANGED << call_stack, stack, 
                                                             p_Ex, saved_pc_Ex, 
                                                             func >>
                                  /\ UNCHANGED <<Cpu, memory, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                               \/ /\ Cpu' = [Cpu EXCEPT ![p_Uob[self]].Res_cpustate[c_Uob[self]][o_U[self]] = 100*c_Uob[self] + o_U[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "Loop_Uo"]
                                  /\ UNCHANGED <<memory, call_stack, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                               \/ /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c_Uob[self]].memuobj[o_U[self]].Mem = 100*c_Uob[self] + o_U[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "Loop_Uo"]
                                  /\ UNCHANGED <<Cpu, call_stack, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                               \/ /\ cfunc_finished' = [cfunc_finished EXCEPT ![self] = TRUE]
                                  /\ pc' = [pc EXCEPT ![self] = "Loop_Uo"]
                                  /\ UNCHANGED <<Cpu, memory, call_stack, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Cfunc_finished_assign"]
                            /\ UNCHANGED << Cpu, memory, call_stack, stack, 
                                            p_Ex, saved_pc_Ex, func, p_Uob, 
                                            c_Uob, o_U, saved_pc_Uob, 
                                            cfunc_finished, in_cfunc, p_Uobj, 
                                            c, o, saved_pc_Uobj, 
                                            casmfunc_finished, in_casmfunc >>
                 /\ UNCHANGED << cpu, cfi, p_, p_C, p_L, saved_pc_, p_E, c_, 
                                 saved_pc_E, func_, p_U, c_U, saved_pc_U, p_Uo, 
                                 c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, 
                                 p_Uobje, saved_pc, p >>

Cfunc_finished_assign(self) == /\ pc[self] = "Cfunc_finished_assign"
                               /\ cfunc_finished' = [cfunc_finished EXCEPT ![self] = FALSE]
                               /\ in_cfunc' = [in_cfunc EXCEPT ![self] = FALSE]
                               /\ Cpu' = [Cpu EXCEPT ![p_Uob[self]].Pc = saved_pc_Uob[self]]
                               /\ /\ p_' = [p_ EXCEPT ![self] = p_Uob[self]]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                                           pc        |->  "End_Uo",
                                                                           p_        |->  p_[self] ] >>
                                                                       \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "Start_"]
                               /\ UNCHANGED << cpu, memory, cfi, call_stack, 
                                               p_C, p_L, saved_pc_, p_E, c_, 
                                               saved_pc_E, func_, p_Ex, 
                                               saved_pc_Ex, func, p_U, c_U, 
                                               saved_pc_U, p_Uo, c_Uo, o_, 
                                               saved_pc_Uo, In_uobj, 
                                               Uobj_finished, p_Uob, c_Uob, 
                                               o_U, saved_pc_Uob, p_Uobj, c, o, 
                                               saved_pc_Uobj, 
                                               casmfunc_finished, in_casmfunc, 
                                               p_Uobje, saved_pc, p >>

End_Uo(self) == /\ pc[self] = "End_Uo"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ cfunc_finished' = [cfunc_finished EXCEPT ![self] = Head(stack[self]).cfunc_finished]
                /\ in_cfunc' = [in_cfunc EXCEPT ![self] = Head(stack[self]).in_cfunc]
                /\ p_Uob' = [p_Uob EXCEPT ![self] = Head(stack[self]).p_Uob]
                /\ c_Uob' = [c_Uob EXCEPT ![self] = Head(stack[self]).c_Uob]
                /\ o_U' = [o_U EXCEPT ![self] = Head(stack[self]).o_U]
                /\ saved_pc_Uob' = [saved_pc_Uob EXCEPT ![self] = Head(stack[self]).saved_pc_Uob]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << cpu, Cpu, memory, cfi, call_stack, p_, p_C, 
                                p_L, saved_pc_, p_E, c_, saved_pc_E, func_, 
                                p_Ex, saved_pc_Ex, func, p_U, c_U, saved_pc_U, 
                                p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                                Uobj_finished, p_Uobj, c, o, saved_pc_Uobj, 
                                casmfunc_finished, in_casmfunc, p_Uobje, 
                                saved_pc, p >>

Uobject_code_c_func(self) == Start_Uob(self) \/ Loop_Uo(self)
                                \/ Cfunc_finished_assign(self)
                                \/ End_Uo(self)

Start_Uobj(self) == /\ pc[self] = "Start_Uobj"
                    /\ IF ~in_casmfunc[self]
                          THEN /\ Cpu' = [Cpu EXCEPT ![p_Uobj[self]].Pc = UBER]
                               /\ /\ p_' = [p_ EXCEPT ![self] = p_Uobj[self]]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                                           pc        |->  "Loop_Uob",
                                                                           p_        |->  p_[self] ] >>
                                                                       \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "Start_"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "End_Uob"]
                               /\ UNCHANGED << Cpu, stack, p_ >>
                    /\ UNCHANGED << cpu, memory, cfi, call_stack, p_C, p_L, 
                                    saved_pc_, p_E, c_, saved_pc_E, func_, 
                                    p_Ex, saved_pc_Ex, func, p_U, c_U, 
                                    saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, 
                                    In_uobj, Uobj_finished, p_Uob, c_Uob, o_U, 
                                    saved_pc_Uob, cfunc_finished, in_cfunc, 
                                    p_Uobj, c, o, saved_pc_Uobj, 
                                    casmfunc_finished, in_casmfunc, p_Uobje, 
                                    saved_pc, p >>

Loop_Uob(self) == /\ pc[self] = "Loop_Uob"
                  /\ IF ~casmfunc_finished[self]
                        THEN /\ \/ /\ IF call_stack > 0
                                         THEN /\ call_stack' = call_stack - 1
                                              /\ /\ c_Uob' = [c_Uob EXCEPT ![self] = c[self]]
                                                 /\ o_U' = [o_U EXCEPT ![self] = o[self]]
                                                 /\ p_Uob' = [p_Uob EXCEPT ![self] = p_Uobj[self]]
                                                 /\ saved_pc_Uob' = [saved_pc_Uob EXCEPT ![self] = UBER]
                                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobject_code_c_func",
                                                                                          pc        |->  "Loop_Uob",
                                                                                          cfunc_finished |->  cfunc_finished[self],
                                                                                          in_cfunc  |->  in_cfunc[self],
                                                                                          p_Uob     |->  p_Uob[self],
                                                                                          c_Uob     |->  c_Uob[self],
                                                                                          o_U       |->  o_U[self],
                                                                                          saved_pc_Uob |->  saved_pc_Uob[self] ] >>
                                                                                      \o stack[self]]
                                              /\ cfunc_finished' = [cfunc_finished EXCEPT ![self] = FALSE]
                                              /\ in_cfunc' = [in_cfunc EXCEPT ![self] = FALSE]
                                              /\ pc' = [pc EXCEPT ![self] = "Start_Uob"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Loop_Uob"]
                                              /\ UNCHANGED << call_stack, 
                                                              stack, p_Uob, 
                                                              c_Uob, o_U, 
                                                              saved_pc_Uob, 
                                                              cfunc_finished, 
                                                              in_cfunc >>
                                   /\ UNCHANGED <<Cpu, memory, p_Ex, saved_pc_Ex, func, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                                \/ /\ IF call_stack > 0
                                         THEN /\ call_stack' = call_stack - 1
                                              /\ /\ c' = [c EXCEPT ![self] = c[self]]
                                                 /\ o' = [o EXCEPT ![self] = o[self]]
                                                 /\ p_Uobj' = [p_Uobj EXCEPT ![self] = p_Uobj[self]]
                                                 /\ saved_pc_Uobj' = [saved_pc_Uobj EXCEPT ![self] = UBER]
                                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobject_code_casm_func",
                                                                                          pc        |->  "Loop_Uob",
                                                                                          casmfunc_finished |->  casmfunc_finished[self],
                                                                                          in_casmfunc |->  in_casmfunc[self],
                                                                                          p_Uobj    |->  p_Uobj[self],
                                                                                          c         |->  c[self],
                                                                                          o         |->  o[self],
                                                                                          saved_pc_Uobj |->  saved_pc_Uobj[self] ] >>
                                                                                      \o stack[self]]
                                              /\ casmfunc_finished' = [casmfunc_finished EXCEPT ![self] = FALSE]
                                              /\ in_casmfunc' = [in_casmfunc EXCEPT ![self] = FALSE]
                                              /\ pc' = [pc EXCEPT ![self] = "Start_Uobj"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Loop_Uob"]
                                              /\ UNCHANGED << call_stack, 
                                                              stack, p_Uobj, c, 
                                                              o, saved_pc_Uobj, 
                                                              casmfunc_finished, 
                                                              in_casmfunc >>
                                   /\ UNCHANGED <<Cpu, memory, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc>>
                                \/ /\ IF call_stack > 0
                                         THEN /\ call_stack' = call_stack - 1
                                              /\ /\ func' = [func EXCEPT ![self] = TRUE]
                                                 /\ p_Ex' = [p_Ex EXCEPT ![self] = p_Uobj[self]]
                                                 /\ saved_pc_Ex' = [saved_pc_Ex EXCEPT ![self] = UBER]
                                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Exit_sentinel",
                                                                                          pc        |->  "Loop_Uob",
                                                                                          p_Ex      |->  p_Ex[self],
                                                                                          saved_pc_Ex |->  saved_pc_Ex[self],
                                                                                          func      |->  func[self] ] >>
                                                                                      \o stack[self]]
                                              /\ pc' = [pc EXCEPT ![self] = "Start_Ex"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Loop_Uob"]
                                              /\ UNCHANGED << call_stack, 
                                                              stack, p_Ex, 
                                                              saved_pc_Ex, 
                                                              func >>
                                   /\ UNCHANGED <<Cpu, memory, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                                \/ /\ Cpu' = [Cpu EXCEPT ![p_Uobj[self]].Res_cpustate[c[self]][o[self]] = 100*c[self] + o[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "Loop_Uob"]
                                   /\ UNCHANGED <<memory, call_stack, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                                \/ /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c[self]].memuobj[o[self]].Mem = 100*c[self] + o[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "Loop_Uob"]
                                   /\ UNCHANGED <<Cpu, call_stack, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                                \/ /\ casmfunc_finished' = [casmfunc_finished EXCEPT ![self] = TRUE]
                                   /\ pc' = [pc EXCEPT ![self] = "Loop_Uob"]
                                   /\ UNCHANGED <<Cpu, memory, call_stack, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, in_casmfunc>>
                             /\ p_' = p_
                        ELSE /\ casmfunc_finished' = [casmfunc_finished EXCEPT ![self] = FALSE]
                             /\ in_casmfunc' = [in_casmfunc EXCEPT ![self] = FALSE]
                             /\ Cpu' = [Cpu EXCEPT ![p_Uobj[self]].Pc = saved_pc_Uobj[self]]
                             /\ /\ p_' = [p_ EXCEPT ![self] = p_Uobj[self]]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                                         pc        |->  "End_Uob",
                                                                         p_        |->  p_[self] ] >>
                                                                     \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "Start_"]
                             /\ UNCHANGED << memory, call_stack, p_Ex, 
                                             saved_pc_Ex, func, p_Uob, c_Uob, 
                                             o_U, saved_pc_Uob, cfunc_finished, 
                                             in_cfunc, p_Uobj, c, o, 
                                             saved_pc_Uobj >>
                  /\ UNCHANGED << cpu, cfi, p_C, p_L, saved_pc_, p_E, c_, 
                                  saved_pc_E, func_, p_U, c_U, saved_pc_U, 
                                  p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                                  Uobj_finished, p_Uobje, saved_pc, p >>

End_Uob(self) == /\ pc[self] = "End_Uob"
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ casmfunc_finished' = [casmfunc_finished EXCEPT ![self] = Head(stack[self]).casmfunc_finished]
                 /\ in_casmfunc' = [in_casmfunc EXCEPT ![self] = Head(stack[self]).in_casmfunc]
                 /\ p_Uobj' = [p_Uobj EXCEPT ![self] = Head(stack[self]).p_Uobj]
                 /\ c' = [c EXCEPT ![self] = Head(stack[self]).c]
                 /\ o' = [o EXCEPT ![self] = Head(stack[self]).o]
                 /\ saved_pc_Uobj' = [saved_pc_Uobj EXCEPT ![self] = Head(stack[self]).saved_pc_Uobj]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << cpu, Cpu, memory, cfi, call_stack, p_, p_C, 
                                 p_L, saved_pc_, p_E, c_, saved_pc_E, func_, 
                                 p_Ex, saved_pc_Ex, func, p_U, c_U, saved_pc_U, 
                                 p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                                 Uobj_finished, p_Uob, c_Uob, o_U, 
                                 saved_pc_Uob, cfunc_finished, in_cfunc, 
                                 p_Uobje, saved_pc, p >>

Uobject_code_casm_func(self) == Start_Uobj(self) \/ Loop_Uob(self)
                                   \/ End_Uob(self)

Start(self) == /\ pc[self] = "Start"
               /\ Cpu' = [Cpu EXCEPT ![p_Uobje[self]].Pc = LEGACY]
               /\ /\ p_' = [p_ EXCEPT ![self] = p_Uobje[self]]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                           pc        |->  "End",
                                                           p_        |->  p_[self] ] >>
                                                       \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "Start_"]
               /\ UNCHANGED << cpu, memory, cfi, call_stack, p_C, p_L, 
                               saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                               saved_pc_Ex, func, p_U, c_U, saved_pc_U, p_Uo, 
                               c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, 
                               p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
                               in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                               casmfunc_finished, in_casmfunc, p_Uobje, 
                               saved_pc, p >>

End(self) == /\ pc[self] = "End"
             /\ Cpu' = [Cpu EXCEPT ![p_Uobje[self]].Pc = saved_pc[self]]
             /\ /\ p_' = [p_ EXCEPT ![self] = p_Uobje[self]]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CFI_observer",
                                                         pc        |->  Head(stack[self]).pc,
                                                         p_        |->  p_[self] ] >>
                                                     \o Tail(stack[self])]
             /\ pc' = [pc EXCEPT ![self] = "Start_"]
             /\ UNCHANGED << cpu, memory, cfi, call_stack, p_C, p_L, saved_pc_, 
                             p_E, c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, 
                             func, p_U, c_U, saved_pc_U, p_Uo, c_Uo, o_, 
                             saved_pc_Uo, In_uobj, Uobj_finished, p_Uob, c_Uob, 
                             o_U, saved_pc_Uob, cfunc_finished, in_cfunc, 
                             p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, 
                             in_casmfunc, p_Uobje, saved_pc, p >>

Uobject_code_legacy_func(self) == Start(self) \/ End(self)

Loop(self) == /\ pc[self] = "Loop"
              /\ \/ /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "Loop"]
                    /\ UNCHANGED <<stack, p>>
                 \/ /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "Loop"]
                    /\ UNCHANGED <<stack, p>>
                 \/ /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << cpu, Cpu, memory, cfi, call_stack, p_, p_C, p_L, 
                              saved_pc_, p_E, c_, saved_pc_E, func_, p_Ex, 
                              saved_pc_Ex, func, p_U, c_U, saved_pc_U, p_Uo, 
                              c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, 
                              p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
                              in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                              casmfunc_finished, in_casmfunc, p_Uobje, 
                              saved_pc >>

device_process(self) == Loop(self)

A_ == /\ pc[1] = "A_"
      /\ /\ p_C' = [p_C EXCEPT ![1] = 1]
         /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "Cpu_process",
                                               pc        |->  "Done",
                                               p_C       |->  p_C[1] ] >>
                                           \o stack[1]]
      /\ pc' = [pc EXCEPT ![1] = "Start_C"]
      /\ UNCHANGED << cpu, Cpu, memory, cfi, call_stack, p_, p_L, saved_pc_, 
                      p_E, c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                      c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                      Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                      cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                      casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, p >>

one == A_

A == /\ pc[2] = "A"
     /\ /\ p_C' = [p_C EXCEPT ![2] = 2]
        /\ stack' = [stack EXCEPT ![2] = << [ procedure |->  "Cpu_process",
                                              pc        |->  "Done",
                                              p_C       |->  p_C[2] ] >>
                                          \o stack[2]]
     /\ pc' = [pc EXCEPT ![2] = "Start_C"]
     /\ UNCHANGED << cpu, Cpu, memory, cfi, call_stack, p_, p_L, saved_pc_, 
                     p_E, c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                     c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                     Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                     cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                     casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, p >>

two == A

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two
           \/ (\E self \in ProcSet:  \/ CFI_observer(self) \/ Cpu_process(self)
                                     \/ Legacy_code(self) \/ Entry_sentinel(self)
                                     \/ Exit_sentinel(self)
                                     \/ Uobjcollection_code(self)
                                     \/ Uobject_code(self)
                                     \/ Uobject_code_c_func(self)
                                     \/ Uobject_code_casm_func(self)
                                     \/ Uobject_code_legacy_func(self)
                                     \/ device_process(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-63c4cffedd1e5dec5d2801f5f7bebd11

(* Memory allocated to uberOject only self-accessed *)
MI == \A col \in 1..MAXUOBJCOLLECTIONS: \A obj \in 1..MAXUOBJSWITHINCOLLECTION: 
                    memory.Mem_uobjcollection[col].memuobj[obj].Mem = 100*col + obj \/
                    memory.Mem_uobjcollection[col].memuobj[obj].Mem = 0

                    
(* Memory safety follows from MI + all other memory contains no access by uberObjects *)
MS == \A col \in 1..MAXUOBJCOLLECTIONS: \A obj \in 1..MAXUOBJSWITHINCOLLECTION:
                    memory.Mem_legacy /= 100*col + obj /\
                    TRUE
                    
uprog_inv1 == \A col \in 1..MAXUOBJCOLLECTIONS: \A obj \in 1..MAXUOBJSWITHINCOLLECTION:
                    memory.Mem_legacy /= 100*col + obj /\
                    TRUE \* No memory access outside of a uObject's uobj_local_data
CFI == cfi = TRUE

=============================================================================
\* Modification History
\* Last modified Tue Apr 06 08:57:23 PDT 2021 by uber
\* Last modified Mon Feb 08 06:45:36 PST 2021 by mjmccall
\* Created Wed Jan 20 09:49:35 PST 2021 by mjmccall
