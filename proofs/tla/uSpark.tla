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
                   [Mem |-> 0]
                  ]
                ]
              ]
             ],
             
    \*line = 0;   \* for debugging traces       
    cfi = TRUE; \* for tracking CFI, any time CF is altered, check src/dest

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
            with col \in 1..MAXUOBJCOLLECTIONS do
                call Entry_sentinel(p, col, LEGACY, FALSE);
            end with;
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
    begin
Start:
    if ~In_uobj then
        Cpu[p].Pc := UBER;
        call CFI_observer(p);
Loop:
        while ~Uobj_finished do
            either
                call Uobject_code_c_func(p, c, o, UBER);
            or 
                call Uobject_code_casm_func(p, c, o, UBER);
            or  
                call Exit_sentinel(p, UBER, TRUE);                          \* Call legacy function
            or 
                Cpu[p].Res_cpustate[c][o] := 100*c + o;                     \* Access the CPU state reserved to this object
            or 
                memory.Mem_uobjcollection[c].memuobj[o].Mem := 100*c + o;   \* Access this object's allocated memory
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
                call Uobject_code_c_func(p, c, o, UBER);
            or 
                call Uobject_code_casm_func(p, c, o, UBER);
            or  

                call Exit_sentinel(p, UBER, TRUE);
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
                call Uobject_code_c_func(p, c, o, UBER);
            or 
                call Uobject_code_casm_func(p, c, o, UBER);
            or  
                call Exit_sentinel(p, UBER, TRUE);
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

(* Iterate through each CPU process. This will become 
the processes when multithreading is implemented *)
begin
Loop:
while cpu > 0 do
    call Cpu_process(cpu);
Dec:
    cpu := cpu - 1;
end while;

end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7c5b65bfe537008e0cf5632193526bb0
\* Label Start of procedure CFI_observer at line 46 col 5 changed to Start_
\* Label Start of procedure Cpu_process at line 59 col 5 changed to Start_C
\* Label Call of procedure Cpu_process at line 62 col 9 changed to Call_
\* Label Start of procedure Legacy_code at line 80 col 5 changed to Start_L
\* Label Loop of procedure Legacy_code at line 83 col 5 changed to Loop_
\* Label Start of procedure Entry_sentinel at line 108 col 5 changed to Start_E
\* Label End of procedure Entry_sentinel at line 119 col 5 changed to End_
\* Label Start of procedure Exit_sentinel at line 130 col 5 changed to Start_Ex
\* Label End of procedure Exit_sentinel at line 140 col 5 changed to End_E
\* Label Start of procedure Uobjcollection_code at line 151 col 5 changed to Start_U
\* Label Start of procedure Uobject_code at line 172 col 5 changed to Start_Uo
\* Label Loop of procedure Uobject_code at line 176 col 9 changed to Loop_U
\* Label End of procedure Uobject_code at line 198 col 5 changed to End_U
\* Label Start of procedure Uobject_code_c_func at line 205 col 5 changed to Start_Uob
\* Label Loop of procedure Uobject_code_c_func at line 209 col 9 changed to Loop_Uo
\* Label End of procedure Uobject_code_c_func at line 233 col 5 changed to End_Uo
\* Label Start of procedure Uobject_code_casm_func at line 240 col 5 changed to Start_Uobj
\* Label Loop of procedure Uobject_code_casm_func at line 244 col 9 changed to Loop_Uob
\* Label End of procedure Uobject_code_casm_func at line 265 col 5 changed to End_Uob
\* Label Loop of procedure device_process at line 281 col 5 changed to Loop_d
\* Parameter p of procedure CFI_observer at line 44 col 24 changed to p_
\* Parameter p of procedure Cpu_process at line 57 col 23 changed to p_C
\* Parameter p of procedure Legacy_code at line 78 col 23 changed to p_L
\* Parameter saved_pc of procedure Legacy_code at line 78 col 26 changed to saved_pc_
\* Parameter p of procedure Entry_sentinel at line 106 col 26 changed to p_E
\* Parameter c of procedure Entry_sentinel at line 106 col 29 changed to c_
\* Parameter saved_pc of procedure Entry_sentinel at line 106 col 32 changed to saved_pc_E
\* Parameter func of procedure Entry_sentinel at line 106 col 42 changed to func_
\* Parameter p of procedure Exit_sentinel at line 128 col 25 changed to p_Ex
\* Parameter saved_pc of procedure Exit_sentinel at line 128 col 28 changed to saved_pc_Ex
\* Parameter p of procedure Uobjcollection_code at line 149 col 31 changed to p_U
\* Parameter c of procedure Uobjcollection_code at line 149 col 34 changed to c_U
\* Parameter saved_pc of procedure Uobjcollection_code at line 149 col 37 changed to saved_pc_U
\* Parameter p of procedure Uobject_code at line 167 col 24 changed to p_Uo
\* Parameter c of procedure Uobject_code at line 167 col 27 changed to c_Uo
\* Parameter o of procedure Uobject_code at line 167 col 30 changed to o_
\* Parameter saved_pc of procedure Uobject_code at line 167 col 33 changed to saved_pc_Uo
\* Parameter p of procedure Uobject_code_c_func at line 201 col 31 changed to p_Uob
\* Parameter c of procedure Uobject_code_c_func at line 201 col 34 changed to c_Uob
\* Parameter o of procedure Uobject_code_c_func at line 201 col 37 changed to o_U
\* Parameter saved_pc of procedure Uobject_code_c_func at line 201 col 40 changed to saved_pc_Uob
\* Parameter p of procedure Uobject_code_casm_func at line 236 col 34 changed to p_Uobj
\* Parameter saved_pc of procedure Uobject_code_casm_func at line 236 col 43 changed to saved_pc_Uobj
\* Parameter p of procedure Uobject_code_legacy_func at line 268 col 36 changed to p_Uobje
CONSTANT defaultInitValue
VARIABLES cpu, Cpu, memory, cfi, pc, stack, p_, p_C, p_L, saved_pc_, p_E, c_, 
          saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, c_U, saved_pc_U, 
          p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, p_Uob, c_Uob, 
          o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, 
          saved_pc_Uobj, casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, p

vars == << cpu, Cpu, memory, cfi, pc, stack, p_, p_C, p_L, saved_pc_, p_E, c_, 
           saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, c_U, saved_pc_U, 
           p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, p_Uob, c_Uob, 
           o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, 
           saved_pc_Uobj, casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, 
           p >>

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
                          [Mem |-> 0]
                         ]
                       ]
                     ]
                    ]
        /\ cfi = TRUE
        (* Procedure CFI_observer *)
        /\ p_ = defaultInitValue
        (* Procedure Cpu_process *)
        /\ p_C = defaultInitValue
        (* Procedure Legacy_code *)
        /\ p_L = defaultInitValue
        /\ saved_pc_ = defaultInitValue
        (* Procedure Entry_sentinel *)
        /\ p_E = defaultInitValue
        /\ c_ = defaultInitValue
        /\ saved_pc_E = defaultInitValue
        /\ func_ = defaultInitValue
        (* Procedure Exit_sentinel *)
        /\ p_Ex = defaultInitValue
        /\ saved_pc_Ex = defaultInitValue
        /\ func = defaultInitValue
        (* Procedure Uobjcollection_code *)
        /\ p_U = defaultInitValue
        /\ c_U = defaultInitValue
        /\ saved_pc_U = defaultInitValue
        (* Procedure Uobject_code *)
        /\ p_Uo = defaultInitValue
        /\ c_Uo = defaultInitValue
        /\ o_ = defaultInitValue
        /\ saved_pc_Uo = defaultInitValue
        /\ In_uobj = FALSE
        /\ Uobj_finished = FALSE
        (* Procedure Uobject_code_c_func *)
        /\ p_Uob = defaultInitValue
        /\ c_Uob = defaultInitValue
        /\ o_U = defaultInitValue
        /\ saved_pc_Uob = defaultInitValue
        /\ cfunc_finished = FALSE
        /\ in_cfunc = FALSE
        (* Procedure Uobject_code_casm_func *)
        /\ p_Uobj = defaultInitValue
        /\ c = defaultInitValue
        /\ o = defaultInitValue
        /\ saved_pc_Uobj = defaultInitValue
        /\ casmfunc_finished = FALSE
        /\ in_casmfunc = FALSE
        (* Procedure Uobject_code_legacy_func *)
        /\ p_Uobje = defaultInitValue
        /\ saved_pc = defaultInitValue
        (* Procedure device_process *)
        /\ p = defaultInitValue
        /\ stack = << >>
        /\ pc = "Loop"

Start_ == /\ pc = "Start_"
          /\ IF (Cpu[p_].Pc_prev = LEGACY /\ Cpu[p_].Pc = UBER) \/ (Cpu[p_].Pc_prev = UBER /\ Cpu[p_].Pc = LEGACY)
                THEN /\ cfi' = FALSE
                ELSE /\ TRUE
                     /\ cfi' = cfi
          /\ Cpu' = [Cpu EXCEPT ![p_].Pc_prev = Cpu[p_].Pc]
          /\ pc' = Head(stack).pc
          /\ p_' = Head(stack).p_
          /\ stack' = Tail(stack)
          /\ UNCHANGED << cpu, memory, p_C, p_L, saved_pc_, p_E, c_, 
                          saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, c_U, 
                          saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                          Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                          cfunc_finished, in_cfunc, p_Uobj, c, o, 
                          saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                          p_Uobje, saved_pc, p >>

CFI_observer == Start_

Start_C == /\ pc = "Start_C"
           /\ \/ /\ Cpu' = [Cpu EXCEPT ![p_C].Pr = LEGACY]
                 /\ pc' = "Call_"
                 /\ UNCHANGED <<stack, p_U, c_U, saved_pc_U>>
              \/ /\ \E col \in 1..MAXUOBJCOLLECTIONS:
                      /\ Cpu' = [Cpu EXCEPT ![p_C].Pr = UBER]
                      /\ /\ c_U' = col
                         /\ p_U' = p_C
                         /\ saved_pc_U' = 0
                         /\ stack' = << [ procedure |->  "Uobjcollection_code",
                                          pc        |->  "After_branching",
                                          p_U       |->  p_U,
                                          c_U       |->  c_U,
                                          saved_pc_U |->  saved_pc_U ] >>
                                      \o stack
                      /\ pc' = "Start_U"
           /\ UNCHANGED << cpu, memory, cfi, p_, p_C, p_L, saved_pc_, p_E, c_, 
                           saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_Uo, 
                           c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, 
                           p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
                           in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                           casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, 
                           p >>

Call_ == /\ pc = "Call_"
         /\ /\ p_L' = p_C
            /\ saved_pc_' = 0
            /\ stack' = << [ procedure |->  "Legacy_code",
                             pc        |->  Head(stack).pc,
                             p_L       |->  p_L,
                             saved_pc_ |->  saved_pc_ ] >>
                         \o Tail(stack)
         /\ pc' = "Start_L"
         /\ UNCHANGED << cpu, Cpu, memory, cfi, p_, p_C, p_E, c_, saved_pc_E, 
                         func_, p_Ex, saved_pc_Ex, func, p_U, c_U, saved_pc_U, 
                         p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, Uobj_finished, 
                         p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
                         in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                         casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, p >>

After_branching == /\ pc = "After_branching"
                   /\ pc' = Head(stack).pc
                   /\ p_C' = Head(stack).p_C
                   /\ stack' = Tail(stack)
                   /\ UNCHANGED << cpu, Cpu, memory, cfi, p_, p_L, saved_pc_, 
                                   p_E, c_, saved_pc_E, func_, p_Ex, 
                                   saved_pc_Ex, func, p_U, c_U, saved_pc_U, 
                                   p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                                   Uobj_finished, p_Uob, c_Uob, o_U, 
                                   saved_pc_Uob, cfunc_finished, in_cfunc, 
                                   p_Uobj, c, o, saved_pc_Uobj, 
                                   casmfunc_finished, in_casmfunc, p_Uobje, 
                                   saved_pc, p >>

Cpu_process == Start_C \/ Call_ \/ After_branching

Start_L == /\ pc = "Start_L"
           /\ Cpu' = [Cpu EXCEPT ![p_L].Pc = LEGACY]
           /\ /\ p_' = p_L
              /\ stack' = << [ procedure |->  "CFI_observer",
                               pc        |->  "Loop_",
                               p_        |->  p_ ] >>
                           \o stack
           /\ pc' = "Start_"
           /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, p_E, c_, 
                           saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                           c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, 
                           In_uobj, Uobj_finished, p_Uob, c_Uob, o_U, 
                           saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, 
                           o, saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                           p_Uobje, saved_pc, p >>

Loop_ == /\ pc = "Loop_"
         /\ \/ /\ \E col \in 1..MAXUOBJCOLLECTIONS:
                    /\ /\ c_' = col
                       /\ func_' = FALSE
                       /\ p_E' = p_L
                       /\ saved_pc_E' = LEGACY
                       /\ stack' = << [ procedure |->  "Entry_sentinel",
                                        pc        |->  "Loop_",
                                        p_E       |->  p_E,
                                        c_        |->  c_,
                                        saved_pc_E |->  saved_pc_E,
                                        func_     |->  func_ ] >>
                                    \o stack
                    /\ pc' = "Start_E"
               /\ UNCHANGED <<Cpu, memory, p_>>
            \/ /\ memory' = [memory EXCEPT !.Mem_legacy = LEGACY]
               /\ pc' = "Loop_"
               /\ UNCHANGED <<Cpu, stack, p_, p_E, c_, saved_pc_E, func_>>
            \/ /\ Cpu' = [Cpu EXCEPT ![p_L].Shared_cpustate = LEGACY]
               /\ pc' = "Loop_"
               /\ UNCHANGED <<memory, stack, p_, p_E, c_, saved_pc_E, func_>>
            \/ /\ Cpu' = [Cpu EXCEPT ![p_L].Legacy_cpustate = LEGACY]
               /\ pc' = "Loop_"
               /\ UNCHANGED <<memory, stack, p_, p_E, c_, saved_pc_E, func_>>
            \/ /\ Cpu' = [Cpu EXCEPT ![p_L].Pc = saved_pc_]
               /\ /\ p_' = p_L
                  /\ stack' = << [ procedure |->  "CFI_observer",
                                   pc        |->  Head(stack).pc,
                                   p_        |->  p_ ] >>
                               \o Tail(stack)
               /\ pc' = "Start_"
               /\ UNCHANGED <<memory, p_E, c_, saved_pc_E, func_>>
         /\ UNCHANGED << cpu, cfi, p_C, p_L, saved_pc_, p_Ex, saved_pc_Ex, 
                         func, p_U, c_U, saved_pc_U, p_Uo, c_Uo, o_, 
                         saved_pc_Uo, In_uobj, Uobj_finished, p_Uob, c_Uob, 
                         o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, 
                         c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                         p_Uobje, saved_pc, p >>

Legacy_code == Start_L \/ Loop_

Start_E == /\ pc = "Start_E"
           /\ Cpu' = [Cpu EXCEPT ![p_E].Pc = SENTINEL]
           /\ /\ p_' = p_E
              /\ stack' = << [ procedure |->  "CFI_observer",
                               pc        |->  "Privilege_up",
                               p_        |->  p_ ] >>
                           \o stack
           /\ pc' = "Start_"
           /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, p_E, c_, 
                           saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                           c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, 
                           In_uobj, Uobj_finished, p_Uob, c_Uob, o_U, 
                           saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, 
                           o, saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                           p_Uobje, saved_pc, p >>

Privilege_up == /\ pc = "Privilege_up"
                /\ Cpu' = [Cpu EXCEPT ![p_E].Pr = UBER]
                /\ IF func_
                      THEN /\ pc' = "End_"
                           /\ UNCHANGED << stack, p_U, c_U, saved_pc_U >>
                      ELSE /\ /\ c_U' = c_
                              /\ p_U' = p_E
                              /\ saved_pc_U' = SENTINEL
                              /\ stack' = << [ procedure |->  "Uobjcollection_code",
                                               pc        |->  "End_",
                                               p_U       |->  p_U,
                                               c_U       |->  c_U,
                                               saved_pc_U |->  saved_pc_U ] >>
                                           \o stack
                           /\ pc' = "Start_U"
                /\ UNCHANGED << cpu, memory, cfi, p_, p_C, p_L, saved_pc_, p_E, 
                                c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, func, 
                                p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                                Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                                cfunc_finished, in_cfunc, p_Uobj, c, o, 
                                saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                                p_Uobje, saved_pc, p >>

End_ == /\ pc = "End_"
        /\ Cpu' = [Cpu EXCEPT ![p_E].Pc = saved_pc_E]
        /\ /\ p_' = p_E
           /\ stack' = << [ procedure |->  "CFI_observer",
                            pc        |->  Head(stack).pc,
                            p_        |->  p_ ] >>
                        \o Tail(stack)
        /\ pc' = "Start_"
        /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, p_E, c_, 
                        saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, c_U, 
                        saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                        Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                        cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                        casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, p >>

Entry_sentinel == Start_E \/ Privilege_up \/ End_

Start_Ex == /\ pc = "Start_Ex"
            /\ Cpu' = [Cpu EXCEPT ![p_Ex].Pc = SENTINEL]
            /\ /\ p_' = p_Ex
               /\ stack' = << [ procedure |->  "CFI_observer",
                                pc        |->  "Privilege_down",
                                p_        |->  p_ ] >>
                            \o stack
            /\ pc' = "Start_"
            /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, p_E, c_, 
                            saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                            c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, 
                            In_uobj, Uobj_finished, p_Uob, c_Uob, o_U, 
                            saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, 
                            o, saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                            p_Uobje, saved_pc, p >>

Privilege_down == /\ pc = "Privilege_down"
                  /\ Cpu' = [Cpu EXCEPT ![p_Ex].Pr = LEGACY]
                  /\ IF func
                        THEN /\ /\ p_Uobje' = p_Ex
                                /\ saved_pc' = SENTINEL
                                /\ stack' = << [ procedure |->  "Uobject_code_legacy_func",
                                                 pc        |->  "End_E",
                                                 p_Uobje   |->  p_Uobje,
                                                 saved_pc  |->  saved_pc ] >>
                                             \o stack
                             /\ pc' = "Start"
                             /\ UNCHANGED << p_L, saved_pc_ >>
                        ELSE /\ /\ p_L' = p_Ex
                                /\ saved_pc_' = SENTINEL
                                /\ stack' = << [ procedure |->  "Legacy_code",
                                                 pc        |->  "End_E",
                                                 p_L       |->  p_L,
                                                 saved_pc_ |->  saved_pc_ ] >>
                                             \o stack
                             /\ pc' = "Start_L"
                             /\ UNCHANGED << p_Uobje, saved_pc >>
                  /\ UNCHANGED << cpu, memory, cfi, p_, p_C, p_E, c_, 
                                  saved_pc_E, func_, p_Ex, saved_pc_Ex, func, 
                                  p_U, c_U, saved_pc_U, p_Uo, c_Uo, o_, 
                                  saved_pc_Uo, In_uobj, Uobj_finished, p_Uob, 
                                  c_Uob, o_U, saved_pc_Uob, cfunc_finished, 
                                  in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                                  casmfunc_finished, in_casmfunc, p >>

End_E == /\ pc = "End_E"
         /\ Cpu' = [Cpu EXCEPT ![p_Ex].Pc = saved_pc_Ex]
         /\ /\ p_' = p_Ex
            /\ stack' = << [ procedure |->  "CFI_observer",
                             pc        |->  Head(stack).pc,
                             p_        |->  p_ ] >>
                         \o Tail(stack)
         /\ pc' = "Start_"
         /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, p_E, c_, 
                         saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, c_U, 
                         saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                         Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                         cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                         casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, p >>

Exit_sentinel == Start_Ex \/ Privilege_down \/ End_E

Start_U == /\ pc = "Start_U"
           /\ Cpu' = [Cpu EXCEPT ![p_U].Pc = UBER]
           /\ /\ p_' = p_U
              /\ stack' = << [ procedure |->  "CFI_observer",
                               pc        |->  "Call",
                               p_        |->  p_ ] >>
                           \o stack
           /\ pc' = "Start_"
           /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, p_E, c_, 
                           saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                           c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, 
                           In_uobj, Uobj_finished, p_Uob, c_Uob, o_U, 
                           saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, 
                           o, saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                           p_Uobje, saved_pc, p >>

Call == /\ pc = "Call"
        /\ \E object \in 1..MAXUOBJCOLLECTIONS:
             /\ /\ c_Uo' = c_U
                /\ o_' = object
                /\ p_Uo' = p_U
                /\ saved_pc_Uo' = saved_pc_U
                /\ stack' = << [ procedure |->  "Uobject_code",
                                 pc        |->  "Return",
                                 In_uobj   |->  In_uobj,
                                 Uobj_finished |->  Uobj_finished,
                                 p_Uo      |->  p_Uo,
                                 c_Uo      |->  c_Uo,
                                 o_        |->  o_,
                                 saved_pc_Uo |->  saved_pc_Uo ] >>
                             \o stack
             /\ In_uobj' = FALSE
             /\ Uobj_finished' = FALSE
             /\ pc' = "Start_Uo"
        /\ UNCHANGED << cpu, Cpu, memory, cfi, p_, p_C, p_L, saved_pc_, p_E, 
                        c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                        c_U, saved_pc_U, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                        cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                        casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, p >>

Return == /\ pc = "Return"
          /\ Cpu' = [Cpu EXCEPT ![p_U].Pc = saved_pc_U]
          /\ /\ p_' = p_U
             /\ stack' = << [ procedure |->  "CFI_observer",
                              pc        |->  Head(stack).pc,
                              p_        |->  p_ ] >>
                          \o Tail(stack)
          /\ pc' = "Start_"
          /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, p_E, c_, 
                          saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, c_U, 
                          saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                          Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                          cfunc_finished, in_cfunc, p_Uobj, c, o, 
                          saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                          p_Uobje, saved_pc, p >>

Uobjcollection_code == Start_U \/ Call \/ Return

Start_Uo == /\ pc = "Start_Uo"
            /\ IF ~In_uobj
                  THEN /\ Cpu' = [Cpu EXCEPT ![p_Uo].Pc = UBER]
                       /\ /\ p_' = p_Uo
                          /\ stack' = << [ procedure |->  "CFI_observer",
                                           pc        |->  "Loop_U",
                                           p_        |->  p_ ] >>
                                       \o stack
                       /\ pc' = "Start_"
                  ELSE /\ pc' = "Uobj_finished_assign"
                       /\ UNCHANGED << Cpu, stack, p_ >>
            /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, p_E, c_, 
                            saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                            c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, 
                            In_uobj, Uobj_finished, p_Uob, c_Uob, o_U, 
                            saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, 
                            o, saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                            p_Uobje, saved_pc, p >>

Loop_U == /\ pc = "Loop_U"
          /\ IF ~Uobj_finished
                THEN /\ \/ /\ /\ c_Uob' = c_Uo
                              /\ o_U' = o_
                              /\ p_Uob' = p_Uo
                              /\ saved_pc_Uob' = UBER
                              /\ stack' = << [ procedure |->  "Uobject_code_c_func",
                                               pc        |->  "Loop_U",
                                               cfunc_finished |->  cfunc_finished,
                                               in_cfunc  |->  in_cfunc,
                                               p_Uob     |->  p_Uob,
                                               c_Uob     |->  c_Uob,
                                               o_U       |->  o_U,
                                               saved_pc_Uob |->  saved_pc_Uob ] >>
                                           \o stack
                           /\ cfunc_finished' = FALSE
                           /\ in_cfunc' = FALSE
                           /\ pc' = "Start_Uob"
                           /\ UNCHANGED <<Cpu, memory, p_Ex, saved_pc_Ex, func, Uobj_finished, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                        \/ /\ /\ c' = c_Uo
                              /\ o' = o_
                              /\ p_Uobj' = p_Uo
                              /\ saved_pc_Uobj' = UBER
                              /\ stack' = << [ procedure |->  "Uobject_code_casm_func",
                                               pc        |->  "Loop_U",
                                               casmfunc_finished |->  casmfunc_finished,
                                               in_casmfunc |->  in_casmfunc,
                                               p_Uobj    |->  p_Uobj,
                                               c         |->  c,
                                               o         |->  o,
                                               saved_pc_Uobj |->  saved_pc_Uobj ] >>
                                           \o stack
                           /\ casmfunc_finished' = FALSE
                           /\ in_casmfunc' = FALSE
                           /\ pc' = "Start_Uobj"
                           /\ UNCHANGED <<Cpu, memory, p_Ex, saved_pc_Ex, func, Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc>>
                        \/ /\ /\ func' = TRUE
                              /\ p_Ex' = p_Uo
                              /\ saved_pc_Ex' = UBER
                              /\ stack' = << [ procedure |->  "Exit_sentinel",
                                               pc        |->  "Loop_U",
                                               p_Ex      |->  p_Ex,
                                               saved_pc_Ex |->  saved_pc_Ex,
                                               func      |->  func ] >>
                                           \o stack
                           /\ pc' = "Start_Ex"
                           /\ UNCHANGED <<Cpu, memory, Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                        \/ /\ Cpu' = [Cpu EXCEPT ![p_Uo].Res_cpustate[c_Uo][o_] = 100*c_Uo + o_]
                           /\ pc' = "Loop_U"
                           /\ UNCHANGED <<memory, stack, p_Ex, saved_pc_Ex, func, Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                        \/ /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c_Uo].memuobj[o_].Mem = 100*c_Uo + o_]
                           /\ pc' = "Loop_U"
                           /\ UNCHANGED <<Cpu, stack, p_Ex, saved_pc_Ex, func, Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                        \/ /\ Uobj_finished' = TRUE
                           /\ pc' = "Loop_U"
                           /\ UNCHANGED <<Cpu, memory, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                ELSE /\ pc' = "Uobj_finished_assign"
                     /\ UNCHANGED << Cpu, memory, stack, p_Ex, saved_pc_Ex, 
                                     func, Uobj_finished, p_Uob, c_Uob, o_U, 
                                     saved_pc_Uob, cfunc_finished, in_cfunc, 
                                     p_Uobj, c, o, saved_pc_Uobj, 
                                     casmfunc_finished, in_casmfunc >>
          /\ UNCHANGED << cpu, cfi, p_, p_C, p_L, saved_pc_, p_E, c_, 
                          saved_pc_E, func_, p_U, c_U, saved_pc_U, p_Uo, c_Uo, 
                          o_, saved_pc_Uo, In_uobj, p_Uobje, saved_pc, p >>

Uobj_finished_assign == /\ pc = "Uobj_finished_assign"
                        /\ Uobj_finished' = FALSE
                        /\ In_uobj' = FALSE
                        /\ Cpu' = [Cpu EXCEPT ![p_Uo].Pc = saved_pc_Uo]
                        /\ /\ p_' = p_Uo
                           /\ stack' = << [ procedure |->  "CFI_observer",
                                            pc        |->  "End_U",
                                            p_        |->  p_ ] >>
                                        \o stack
                        /\ pc' = "Start_"
                        /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, 
                                        p_E, c_, saved_pc_E, func_, p_Ex, 
                                        saved_pc_Ex, func, p_U, c_U, 
                                        saved_pc_U, p_Uo, c_Uo, o_, 
                                        saved_pc_Uo, p_Uob, c_Uob, o_U, 
                                        saved_pc_Uob, cfunc_finished, in_cfunc, 
                                        p_Uobj, c, o, saved_pc_Uobj, 
                                        casmfunc_finished, in_casmfunc, 
                                        p_Uobje, saved_pc, p >>

End_U == /\ pc = "End_U"
         /\ pc' = Head(stack).pc
         /\ In_uobj' = Head(stack).In_uobj
         /\ Uobj_finished' = Head(stack).Uobj_finished
         /\ p_Uo' = Head(stack).p_Uo
         /\ c_Uo' = Head(stack).c_Uo
         /\ o_' = Head(stack).o_
         /\ saved_pc_Uo' = Head(stack).saved_pc_Uo
         /\ stack' = Tail(stack)
         /\ UNCHANGED << cpu, Cpu, memory, cfi, p_, p_C, p_L, saved_pc_, p_E, 
                         c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                         c_U, saved_pc_U, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                         cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                         casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, p >>

Uobject_code == Start_Uo \/ Loop_U \/ Uobj_finished_assign \/ End_U

Start_Uob == /\ pc = "Start_Uob"
             /\ IF ~in_cfunc
                   THEN /\ Cpu' = [Cpu EXCEPT ![p_Uob].Pc = UBER]
                        /\ /\ p_' = p_Uob
                           /\ stack' = << [ procedure |->  "CFI_observer",
                                            pc        |->  "Loop_Uo",
                                            p_        |->  p_ ] >>
                                        \o stack
                        /\ pc' = "Start_"
                   ELSE /\ pc' = "Cfunc_finished_assign"
                        /\ UNCHANGED << Cpu, stack, p_ >>
             /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, p_E, c_, 
                             saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                             c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, 
                             In_uobj, Uobj_finished, p_Uob, c_Uob, o_U, 
                             saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, 
                             o, saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                             p_Uobje, saved_pc, p >>

Loop_Uo == /\ pc = "Loop_Uo"
           /\ IF ~cfunc_finished
                 THEN /\ \/ /\ /\ c_Uob' = c_Uob
                               /\ o_U' = o_U
                               /\ p_Uob' = p_Uob
                               /\ saved_pc_Uob' = UBER
                               /\ stack' = << [ procedure |->  "Uobject_code_c_func",
                                                pc        |->  "Loop_Uo",
                                                cfunc_finished |->  cfunc_finished,
                                                in_cfunc  |->  in_cfunc,
                                                p_Uob     |->  p_Uob,
                                                c_Uob     |->  c_Uob,
                                                o_U       |->  o_U,
                                                saved_pc_Uob |->  saved_pc_Uob ] >>
                                            \o stack
                            /\ cfunc_finished' = FALSE
                            /\ in_cfunc' = FALSE
                            /\ pc' = "Start_Uob"
                            /\ UNCHANGED <<Cpu, memory, p_Ex, saved_pc_Ex, func, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                         \/ /\ /\ c' = c_Uob
                               /\ o' = o_U
                               /\ p_Uobj' = p_Uob
                               /\ saved_pc_Uobj' = UBER
                               /\ stack' = << [ procedure |->  "Uobject_code_casm_func",
                                                pc        |->  "Loop_Uo",
                                                casmfunc_finished |->  casmfunc_finished,
                                                in_casmfunc |->  in_casmfunc,
                                                p_Uobj    |->  p_Uobj,
                                                c         |->  c,
                                                o         |->  o,
                                                saved_pc_Uobj |->  saved_pc_Uobj ] >>
                                            \o stack
                            /\ casmfunc_finished' = FALSE
                            /\ in_casmfunc' = FALSE
                            /\ pc' = "Start_Uobj"
                            /\ UNCHANGED <<Cpu, memory, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc>>
                         \/ /\ /\ func' = TRUE
                               /\ p_Ex' = p_Uob
                               /\ saved_pc_Ex' = UBER
                               /\ stack' = << [ procedure |->  "Exit_sentinel",
                                                pc        |->  "Loop_Uo",
                                                p_Ex      |->  p_Ex,
                                                saved_pc_Ex |->  saved_pc_Ex,
                                                func      |->  func ] >>
                                            \o stack
                            /\ pc' = "Start_Ex"
                            /\ UNCHANGED <<Cpu, memory, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                         \/ /\ Cpu' = [Cpu EXCEPT ![p_Uob].Res_cpustate[c_Uob][o_U] = 100*c_Uob + o_U]
                            /\ pc' = "Loop_Uo"
                            /\ UNCHANGED <<memory, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                         \/ /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c_Uob].memuobj[o_U].Mem = 100*c_Uob + o_U]
                            /\ pc' = "Loop_Uo"
                            /\ UNCHANGED <<Cpu, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                         \/ /\ cfunc_finished' = TRUE
                            /\ pc' = "Loop_Uo"
                            /\ UNCHANGED <<Cpu, memory, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                 ELSE /\ pc' = "Cfunc_finished_assign"
                      /\ UNCHANGED << Cpu, memory, stack, p_Ex, saved_pc_Ex, 
                                      func, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                                      cfunc_finished, in_cfunc, p_Uobj, c, o, 
                                      saved_pc_Uobj, casmfunc_finished, 
                                      in_casmfunc >>
           /\ UNCHANGED << cpu, cfi, p_, p_C, p_L, saved_pc_, p_E, c_, 
                           saved_pc_E, func_, p_U, c_U, saved_pc_U, p_Uo, c_Uo, 
                           o_, saved_pc_Uo, In_uobj, Uobj_finished, p_Uobje, 
                           saved_pc, p >>

Cfunc_finished_assign == /\ pc = "Cfunc_finished_assign"
                         /\ cfunc_finished' = FALSE
                         /\ in_cfunc' = FALSE
                         /\ Cpu' = [Cpu EXCEPT ![p_Uob].Pc = saved_pc_Uob]
                         /\ /\ p_' = p_Uob
                            /\ stack' = << [ procedure |->  "CFI_observer",
                                             pc        |->  "End_Uo",
                                             p_        |->  p_ ] >>
                                         \o stack
                         /\ pc' = "Start_"
                         /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, 
                                         p_E, c_, saved_pc_E, func_, p_Ex, 
                                         saved_pc_Ex, func, p_U, c_U, 
                                         saved_pc_U, p_Uo, c_Uo, o_, 
                                         saved_pc_Uo, In_uobj, Uobj_finished, 
                                         p_Uob, c_Uob, o_U, saved_pc_Uob, 
                                         p_Uobj, c, o, saved_pc_Uobj, 
                                         casmfunc_finished, in_casmfunc, 
                                         p_Uobje, saved_pc, p >>

End_Uo == /\ pc = "End_Uo"
          /\ pc' = Head(stack).pc
          /\ cfunc_finished' = Head(stack).cfunc_finished
          /\ in_cfunc' = Head(stack).in_cfunc
          /\ p_Uob' = Head(stack).p_Uob
          /\ c_Uob' = Head(stack).c_Uob
          /\ o_U' = Head(stack).o_U
          /\ saved_pc_Uob' = Head(stack).saved_pc_Uob
          /\ stack' = Tail(stack)
          /\ UNCHANGED << cpu, Cpu, memory, cfi, p_, p_C, p_L, saved_pc_, p_E, 
                          c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                          c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, 
                          In_uobj, Uobj_finished, p_Uobj, c, o, saved_pc_Uobj, 
                          casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, p >>

Uobject_code_c_func == Start_Uob \/ Loop_Uo \/ Cfunc_finished_assign
                          \/ End_Uo

Start_Uobj == /\ pc = "Start_Uobj"
              /\ IF ~in_casmfunc
                    THEN /\ Cpu' = [Cpu EXCEPT ![p_Uobj].Pc = UBER]
                         /\ /\ p_' = p_Uobj
                            /\ stack' = << [ procedure |->  "CFI_observer",
                                             pc        |->  "Loop_Uob",
                                             p_        |->  p_ ] >>
                                         \o stack
                         /\ pc' = "Start_"
                    ELSE /\ pc' = "End_Uob"
                         /\ UNCHANGED << Cpu, stack, p_ >>
              /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, p_E, c_, 
                              saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                              c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, 
                              In_uobj, Uobj_finished, p_Uob, c_Uob, o_U, 
                              saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, 
                              c, o, saved_pc_Uobj, casmfunc_finished, 
                              in_casmfunc, p_Uobje, saved_pc, p >>

Loop_Uob == /\ pc = "Loop_Uob"
            /\ IF ~casmfunc_finished
                  THEN /\ \/ /\ /\ c_Uob' = c
                                /\ o_U' = o
                                /\ p_Uob' = p_Uobj
                                /\ saved_pc_Uob' = UBER
                                /\ stack' = << [ procedure |->  "Uobject_code_c_func",
                                                 pc        |->  "Loop_Uob",
                                                 cfunc_finished |->  cfunc_finished,
                                                 in_cfunc  |->  in_cfunc,
                                                 p_Uob     |->  p_Uob,
                                                 c_Uob     |->  c_Uob,
                                                 o_U       |->  o_U,
                                                 saved_pc_Uob |->  saved_pc_Uob ] >>
                                             \o stack
                             /\ cfunc_finished' = FALSE
                             /\ in_cfunc' = FALSE
                             /\ pc' = "Start_Uob"
                             /\ UNCHANGED <<Cpu, memory, p_Ex, saved_pc_Ex, func, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                          \/ /\ /\ c' = c
                                /\ o' = o
                                /\ p_Uobj' = p_Uobj
                                /\ saved_pc_Uobj' = UBER
                                /\ stack' = << [ procedure |->  "Uobject_code_casm_func",
                                                 pc        |->  "Loop_Uob",
                                                 casmfunc_finished |->  casmfunc_finished,
                                                 in_casmfunc |->  in_casmfunc,
                                                 p_Uobj    |->  p_Uobj,
                                                 c         |->  c,
                                                 o         |->  o,
                                                 saved_pc_Uobj |->  saved_pc_Uobj ] >>
                                             \o stack
                             /\ casmfunc_finished' = FALSE
                             /\ in_casmfunc' = FALSE
                             /\ pc' = "Start_Uobj"
                             /\ UNCHANGED <<Cpu, memory, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc>>
                          \/ /\ /\ func' = TRUE
                                /\ p_Ex' = p_Uobj
                                /\ saved_pc_Ex' = UBER
                                /\ stack' = << [ procedure |->  "Exit_sentinel",
                                                 pc        |->  "Loop_Uob",
                                                 p_Ex      |->  p_Ex,
                                                 saved_pc_Ex |->  saved_pc_Ex,
                                                 func      |->  func ] >>
                                             \o stack
                             /\ pc' = "Start_Ex"
                             /\ UNCHANGED <<Cpu, memory, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                          \/ /\ Cpu' = [Cpu EXCEPT ![p_Uobj].Res_cpustate[c][o] = 100*c + o]
                             /\ pc' = "Loop_Uob"
                             /\ UNCHANGED <<memory, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                          \/ /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c].memuobj[o].Mem = 100*c + o]
                             /\ pc' = "Loop_Uob"
                             /\ UNCHANGED <<Cpu, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, casmfunc_finished, in_casmfunc>>
                          \/ /\ casmfunc_finished' = TRUE
                             /\ pc' = "Loop_Uob"
                             /\ UNCHANGED <<Cpu, memory, stack, p_Ex, saved_pc_Ex, func, p_Uob, c_Uob, o_U, saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, in_casmfunc>>
                       /\ p_' = p_
                  ELSE /\ casmfunc_finished' = FALSE
                       /\ in_casmfunc' = FALSE
                       /\ Cpu' = [Cpu EXCEPT ![p_Uobj].Pc = saved_pc_Uobj]
                       /\ /\ p_' = p_Uobj
                          /\ stack' = << [ procedure |->  "CFI_observer",
                                           pc        |->  "End_Uob",
                                           p_        |->  p_ ] >>
                                       \o stack
                       /\ pc' = "Start_"
                       /\ UNCHANGED << memory, p_Ex, saved_pc_Ex, func, p_Uob, 
                                       c_Uob, o_U, saved_pc_Uob, 
                                       cfunc_finished, in_cfunc, p_Uobj, c, o, 
                                       saved_pc_Uobj >>
            /\ UNCHANGED << cpu, cfi, p_C, p_L, saved_pc_, p_E, c_, saved_pc_E, 
                            func_, p_U, c_U, saved_pc_U, p_Uo, c_Uo, o_, 
                            saved_pc_Uo, In_uobj, Uobj_finished, p_Uobje, 
                            saved_pc, p >>

End_Uob == /\ pc = "End_Uob"
           /\ pc' = Head(stack).pc
           /\ casmfunc_finished' = Head(stack).casmfunc_finished
           /\ in_casmfunc' = Head(stack).in_casmfunc
           /\ p_Uobj' = Head(stack).p_Uobj
           /\ c' = Head(stack).c
           /\ o' = Head(stack).o
           /\ saved_pc_Uobj' = Head(stack).saved_pc_Uobj
           /\ stack' = Tail(stack)
           /\ UNCHANGED << cpu, Cpu, memory, cfi, p_, p_C, p_L, saved_pc_, p_E, 
                           c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                           c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, 
                           In_uobj, Uobj_finished, p_Uob, c_Uob, o_U, 
                           saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobje, 
                           saved_pc, p >>

Uobject_code_casm_func == Start_Uobj \/ Loop_Uob \/ End_Uob

Start == /\ pc = "Start"
         /\ Cpu' = [Cpu EXCEPT ![p_Uobje].Pc = LEGACY]
         /\ /\ p_' = p_Uobje
            /\ stack' = << [ procedure |->  "CFI_observer",
                             pc        |->  "End",
                             p_        |->  p_ ] >>
                         \o stack
         /\ pc' = "Start_"
         /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, p_E, c_, 
                         saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, c_U, 
                         saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                         Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                         cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                         casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, p >>

End == /\ pc = "End"
       /\ Cpu' = [Cpu EXCEPT ![p_Uobje].Pc = saved_pc]
       /\ /\ p_' = p_Uobje
          /\ stack' = << [ procedure |->  "CFI_observer",
                           pc        |->  Head(stack).pc,
                           p_        |->  p_ ] >>
                       \o Tail(stack)
       /\ pc' = "Start_"
       /\ UNCHANGED << cpu, memory, cfi, p_C, p_L, saved_pc_, p_E, c_, 
                       saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, c_U, 
                       saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                       Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                       cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                       casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, p >>

Uobject_code_legacy_func == Start \/ End

Loop_d == /\ pc = "Loop_d"
          /\ \/ /\ TRUE
                /\ pc' = "Loop_d"
                /\ UNCHANGED <<stack, p>>
             \/ /\ TRUE
                /\ pc' = "Loop_d"
                /\ UNCHANGED <<stack, p>>
             \/ /\ pc' = Head(stack).pc
                /\ p' = Head(stack).p
                /\ stack' = Tail(stack)
          /\ UNCHANGED << cpu, Cpu, memory, cfi, p_, p_C, p_L, saved_pc_, p_E, 
                          c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                          c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, 
                          In_uobj, Uobj_finished, p_Uob, c_Uob, o_U, 
                          saved_pc_Uob, cfunc_finished, in_cfunc, p_Uobj, c, o, 
                          saved_pc_Uobj, casmfunc_finished, in_casmfunc, 
                          p_Uobje, saved_pc >>

device_process == Loop_d

Loop == /\ pc = "Loop"
        /\ IF cpu > 0
              THEN /\ /\ p_C' = cpu
                      /\ stack' = << [ procedure |->  "Cpu_process",
                                       pc        |->  "Dec",
                                       p_C       |->  p_C ] >>
                                   \o stack
                   /\ pc' = "Start_C"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << stack, p_C >>
        /\ UNCHANGED << cpu, Cpu, memory, cfi, p_, p_L, saved_pc_, p_E, c_, 
                        saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, c_U, 
                        saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                        Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                        cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                        casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, p >>

Dec == /\ pc = "Dec"
       /\ cpu' = cpu - 1
       /\ pc' = "Loop"
       /\ UNCHANGED << Cpu, memory, cfi, stack, p_, p_C, p_L, saved_pc_, p_E, 
                       c_, saved_pc_E, func_, p_Ex, saved_pc_Ex, func, p_U, 
                       c_U, saved_pc_U, p_Uo, c_Uo, o_, saved_pc_Uo, In_uobj, 
                       Uobj_finished, p_Uob, c_Uob, o_U, saved_pc_Uob, 
                       cfunc_finished, in_cfunc, p_Uobj, c, o, saved_pc_Uobj, 
                       casmfunc_finished, in_casmfunc, p_Uobje, saved_pc, p >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == CFI_observer \/ Cpu_process \/ Legacy_code \/ Entry_sentinel
           \/ Exit_sentinel \/ Uobjcollection_code \/ Uobject_code
           \/ Uobject_code_c_func \/ Uobject_code_casm_func
           \/ Uobject_code_legacy_func \/ device_process \/ Loop \/ Dec
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-63c4cffedd1e5dec5d2801f5f7bebd11

(* Memory allocated to uberOject only self-accessed *)
MI == \A col \in 1..MAXUOBJCOLLECTIONS: \A obj \in 1..MAXUOBJSWITHINCOLLECTION: 
                    memory.Mem_uobjcollection[col].memuobj[obj].Mem = 100*col + obj \/
                    memory.Mem_uobjcollection[col].memuobj[obj].Mem = 0
(* Memory safety follows from MI + all other memory contains no access by uberObjects *)
MS == \A col \in 1..MAXUOBJCOLLECTIONS: \A obj \in 1..MAXUOBJSWITHINCOLLECTION:
                    memory.Mem_legacy /= 100*col + obj /\
                    TRUE
CFI == cfi = TRUE

=============================================================================
\* Modification History
\* Last modified Thu Jan 21 08:29:04 PST 2021 by mjmccall
\* Created Wed Jan 20 09:49:35 PST 2021 by mjmccall
