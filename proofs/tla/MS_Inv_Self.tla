---------------------------- MODULE MS_Inv_Self ----------------------------
EXTENDS Sequences, Integers, TLAPS
CONSTANTS (*MAXCPUS,*) MAXUOBJCOLLECTIONS, MAXUOBJSWITHINCOLLECTION

MAXCPUS == 2

LEGACY == 1
SENTINEL == 2
UBER == 3

LOAD == 1
STORE == 2
LEGLOAD == 3
LEGSTORE == 4
CS == 5

(* --algorithm execution
variables Cpu = [cp \in 1..MAXCPUS |->
            [Id |-> cp,                             \* unique CPU identifier
             Pc |-> [x \in 1..2 |-> 0],             \* program counter (currently abstracted to object control)
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
    call_stack = 3,
    memory_load_return = 0;
    
procedure memory_load(p, c, o, l) begin
Start:
if l then
Load_Legacy:
    Cpu[p].Pc[2] := LEGLOAD;
    memory_load_return := memory.Mem_legacy;
LL_Done:
    Cpu[p].Pc[2] := 0;
    return;
else
Load:
    Cpu[p].Pc[2] := LOAD;
    memory_load_return := memory.Mem_uobjcollection[c].memuobj[o].uobj_local_data;
L_Done:
    Cpu[p].Pc[2] := 0;
    return;
end if;
end procedure;

procedure memory_store(p, c, o, l, val) begin
Start:
if l then
Store_Legacy:
    Cpu[p].Pc[2] := LEGSTORE;
    memory.Mem_legacy := val;
LS_Done:
    Cpu[p].Pc[2] := 0;
    return;
else
Store:
    Cpu[p].Pc[2] := STORE;
    memory.Mem_uobjcollection[c].memuobj[o].uobj_local_data := val;
S_Done:
    Cpu[p].Pc[2] := 0;
    return;
end if;
end procedure;

(***************************************************************************)
(* Cpu_process(p) runs legacy code or an uObject collection on processor   *)
(* p.                                                                      *)
(***************************************************************************)
procedure Cpu_process(p)
    variables collection;
    begin
Start:
    with col \in 1..MAXUOBJCOLLECTIONS do
        collection := col;   
    end with;
    either
        Cpu[p].Pr := LEGACY;
Call:
        call Legacy_code(p, 0);
        return;
    or
        Cpu[p].Pr := UBER;
Collection:
        Cpu[p].Collection := collection;
        call Uobjcollection_code(p, collection, 0);
After_branching:
        return;
    end either;
end procedure;

(***************************************************************************)
(* Legacy_code(p, saved_pc) accesses cpu state or legacy memory; or calls  *)
(* uObject collection code.                                                *)
(***************************************************************************)
procedure Legacy_code(p, saved_pc)
    variables collection;
    begin
Start:
    Cpu[p].Pc[1] := LEGACY;
Loop:
    while TRUE do
        either
            if call_stack > 0 then
                call_stack := call_stack - 1;
                with col \in 1..MAXUOBJCOLLECTIONS do
                    Cpu[p].Collection := col;
                    call Uobjcollection_code(p, col, LEGACY) \* Sentinel will not allow this to happen if legacy called from uObject code
                end with;
            end if;
        or 
            call memory_load(p, 0, 0, TRUE);
        or 
            call memory_store(p, 0, 0, TRUE, 0);
        or
            Cpu[p].Pc[1] := saved_pc;
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
    Cpu[p].Pc[1] := UBER;
Call:
    with object \in 1..MAXUOBJCOLLECTIONS do
        Cpu[p].Object := object;
        call Uobject_code(p, c, object, saved_pc);
    end with;
Return:
    Cpu[p].Pc[1] := saved_pc;
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
    await memory.Mem_uobjcollection[c].memuobj[o].lock = 0;
\*CS_Lock:
    memory.Mem_uobjcollection[c].memuobj[o].lock := 1;
    if ~In_uobj then
        Cpu[p].Pc[1] := UBER;
CS_Start:
        Cpu[p].Pc[2] := CS;
CS_Loop:
        while ~Uobj_finished do
            either
                if call_stack > 0 then
                    call_stack := call_stack - 1;
                    call Uobject_code_legacy_func(p, UBER);
                    
                end if;
            or 
                (* Section 1.6: memory safety: invariant 1 *)
CS_Read:
                call memory_load(p, c, o, FALSE);
            or
                (* Section 1.6: memory safety: invariant 1 *)
CS_Write:
                call memory_store(p, c, o, FALSE, 0);
            or
CS_Exit:
                Cpu[p].Pc[2] := 0;
                Uobj_finished := TRUE;
            end either;
        end while;
    end if;
CS_Unlock:    
    memory.Mem_uobjcollection[c].memuobj[o].lock := 0;
    Uobj_finished := FALSE;
    In_uobj := FALSE;
    Cpu[p].Pc[1] := saved_pc;
End:
    return;
end procedure;

procedure Uobject_code_legacy_func(p, saved_pc) begin
Start:
    Cpu[p].Pc[1] := LEGACY;
End:
    Cpu[p].Pc[1] := saved_pc;
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
\* BEGIN TRANSLATION (chksum(pcal) = "9039838b" /\ chksum(tla) = "20a2af9")
\* Label Start of procedure memory_load at line 47 col 1 changed to Start_
\* Label Start of procedure memory_store at line 66 col 1 changed to Start_m
\* Label Start of procedure Cpu_process at line 91 col 5 changed to Start_C
\* Label Call of procedure Cpu_process at line 97 col 9 changed to Call_
\* Label Start of procedure Legacy_code at line 117 col 5 changed to Start_L
\* Label Start of procedure Uobjcollection_code at line 145 col 5 changed to Start_U
\* Label Start of procedure Uobject_code at line 165 col 5 changed to Start_Uo
\* Label End of procedure Uobject_code at line 201 col 5 changed to End_
\* Label A of process one at line 215 col 5 changed to A_
\* Procedure variable collection of procedure Cpu_process at line 88 col 15 changed to collection_
\* Parameter p of procedure memory_load at line 45 col 23 changed to p_
\* Parameter c of procedure memory_load at line 45 col 26 changed to c_
\* Parameter o of procedure memory_load at line 45 col 29 changed to o_
\* Parameter l of procedure memory_load at line 45 col 32 changed to l_
\* Parameter p of procedure memory_store at line 64 col 24 changed to p_m
\* Parameter c of procedure memory_store at line 64 col 27 changed to c_m
\* Parameter o of procedure memory_store at line 64 col 30 changed to o_m
\* Parameter p of procedure Cpu_process at line 87 col 23 changed to p_C
\* Parameter p of procedure Legacy_code at line 113 col 23 changed to p_L
\* Parameter saved_pc of procedure Legacy_code at line 113 col 26 changed to saved_pc_
\* Parameter p of procedure Uobjcollection_code at line 143 col 31 changed to p_U
\* Parameter c of procedure Uobjcollection_code at line 143 col 34 changed to c_U
\* Parameter saved_pc of procedure Uobjcollection_code at line 143 col 37 changed to saved_pc_U
\* Parameter p of procedure Uobject_code at line 160 col 24 changed to p_Uo
\* Parameter saved_pc of procedure Uobject_code at line 160 col 33 changed to saved_pc_Uo
CONSTANT defaultInitValue
VARIABLES Cpu, memory, call_stack, memory_load_return, pc, stack, p_, c_, o_, 
          l_, p_m, c_m, o_m, l, val, p_C, collection_, p_L, saved_pc_, 
          collection, p_U, c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, 
          Uobj_finished, p, saved_pc

vars == << Cpu, memory, call_stack, memory_load_return, pc, stack, p_, c_, o_, 
           l_, p_m, c_m, o_m, l, val, p_C, collection_, p_L, saved_pc_, 
           collection, p_U, c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, 
           Uobj_finished, p, saved_pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ Cpu =       [cp \in 1..MAXCPUS |->
                   [Id |-> cp,
                    Pc |-> [x \in 1..2 |-> 0],
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
        /\ memory_load_return = 0
        (* Procedure memory_load *)
        /\ p_ = [ self \in ProcSet |-> defaultInitValue]
        /\ c_ = [ self \in ProcSet |-> defaultInitValue]
        /\ o_ = [ self \in ProcSet |-> defaultInitValue]
        /\ l_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure memory_store *)
        /\ p_m = [ self \in ProcSet |-> defaultInitValue]
        /\ c_m = [ self \in ProcSet |-> defaultInitValue]
        /\ o_m = [ self \in ProcSet |-> defaultInitValue]
        /\ l = [ self \in ProcSet |-> defaultInitValue]
        /\ val = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Cpu_process *)
        /\ p_C = [ self \in ProcSet |-> defaultInitValue]
        /\ collection_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Legacy_code *)
        /\ p_L = [ self \in ProcSet |-> defaultInitValue]
        /\ saved_pc_ = [ self \in ProcSet |-> defaultInitValue]
        /\ collection = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Uobjcollection_code *)
        /\ p_U = [ self \in ProcSet |-> defaultInitValue]
        /\ c_U = [ self \in ProcSet |-> defaultInitValue]
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
                /\ IF l_[self]
                      THEN /\ pc' = [pc EXCEPT ![self] = "Load_Legacy"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Load"]
                /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                stack, p_, c_, o_, l_, p_m, c_m, o_m, l, val, 
                                p_C, collection_, p_L, saved_pc_, collection, 
                                p_U, c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                In_uobj, Uobj_finished, p, saved_pc >>

Load_Legacy(self) == /\ pc[self] = "Load_Legacy"
                     /\ Cpu' = [Cpu EXCEPT ![p_[self]].Pc[2] = LEGLOAD]
                     /\ memory_load_return' = memory.Mem_legacy
                     /\ pc' = [pc EXCEPT ![self] = "LL_Done"]
                     /\ UNCHANGED << memory, call_stack, stack, p_, c_, o_, l_, 
                                     p_m, c_m, o_m, l, val, p_C, collection_, 
                                     p_L, saved_pc_, collection, p_U, c_U, 
                                     saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                     In_uobj, Uobj_finished, p, saved_pc >>

LL_Done(self) == /\ pc[self] = "LL_Done"
                 /\ Cpu' = [Cpu EXCEPT ![p_[self]].Pc[2] = 0]
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ p_' = [p_ EXCEPT ![self] = Head(stack[self]).p_]
                 /\ c_' = [c_ EXCEPT ![self] = Head(stack[self]).c_]
                 /\ o_' = [o_ EXCEPT ![self] = Head(stack[self]).o_]
                 /\ l_' = [l_ EXCEPT ![self] = Head(stack[self]).l_]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << memory, call_stack, memory_load_return, p_m, 
                                 c_m, o_m, l, val, p_C, collection_, p_L, 
                                 saved_pc_, collection, p_U, c_U, saved_pc_U, 
                                 p_Uo, c, o, saved_pc_Uo, In_uobj, 
                                 Uobj_finished, p, saved_pc >>

Load(self) == /\ pc[self] = "Load"
              /\ Cpu' = [Cpu EXCEPT ![p_[self]].Pc[2] = LOAD]
              /\ memory_load_return' = memory.Mem_uobjcollection[c_[self]].memuobj[o_[self]].uobj_local_data
              /\ pc' = [pc EXCEPT ![self] = "L_Done"]
              /\ UNCHANGED << memory, call_stack, stack, p_, c_, o_, l_, p_m, 
                              c_m, o_m, l, val, p_C, collection_, p_L, 
                              saved_pc_, collection, p_U, c_U, saved_pc_U, 
                              p_Uo, c, o, saved_pc_Uo, In_uobj, Uobj_finished, 
                              p, saved_pc >>

L_Done(self) == /\ pc[self] = "L_Done"
                /\ Cpu' = [Cpu EXCEPT ![p_[self]].Pc[2] = 0]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ p_' = [p_ EXCEPT ![self] = Head(stack[self]).p_]
                /\ c_' = [c_ EXCEPT ![self] = Head(stack[self]).c_]
                /\ o_' = [o_ EXCEPT ![self] = Head(stack[self]).o_]
                /\ l_' = [l_ EXCEPT ![self] = Head(stack[self]).l_]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << memory, call_stack, memory_load_return, p_m, 
                                c_m, o_m, l, val, p_C, collection_, p_L, 
                                saved_pc_, collection, p_U, c_U, saved_pc_U, 
                                p_Uo, c, o, saved_pc_Uo, In_uobj, 
                                Uobj_finished, p, saved_pc >>

memory_load(self) == Start_(self) \/ Load_Legacy(self) \/ LL_Done(self)
                        \/ Load(self) \/ L_Done(self)

Start_m(self) == /\ pc[self] = "Start_m"
                 /\ IF l[self]
                       THEN /\ pc' = [pc EXCEPT ![self] = "Store_Legacy"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Store"]
                 /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                 stack, p_, c_, o_, l_, p_m, c_m, o_m, l, val, 
                                 p_C, collection_, p_L, saved_pc_, collection, 
                                 p_U, c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                 In_uobj, Uobj_finished, p, saved_pc >>

Store_Legacy(self) == /\ pc[self] = "Store_Legacy"
                      /\ Cpu' = [Cpu EXCEPT ![p_m[self]].Pc[2] = LEGSTORE]
                      /\ memory' = [memory EXCEPT !.Mem_legacy = val[self]]
                      /\ pc' = [pc EXCEPT ![self] = "LS_Done"]
                      /\ UNCHANGED << call_stack, memory_load_return, stack, 
                                      p_, c_, o_, l_, p_m, c_m, o_m, l, val, 
                                      p_C, collection_, p_L, saved_pc_, 
                                      collection, p_U, c_U, saved_pc_U, p_Uo, 
                                      c, o, saved_pc_Uo, In_uobj, 
                                      Uobj_finished, p, saved_pc >>

LS_Done(self) == /\ pc[self] = "LS_Done"
                 /\ Cpu' = [Cpu EXCEPT ![p_m[self]].Pc[2] = 0]
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ p_m' = [p_m EXCEPT ![self] = Head(stack[self]).p_m]
                 /\ c_m' = [c_m EXCEPT ![self] = Head(stack[self]).c_m]
                 /\ o_m' = [o_m EXCEPT ![self] = Head(stack[self]).o_m]
                 /\ l' = [l EXCEPT ![self] = Head(stack[self]).l]
                 /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << memory, call_stack, memory_load_return, p_, 
                                 c_, o_, l_, p_C, collection_, p_L, saved_pc_, 
                                 collection, p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                 saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                 saved_pc >>

Store(self) == /\ pc[self] = "Store"
               /\ Cpu' = [Cpu EXCEPT ![p_m[self]].Pc[2] = STORE]
               /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c_m[self]].memuobj[o_m[self]].uobj_local_data = val[self]]
               /\ pc' = [pc EXCEPT ![self] = "S_Done"]
               /\ UNCHANGED << call_stack, memory_load_return, stack, p_, c_, 
                               o_, l_, p_m, c_m, o_m, l, val, p_C, collection_, 
                               p_L, saved_pc_, collection, p_U, c_U, 
                               saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, 
                               Uobj_finished, p, saved_pc >>

S_Done(self) == /\ pc[self] = "S_Done"
                /\ Cpu' = [Cpu EXCEPT ![p_m[self]].Pc[2] = 0]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ p_m' = [p_m EXCEPT ![self] = Head(stack[self]).p_m]
                /\ c_m' = [c_m EXCEPT ![self] = Head(stack[self]).c_m]
                /\ o_m' = [o_m EXCEPT ![self] = Head(stack[self]).o_m]
                /\ l' = [l EXCEPT ![self] = Head(stack[self]).l]
                /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << memory, call_stack, memory_load_return, p_, c_, 
                                o_, l_, p_C, collection_, p_L, saved_pc_, 
                                collection, p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                saved_pc >>

memory_store(self) == Start_m(self) \/ Store_Legacy(self) \/ LS_Done(self)
                         \/ Store(self) \/ S_Done(self)

Start_C(self) == /\ pc[self] = "Start_C"
                 /\ \E col \in 1..MAXUOBJCOLLECTIONS:
                      collection_' = [collection_ EXCEPT ![self] = col]
                 /\ \/ /\ Cpu' = [Cpu EXCEPT ![p_C[self]].Pr = LEGACY]
                       /\ pc' = [pc EXCEPT ![self] = "Call_"]
                    \/ /\ Cpu' = [Cpu EXCEPT ![p_C[self]].Pr = UBER]
                       /\ pc' = [pc EXCEPT ![self] = "Collection"]
                 /\ UNCHANGED << memory, call_stack, memory_load_return, stack, 
                                 p_, c_, o_, l_, p_m, c_m, o_m, l, val, p_C, 
                                 p_L, saved_pc_, collection, p_U, c_U, 
                                 saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, 
                                 Uobj_finished, p, saved_pc >>

Call_(self) == /\ pc[self] = "Call_"
               /\ /\ collection_' = [collection_ EXCEPT ![self] = Head(stack[self]).collection_]
                  /\ p_L' = [p_L EXCEPT ![self] = p_C[self]]
                  /\ saved_pc_' = [saved_pc_ EXCEPT ![self] = 0]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Legacy_code",
                                                           pc        |->  Head(stack[self]).pc,
                                                           collection |->  collection[self],
                                                           p_L       |->  p_L[self],
                                                           saved_pc_ |->  saved_pc_[self] ] >>
                                                       \o Tail(stack[self])]
               /\ collection' = [collection EXCEPT ![self] = defaultInitValue]
               /\ pc' = [pc EXCEPT ![self] = "Start_L"]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, p_, 
                               c_, o_, l_, p_m, c_m, o_m, l, val, p_C, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

Collection(self) == /\ pc[self] = "Collection"
                    /\ Cpu' = [Cpu EXCEPT ![p_C[self]].Collection = collection_[self]]
                    /\ /\ c_U' = [c_U EXCEPT ![self] = collection_[self]]
                       /\ p_U' = [p_U EXCEPT ![self] = p_C[self]]
                       /\ saved_pc_U' = [saved_pc_U EXCEPT ![self] = 0]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobjcollection_code",
                                                                pc        |->  "After_branching",
                                                                p_U       |->  p_U[self],
                                                                c_U       |->  c_U[self],
                                                                saved_pc_U |->  saved_pc_U[self] ] >>
                                                            \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "Start_U"]
                    /\ UNCHANGED << memory, call_stack, memory_load_return, p_, 
                                    c_, o_, l_, p_m, c_m, o_m, l, val, p_C, 
                                    collection_, p_L, saved_pc_, collection, 
                                    p_Uo, c, o, saved_pc_Uo, In_uobj, 
                                    Uobj_finished, p, saved_pc >>

After_branching(self) == /\ pc[self] = "After_branching"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ collection_' = [collection_ EXCEPT ![self] = Head(stack[self]).collection_]
                         /\ p_C' = [p_C EXCEPT ![self] = Head(stack[self]).p_C]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << Cpu, memory, call_stack, 
                                         memory_load_return, p_, c_, o_, l_, 
                                         p_m, c_m, o_m, l, val, p_L, saved_pc_, 
                                         collection, p_U, c_U, saved_pc_U, 
                                         p_Uo, c, o, saved_pc_Uo, In_uobj, 
                                         Uobj_finished, p, saved_pc >>

Cpu_process(self) == Start_C(self) \/ Call_(self) \/ Collection(self)
                        \/ After_branching(self)

Start_L(self) == /\ pc[self] = "Start_L"
                 /\ Cpu' = [Cpu EXCEPT ![p_L[self]].Pc[1] = LEGACY]
                 /\ pc' = [pc EXCEPT ![self] = "Loop"]
                 /\ UNCHANGED << memory, call_stack, memory_load_return, stack, 
                                 p_, c_, o_, l_, p_m, c_m, o_m, l, val, p_C, 
                                 collection_, p_L, saved_pc_, collection, p_U, 
                                 c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                 In_uobj, Uobj_finished, p, saved_pc >>

Loop(self) == /\ pc[self] = "Loop"
              /\ \/ /\ IF call_stack > 0
                          THEN /\ call_stack' = call_stack - 1
                               /\ \E col \in 1..MAXUOBJCOLLECTIONS:
                                    /\ Cpu' = [Cpu EXCEPT ![p_L[self]].Collection = col]
                                    /\ /\ c_U' = [c_U EXCEPT ![self] = col]
                                       /\ p_U' = [p_U EXCEPT ![self] = p_L[self]]
                                       /\ saved_pc_U' = [saved_pc_U EXCEPT ![self] = LEGACY]
                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobjcollection_code",
                                                                                pc        |->  "Loop",
                                                                                p_U       |->  p_U[self],
                                                                                c_U       |->  c_U[self],
                                                                                saved_pc_U |->  saved_pc_U[self] ] >>
                                                                            \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "Start_U"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Loop"]
                               /\ UNCHANGED << Cpu, call_stack, stack, p_U, 
                                               c_U, saved_pc_U >>
                    /\ UNCHANGED <<p_, c_, o_, l_, p_m, c_m, o_m, l, val, p_L, saved_pc_, collection>>
                 \/ /\ /\ c_' = [c_ EXCEPT ![self] = 0]
                       /\ l_' = [l_ EXCEPT ![self] = TRUE]
                       /\ o_' = [o_ EXCEPT ![self] = 0]
                       /\ p_' = [p_ EXCEPT ![self] = p_L[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "memory_load",
                                                                pc        |->  "Loop",
                                                                p_        |->  p_[self],
                                                                c_        |->  c_[self],
                                                                o_        |->  o_[self],
                                                                l_        |->  l_[self] ] >>
                                                            \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "Start_"]
                    /\ UNCHANGED <<Cpu, call_stack, p_m, c_m, o_m, l, val, p_L, saved_pc_, collection, p_U, c_U, saved_pc_U>>
                 \/ /\ /\ c_m' = [c_m EXCEPT ![self] = 0]
                       /\ l' = [l EXCEPT ![self] = TRUE]
                       /\ o_m' = [o_m EXCEPT ![self] = 0]
                       /\ p_m' = [p_m EXCEPT ![self] = p_L[self]]
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "memory_store",
                                                                pc        |->  "Loop",
                                                                p_m       |->  p_m[self],
                                                                c_m       |->  c_m[self],
                                                                o_m       |->  o_m[self],
                                                                l         |->  l[self],
                                                                val       |->  val[self] ] >>
                                                            \o stack[self]]
                       /\ val' = [val EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "Start_m"]
                    /\ UNCHANGED <<Cpu, call_stack, p_, c_, o_, l_, p_L, saved_pc_, collection, p_U, c_U, saved_pc_U>>
                 \/ /\ Cpu' = [Cpu EXCEPT ![p_L[self]].Pc[1] = saved_pc_[self]]
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ collection' = [collection EXCEPT ![self] = Head(stack[self]).collection]
                    /\ p_L' = [p_L EXCEPT ![self] = Head(stack[self]).p_L]
                    /\ saved_pc_' = [saved_pc_ EXCEPT ![self] = Head(stack[self]).saved_pc_]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED <<call_stack, p_, c_, o_, l_, p_m, c_m, o_m, l, val, p_U, c_U, saved_pc_U>>
              /\ UNCHANGED << memory, memory_load_return, p_C, collection_, 
                              p_Uo, c, o, saved_pc_Uo, In_uobj, Uobj_finished, 
                              p, saved_pc >>

Legacy_code(self) == Start_L(self) \/ Loop(self)

Start_U(self) == /\ pc[self] = "Start_U"
                 /\ Cpu' = [Cpu EXCEPT ![p_U[self]].Pc[1] = UBER]
                 /\ pc' = [pc EXCEPT ![self] = "Call"]
                 /\ UNCHANGED << memory, call_stack, memory_load_return, stack, 
                                 p_, c_, o_, l_, p_m, c_m, o_m, l, val, p_C, 
                                 collection_, p_L, saved_pc_, collection, p_U, 
                                 c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                 In_uobj, Uobj_finished, p, saved_pc >>

Call(self) == /\ pc[self] = "Call"
              /\ \E object \in 1..MAXUOBJCOLLECTIONS:
                   /\ Cpu' = [Cpu EXCEPT ![p_U[self]].Object = object]
                   /\ /\ c' = [c EXCEPT ![self] = c_U[self]]
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
              /\ UNCHANGED << memory, call_stack, memory_load_return, p_, c_, 
                              o_, l_, p_m, c_m, o_m, l, val, p_C, collection_, 
                              p_L, saved_pc_, collection, p_U, c_U, saved_pc_U, 
                              p, saved_pc >>

Return(self) == /\ pc[self] = "Return"
                /\ Cpu' = [Cpu EXCEPT ![p_U[self]].Pc[1] = saved_pc_U[self]]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ p_U' = [p_U EXCEPT ![self] = Head(stack[self]).p_U]
                /\ c_U' = [c_U EXCEPT ![self] = Head(stack[self]).c_U]
                /\ saved_pc_U' = [saved_pc_U EXCEPT ![self] = Head(stack[self]).saved_pc_U]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << memory, call_stack, memory_load_return, p_, c_, 
                                o_, l_, p_m, c_m, o_m, l, val, p_C, 
                                collection_, p_L, saved_pc_, collection, p_Uo, 
                                c, o, saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                saved_pc >>

Uobjcollection_code(self) == Start_U(self) \/ Call(self) \/ Return(self)

Start_Uo(self) == /\ pc[self] = "Start_Uo"
                  /\ memory.Mem_uobjcollection[c[self]].memuobj[o[self]].lock = 0
                  /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c[self]].memuobj[o[self]].lock = 1]
                  /\ IF ~In_uobj[self]
                        THEN /\ Cpu' = [Cpu EXCEPT ![p_Uo[self]].Pc[1] = UBER]
                             /\ pc' = [pc EXCEPT ![self] = "CS_Start"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "CS_Unlock"]
                             /\ Cpu' = Cpu
                  /\ UNCHANGED << call_stack, memory_load_return, stack, p_, 
                                  c_, o_, l_, p_m, c_m, o_m, l, val, p_C, 
                                  collection_, p_L, saved_pc_, collection, p_U, 
                                  c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                  In_uobj, Uobj_finished, p, saved_pc >>

CS_Start(self) == /\ pc[self] = "CS_Start"
                  /\ Cpu' = [Cpu EXCEPT ![p_Uo[self]].Pc[2] = CS]
                  /\ pc' = [pc EXCEPT ![self] = "CS_Loop"]
                  /\ UNCHANGED << memory, call_stack, memory_load_return, 
                                  stack, p_, c_, o_, l_, p_m, c_m, o_m, l, val, 
                                  p_C, collection_, p_L, saved_pc_, collection, 
                                  p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                  saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                  saved_pc >>

CS_Loop(self) == /\ pc[self] = "CS_Loop"
                 /\ IF ~Uobj_finished[self]
                       THEN /\ \/ /\ IF call_stack > 0
                                        THEN /\ call_stack' = call_stack - 1
                                             /\ /\ p' = [p EXCEPT ![self] = p_Uo[self]]
                                                /\ saved_pc' = [saved_pc EXCEPT ![self] = UBER]
                                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Uobject_code_legacy_func",
                                                                                         pc        |->  "CS_Loop",
                                                                                         p         |->  p[self],
                                                                                         saved_pc  |->  saved_pc[self] ] >>
                                                                                     \o stack[self]]
                                             /\ pc' = [pc EXCEPT ![self] = "Start"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "CS_Loop"]
                                             /\ UNCHANGED << call_stack, stack, 
                                                             p, saved_pc >>
                               \/ /\ pc' = [pc EXCEPT ![self] = "CS_Read"]
                                  /\ UNCHANGED <<call_stack, stack, p, saved_pc>>
                               \/ /\ pc' = [pc EXCEPT ![self] = "CS_Write"]
                                  /\ UNCHANGED <<call_stack, stack, p, saved_pc>>
                               \/ /\ pc' = [pc EXCEPT ![self] = "CS_Exit"]
                                  /\ UNCHANGED <<call_stack, stack, p, saved_pc>>
                       ELSE /\ pc' = [pc EXCEPT ![self] = "CS_Unlock"]
                            /\ UNCHANGED << call_stack, stack, p, saved_pc >>
                 /\ UNCHANGED << Cpu, memory, memory_load_return, p_, c_, o_, 
                                 l_, p_m, c_m, o_m, l, val, p_C, collection_, 
                                 p_L, saved_pc_, collection, p_U, c_U, 
                                 saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, 
                                 Uobj_finished >>

CS_Read(self) == /\ pc[self] = "CS_Read"
                 /\ /\ c_' = [c_ EXCEPT ![self] = c[self]]
                    /\ l_' = [l_ EXCEPT ![self] = FALSE]
                    /\ o_' = [o_ EXCEPT ![self] = o[self]]
                    /\ p_' = [p_ EXCEPT ![self] = p_Uo[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "memory_load",
                                                             pc        |->  "CS_Loop",
                                                             p_        |->  p_[self],
                                                             c_        |->  c_[self],
                                                             o_        |->  o_[self],
                                                             l_        |->  l_[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Start_"]
                 /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                 p_m, c_m, o_m, l, val, p_C, collection_, p_L, 
                                 saved_pc_, collection, p_U, c_U, saved_pc_U, 
                                 p_Uo, c, o, saved_pc_Uo, In_uobj, 
                                 Uobj_finished, p, saved_pc >>

CS_Write(self) == /\ pc[self] = "CS_Write"
                  /\ /\ c_m' = [c_m EXCEPT ![self] = c[self]]
                     /\ l' = [l EXCEPT ![self] = FALSE]
                     /\ o_m' = [o_m EXCEPT ![self] = o[self]]
                     /\ p_m' = [p_m EXCEPT ![self] = p_Uo[self]]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "memory_store",
                                                              pc        |->  "CS_Loop",
                                                              p_m       |->  p_m[self],
                                                              c_m       |->  c_m[self],
                                                              o_m       |->  o_m[self],
                                                              l         |->  l[self],
                                                              val       |->  val[self] ] >>
                                                          \o stack[self]]
                     /\ val' = [val EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = "Start_m"]
                  /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                  p_, c_, o_, l_, p_C, collection_, p_L, 
                                  saved_pc_, collection, p_U, c_U, saved_pc_U, 
                                  p_Uo, c, o, saved_pc_Uo, In_uobj, 
                                  Uobj_finished, p, saved_pc >>

CS_Exit(self) == /\ pc[self] = "CS_Exit"
                 /\ Cpu' = [Cpu EXCEPT ![p_Uo[self]].Pc[2] = 0]
                 /\ Uobj_finished' = [Uobj_finished EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "CS_Loop"]
                 /\ UNCHANGED << memory, call_stack, memory_load_return, stack, 
                                 p_, c_, o_, l_, p_m, c_m, o_m, l, val, p_C, 
                                 collection_, p_L, saved_pc_, collection, p_U, 
                                 c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                 In_uobj, p, saved_pc >>

CS_Unlock(self) == /\ pc[self] = "CS_Unlock"
                   /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c[self]].memuobj[o[self]].lock = 0]
                   /\ Uobj_finished' = [Uobj_finished EXCEPT ![self] = FALSE]
                   /\ In_uobj' = [In_uobj EXCEPT ![self] = FALSE]
                   /\ Cpu' = [Cpu EXCEPT ![p_Uo[self]].Pc[1] = saved_pc_Uo[self]]
                   /\ pc' = [pc EXCEPT ![self] = "End_"]
                   /\ UNCHANGED << call_stack, memory_load_return, stack, p_, 
                                   c_, o_, l_, p_m, c_m, o_m, l, val, p_C, 
                                   collection_, p_L, saved_pc_, collection, 
                                   p_U, c_U, saved_pc_U, p_Uo, c, o, 
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
              /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, p_, 
                              c_, o_, l_, p_m, c_m, o_m, l, val, p_C, 
                              collection_, p_L, saved_pc_, collection, p_U, 
                              c_U, saved_pc_U, p, saved_pc >>

Uobject_code(self) == Start_Uo(self) \/ CS_Start(self) \/ CS_Loop(self)
                         \/ CS_Read(self) \/ CS_Write(self)
                         \/ CS_Exit(self) \/ CS_Unlock(self) \/ End_(self)

Start(self) == /\ pc[self] = "Start"
               /\ Cpu' = [Cpu EXCEPT ![p[self]].Pc[1] = LEGACY]
               /\ pc' = [pc EXCEPT ![self] = "End"]
               /\ UNCHANGED << memory, call_stack, memory_load_return, stack, 
                               p_, c_, o_, l_, p_m, c_m, o_m, l, val, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

End(self) == /\ pc[self] = "End"
             /\ Cpu' = [Cpu EXCEPT ![p[self]].Pc[1] = saved_pc[self]]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
             /\ saved_pc' = [saved_pc EXCEPT ![self] = Head(stack[self]).saved_pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << memory, call_stack, memory_load_return, p_, c_, 
                             o_, l_, p_m, c_m, o_m, l, val, p_C, collection_, 
                             p_L, saved_pc_, collection, p_U, c_U, saved_pc_U, 
                             p_Uo, c, o, saved_pc_Uo, In_uobj, Uobj_finished >>

Uobject_code_legacy_func(self) == Start(self) \/ End(self)

A_ == /\ pc[1] = "A_"
      /\ /\ p_C' = [p_C EXCEPT ![1] = 1]
         /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "Cpu_process",
                                               pc        |->  "Done",
                                               collection_ |->  collection_[1],
                                               p_C       |->  p_C[1] ] >>
                                           \o stack[1]]
      /\ collection_' = [collection_ EXCEPT ![1] = defaultInitValue]
      /\ pc' = [pc EXCEPT ![1] = "Start_C"]
      /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, p_, c_, o_, 
                      l_, p_m, c_m, o_m, l, val, p_L, saved_pc_, collection, 
                      p_U, c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, 
                      Uobj_finished, p, saved_pc >>

one == A_

A == /\ pc[2] = "A"
     /\ /\ p_C' = [p_C EXCEPT ![2] = 2]
        /\ stack' = [stack EXCEPT ![2] = << [ procedure |->  "Cpu_process",
                                              pc        |->  "Done",
                                              collection_ |->  collection_[2],
                                              p_C       |->  p_C[2] ] >>
                                          \o stack[2]]
     /\ collection_' = [collection_ EXCEPT ![2] = defaultInitValue]
     /\ pc' = [pc EXCEPT ![2] = "Start_C"]
     /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, p_, c_, o_, 
                     l_, p_m, c_m, o_m, l, val, p_L, saved_pc_, collection, 
                     p_U, c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, 
                     Uobj_finished, p, saved_pc >>

two == A

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two
           \/ (\E self \in ProcSet:  \/ memory_load(self) \/ memory_store(self)
                                     \/ Cpu_process(self) \/ Legacy_code(self)
                                     \/ Uobjcollection_code(self)
                                     \/ Uobject_code(self)
                                     \/ Uobject_code_legacy_func(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


\*CS == {"CS_Loop", "CS_Write", "CS_Read"}


MS_Inv1 == \A i \in 1..MAXCPUS:
           /\ Cpu[i].Pc[2] = LOAD => c_[i] = Cpu[i].Collection /\ o_[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
           /\ Cpu[i].Pc[2] = STORE => c_m[i] = Cpu[i].Collection /\ o_m[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
\* I still think I am going to have to use the pc to reason about what happens in the previous step when our Pc is set to LOAD (e.g.)    

      


           
MS_Inv6 == \A i \in ProcSet: Cpu[i].Pc[1] = UBER => Cpu[i].Pc[2] \notin {LEGLOAD, LEGSTORE}

MS_Inv7 == \A i \in ProcSet:
           /\ Cpu[i].Pc[2] = CS => memory.Mem_uobjcollection[Cpu[i].Collection].memuobj[Cpu[i].Object].lock = 1
           /\ (Cpu[1].Collection = Cpu[2].Collection /\ Cpu[1].Object = Cpu[2].Object) => Cpu[1].Pc[2] # CS \/ Cpu[2].Pc[2] # CS




THEOREM Spec => []MS_Inv1 
<1>1 Init => MS_Inv1
  <2> SUFFICES ASSUME Init,
                      NEW i \in 1..MAXCPUS
               PROVE  /\ Cpu[i].Pc[2] = LOAD => c_[i] = Cpu[i].Collection /\ o_[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
                      /\ Cpu[i].Pc[2] = STORE => c_m[i] = Cpu[i].Collection /\ o_m[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
    BY DEF MS_Inv1
  <2>1. Cpu[i].Pc[2] = LOAD => c_[i] = Cpu[i].Collection /\ o_[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
    BY DEF Init, MS_Inv1, MAXCPUS, LOAD
  <2>2. Cpu[i].Pc[2] = STORE => c_m[i] = Cpu[i].Collection /\ o_m[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
    BY DEF Init, MS_Inv1, MAXCPUS, STORE
  <2>3. QED
    BY <2>1, <2>2
<1>2 MS_Inv1 /\ [Next]_vars => MS_Inv1'
  <2> SUFFICES ASSUME MS_Inv1,
                      Next
               PROVE  MS_Inv1'
    BY DEF MS_Inv1, vars
  <2>1. CASE one
    BY <2>1 DEF MS_Inv1, one, A_
  <2>2. CASE two
     BY <2>2 DEF MS_Inv1, two, A
  <2>3. CASE \E self \in ProcSet:  \/ memory_load(self) \/ memory_store(self)
                                   \/ Cpu_process(self) \/ Legacy_code(self)
                                   \/ Uobjcollection_code(self)
                                   \/ Uobject_code(self)
                                   \/ Uobject_code_legacy_func(self)
    <3> SUFFICES ASSUME NEW self \in ProcSet,
                        \/ memory_load(self) \/ memory_store(self)
                        \/ Cpu_process(self) \/ Legacy_code(self)
                        \/ Uobjcollection_code(self)
                        \/ Uobject_code(self)
                        \/ Uobject_code_legacy_func(self)
                 PROVE  MS_Inv1'
      BY <2>3 
    <3>1. CASE Start_(self)
      BY <2>3, <3>1 DEF MS_Inv1, Start_
    <3>2. CASE Load_Legacy(self)
      BY <2>3, <3>2 DEF MS_Inv1, Load_Legacy, LEGLOAD, LOAD, STORE
    <3>3. CASE LL_Done(self)  (*** Cpu[i].Pc[2] = 0 ***) (* Need p_[self] \in {1,2}? *)
      <4>1 \E self_1 \in {1} \cup {2} : Cpu'
          = [Cpu EXCEPT
               ![p_[self]] = [Cpu[p_[self]] EXCEPT
                                !.Pc = [Cpu[p_[self]].Pc EXCEPT ![2] = 0]]]
        BY <2>3, <3>3 DEF MS_Inv1, LL_Done, LOAD, STORE, MAXCPUS, ProcSet
      <4>2 CASE (Cpu[1].Pc[2] = 0)' /\ (Cpu[2].Pc[2] = 0)'
        BY <4>1, <2>3, <3>3, <4>2 DEF MS_Inv1, LL_Done, LOAD, STORE, MAXCPUS, ProcSet
      <4> QED BY <4>1, <4>2, <2>3, <3>3 DEF MS_Inv1, LL_Done, LOAD, STORE, MAXCPUS, ProcSet
    <3>4. CASE Load(self)     (*** Cpu[i].Pc[2] = LOAD ***) (* o and c set in call to load, object and collection set before that *)
      BY <2>3, <3>4 DEF MS_Inv1, Load, LOAD, STORE
    <3>5. CASE L_Done(self)   (*** Cpu[i].Pc[2] = 0 ***)
      BY <2>3, <3>5 DEF MS_Inv1, L_Done, LOAD, STORE
    <3>6. CASE Start_m(self)
      BY <2>3, <3>6 DEF MS_Inv1, Start_m
    <3>7. CASE Store_Legacy(self)
      BY <2>3, <3>7 DEF MS_Inv1, Store_Legacy, LEGSTORE, LOAD, STORE
    <3>8. CASE LS_Done(self)  (* Like above 3 *)
      BY <2>3, <3>8 DEF MS_Inv1, LS_Done, LOAD, STORE
    <3>9. CASE Store(self)
      BY <2>3, <3>9 DEF MS_Inv1, Store, LOAD, STORE
    <3>10. CASE S_Done(self)
      BY <2>3, <3>10 DEF MS_Inv1, S_Done, LOAD, STORE
    <3>11. CASE Start_C(self) (* [Cpu[p_C[self]] EXCEPT !.Pr = LEGACY], add obvious fact *)
      BY <2>3, <3>11 DEF MS_Inv1, Start_C
    <3>12. CASE Call_(self)
      BY <2>3, <3>12 DEF MS_Inv1, Call_
    <3>13. CASE Collection(self)   (* !.Collection = collection_[self] *)
      BY <2>3, <3>13 DEF MS_Inv1, Collection
    <3>14. CASE After_branching(self)
      BY <2>3, <3>14 DEF MS_Inv1, After_branching
    <3>15. CASE Start_L(self)
      BY <2>3, <3>15 DEF MS_Inv1, Start_L
    <3>16. CASE Loop(self)  (* [Cpu[p_L[self]] EXCEPT !.Collection = col] *)
      BY <2>3, <3>16 DEF MS_Inv1, Loop
    <3>17. CASE Start_U(self)
      BY <2>3, <3>17 DEF MS_Inv1, Start_U
    <3>18. CASE Call(self)  (* [Cpu[p_U[self]] EXCEPT !.Object = object] *)
      BY <2>3, <3>18 DEF MS_Inv1, Call
    <3>19. CASE Return(self)  (* [Cpu[p_U[self]].Pc EXCEPT ![1] = saved_pc_U[self]] *)
      BY <2>3, <3>19 DEF MS_Inv1, Return
    <3>20. CASE Start_Uo(self)  (* Cpu' = [Cpu EXCEPT ![p_Uo[self]].Pc[1] = UBER] *)
      BY <2>3, <3>20 DEF MS_Inv1, Start_Uo
    <3>21. CASE CS_Start(self)  (* [Cpu[p_Uo[self]].Pc EXCEPT ![2] = CS] *)
      BY <2>3, <3>21 DEF MS_Inv1, CS_Start
    <3>22. CASE CS_Loop(self)
      BY <2>3, <3>22 DEF MS_Inv1, CS_Loop
    <3>23. CASE CS_Read(self) (* c_, o_ *)
      BY <2>3, <3>23 DEF MS_Inv1, CS_Read
    <3>24. CASE CS_Write(self) (* c_m, o_m *)
      BY <2>3, <3>24 DEF MS_Inv1, CS_Write
    <3>25. CASE CS_Exit(self) (* Cpu Pc 2 = 0 *)
      BY <2>3, <3>25 DEF MS_Inv1, CS_Exit
    <3>26. CASE CS_Unlock(self) (* Cpu saved_pc *)
      BY <2>3, <3>26 DEF MS_Inv1, CS_Unlock
    <3>27. CASE End_(self)
      BY <2>3, <3>27 DEF MS_Inv1, End_
    <3>28. CASE Start(self) (* Cpu Pc 1 = Legacy *)
      BY <2>3, <3>28 DEF MS_Inv1, Start
    <3>29. CASE End(self)  (* Cpu Pc 1 = saved_pc *)
      BY <2>3, <3>29 DEF MS_Inv1, End
    <3>30. QED
      BY <2>3, <3>1, <3>10, <3>11, <3>12, <3>13, <3>14, <3>15, <3>16, <3>17, <3>18, <3>19, <3>2, <3>20, <3>21, <3>22, <3>23, <3>24, <3>25, <3>26, <3>27, <3>28, <3>29, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Cpu_process, Legacy_code, Uobjcollection_code, Uobject_code, Uobject_code_legacy_func, memory_load, memory_store
  <2>4. CASE Terminating
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Next
<1> QED BY <1>1, <1>2, PTL DEF Spec







THEOREM Spec => []MS_Inv1 
<1>1 Init => MS_Inv1
  <2> SUFFICES ASSUME Init,
                      NEW i \in 1..MAXCPUS
               PROVE  /\ Cpu[i].Pc[2] = LOAD => c_[i] = Cpu[i].Collection /\ o_[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
                      /\ Cpu[i].Pc[2] = STORE => c_m[i] = Cpu[i].Collection /\ o_m[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
    BY DEF MS_Inv1
  <2>1. Cpu[i].Pc[2] = LOAD => c_[i] = Cpu[i].Collection /\ o_[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
    BY DEF Init, MS_Inv1, MAXCPUS, LOAD
  <2>2. Cpu[i].Pc[2] = STORE => c_m[i] = Cpu[i].Collection /\ o_m[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
    BY DEF Init, MS_Inv1, MAXCPUS, STORE
  <2>3. QED
    BY <2>1, <2>2
<1>2 MS_Inv1 /\ [Next]_vars => MS_Inv1'
  <2> SUFFICES ASSUME MS_Inv1, Next PROVE MS_Inv1'
    BY DEF MS_Inv1, vars
  <2>1. CASE one
    BY <2>1 DEF one, A_, MS_Inv1
  <2>2. CASE two
    BY <2>2 DEF two, A, MS_Inv1
  <2>3. ASSUME NEW self \in ProcSet,
               \/ memory_load(self) \/ memory_store(self)
               \/ Cpu_process(self) \/ Legacy_code(self)
               \/ Uobjcollection_code(self)
               \/ Uobject_code(self)
               \/ Uobject_code_legacy_func(self)
        PROVE  MS_Inv1'
    <3>1. CASE memory_load(self)
      <4>1. CASE Start_(self)
      <4>2. CASE Load_Legacy(self)
      <4>3. CASE LL_Done(self)
      <4>4. CASE Load(self)
      <4>5. CASE L_Done(self)
      <4>6. QED
        BY <3>1, <4>1, <4>2, <4>3, <4>4, <4>5 DEF memory_load
    <3>2. CASE memory_store(self)
    <3>3. CASE Cpu_process(self)
    <3>4. CASE Legacy_code(self)
    <3>5. CASE Start_U(self)
    <3>6. CASE Call(self)
    <3>7. CASE Return(self)
    <3>8. CASE Start_Uo(self)
    <3>9. CASE CS_Start(self)
    <3>10. CASE CS_Loop(self)
    <3>11. CASE CS_Read(self)
    <3>12. CASE CS_Write(self)
    <3>13. CASE CS_Exit(self)
    <3>14. CASE CS_Unlock(self)
    <3>15. CASE End_(self)
    <3>16. CASE Start(self)
    <3>17. CASE End(self)
    <3>18. QED
      BY <2>3, <3>1, <3>10, <3>11, <3>12, <3>13, <3>14, <3>15, <3>16, <3>17, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Uobjcollection_code, Uobject_code, Uobject_code_legacy_func
  <2>4. CASE Terminating
  <2>5. CASE UNCHANGED vars
  <2>6. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, vars
<1> QED BY <1>1, <1>2, PTL DEF Spec






THEOREM Spec => []MS_Inv1
<1>1. Init => MS_Inv1
  <2>1 SUFFICES ASSUME Init PROVE MS_Inv1
    BY DEF Init, MS_Inv1
  <2>2 MS_Inv1
    <3> SUFFICES ASSUME NEW i \in 1..MAXCPUS
                 PROVE  /\ Cpu[i].Pc[2] = LOAD => c_[i] = Cpu[i].Collection /\ o_[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
                        /\ Cpu[i].Pc[2] = STORE => c_m[i] = Cpu[i].Collection /\ o_m[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
      BY DEF MS_Inv1
    <3>1. Cpu[i].Pc[2] = LOAD => c_[i] = Cpu[i].Collection /\ o_[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
      BY <2>1 DEF Init, MS_Inv1, MAXCPUS, STORE, LOAD
    <3>2. Cpu[i].Pc[2] = STORE => c_m[i] = Cpu[i].Collection /\ o_m[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER
      BY <2>1 DEF Init, MS_Inv1, MAXCPUS, STORE, LOAD
    <3>3. QED
      BY <3>1, <3>2   
  <2> QED BY <2>2 DEF Init, MS_Inv1
<1>2. MS_Inv1 /\ [Next]_vars => MS_Inv1'
  <2>1 SUFFICES ASSUME MS_Inv1, Next PROVE MS_Inv1'
    BY DEFS MS_Inv1, vars
  <2>2 MS_Inv1'
    <3>1 CASE A
      BY <2>1, <3>1 DEF A, MS_Inv1
    <3>2 CASE A_
      BY <2>1, <3>2 DEF A_, MS_Inv1
    <3>3 CASE \E i \in ProcSet : memory_load(i)
      <4>1 CASE \E i \in ProcSet : Start_(i)
        BY <2>1, <3>3, <4>1 DEF Start_, MS_Inv1
      <4>2 CASE \E i \in ProcSet : Load_Legacy(i)
        BY <2>1, <3>3, <4>2 DEF Load_Legacy, MS_Inv1, LEGLOAD, LOAD, STORE
      <4>3 CASE \E i \in ProcSet : LL_Done(i) \* NEED obvious fact (p_[i] \in ProcSet) (TypeOK) (shouldn't need because the index shouldn't matter)
        <5> \E i \in ProcSet : (Cpu[p_[i]].Pc[2] = 0)' (*WHY?*)
          BY <2>1, <3>3, <4>3 DEF LL_Done, MS_Inv1, LOAD, ProcSet
        <5>a CASE \A i \in ProcSet : p_[i] = 1
          BY <2>1, <3>3, <4>3, <5>a(*, (Cpu[p_[i]].Pc[2] = 0)'*) DEF LL_Done, MS_Inv1, LOAD, ProcSet
        <5> QED BY <2>1, <3>3, <4>3 DEF LL_Done, MS_Inv1, LOAD, STORE, ProcSet
      <4>4 CASE \E i \in ProcSet : Load(i) (** MUST say something about Start (previous step), to get values of parameters **)
        BY <2>1, <3>3, <4>4 DEF Load, MS_Inv1
      <4>5 CASE \E i \in ProcSet : L_Done(i) \* same <4>3
        BY <2>1, <3>3, <4>5 DEF L_Done, MS_Inv1, LEGLOAD, LOAD, STORE, ProcSet
      <4> QED BY <2>1, <3>3, <4>1, <4>2, <4>3, <4>4, <4>5 DEF memory_load
    <3>4 CASE \E i \in ProcSet : memory_store(i)
      <4>1 CASE \E i \in ProcSet : Start_m(i) \* Reason about l[i]
        <5>1 (\A i \in ProcSet : c_[i] = Cpu[i].Collection)'
          BY <2>1, <3>4, <4>1 DEF Start_m, MS_Inv1, ProcSet
        <5>2 (\A i \in ProcSet : o_[i] = Cpu[i].Object)'
          BY <2>1, <3>4, <4>1 DEF Start_m, MS_Inv1, ProcSet
        <5> QED BY <5>1, <5>2 DEF MS_Inv1
      <4>2 CASE \E i \in ProcSet : Store_Legacy(i)
        BY <2>1, <3>4, <4>2 DEF Store_Legacy, MS_Inv1
      <4>3 CASE \E i \in ProcSet : Store(i)
        BY <2>1, <3>4, <4>3 DEF Store, MS_Inv1
      <4> QED BY <2>1, <3>4, <4>1, <4>2, <4>3 DEF MS_Inv1, memory_store
    <3>5 CASE \E i \in ProcSet : Cpu_process(i)
      <4>1 CASE \E i \in ProcSet : Start_C(i)
        BY <2>1, <3>5, <4>1 DEF Start_C, MS_Inv1
      <4>2 CASE \E i \in ProcSet : Call_(i)
        BY <2>1, <3>5, <4>2 DEF Call_, MS_Inv1
      <4>3 CASE \E i \in ProcSet : After_branching(i)
        BY <2>1, <3>5, <4>3 DEF After_branching, MS_Inv1
      <4> QED BY <2>1, <3>5, <4>1, <4>2, <4>3 DEF MS_Inv1, Cpu_process
    <3>6 CASE \E i \in ProcSet : Legacy_code(i)
      <4>1 CASE \E i \in ProcSet : Start_L(i)
        BY <2>1, <3>6, <4>1 DEF Start_L, MS_Inv1
      <4>2 CASE \E i \in ProcSet : Loop(i)
        BY <2>1, <3>6, <4>2 DEF Loop, MS_Inv1
      <4> QED BY <2>1, <3>6, <4>1, <4>2 DEF MS_Inv1, Legacy_code
    <3>7 CASE \E i \in ProcSet : Uobjcollection_code(i)
      <4>1 CASE \E i \in ProcSet : Start_U(i)
        BY <2>1, <3>7, <4>1 DEF Start_U, MS_Inv1
      <4>2 CASE \E i \in ProcSet : Call(i)
        BY <2>1, <3>7, <4>2 DEF Call, MS_Inv1
      <4>3 CASE \E i \in ProcSet : Return(i)
        BY <2>1, <3>7, <4>3 DEF Return, MS_Inv1
      <4> QED BY <2>1, <3>7, <4>1, <4>2, <4>3 DEF MS_Inv1, Uobjcollection_code
    <3>8 CASE \E i \in ProcSet : Uobject_code(i)
      <4>1 CASE \E i \in ProcSet : Start_Uo(i)
        BY <2>1, <3>8, <4>1 DEF Start_Uo, MS_Inv1
      <4>3 CASE \E i \in ProcSet : CS_Loop(i)
        BY <2>1, <3>8, <4>3 DEF CS_Loop, MS_Inv1
      <4>4 CASE \E i \in ProcSet : CS_Read(i)
        BY <2>1, <3>8, <4>4 DEF CS_Read, MS_Inv1
      <4>5 CASE \E i \in ProcSet : CS_Write(i)
        BY <2>1, <3>8, <4>5 DEF CS_Write, MS_Inv1
      <4>6 CASE \E i \in ProcSet : CS_Loop(i)
        BY <2>1, <3>8, <4>6 DEF CS_Exit, MS_Inv1
      <4>7 CASE \E i \in ProcSet : CS_Exit(i)
        BY <2>1, <3>8, <4>7 DEF CS_Unlock, MS_Inv1
      <4>8 CASE \E i \in ProcSet : End_(i)
        BY <2>1, <3>8, <4>8 DEF End_, MS_Inv1
      <4> QED BY <2>1, <3>8, <4>1, (*<4>2,*) <4>3, <4>4, <4>5, <4>6, <4>7, <4>8
                 DEF MS_Inv1, Uobject_code
    <3>9 CASE \E i \in ProcSet : Uobject_code_legacy_func(i)
      <4>1 CASE \E i \in ProcSet : Start(i)
        BY <2>1, <3>9, <4>1 DEF Start, MS_Inv1
      <4>2 CASE \E i \in ProcSet : End(i)
        BY <2>1, <3>9, <4>2 DEF End, MS_Inv1
      <4> QED BY <2>1, <3>9, <4>1, <4>2 DEF MS_Inv1, Uobject_code_legacy_func
    <3>10 CASE \E i \in ProcSet : Terminating
      BY <2>1, <3>10 DEF Terminating, MS_Inv1, ProcSet, vars
    <3> QED BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10
          DEF Next, MS_Inv1, one, two
  <2> QED BY <2>2 DEF MS_Inv1
<1> QED
  BY <1>1, <1>2, PTL DEF Spec
  
  
THEOREM Spec => []MS_Inv6
<1>1. Init => MS_Inv6
  <2>1 SUFFICES ASSUME Init PROVE MS_Inv6
    BY DEF Init, MS_Inv6
  <2>2 MS_Inv6
    BY <2>1 DEF Init, MS_Inv6, ProcSet
  <2> QED BY <2>2 DEF Init, MS_Inv6
<1>2. MS_Inv6 /\ [Next]_vars => MS_Inv6'
  <2>1 SUFFICES ASSUME MS_Inv6, Next PROVE MS_Inv6'
    BY DEFS MS_Inv6, vars
  <2>2 MS_Inv6'
    <3>1 CASE A
      BY <2>1, <3>1 DEF A, MS_Inv6
    <3>2 CASE A_
      BY <2>1, <3>2 DEF A_, MS_Inv6
    <3>3 CASE \E i \in ProcSet : memory_load(i)
      <4>1 CASE \E i \in ProcSet : Start_(i)
        BY <2>1, <3>3, <4>1 DEF Start_, MS_Inv6
      <4>2 CASE \E i \in ProcSet : Load_Legacy(i)
        BY <2>1, <3>3, <4>2 DEF Load_Legacy, MS_Inv6
      <4>3 CASE \E i \in ProcSet : Load(i)
        BY <2>1, <3>3, <4>3 DEF Load, MS_Inv6
      <4> QED BY <2>1, <3>3, <4>1, <4>2, <4>3 DEF MS_Inv6, memory_load
    <3>4 CASE \E i \in ProcSet : memory_store(i)
      <4>1 CASE \E i \in ProcSet : Start_m(i)
        <5>1 (\A i \in ProcSet : c_[i] = Cpu[i].Collection)'
          BY <2>1, <3>4, <4>1 DEF Start_m, MS_Inv6, ProcSet
        <5>2 (\A i \in ProcSet : o_[i] = Cpu[i].Object)'
          BY <2>1, <3>4, <4>1 DEF Start_m, MS_Inv6, ProcSet
        <5> QED BY <5>1, <5>2 DEF MS_Inv6
      <4>2 CASE \E i \in ProcSet : Store_Legacy(i)
        BY <2>1, <3>4, <4>2 DEF Store_Legacy, MS_Inv6
      <4>3 CASE \E i \in ProcSet : Store(i)
        BY <2>1, <3>4, <4>3 DEF Store, MS_Inv6
      <4> QED BY <2>1, <3>4, <4>1, <4>2, <4>3 DEF MS_Inv6, memory_store
    <3>5 CASE \E i \in ProcSet : Cpu_process(i)
      <4>1 CASE \E i \in ProcSet : Start_C(i)
        BY <2>1, <3>5, <4>1 DEF Start_C, MS_Inv6
      <4>2 CASE \E i \in ProcSet : Call_(i)
        BY <2>1, <3>5, <4>2 DEF Call_, MS_Inv6
      <4>3 CASE \E i \in ProcSet : After_branching(i)
        BY <2>1, <3>5, <4>3 DEF After_branching, MS_Inv6
      <4> QED BY <2>1, <3>5, <4>1, <4>2, <4>3 DEF MS_Inv6, Cpu_process
    <3>6 CASE \E i \in ProcSet : Legacy_code(i)
      <4>1 CASE (*\A i \in ProcSet :*) Start_L(1)
        <5>1 (pc[1] \notin {"Load_Legacy", "Store_Legacy"})'
          BY <4>1 DEF ProcSet, Start_L, MS_Inv6
        <5>2 (pc[2] \notin {"Load_Legacy", "Store_Legacy"})' \/ (Cpu[2].Pc # "Uber")'
          <6>1 CASE pc[2] \notin {"Load_Legacy", "Store_Legacy"}
            \* more cases?
          <6>2 CASE Cpu[2].Pc # "Uber"
          <6> QED BY <6>1, <6>2
        <5> QED BY <2>1, <3>6, <4>1, <5>1, <5>2 DEF Start_L, MS_Inv6, ProcSet
      <4>2 CASE \E i \in ProcSet : Loop(i)
        BY <2>1, <3>6, <4>2 DEF Loop, MS_Inv6
      <4> QED BY <2>1, <3>6, <4>1, <4>2 DEF MS_Inv6, Legacy_code
    <3>7 CASE \E i \in ProcSet : Uobjcollection_code(i)
      <4>1 CASE \E i \in ProcSet : Start_U(i)
        BY <2>1, <3>7, <4>1 DEF Start_U, MS_Inv6
      <4>2 CASE \E i \in ProcSet : Call(i)
        BY <2>1, <3>7, <4>2 DEF Call, MS_Inv6
      <4>3 CASE \E i \in ProcSet : Return(i)
        BY <2>1, <3>7, <4>3 DEF Return, MS_Inv6
      <4> QED BY <2>1, <3>7, <4>1, <4>2, <4>3 DEF MS_Inv6, Uobjcollection_code
    <3>8 CASE \E i \in ProcSet : Uobject_code(i)
      <4>1 CASE \E i \in ProcSet : Start_Uo(i)
        BY <2>1, <3>8, <4>1 DEF Start_Uo, MS_Inv6
      <4>3 CASE \E i \in ProcSet : CS_Loop(i)
        BY <2>1, <3>8, <4>3 DEF CS_Loop, MS_Inv6
      <4>4 CASE \E i \in ProcSet : CS_Write(i)
        BY <2>1, <3>8, <4>4 DEF CS_Write, MS_Inv6
      <4>5 CASE \E i \in ProcSet : CS_Read(i)
        BY <2>1, <3>8, <4>5 DEF CS_Read, MS_Inv6
      <4>6 CASE \E i \in ProcSet : CS_Exit(i)
        BY <2>1, <3>8, <4>6 DEF CS_Exit, MS_Inv6
      <4>7 CASE \E i \in ProcSet : CS_Unlock(i)
        BY <2>1, <3>8, <4>7 DEF CS_Unlock, MS_Inv6
      <4>8 CASE \E i \in ProcSet : End_(i)
        BY <2>1, <3>8, <4>8 DEF End_, MS_Inv6
      <4> QED BY <2>1, <3>8, <4>1, (*<4>2,*) <4>3, <4>4, <4>5, <4>6, <4>7, <4>8
                 DEF MS_Inv6, Uobject_code
    <3>9 CASE \E i \in ProcSet : Uobject_code_legacy_func(i)
      <4>1 CASE \E i \in ProcSet : Start(i)
        BY <2>1, <3>9, <4>1 DEF Start, MS_Inv6
      <4>2 CASE \E i \in ProcSet : End(i)
        BY <2>1, <3>9, <4>2 DEF End, MS_Inv6
      <4> QED BY <2>1, <3>9, <4>1, <4>2 DEF MS_Inv6, Uobject_code_legacy_func
    <3>10 CASE \E i \in ProcSet : Terminating
      BY <2>1, <3>10 DEF Terminating, MS_Inv6, ProcSet, vars
    <3> QED BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10
          DEF Next, MS_Inv6, one, two
  <2> QED BY <2>2 DEF MS_Inv6
<1> QED
  BY <1>1, <1>2, PTL DEF Spec
  
THEOREM Spec => []MS_Inv7
<1>1. Init => MS_Inv7
  <2>1 SUFFICES ASSUME Init PROVE MS_Inv7
    BY DEF Init, MS_Inv7
  <2>2 MS_Inv7
    <3>1 \A i \in ProcSet: pc[i] = "CS_Loop" => ((memory.Mem_uobjcollection)[Cpu[i].Collection].memuobj)[Cpu[i].Object].lock = 1
      BY <2>1 DEF Init, ProcSet
    <3>2 pc[1] # "CS_Loop" \/ pc[2] # "CS_Loop"
      <4>1 pc[1] = "A_"
        BY <2>1 DEF Init, ProcSet
      <4>2 pc[2] = "A"
        BY <2>1 DEF Init, ProcSet
      <4> QED BY <2>1, <4>1, <4>2 DEF Init, ProcSet
    <3> QED BY <2>1, <3>1, <3>2 DEF Init, MS_Inv7, ProcSet
  <2> QED BY <2>2 DEF Init, MS_Inv7
<1>2. MS_Inv7 /\ [Next]_vars => MS_Inv7'
  <2>1 SUFFICES ASSUME MS_Inv7, Next PROVE MS_Inv7'
    BY DEFS MS_Inv7, vars
  <2>2 MS_Inv7'
    <3>1 CASE A
      BY <2>1, <3>1 DEF A, MS_Inv7
    <3>2 CASE A_
      BY <2>1, <3>2 DEF A_, MS_Inv7
    <3>3 CASE \E i \in ProcSet : memory_load(i)
      <4>1 CASE \E i \in ProcSet : Start_(i)
        BY <2>1, <3>3, <4>1 DEF Start_, MS_Inv7
      <4>2 CASE \E i \in ProcSet : Load_Legacy(i)
        BY <2>1, <3>3, <4>2 DEF Load_Legacy, MS_Inv7
      <4>3 CASE \E i \in ProcSet : Load(i)
        BY <2>1, <3>3, <4>3 DEF Load, MS_Inv7
      <4> QED BY <2>1, <3>3, <4>1, <4>2, <4>3 DEF MS_Inv7, memory_load
    <3>4 CASE \E i \in ProcSet : memory_store(i)
      <4>1 CASE \E i \in ProcSet : Start_m(i)
        <5>1 (\A i \in ProcSet : c_[i] = Cpu[i].Collection)'
          BY <2>1, <3>4, <4>1 DEF Start_m, MS_Inv7, ProcSet
        <5>2 (\A i \in ProcSet : o_[i] = Cpu[i].Object)'
          BY <2>1, <3>4, <4>1 DEF Start_m, MS_Inv7, ProcSet
        <5> QED BY <5>1, <5>2 DEF MS_Inv7
      <4>2 CASE \E i \in ProcSet : Store_Legacy(i)
        BY <2>1, <3>4, <4>2 DEF Store_Legacy, MS_Inv7
      <4>3 CASE \E i \in ProcSet : Store(i)
        BY <2>1, <3>4, <4>3 DEF Store, MS_Inv7
      <4> QED BY <2>1, <3>4, <4>1, <4>2, <4>3 DEF MS_Inv7, memory_store
    <3>5 CASE \E i \in ProcSet : Cpu_process(i)
      <4>1 CASE \E i \in ProcSet : Start_C(i)
        BY <2>1, <3>5, <4>1 DEF Start_C, MS_Inv7
      <4>2 CASE \E i \in ProcSet : Call_(i)
        BY <2>1, <3>5, <4>2 DEF Call_, MS_Inv7
      <4>3 CASE \E i \in ProcSet : After_branching(i)
        BY <2>1, <3>5, <4>3 DEF After_branching, MS_Inv7
      <4> QED BY <2>1, <3>5, <4>1, <4>2, <4>3 DEF MS_Inv7, Cpu_process
    <3>6 CASE \E i \in ProcSet : Legacy_code(i)
      <4>1 CASE \E i \in ProcSet : Start_L(i)
        BY <2>1, <3>6, <4>1 DEF Start_L, MS_Inv7
      <4>2 CASE \E i \in ProcSet : Loop(i)
        BY <2>1, <3>6, <4>2 DEF Loop, MS_Inv7
      <4> QED BY <2>1, <3>6, <4>1, <4>2 DEF MS_Inv7, Legacy_code
    <3>7 CASE \E i \in ProcSet : Uobjcollection_code(i)
      <4>1 CASE \E i \in ProcSet : Start_U(i)
        BY <2>1, <3>7, <4>1 DEF Start_U, MS_Inv7
      <4>2 CASE \E i \in ProcSet : Call(i)
        BY <2>1, <3>7, <4>2 DEF Call, MS_Inv7
      <4>3 CASE \E i \in ProcSet : Return(i)
        BY <2>1, <3>7, <4>3 DEF Return, MS_Inv7
      <4> QED BY <2>1, <3>7, <4>1, <4>2, <4>3 DEF MS_Inv7, Uobjcollection_code
    <3>8 CASE \E i \in ProcSet : Uobject_code(i)
      <4>1 CASE \E i \in ProcSet : Start_Uo(i)
        BY <2>1, <3>8, <4>1 DEF Start_Uo, MS_Inv7
      <4>3 CASE \E i \in ProcSet : CS_Loop(i)
        BY <2>1, <3>8, <4>3 DEF CS_Loop, MS_Inv7
      <4>4 CASE \E i \in ProcSet : CS_Loop(i)
        BY <2>1, <3>8, <4>4 DEF CS_Write, MS_Inv7
      <4>5 CASE \E i \in ProcSet : CS_Write(i)
        BY <2>1, <3>8, <4>5 DEF CS_Read, MS_Inv7
      <4>6 CASE \E i \in ProcSet : CS_Read(i)
        BY <2>1, <3>8, <4>6 DEF CS_Exit, MS_Inv7
      <4>7 CASE \E i \in ProcSet : CS_Exit(i)
        BY <2>1, <3>8, <4>7 DEF CS_Unlock, MS_Inv7
      <4>8 CASE \E i \in ProcSet : End_(i)
        BY <2>1, <3>8, <4>8 DEF End_, MS_Inv7
      <4> QED BY <2>1, <3>8, <4>1, (*<4>2,*) <4>3, <4>4, <4>5, <4>6, <4>7, <4>8
                 DEF MS_Inv7, Uobject_code
    <3>9 CASE \E i \in ProcSet : Uobject_code_legacy_func(i)
      <4>1 CASE \E i \in ProcSet : Start(i)
        BY <2>1, <3>9, <4>1 DEF Start, MS_Inv7
      <4>2 CASE \E i \in ProcSet : End(i)
        BY <2>1, <3>9, <4>2 DEF End, MS_Inv7
      <4> QED BY <2>1, <3>9, <4>1, <4>2 DEF MS_Inv7, Uobject_code_legacy_func
    <3>10 CASE \E i \in ProcSet : Terminating
      BY <2>1, <3>10 DEF Terminating, MS_Inv7, ProcSet, vars
    <3> QED BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10
          DEF Next, MS_Inv7, one, two
  <2> QED BY <2>2 DEF MS_Inv7
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

=============================================================================
\* Modification History
\* Last modified Tue Jun 08 13:04:17 PDT 2021 by uber
\* Created Thu Jun 03 04:38:11 PDT 2021 by uber
