---- MODULE cmodel ----
EXTENDS TLC, Sequences, Integers
CONSTANTS MAXUOBJCOLLECTIONS, MAXUOBJSWITHINCOLLECTION


MAXCPUS == 2

LEGACY == 1
SENTINEL == 2
UBER == 3

LOAD == 1
STORE == 2
LEGLOAD == 3
LEGSTORE == 4
CS == 5


(*--algorithm squares
variables
    Cpu = [cp \in 1..MAXCPUS |->
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
    Cpu[p].Pc[2] := STORE; \* pc[i] # store => Cpu[i].Pc[2] # STORE
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



end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "dbfba9ae" /\ chksum(tla) = "abfda124")
\* Label Start of procedure memory_load at line 52 col 1 changed to Start_
\* Label Start of procedure memory_store at line 71 col 1 changed to Start_m
\* Label Start of procedure Cpu_process at line 96 col 5 changed to Start_C
\* Label Call of procedure Cpu_process at line 102 col 9 changed to Call_
\* Label Start of procedure Legacy_code at line 122 col 5 changed to Start_L
\* Label Start of procedure Uobjcollection_code at line 150 col 5 changed to Start_U
\* Label Start of procedure Uobject_code at line 170 col 5 changed to Start_Uo
\* Label End of procedure Uobject_code at line 206 col 5 changed to End_
\* Label A of process one at line 220 col 5 changed to A_
\* Procedure variable collection of procedure Cpu_process at line 93 col 15 changed to collection_
\* Parameter p of procedure memory_load at line 50 col 23 changed to p_
\* Parameter c of procedure memory_load at line 50 col 26 changed to c_
\* Parameter o of procedure memory_load at line 50 col 29 changed to o_
\* Parameter l of procedure memory_load at line 50 col 32 changed to l_
\* Parameter p of procedure memory_store at line 69 col 24 changed to p_m
\* Parameter c of procedure memory_store at line 69 col 27 changed to c_m
\* Parameter o of procedure memory_store at line 69 col 30 changed to o_m
\* Parameter p of procedure Cpu_process at line 92 col 23 changed to p_C
\* Parameter p of procedure Legacy_code at line 118 col 23 changed to p_L
\* Parameter saved_pc of procedure Legacy_code at line 118 col 26 changed to saved_pc_
\* Parameter p of procedure Uobjcollection_code at line 148 col 31 changed to p_U
\* Parameter c of procedure Uobjcollection_code at line 148 col 34 changed to c_U
\* Parameter saved_pc of procedure Uobjcollection_code at line 148 col 37 changed to saved_pc_U
\* Parameter p of procedure Uobject_code at line 165 col 24 changed to p_Uo
\* Parameter saved_pc of procedure Uobject_code at line 165 col 33 changed to saved_pc_Uo
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
        /\ Cpu = [cp \in 1..MAXCPUS |->
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

MS_Inv1 == \A i \in 1..MAXCPUS:
           /\ Cpu[i].Pc[2] = LOAD => (c_[i] = Cpu[i].Collection /\ o_[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER) \/ l_[i]
           /\ Cpu[i].Pc[2] = STORE => (c_m[i] = Cpu[i].Collection /\ o_m[i] = Cpu[i].Object /\ Cpu[i].Pc[1] = UBER) \/ l[i]
\* I still think I am going to have to use the pc to reason about what happens in the previous step when our Pc is set to LOAD (e.g.)    
(** changed to account for legacy call **)
      
           
MS_Inv6 == \A i \in ProcSet: Cpu[i].Pc[1] = UBER => Cpu[i].Pc[2] \notin {LEGLOAD, LEGSTORE}

MS_Inv7 == \A i \in ProcSet:
           /\ Cpu[i].Pc[2] = CS => memory.Mem_uobjcollection[Cpu[i].Collection].memuobj[Cpu[i].Object].lock = 1
           /\ (Cpu[1].Collection = Cpu[2].Collection /\ Cpu[1].Object = Cpu[2].Object) => Cpu[1].Pc[2] # CS \/ Cpu[2].Pc[2] # CS


====

