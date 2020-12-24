---------------------------- MODULE uSpark_basic ----------------------------
EXTENDS TLC, Sequences, Integers, MMU_TLB
CONSTANTS MAXCPUS, MAXUOBJCOLLECTIONS, MAXUOBJSWITHINCOLLECTION, MAXUOBJCOLLECTIONSTACKSIZE, MAXUOBJDEVMMIO,
            func_set, maxvars
E(n) == IF n \in MAXCPUS THEN TRUE ELSE FALSE
R(n) == 1..n

LEGACY == -1
SENTINEL == 0
UBER == 1


(*Mem_Integrity == [](\A c \in 1..MAXUOBJCOLLECTIONS: \A o \in 1..MAXUOBJSWITHINCOLLECTION: 
                    memory.memuobjcollection[c].memuobjs[o].Local = o)
*)
\*CF_Integrity_1 == [](\A l \in 1..MAXCPUS: ~((Cpu[l].Pc = LEGACY ~> Cpu[l].Pc > 0) \/ (Cpu[l].Pc > 0 ~> Cpu[l].Pc = LEGACY))) \* express next, not leads to
(*CF_Integrity_2 == [](\A l \in 1..MAXCPUS: ((Cpu[l].Pc = LEGACY ~> Cpu[l].Pc > 0) => Cpu[l].Pc = LEGACY ~> Cpu[l].Pc = SENTINEL /\
                    (Cpu[l].Pc > 0 ~> Cpu[l].Pc = LEGACY) => Cpu[l].Pc = LEGACY ~> Cpu[l].Pc = SENTINEL)
*)
\*Mem_Integrity == []()

Until(A, B) == ([](A \/ B) /\ <>B) \/ B             \* A Until B (without second disjunct, behavior doesn't end with B, with, who knows?)
Buffer(A, B, C) == [](A => (Until((A /\ ~C), B)))   \* If A leads to C, B must occur between A and C
\*CFI == [](\A p \in 1..MAXCPUS: Buffer(LEGACY, SENTINEL, UBER) /\ Buffer(UBER, SENTINEL, LEGACY))

(* --algorithm execution
variables cpu = MAXCPUS, \* for test iterating through CPUs
          \*collection \in 1..MAXUOBJCOLLECTIONS,
          \*object \in 1.. MAXUOBJSWITHINCOLLECTION,
    Cpu = [cp \in 1..MAXCPUS |->
            [Id |-> cp,                              \* unique CPU identifier
             Pc |-> -2,
             Pr |-> 0,                              \* program counter (currently abstracted to object control
             Shared_cpustate |-> [r \in 1..3 |-> 0], \*{},\*<<1,2,3>>,
             Legacy_cpustate |-> [r \in 1..3 |-> 0], \*{},\*<<4,5,6>>,
             Res_cpustate |-> [m \in 1..MAXUOBJCOLLECTIONS |->
                 [n \in 1..MAXUOBJSWITHINCOLLECTION |-> {}]
             ]
            ]
          ],
             
    memory = [Mem_legacy |-> 0,
              memuobjcollection |-> [co \in 1..MAXUOBJCOLLECTIONS |->
                [Uobject_stack |-> [s \in (1..MAXCPUS) \X (1..MAXUOBJCOLLECTIONSTACKSIZE) |-> {}],
                 memuobj |-> [o \in 1..MAXUOBJSWITHINCOLLECTION |->
                   [\*Uobj_ssa |-> [ssa \in 1..MAXCPUS |-> {}],               \* state save for area Uobj_code[]
                    \*Uobj_code |-> {},                                       
                    \*Uobj_data |-> {},
                    \*Uobj_dmadata |-> {},                                    
                    \*Uobj_devmmio |-> [dev \in 1..MAXUOBJDEVMMIO |-> {}],    \* uobject device end-point pads
                    Global |-> 0,
                    Local |-> o,
                    Device |-> 0,
                    System |-> 0]
                  ]
                ]
               ]
             ];            
             

(* p = processor ID *)
procedure Cpu_process(p) begin
Start:
    either
        Cpu[p].Pr := LEGACY;
        call Legacy_code(p);
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

(* p = processor ID *)
procedure Legacy_code(p) begin
Start:
    Cpu[p].Pc := LEGACY;           \* guest has control
Loop:
    while TRUE do
        either
            with coll \in 1..MAXUOBJCOLLECTIONS do
                call Uobjcollection_code(p, coll, LEGACY);     \* call uObject
            end with;
        or
            skip;                                   \* Execute code from memory.mem_legacy[]
        or 
            memory.Mem_legacy := LEGACY;                \* Read/write to memory.mem_legacy[]
            skip;
        or  
            with pr \in 1..MAXCPUS, r \in {1,2,3} do
                Cpu[pr].Shared_cpustate[r] := LEGACY; \* Read/write to cpu[x].shared_cpustate[]
            end with;
        or  
            \*** WRITE TO MORE THAN 1? ***\
            with pr \in 1..MAXCPUS, r \in {1,2,3} do
                Cpu[pr].Legacy_cpustate[r] := LEGACY; \* Read/write to cpu[x].legacy_cpustate[]
            end with;
        or  
            return; 
        end either;
    end while;
end procedure;

(* to replace uObject call in Legacy_cope()? *)
procedure Entry_sentinel(x,y) begin
Start:
    Cpu[x].Pc := SENTINEL; \*** WHY DID I PUT THIS HERE? ***\
Privilege_up:
    Cpu[p].Pr := UBER;
    call Uobjcollection_code(x, y, LEGACY);
end procedure;

(* to replace uObject call in Legacy_cope()? *)
procedure Exit_sentinel(x,y) begin
Start:
    Cpu[x].Pc := SENTINEL; \*** WHY DID I PUT THIS HERE? ***\
Privilege_down:
    Cpu[p].Pr := LEGACY;
PC_Legacy:
    Cpu[x].Pc := LEGACY;
end procedure;
 
(* I am temporarily passing in PC right now, could set *)
procedure Uobjcollection_code(p, c, saved_pc) begin
Start:
    Cpu[p].Pc := p;
    with o \in 1..MAXUOBJCOLLECTIONS do (* Should this be all of them? *)
        call Uobject_code(p, c, o);
    end with;
Return:
    Cpu[p].Pc := saved_pc; \* pc_pre_uobjectcollection_code;
\*Cpu_assign:
\*    Cpu[x].Sp := 0;  \* sp_pre_uobjectcollection_code;
    return;
end procedure;

procedure Uobject_code(x, y, z)
    variables Uobject_code_c_func = func_set,       \* {f1..fn}, \* are these in these sets, or equal to these sets
        Uobject_code_casm_func = func_set,          \*{c1..cn}, 
        Uobject_code_legacy_func = func_set,        \*{l1..ln},
        Uobjects = {1..MAXUOBJSWITHINCOLLECTION}, 
        In_uobj = FALSE,
        Uobj_finished = FALSE; 
    begin
Start:
    if ~In_uobj then
Loop:
        while ~Uobj_finished do
            either
                with f \in Uobject_code_c_func do
                    Cpu[x].Pc :=  f; \*\in Uobject_code_c_func; \* try all?
                end with;
            or 
                with cf \in Uobject_code_casm_func do
                    Cpu[x].Pc :=  cf;\* \in Uobject_code_casm_func;
                end with;
            or  
                with l \in Uobject_code_legacy_func do
                    Cpu[x].Pc := l;\* \in Uobject_code_legacy_func;
                end with;
            or 
                (*cpu[x].uobjcoll_cpustate[y].uobj_cpustate[z].res_cpustate[] := z; *) (*TODO*)
                
                skip;
            or 
                memory.memuobjcollection[y].memuobj[z].Local(*uobj_data*) := z;
                skip;
            or 
                \*Read/write memory.memuobjcollection[y].uobject_stack[x][] within extent of local_frame 
                skip;
            or 
                Uobj_finished := TRUE;
            end either;
        end while;
    end if;
Uobj_finished_assign:
    Uobj_finished := FALSE;
    In_uobj := FALSE;
    Cpu[x].Pc := 0;\*pc_pre_uobject_code;
Cpu_assign:
    \*Cpu[x].Sp := 0;\*sp_pre_uobject_code; NO SP FOR NOW
    return;
end procedure;

procedure Uobject_code_c_func(x, y, z)
    variables cfunc_finished, in_cfunc (*??*);
    begin
Start:
    if ~in_cfunc then
Loop:
        while ~cfunc_finished do 
            either
                with f \in Uobject_code_c_func do
                    Cpu[x].Pc :=  f; \*\in Uobject_code_c_func; \* try all?
                end with;
            or 
                with cf \in Uobject_code_casm_func do
                Cpu[x].Pc :=  cf;\* \in Uobject_code_casm_func;
                end with;
            or  
                with l \in Uobject_code_legacy_func do
                    Cpu[x].Pc := l;\* \in Uobject_code_legacy_func;
                end with; 
            or 
                \*Read/write cpu[x].uobjcoll_cpustate[y].uobj_cpustate[z].res_cpustate[]
                skip; 
            or 
                \*Read/write memory.memuobjcollection[y].memuobj[z].uobj_data 
                skip;
            or 
                \*Read/write memory.memuobjcollection[y].uobject_stack[x][] within extent of local_frame 
                skip;
            or 
                cfunc_finished := TRUE;
            end either;
        end while;
    end if;
Cfunc_finished_assign:
    cfunc_finished := FALSE; 
    in_cfunc := FALSE; (* Where declared / assigned to? *)
    Cpu[x].Pc := 0;\*pc_pre_cfunc_code;
\*Cpu_assign: 
    \*Cpu[x].Sp := 0;\*sp_pre_cfunc_code;   NO SP FOR NOW
\*End:
    \*return;   TODO
end procedure;

procedure Uobject_code_casm_func(x, y, z)
    variable casmfunc_finished, in_casmfunc (*??*);
    begin
Start: 
    if ~in_casmfunc then
Loop:
        while ~casmfunc_finished do
            either
                with f \in Uobject_code_c_func do
                    Cpu[x].Pc :=  f; \*\in Uobject_code_c_func; \* try all?
                end with;
            or 
                with cf \in Uobject_code_casm_func do
                Cpu[x].Pc :=  cf;\* \in Uobject_code_casm_func;
                end with;
            or  
                with l \in Uobject_code_legacy_func do
                    Cpu[x].Pc := l;\* \in Uobject_code_legacy_func;
                end with;
            or
                \*Read/write cpu[x].uobjcoll_cpustate[y].uobj_cpustate[z].res_cpustate[] 
                skip;
            or
                \*Read/write memory.memuobjcollection[y].memuobj[z].uobj_data 
                skip;
            or
                \*Read/write memory.memuobjcollection[y].uobject_stack[x][] within extent of local_frame 
                skip;
            or
                casmfunc_finished := TRUE; 
            end either;
        end while;
        casmfunc_finished := FALSE;
        in_casmfunc := FALSE; (* Where declared / assigned to? *)
        Cpu[x].Pc := 0;\*pc_pre_casmfunc_code;
\*Cpu_assign:
        \*Cpu[x].Sp := 0;\*sp_pre_casmfunc_code;    NO SP FOR NOW
    end if;
\*End:
    \*return;
end procedure;

procedure Uobject_code_legacy_func(x,y,z) begin
Start:
    memory.memuobjcollection[y].uobject_sssa[x].sp := Cpu[x].sp;
Memory_assign:
    memory.memuobjcollection[y].uobject_sssa[x].lr := Cpu[x].lr;
Memory_assign_pc:
    memory.memuobjcollection[y].uobject_sssa[x].pc := 0;\*pc_pre_legacy_func;
    Cpu[x].Lr := 0;\*resumelegacy; (*??*)
Cpu_assign:
    Cpu[x].Pc := 0;\*legacy_code; (*??*)
\*Resumelegacy:
    \*Cpu[x].Sp := memory.memuobjcollection[y].uobject_sssa[x].sp;  NO SP FOR NOW
Cpu_assign_pc:
    Cpu[x].Pc := memory.memuobjcollection[y].uobject_sssa[x].pc;
    \*return;
end procedure;

procedure device_process(x) begin
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
end procedure;

begin
Loop:
while cpu > 0 do
    call Cpu_process(cpu);
Dec:
    cpu := cpu - 1;
end while;

end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-af4e2ae39ac9dc6ffda1922e0e9f2f2f
\* Label Start of procedure Cpu_process at line 64 col 5 changed to Start_
\* Label Start of procedure Legacy_code at line 81 col 5 changed to Start_L
\* Label Loop of procedure Legacy_code at line 83 col 5 changed to Loop_
\* Label Start of procedure Entry_sentinel at line 111 col 5 changed to Start_E
\* Label Start of procedure Exit_sentinel at line 120 col 5 changed to Start_Ex
\* Label Start of procedure Uobjcollection_code at line 130 col 5 changed to Start_U
\* Label Start of procedure Uobject_code at line 150 col 5 changed to Start_Uo
\* Label Loop of procedure Uobject_code at line 152 col 9 changed to Loop_U
\* Label Cpu_assign of procedure Uobject_code at line 186 col 5 changed to Cpu_assign_
\* Label Start of procedure Uobject_code_c_func at line 193 col 5 changed to Start_Uob
\* Label Loop of procedure Uobject_code_c_func at line 195 col 9 changed to Loop_Uo
\* Label Start of procedure Uobject_code_casm_func at line 236 col 5 changed to Start_Uobj
\* Label Loop of procedure Uobject_code_casm_func at line 238 col 9 changed to Loop_Uob
\* Label Loop of procedure device_process at line 293 col 5 changed to Loop_d
\* Procedure Uobject_code_c_func at line 189 col 1 changed to Uobject_code_c_func_
\* Procedure Uobject_code_casm_func at line 232 col 1 changed to Uobject_code_casm_func_
\* Procedure Uobject_code_legacy_func at line 274 col 1 changed to Uobject_code_legacy_func_
\* Parameter p of procedure Cpu_process at line 62 col 23 changed to p_
\* Parameter p of procedure Legacy_code at line 79 col 23 changed to p_L
\* Parameter x of procedure Entry_sentinel at line 109 col 26 changed to x_
\* Parameter y of procedure Entry_sentinel at line 109 col 28 changed to y_
\* Parameter x of procedure Exit_sentinel at line 118 col 25 changed to x_E
\* Parameter y of procedure Exit_sentinel at line 118 col 27 changed to y_E
\* Parameter x of procedure Uobject_code at line 141 col 24 changed to x_U
\* Parameter y of procedure Uobject_code at line 141 col 27 changed to y_U
\* Parameter z of procedure Uobject_code at line 141 col 30 changed to z_
\* Parameter x of procedure Uobject_code_c_func at line 189 col 31 changed to x_Uo
\* Parameter y of procedure Uobject_code_c_func at line 189 col 34 changed to y_Uo
\* Parameter z of procedure Uobject_code_c_func at line 189 col 37 changed to z_U
\* Parameter x of procedure Uobject_code_casm_func at line 232 col 34 changed to x_Uob
\* Parameter y of procedure Uobject_code_casm_func at line 232 col 37 changed to y_Uob
\* Parameter z of procedure Uobject_code_casm_func at line 232 col 40 changed to z_Uo
\* Parameter x of procedure Uobject_code_legacy_func at line 274 col 36 changed to x_Uobj
CONSTANT defaultInitValue
VARIABLES cpu, Cpu, memory, pc, stack, p_, p_L, x_, y_, x_E, y_E, p, c, 
          saved_pc, x_U, y_U, z_, Uobject_code_c_func, Uobject_code_casm_func, 
          Uobject_code_legacy_func, Uobjects, In_uobj, Uobj_finished, x_Uo, 
          y_Uo, z_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
          casmfunc_finished, in_casmfunc, x_Uobj, y, z, x

vars == << cpu, Cpu, memory, pc, stack, p_, p_L, x_, y_, x_E, y_E, p, c, 
           saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
           Uobject_code_casm_func, Uobject_code_legacy_func, Uobjects, 
           In_uobj, Uobj_finished, x_Uo, y_Uo, z_U, cfunc_finished, in_cfunc, 
           x_Uob, y_Uob, z_Uo, casmfunc_finished, in_casmfunc, x_Uobj, y, z, 
           x >>

Init == (* Global variables *)
        /\ cpu = MAXCPUS
        /\ Cpu = [cp \in 1..MAXCPUS |->
                   [Id |-> cp,
                    Pc |-> -2,
                    Pr |-> 0,
                    Shared_cpustate |-> [r \in 1..3 |-> 0],
                    Legacy_cpustate |-> [r \in 1..3 |-> 0],
                    Res_cpustate |-> [m \in 1..MAXUOBJCOLLECTIONS |->
                        [n \in 1..MAXUOBJSWITHINCOLLECTION |-> {}]
                    ]
                   ]
                 ]
        /\ memory = [Mem_legacy |-> 0,
                     memuobjcollection |-> [co \in 1..MAXUOBJCOLLECTIONS |->
                       [Uobject_stack |-> [s \in (1..MAXCPUS) \X (1..MAXUOBJCOLLECTIONSTACKSIZE) |-> {}],
                        memuobj |-> [o \in 1..MAXUOBJSWITHINCOLLECTION |->
                          [
                    
                    
                    
                    
                           Global |-> 0,
                           Local |-> o,
                           Device |-> 0,
                           System |-> 0]
                         ]
                       ]
                      ]
                    ]
        (* Procedure Cpu_process *)
        /\ p_ = defaultInitValue
        (* Procedure Legacy_code *)
        /\ p_L = defaultInitValue
        (* Procedure Entry_sentinel *)
        /\ x_ = defaultInitValue
        /\ y_ = defaultInitValue
        (* Procedure Exit_sentinel *)
        /\ x_E = defaultInitValue
        /\ y_E = defaultInitValue
        (* Procedure Uobjcollection_code *)
        /\ p = defaultInitValue
        /\ c = defaultInitValue
        /\ saved_pc = defaultInitValue
        (* Procedure Uobject_code *)
        /\ x_U = defaultInitValue
        /\ y_U = defaultInitValue
        /\ z_ = defaultInitValue
        /\ Uobject_code_c_func = func_set
        /\ Uobject_code_casm_func = func_set
        /\ Uobject_code_legacy_func = func_set
        /\ Uobjects = {1..MAXUOBJSWITHINCOLLECTION}
        /\ In_uobj = FALSE
        /\ Uobj_finished = FALSE
        (* Procedure Uobject_code_c_func_ *)
        /\ x_Uo = defaultInitValue
        /\ y_Uo = defaultInitValue
        /\ z_U = defaultInitValue
        /\ cfunc_finished = defaultInitValue
        /\ in_cfunc = defaultInitValue
        (* Procedure Uobject_code_casm_func_ *)
        /\ x_Uob = defaultInitValue
        /\ y_Uob = defaultInitValue
        /\ z_Uo = defaultInitValue
        /\ casmfunc_finished = defaultInitValue
        /\ in_casmfunc = defaultInitValue
        (* Procedure Uobject_code_legacy_func_ *)
        /\ x_Uobj = defaultInitValue
        /\ y = defaultInitValue
        /\ z = defaultInitValue
        (* Procedure device_process *)
        /\ x = defaultInitValue
        /\ stack = << >>
        /\ pc = "Loop"

Start_ == /\ pc = "Start_"
          /\ \/ /\ Cpu' = [Cpu EXCEPT ![p_].Pr = LEGACY]
                /\ /\ p_L' = p_
                   /\ stack' = << [ procedure |->  "Legacy_code",
                                    pc        |->  Head(stack).pc,
                                    p_L       |->  p_L ] >>
                                \o Tail(stack)
                /\ pc' = "Start_L"
                /\ UNCHANGED <<p, c, saved_pc>>
             \/ /\ \E col \in 1..MAXUOBJCOLLECTIONS:
                     /\ Cpu' = [Cpu EXCEPT ![p_].Pr = UBER]
                     /\ /\ c' = col
                        /\ p' = p_
                        /\ saved_pc' = 0
                        /\ stack' = << [ procedure |->  "Uobjcollection_code",
                                         pc        |->  "After_branching",
                                         p         |->  p,
                                         c         |->  c,
                                         saved_pc  |->  saved_pc ] >>
                                     \o stack
                     /\ pc' = "Start_U"
                /\ p_L' = p_L
          /\ UNCHANGED << cpu, memory, p_, x_, y_, x_E, y_E, x_U, y_U, z_, 
                          Uobject_code_c_func, Uobject_code_casm_func, 
                          Uobject_code_legacy_func, Uobjects, In_uobj, 
                          Uobj_finished, x_Uo, y_Uo, z_U, cfunc_finished, 
                          in_cfunc, x_Uob, y_Uob, z_Uo, casmfunc_finished, 
                          in_casmfunc, x_Uobj, y, z, x >>

After_branching == /\ pc = "After_branching"
                   /\ pc' = Head(stack).pc
                   /\ p_' = Head(stack).p_
                   /\ stack' = Tail(stack)
                   /\ UNCHANGED << cpu, Cpu, memory, p_L, x_, y_, x_E, y_E, p, 
                                   c, saved_pc, x_U, y_U, z_, 
                                   Uobject_code_c_func, Uobject_code_casm_func, 
                                   Uobject_code_legacy_func, Uobjects, In_uobj, 
                                   Uobj_finished, x_Uo, y_Uo, z_U, 
                                   cfunc_finished, in_cfunc, x_Uob, y_Uob, 
                                   z_Uo, casmfunc_finished, in_casmfunc, 
                                   x_Uobj, y, z, x >>

Cpu_process == Start_ \/ After_branching

Start_L == /\ pc = "Start_L"
           /\ Cpu' = [Cpu EXCEPT ![p_L].Pc = LEGACY]
           /\ pc' = "Loop_"
           /\ UNCHANGED << cpu, memory, stack, p_, p_L, x_, y_, x_E, y_E, p, c, 
                           saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
                           Uobject_code_casm_func, Uobject_code_legacy_func, 
                           Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_U, 
                           cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
                           casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Loop_ == /\ pc = "Loop_"
         /\ \/ /\ \E coll \in 1..MAXUOBJCOLLECTIONS:
                    /\ /\ c' = coll
                       /\ p' = p_L
                       /\ saved_pc' = LEGACY
                       /\ stack' = << [ procedure |->  "Uobjcollection_code",
                                        pc        |->  "Loop_",
                                        p         |->  p,
                                        c         |->  c,
                                        saved_pc  |->  saved_pc ] >>
                                    \o stack
                    /\ pc' = "Start_U"
               /\ UNCHANGED <<Cpu, memory, p_L>>
            \/ /\ TRUE
               /\ pc' = "Loop_"
               /\ UNCHANGED <<Cpu, memory, stack, p_L, p, c, saved_pc>>
            \/ /\ memory' = [memory EXCEPT !.Mem_legacy = LEGACY]
               /\ TRUE
               /\ pc' = "Loop_"
               /\ UNCHANGED <<Cpu, stack, p_L, p, c, saved_pc>>
            \/ /\ \E pr \in 1..MAXCPUS:
                    \E r \in {1,2,3}:
                      Cpu' = [Cpu EXCEPT ![pr].Shared_cpustate[r] = LEGACY]
               /\ pc' = "Loop_"
               /\ UNCHANGED <<memory, stack, p_L, p, c, saved_pc>>
            \/ /\ \E pr \in 1..MAXCPUS:
                    \E r \in {1,2,3}:
                      Cpu' = [Cpu EXCEPT ![pr].Legacy_cpustate[r] = LEGACY]
               /\ pc' = "Loop_"
               /\ UNCHANGED <<memory, stack, p_L, p, c, saved_pc>>
            \/ /\ pc' = Head(stack).pc
               /\ p_L' = Head(stack).p_L
               /\ stack' = Tail(stack)
               /\ UNCHANGED <<Cpu, memory, p, c, saved_pc>>
         /\ UNCHANGED << cpu, p_, x_, y_, x_E, y_E, x_U, y_U, z_, 
                         Uobject_code_c_func, Uobject_code_casm_func, 
                         Uobject_code_legacy_func, Uobjects, In_uobj, 
                         Uobj_finished, x_Uo, y_Uo, z_U, cfunc_finished, 
                         in_cfunc, x_Uob, y_Uob, z_Uo, casmfunc_finished, 
                         in_casmfunc, x_Uobj, y, z, x >>

Legacy_code == Start_L \/ Loop_

Start_E == /\ pc = "Start_E"
           /\ Cpu' = [Cpu EXCEPT ![x_].Pc = SENTINEL]
           /\ pc' = "Privilege_up"
           /\ UNCHANGED << cpu, memory, stack, p_, p_L, x_, y_, x_E, y_E, p, c, 
                           saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
                           Uobject_code_casm_func, Uobject_code_legacy_func, 
                           Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_U, 
                           cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
                           casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Privilege_up == /\ pc = "Privilege_up"
                /\ Cpu' = [Cpu EXCEPT ![p].Pr = UBER]
                /\ /\ c' = y_
                   /\ p' = x_
                   /\ saved_pc' = LEGACY
                   /\ stack' = << [ procedure |->  "Uobjcollection_code",
                                    pc        |->  "Error",
                                    p         |->  p,
                                    c         |->  c,
                                    saved_pc  |->  saved_pc ] >>
                                \o stack
                /\ pc' = "Start_U"
                /\ UNCHANGED << cpu, memory, p_, p_L, x_, y_, x_E, y_E, x_U, 
                                y_U, z_, Uobject_code_c_func, 
                                Uobject_code_casm_func, 
                                Uobject_code_legacy_func, Uobjects, In_uobj, 
                                Uobj_finished, x_Uo, y_Uo, z_U, cfunc_finished, 
                                in_cfunc, x_Uob, y_Uob, z_Uo, 
                                casmfunc_finished, in_casmfunc, x_Uobj, y, z, 
                                x >>

Entry_sentinel == Start_E \/ Privilege_up

Start_Ex == /\ pc = "Start_Ex"
            /\ Cpu' = [Cpu EXCEPT ![x_E].Pc = SENTINEL]
            /\ pc' = "Privilege_down"
            /\ UNCHANGED << cpu, memory, stack, p_, p_L, x_, y_, x_E, y_E, p, 
                            c, saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
                            Uobject_code_casm_func, Uobject_code_legacy_func, 
                            Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_U, 
                            cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
                            casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Privilege_down == /\ pc = "Privilege_down"
                  /\ Cpu' = [Cpu EXCEPT ![p].Pr = LEGACY]
                  /\ pc' = "PC_Legacy"
                  /\ UNCHANGED << cpu, memory, stack, p_, p_L, x_, y_, x_E, 
                                  y_E, p, c, saved_pc, x_U, y_U, z_, 
                                  Uobject_code_c_func, Uobject_code_casm_func, 
                                  Uobject_code_legacy_func, Uobjects, In_uobj, 
                                  Uobj_finished, x_Uo, y_Uo, z_U, 
                                  cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
                                  casmfunc_finished, in_casmfunc, x_Uobj, y, z, 
                                  x >>

PC_Legacy == /\ pc = "PC_Legacy"
             /\ Cpu' = [Cpu EXCEPT ![x_E].Pc = LEGACY]
             /\ pc' = "Error"
             /\ UNCHANGED << cpu, memory, stack, p_, p_L, x_, y_, x_E, y_E, p, 
                             c, saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
                             Uobject_code_casm_func, Uobject_code_legacy_func, 
                             Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_U, 
                             cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
                             casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Exit_sentinel == Start_Ex \/ Privilege_down \/ PC_Legacy

Start_U == /\ pc = "Start_U"
           /\ Cpu' = [Cpu EXCEPT ![p].Pc = p]
           /\ \E o \in 1..MAXUOBJCOLLECTIONS:
                /\ /\ stack' = << [ procedure |->  "Uobject_code",
                                    pc        |->  "Return",
                                    Uobject_code_c_func |->  Uobject_code_c_func,
                                    Uobject_code_casm_func |->  Uobject_code_casm_func,
                                    Uobject_code_legacy_func |->  Uobject_code_legacy_func,
                                    Uobjects  |->  Uobjects,
                                    In_uobj   |->  In_uobj,
                                    Uobj_finished |->  Uobj_finished,
                                    x_U       |->  x_U,
                                    y_U       |->  y_U,
                                    z_        |->  z_ ] >>
                                \o stack
                   /\ x_U' = p
                   /\ y_U' = c
                   /\ z_' = o
                /\ Uobject_code_c_func' = func_set
                /\ Uobject_code_casm_func' = func_set
                /\ Uobject_code_legacy_func' = func_set
                /\ Uobjects' = {1..MAXUOBJSWITHINCOLLECTION}
                /\ In_uobj' = FALSE
                /\ Uobj_finished' = FALSE
                /\ pc' = "Start_Uo"
           /\ UNCHANGED << cpu, memory, p_, p_L, x_, y_, x_E, y_E, p, c, 
                           saved_pc, x_Uo, y_Uo, z_U, cfunc_finished, in_cfunc, 
                           x_Uob, y_Uob, z_Uo, casmfunc_finished, in_casmfunc, 
                           x_Uobj, y, z, x >>

Return == /\ pc = "Return"
          /\ Cpu' = [Cpu EXCEPT ![x].Pc = saved_pc]
          /\ pc' = Head(stack).pc
          /\ p' = Head(stack).p
          /\ c' = Head(stack).c
          /\ saved_pc' = Head(stack).saved_pc
          /\ stack' = Tail(stack)
          /\ UNCHANGED << cpu, memory, p_, p_L, x_, y_, x_E, y_E, x_U, y_U, z_, 
                          Uobject_code_c_func, Uobject_code_casm_func, 
                          Uobject_code_legacy_func, Uobjects, In_uobj, 
                          Uobj_finished, x_Uo, y_Uo, z_U, cfunc_finished, 
                          in_cfunc, x_Uob, y_Uob, z_Uo, casmfunc_finished, 
                          in_casmfunc, x_Uobj, y, z, x >>

Uobjcollection_code == Start_U \/ Return

Start_Uo == /\ pc = "Start_Uo"
            /\ IF ~In_uobj
                  THEN /\ pc' = "Loop_U"
                  ELSE /\ pc' = "Uobj_finished_assign"
            /\ UNCHANGED << cpu, Cpu, memory, stack, p_, p_L, x_, y_, x_E, y_E, 
                            p, c, saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
                            Uobject_code_casm_func, Uobject_code_legacy_func, 
                            Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_U, 
                            cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
                            casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Loop_U == /\ pc = "Loop_U"
          /\ IF ~Uobj_finished
                THEN /\ \/ /\ \E f \in Uobject_code_c_func:
                                Cpu' = [Cpu EXCEPT ![x_U].Pc = f]
                           /\ UNCHANGED <<memory, Uobj_finished>>
                        \/ /\ \E cf \in Uobject_code_casm_func:
                                Cpu' = [Cpu EXCEPT ![x_U].Pc = cf]
                           /\ UNCHANGED <<memory, Uobj_finished>>
                        \/ /\ \E l \in Uobject_code_legacy_func:
                                Cpu' = [Cpu EXCEPT ![x_U].Pc = l]
                           /\ UNCHANGED <<memory, Uobj_finished>>
                        \/ /\ TRUE
                           /\ UNCHANGED <<Cpu, memory, Uobj_finished>>
                        \/ /\ memory' = [memory EXCEPT !.memuobjcollection[y_U].memuobj[z_].Local = z_]
                           /\ TRUE
                           /\ UNCHANGED <<Cpu, Uobj_finished>>
                        \/ /\ TRUE
                           /\ UNCHANGED <<Cpu, memory, Uobj_finished>>
                        \/ /\ Uobj_finished' = TRUE
                           /\ UNCHANGED <<Cpu, memory>>
                     /\ pc' = "Loop_U"
                ELSE /\ pc' = "Uobj_finished_assign"
                     /\ UNCHANGED << Cpu, memory, Uobj_finished >>
          /\ UNCHANGED << cpu, stack, p_, p_L, x_, y_, x_E, y_E, p, c, 
                          saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
                          Uobject_code_casm_func, Uobject_code_legacy_func, 
                          Uobjects, In_uobj, x_Uo, y_Uo, z_U, cfunc_finished, 
                          in_cfunc, x_Uob, y_Uob, z_Uo, casmfunc_finished, 
                          in_casmfunc, x_Uobj, y, z, x >>

Uobj_finished_assign == /\ pc = "Uobj_finished_assign"
                        /\ Uobj_finished' = FALSE
                        /\ In_uobj' = FALSE
                        /\ Cpu' = [Cpu EXCEPT ![x_U].Pc = 0]
                        /\ pc' = "Cpu_assign_"
                        /\ UNCHANGED << cpu, memory, stack, p_, p_L, x_, y_, 
                                        x_E, y_E, p, c, saved_pc, x_U, y_U, z_, 
                                        Uobject_code_c_func, 
                                        Uobject_code_casm_func, 
                                        Uobject_code_legacy_func, Uobjects, 
                                        x_Uo, y_Uo, z_U, cfunc_finished, 
                                        in_cfunc, x_Uob, y_Uob, z_Uo, 
                                        casmfunc_finished, in_casmfunc, x_Uobj, 
                                        y, z, x >>

Cpu_assign_ == /\ pc = "Cpu_assign_"
               /\ pc' = Head(stack).pc
               /\ Uobject_code_c_func' = Head(stack).Uobject_code_c_func
               /\ Uobject_code_casm_func' = Head(stack).Uobject_code_casm_func
               /\ Uobject_code_legacy_func' = Head(stack).Uobject_code_legacy_func
               /\ Uobjects' = Head(stack).Uobjects
               /\ In_uobj' = Head(stack).In_uobj
               /\ Uobj_finished' = Head(stack).Uobj_finished
               /\ x_U' = Head(stack).x_U
               /\ y_U' = Head(stack).y_U
               /\ z_' = Head(stack).z_
               /\ stack' = Tail(stack)
               /\ UNCHANGED << cpu, Cpu, memory, p_, p_L, x_, y_, x_E, y_E, p, 
                               c, saved_pc, x_Uo, y_Uo, z_U, cfunc_finished, 
                               in_cfunc, x_Uob, y_Uob, z_Uo, casmfunc_finished, 
                               in_casmfunc, x_Uobj, y, z, x >>

Uobject_code == Start_Uo \/ Loop_U \/ Uobj_finished_assign \/ Cpu_assign_

Start_Uob == /\ pc = "Start_Uob"
             /\ IF ~in_cfunc
                   THEN /\ pc' = "Loop_Uo"
                   ELSE /\ pc' = "Cfunc_finished_assign"
             /\ UNCHANGED << cpu, Cpu, memory, stack, p_, p_L, x_, y_, x_E, 
                             y_E, p, c, saved_pc, x_U, y_U, z_, 
                             Uobject_code_c_func, Uobject_code_casm_func, 
                             Uobject_code_legacy_func, Uobjects, In_uobj, 
                             Uobj_finished, x_Uo, y_Uo, z_U, cfunc_finished, 
                             in_cfunc, x_Uob, y_Uob, z_Uo, casmfunc_finished, 
                             in_casmfunc, x_Uobj, y, z, x >>

Loop_Uo == /\ pc = "Loop_Uo"
           /\ IF ~cfunc_finished
                 THEN /\ \/ /\ \E f \in Uobject_code_c_func:
                                 Cpu' = [Cpu EXCEPT ![x_Uo].Pc = f]
                            /\ UNCHANGED cfunc_finished
                         \/ /\ \E cf \in Uobject_code_casm_func:
                                 Cpu' = [Cpu EXCEPT ![x_Uo].Pc = cf]
                            /\ UNCHANGED cfunc_finished
                         \/ /\ \E l \in Uobject_code_legacy_func:
                                 Cpu' = [Cpu EXCEPT ![x_Uo].Pc = l]
                            /\ UNCHANGED cfunc_finished
                         \/ /\ TRUE
                            /\ UNCHANGED <<Cpu, cfunc_finished>>
                         \/ /\ TRUE
                            /\ UNCHANGED <<Cpu, cfunc_finished>>
                         \/ /\ TRUE
                            /\ UNCHANGED <<Cpu, cfunc_finished>>
                         \/ /\ cfunc_finished' = TRUE
                            /\ Cpu' = Cpu
                      /\ pc' = "Loop_Uo"
                 ELSE /\ pc' = "Cfunc_finished_assign"
                      /\ UNCHANGED << Cpu, cfunc_finished >>
           /\ UNCHANGED << cpu, memory, stack, p_, p_L, x_, y_, x_E, y_E, p, c, 
                           saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
                           Uobject_code_casm_func, Uobject_code_legacy_func, 
                           Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_U, 
                           in_cfunc, x_Uob, y_Uob, z_Uo, casmfunc_finished, 
                           in_casmfunc, x_Uobj, y, z, x >>

Cfunc_finished_assign == /\ pc = "Cfunc_finished_assign"
                         /\ cfunc_finished' = FALSE
                         /\ in_cfunc' = FALSE
                         /\ Cpu' = [Cpu EXCEPT ![x_Uo].Pc = 0]
                         /\ pc' = "Error"
                         /\ UNCHANGED << cpu, memory, stack, p_, p_L, x_, y_, 
                                         x_E, y_E, p, c, saved_pc, x_U, y_U, 
                                         z_, Uobject_code_c_func, 
                                         Uobject_code_casm_func, 
                                         Uobject_code_legacy_func, Uobjects, 
                                         In_uobj, Uobj_finished, x_Uo, y_Uo, 
                                         z_U, x_Uob, y_Uob, z_Uo, 
                                         casmfunc_finished, in_casmfunc, 
                                         x_Uobj, y, z, x >>

Uobject_code_c_func_ == Start_Uob \/ Loop_Uo \/ Cfunc_finished_assign

Start_Uobj == /\ pc = "Start_Uobj"
              /\ IF ~in_casmfunc
                    THEN /\ pc' = "Loop_Uob"
                    ELSE /\ pc' = "Error"
              /\ UNCHANGED << cpu, Cpu, memory, stack, p_, p_L, x_, y_, x_E, 
                              y_E, p, c, saved_pc, x_U, y_U, z_, 
                              Uobject_code_c_func, Uobject_code_casm_func, 
                              Uobject_code_legacy_func, Uobjects, In_uobj, 
                              Uobj_finished, x_Uo, y_Uo, z_U, cfunc_finished, 
                              in_cfunc, x_Uob, y_Uob, z_Uo, casmfunc_finished, 
                              in_casmfunc, x_Uobj, y, z, x >>

Loop_Uob == /\ pc = "Loop_Uob"
            /\ IF ~casmfunc_finished
                  THEN /\ \/ /\ \E f \in Uobject_code_c_func:
                                  Cpu' = [Cpu EXCEPT ![x_Uob].Pc = f]
                             /\ UNCHANGED casmfunc_finished
                          \/ /\ \E cf \in Uobject_code_casm_func:
                                  Cpu' = [Cpu EXCEPT ![x_Uob].Pc = cf]
                             /\ UNCHANGED casmfunc_finished
                          \/ /\ \E l \in Uobject_code_legacy_func:
                                  Cpu' = [Cpu EXCEPT ![x_Uob].Pc = l]
                             /\ UNCHANGED casmfunc_finished
                          \/ /\ TRUE
                             /\ UNCHANGED <<Cpu, casmfunc_finished>>
                          \/ /\ TRUE
                             /\ UNCHANGED <<Cpu, casmfunc_finished>>
                          \/ /\ TRUE
                             /\ UNCHANGED <<Cpu, casmfunc_finished>>
                          \/ /\ casmfunc_finished' = TRUE
                             /\ Cpu' = Cpu
                       /\ pc' = "Loop_Uob"
                       /\ UNCHANGED in_casmfunc
                  ELSE /\ casmfunc_finished' = FALSE
                       /\ in_casmfunc' = FALSE
                       /\ Cpu' = [Cpu EXCEPT ![x_Uob].Pc = 0]
                       /\ pc' = "Error"
            /\ UNCHANGED << cpu, memory, stack, p_, p_L, x_, y_, x_E, y_E, p, 
                            c, saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
                            Uobject_code_casm_func, Uobject_code_legacy_func, 
                            Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_U, 
                            cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
                            x_Uobj, y, z, x >>

Uobject_code_casm_func_ == Start_Uobj \/ Loop_Uob

Start == /\ pc = "Start"
         /\ memory' = [memory EXCEPT !.memuobjcollection[y].uobject_sssa[x_Uobj].sp = Cpu[x_Uobj].sp]
         /\ pc' = "Memory_assign"
         /\ UNCHANGED << cpu, Cpu, stack, p_, p_L, x_, y_, x_E, y_E, p, c, 
                         saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
                         Uobject_code_casm_func, Uobject_code_legacy_func, 
                         Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_U, 
                         cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
                         casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Memory_assign == /\ pc = "Memory_assign"
                 /\ memory' = [memory EXCEPT !.memuobjcollection[y].uobject_sssa[x_Uobj].lr = Cpu[x_Uobj].lr]
                 /\ pc' = "Memory_assign_pc"
                 /\ UNCHANGED << cpu, Cpu, stack, p_, p_L, x_, y_, x_E, y_E, p, 
                                 c, saved_pc, x_U, y_U, z_, 
                                 Uobject_code_c_func, Uobject_code_casm_func, 
                                 Uobject_code_legacy_func, Uobjects, In_uobj, 
                                 Uobj_finished, x_Uo, y_Uo, z_U, 
                                 cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
                                 casmfunc_finished, in_casmfunc, x_Uobj, y, z, 
                                 x >>

Memory_assign_pc == /\ pc = "Memory_assign_pc"
                    /\ memory' = [memory EXCEPT !.memuobjcollection[y].uobject_sssa[x_Uobj].pc = 0]
                    /\ Cpu' = [Cpu EXCEPT ![x_Uobj].Lr = 0]
                    /\ pc' = "Cpu_assign"
                    /\ UNCHANGED << cpu, stack, p_, p_L, x_, y_, x_E, y_E, p, 
                                    c, saved_pc, x_U, y_U, z_, 
                                    Uobject_code_c_func, 
                                    Uobject_code_casm_func, 
                                    Uobject_code_legacy_func, Uobjects, 
                                    In_uobj, Uobj_finished, x_Uo, y_Uo, z_U, 
                                    cfunc_finished, in_cfunc, x_Uob, y_Uob, 
                                    z_Uo, casmfunc_finished, in_casmfunc, 
                                    x_Uobj, y, z, x >>

Cpu_assign == /\ pc = "Cpu_assign"
              /\ Cpu' = [Cpu EXCEPT ![x_Uobj].Pc = 0]
              /\ pc' = "Cpu_assign_pc"
              /\ UNCHANGED << cpu, memory, stack, p_, p_L, x_, y_, x_E, y_E, p, 
                              c, saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
                              Uobject_code_casm_func, Uobject_code_legacy_func, 
                              Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, 
                              z_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, 
                              z_Uo, casmfunc_finished, in_casmfunc, x_Uobj, y, 
                              z, x >>

Cpu_assign_pc == /\ pc = "Cpu_assign_pc"
                 /\ Cpu' = [Cpu EXCEPT ![x_Uobj].Pc = memory.memuobjcollection[y].uobject_sssa[x_Uobj].pc]
                 /\ pc' = "Error"
                 /\ UNCHANGED << cpu, memory, stack, p_, p_L, x_, y_, x_E, y_E, 
                                 p, c, saved_pc, x_U, y_U, z_, 
                                 Uobject_code_c_func, Uobject_code_casm_func, 
                                 Uobject_code_legacy_func, Uobjects, In_uobj, 
                                 Uobj_finished, x_Uo, y_Uo, z_U, 
                                 cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
                                 casmfunc_finished, in_casmfunc, x_Uobj, y, z, 
                                 x >>

Uobject_code_legacy_func_ == Start \/ Memory_assign \/ Memory_assign_pc
                                \/ Cpu_assign \/ Cpu_assign_pc

Loop_d == /\ pc = "Loop_d"
          /\ \/ /\ TRUE
                /\ pc' = "Loop_d"
                /\ UNCHANGED <<stack, x>>
             \/ /\ TRUE
                /\ pc' = "Loop_d"
                /\ UNCHANGED <<stack, x>>
             \/ /\ pc' = Head(stack).pc
                /\ x' = Head(stack).x
                /\ stack' = Tail(stack)
          /\ UNCHANGED << cpu, Cpu, memory, p_, p_L, x_, y_, x_E, y_E, p, c, 
                          saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
                          Uobject_code_casm_func, Uobject_code_legacy_func, 
                          Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_U, 
                          cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
                          casmfunc_finished, in_casmfunc, x_Uobj, y, z >>

device_process == Loop_d

Loop == /\ pc = "Loop"
        /\ IF cpu > 0
              THEN /\ /\ p_' = cpu
                      /\ stack' = << [ procedure |->  "Cpu_process",
                                       pc        |->  "Dec",
                                       p_        |->  p_ ] >>
                                   \o stack
                   /\ pc' = "Start_"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << stack, p_ >>
        /\ UNCHANGED << cpu, Cpu, memory, p_L, x_, y_, x_E, y_E, p, c, 
                        saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
                        Uobject_code_casm_func, Uobject_code_legacy_func, 
                        Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_U, 
                        cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
                        casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Dec == /\ pc = "Dec"
       /\ cpu' = cpu - 1
       /\ pc' = "Loop"
       /\ UNCHANGED << Cpu, memory, stack, p_, p_L, x_, y_, x_E, y_E, p, c, 
                       saved_pc, x_U, y_U, z_, Uobject_code_c_func, 
                       Uobject_code_casm_func, Uobject_code_legacy_func, 
                       Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_U, 
                       cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uo, 
                       casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Cpu_process \/ Legacy_code \/ Entry_sentinel \/ Exit_sentinel
           \/ Uobjcollection_code \/ Uobject_code \/ Uobject_code_c_func_
           \/ Uobject_code_casm_func_ \/ Uobject_code_legacy_func_
           \/ device_process \/ Loop \/ Dec
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-961b9449a8c98fa4a5d23d971ed018df

Mem_Integrity == [](\A c1 \in 1..MAXUOBJCOLLECTIONS: \A o \in 1..MAXUOBJSWITHINCOLLECTION: 
                    memory.memuobjcollection[c1].memuobjs[o].Local = o)
CFI == [](\A p1 \in 1..MAXCPUS: Buffer(Cpu[p1].Pc = LEGACY, Cpu[p1].Pc = SENTINEL, Cpu[p1].Pc = UBER) /\
                                Buffer(Cpu[p1].Pc = UBER, Cpu[p1].Pc = SENTINEL, Cpu[p1].Pc = LEGACY))

=============================================================================
\* Modification History
\* Last modified Wed Dec 23 09:52:21 PST 2020 by mjmccall
\* Created Thu Dec 17 08:07:51 PST 2020 by mjmccall
