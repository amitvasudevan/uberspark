---------------------------- MODULE uSpark_basic ----------------------------
EXTENDS TLC, Sequences, Integers(*, MMU_TLB*)
CONSTANTS MAXCPUS, MAXUOBJCOLLECTIONS, MAXUOBJSWITHINCOLLECTION, MAXUOBJCOLLECTIONSTACKSIZE, MAXUOBJDEVMMIO,
            func_set, maxvars
E(n) == IF n \in MAXCPUS THEN TRUE ELSE FALSE
R(n) == 1..n

LEGACY == 1
SENTINEL == 2
UBER == 3


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
             Pc |-> 0,                              \* program counter (currently abstracted to object control
             Pr |-> 0,                               \* privelege
             Shared_cpustate |-> [r \in 1..3 |-> 0], \*{},\*<<1,2,3>>,
             Legacy_cpustate |-> [r \in 1..3 |-> 0], \*{},\*<<4,5,6>>,
             Res_cpustate |-> [m \in 1..MAXUOBJCOLLECTIONS |->
                 [n \in 1..MAXUOBJSWITHINCOLLECTION |-> {}]
             ]
            ]
          ],
             
    memory = [Mem_legacy |-> 0,
              Mem_global |-> 0, 
              memuobjcollection |-> [co \in 1..MAXUOBJCOLLECTIONS |->
                [Uobject_stack |-> [s \in (1..MAXCPUS) \X (1..MAXUOBJCOLLECTIONSTACKSIZE) |-> {}],
                 memuobj |-> [o \in 1..MAXUOBJSWITHINCOLLECTION |->
                   [\*Uobj_ssa |-> [ssa \in 1..MAXCPUS |-> {}],               \* state save for area Uobj_code[]
                    \*Uobj_code |-> {},                                       
                    \*Uobj_data |-> {},
                    \*Uobj_dmadata |-> {},                                    
                    \*Uobj_devmmio |-> [dev \in 1..MAXUOBJDEVMMIO |-> {}],    \* uobject device end-point pads
                    (*Global |-> 0,
                    Local |-> o,
                    Device |-> 0,
                    System |-> 0*)
                    Mem |-> 0]
                  ]
                ]
               ]
             ],
             
    cfi = TRUE, \* for tracking CFI, any time CF is altered, check src/dest
    Pc_src = 0;         
           
\* this should be more elegant -- requires too much manual tracking of CF
procedure CFI_observer(Pc, p) begin
Start:
    if (Pc = LEGACY /\ Cpu[p].Pc = UBER) \/ (Pc = UBER /\ Cpu[p].Pc = LEGACY) then
        cfi := FALSE;
    end if;
    return;
end procedure;

(* p = processor ID *)
procedure Cpu_process(p) begin
Start:
    either
        Cpu[p].Pr := LEGACY;
        Pc_src := LEGACY;
Call:
        call Legacy_code(p);
Observe_legacy:
        call CFI_observer(Pc_src, p);
        return;
    or
        with col \in 1..MAXUOBJCOLLECTIONS do
            Cpu[p].Pr := UBER;      
            Pc_src := LEGACY;
            call Uobjcollection_code(p, col, Pc_src);
        end with;
Observe_uber:
        call CFI_observer(Pc_src, p);
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
            Pc_src := LEGACY;
            with coll \in 1..MAXUOBJCOLLECTIONS do
                call Entry_sentinel(p, coll, Pc_src, FALSE); \* FIX? and DELETE big model that was checked
                \*call Uobjcollection_code(p, coll, LEGACY);     \* call uObject
            end with;
Obs_uO:
            call CFI_observer(Pc_src, p);
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

(* call uObject from legacy, currently stands in for all entry sentinals *)
procedure Entry_sentinel(x,y,z,func) begin
Start:
    Cpu[x].Pc := SENTINEL;
    Pc_src := SENTINEL;
Privilege_up:
    Cpu[x].Pr := UBER;
    if func then
        call Uobject_code_c_func(x, y, z);
    else
        call Uobjcollection_code(x, y, LEGACY);
    end if;
Obs:
    call CFI_observer(Pc_src, p);
End:
    return;
end procedure;

(* Call legacy from uObject *)
procedure Exit_sentinel(x,y,z,func) begin
Start:
    Cpu[x].Pc := SENTINEL;
    Pc_src := SENTINEL;
Privilege_down:
    Cpu[x].Pr := LEGACY;
    if func then
        call Uobject_code_legacy_func(x,y,z);
    else
        call Legacy_code(x);
    end if;
Obs:
    call CFI_observer(Pc_src, p);
End:
    return;
end procedure;
 
(* I am temporarily passing in PC right now, could set *)
procedure Uobjcollection_code(p, c, saved_pc) begin
Start:
    Cpu[p].Pc := UBER;\*p;
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
    variables Uobject_code_c_funcs = func_set,       \* {f1..fn}, \* are these in these sets, or equal to these sets
        Uobject_code_casm_funcs = func_set,          \*{c1..cn}, 
        Uobject_code_legacy_funcs = func_set,        \*{l1..ln},
        Uobjects = {1..MAXUOBJSWITHINCOLLECTION}, 
        In_uobj = FALSE,
        Uobj_finished = FALSE; 
    begin
Start:
    if ~In_uobj then
        Pc_src := UBER;
Loop:
        while ~Uobj_finished do
            either
                (*with f \in Uobject_code_c_funcs do
                    Cpu[x].Pc :=  f; \*\in Uobject_code_c_func; \* try all?
                end with;*)
                call Uobject_code_c_func(x, y, z);
            or 
                (*with cf \in Uobject_code_casm_funcs do
                    Cpu[x].Pc :=  cf;\* \in Uobject_code_casm_func;
                end with;*)
                call Uobject_code_casm_func(x, y, z);
            or  
                (*with l \in Uobject_code_legacy_funcs do
                    Cpu[x].Pc := l;\* \in Uobject_code_legacy_func;
                end with;*)
                call Exit_sentinel(x,y,Pc_src,TRUE); \*Uobject_code_legacy_func(x,y,z);
Obs:
                call CFI_observer(Pc_src, x);
            or 
                (*cpu[x].uobjcoll_cpustate[y].uobj_cpustate[z].res_cpustate[] := z; *) (*TODO*)
                skip;
            or 
                memory.memuobjcollection[y].memuobj[z].Mem(*uobj_data*) := z;
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
\*Cpu_assign:
    \*Cpu[x].Sp := 0;\*sp_pre_uobject_code; NO SP FOR NOW
End:
    return;
end procedure;

procedure Uobject_code_c_func(x, y, z)
    variables Uobject_code_c_funcs = func_set,       \* {f1..fn}, \* are these in these sets, or equal to these sets
        Uobject_code_casm_funcs = func_set,          \*{c1..cn}, 
        Uobject_code_legacy_funcs = func_set,        \*{l1..ln},
        cfunc_finished, in_cfunc (*??*);
    begin
Start:
    if ~in_cfunc then
        Pc_src := UBER;
Loop:
        while ~cfunc_finished do 
            either
                \*with f \in Uobject_code_c_funcs do
                    \*Cpu[x].Pc :=  f; \*\in Uobject_code_c_func; \* try all?
                \*end with;
                \* Pc and function calls not this fine-grained yet
                call Uobject_code_c_func(x, y, z);
            or 
                (*with cf \in Uobject_code_casm_funcs do
                Cpu[x].Pc :=  cf;\* \in Uobject_code_casm_func;
                end with;*)
                call Uobject_code_casm_func(x, y, z);
            or  
                (*with l \in Uobject_code_legacy_funcs do
                    Cpu[x].Pc := l;\* \in Uobject_code_legacy_func;
                end with;*)
                call Exit_sentinel(x,y,Pc_src,TRUE);
Obs:
                call CFI_observer(Pc_src, x);
            or 
                \*Read/write cpu[x].uobjcoll_cpustate[y].uobj_cpustate[z].res_cpustate[]
                skip; 
            or 
                memory.memuobjcollection[y].memuobj[z].Mem(*uobj_data*) := z;
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
End:    
    return;
end procedure;

procedure Uobject_code_casm_func(x, y, z)
    variable Uobject_code_c_funcs = func_set,       \* {f1..fn}, \* are these in these sets, or equal to these sets
        Uobject_code_casm_funcs = func_set,          \*{c1..cn}, 
        Uobject_code_legacy_funcs = func_set,        \*{l1..ln},
        casmfunc_finished, in_casmfunc (*??*);
    begin
Start: 
    if ~in_casmfunc then
        Pc_src := UBER;
Loop:
        while ~casmfunc_finished do
            either
                (*with f \in Uobject_code_c_funcs do
                    Cpu[x].Pc :=  f; \*\in Uobject_code_c_func; \* try all?
                end with;*)
                call Uobject_code_c_func(x, y, z);
            or 
                (*with cf \in Uobject_code_casm_funcs do
                Cpu[x].Pc :=  cf;\* \in Uobject_code_casm_func;
                end with;*)
                call Uobject_code_casm_func(x, y, z);
            or  
               (* with l \in Uobject_code_legacy_funcs do
                    Cpu[x].Pc := l;\* \in Uobject_code_legacy_func;
                end with;*)
                call Exit_sentinel(x,y,Pc_src,TRUE);
Obs:
                call CFI_observer(Pc_src, x);
            or
                \*Read/write cpu[x].uobjcoll_cpustate[y].uobj_cpustate[z].res_cpustate[] 
                skip;
            or
                memory.memuobjcollection[y].memuobj[z].Mem(*uobj_data*) := z;
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
End:
    return;
end procedure;

procedure Uobject_code_legacy_func(x,y,z) begin
Start:
    memory.memuobjcollection[y].uobject_sssa[x].sp := Cpu[x].sp;
Memory_assign:
    memory.memuobjcollection[y].uobject_sssa[x].lr := Cpu[x].lr;
Memory_assign_pc:
    memory.memuobjcollection[y].uobject_sssa[x].Pc := z;\*pc_pre_legacy_func;
    Cpu[x].Lr := 0;\*resumelegacy; (*??*)
Cpu_assign:
    Cpu[x].Pc := LEGACY;
\*Resumelegacy:
    \*Cpu[x].Sp := memory.memuobjcollection[y].uobject_sssa[x].sp;  NO SP FOR NOW
Cpu_assign_pc:
    Cpu[x].Pc := memory.memuobjcollection[y].uobject_sssa[x].Pc;
End:
    return;
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
    return;
end procedure;

begin
Loop:
while cpu > 0 do
    call Cpu_process(cpu);
Dec:
    cpu := cpu - 1;
end while;

end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-44dcd5ce82fa9d37a8f2dda3d70d54f2
\* Label Start of procedure CFI_observer at line 69 col 5 changed to Start_
\* Label Start of procedure Cpu_process at line 78 col 5 changed to Start_C
\* Label Start of procedure Legacy_code at line 102 col 5 changed to Start_L
\* Label Loop of procedure Legacy_code at line 104 col 5 changed to Loop_
\* Label Start of procedure Entry_sentinel at line 136 col 5 changed to Start_E
\* Label Obs of procedure Entry_sentinel at line 146 col 5 changed to Obs_
\* Label End of procedure Entry_sentinel at line 148 col 5 changed to End_
\* Label Start of procedure Exit_sentinel at line 154 col 5 changed to Start_Ex
\* Label Obs of procedure Exit_sentinel at line 164 col 5 changed to Obs_E
\* Label End of procedure Exit_sentinel at line 166 col 5 changed to End_E
\* Label Start of procedure Uobjcollection_code at line 172 col 5 changed to Start_U
\* Label Start of procedure Uobject_code at line 192 col 5 changed to Start_Uo
\* Label Loop of procedure Uobject_code at line 195 col 9 changed to Loop_U
\* Label Obs of procedure Uobject_code at line 212 col 17 changed to Obs_U
\* Label End of procedure Uobject_code at line 233 col 5 changed to End_U
\* Label Start of procedure Uobject_code_c_func at line 243 col 5 changed to Start_Uob
\* Label Loop of procedure Uobject_code_c_func at line 246 col 9 changed to Loop_Uo
\* Label Obs of procedure Uobject_code_c_func at line 264 col 17 changed to Obs_Uo
\* Label End of procedure Uobject_code_c_func at line 285 col 5 changed to End_Uo
\* Label Start of procedure Uobject_code_casm_func at line 295 col 5 changed to Start_Uobj
\* Label Loop of procedure Uobject_code_casm_func at line 298 col 9 changed to Loop_Uob
\* Label End of procedure Uobject_code_casm_func at line 335 col 5 changed to End_Uob
\* Label Loop of procedure device_process at line 358 col 5 changed to Loop_d
\* Procedure variable Uobject_code_c_funcs of procedure Uobject_code at line 184 col 15 changed to Uobject_code_c_funcs_
\* Procedure variable Uobject_code_casm_funcs of procedure Uobject_code at line 185 col 9 changed to Uobject_code_casm_funcs_
\* Procedure variable Uobject_code_legacy_funcs of procedure Uobject_code at line 186 col 9 changed to Uobject_code_legacy_funcs_
\* Procedure variable Uobject_code_c_funcs of procedure Uobject_code_c_func at line 237 col 15 changed to Uobject_code_c_funcs_U
\* Procedure variable Uobject_code_casm_funcs of procedure Uobject_code_c_func at line 238 col 9 changed to Uobject_code_casm_funcs_U
\* Procedure variable Uobject_code_legacy_funcs of procedure Uobject_code_c_func at line 239 col 9 changed to Uobject_code_legacy_funcs_U
\* Parameter p of procedure CFI_observer at line 67 col 28 changed to p_
\* Parameter p of procedure Cpu_process at line 76 col 23 changed to p_C
\* Parameter p of procedure Legacy_code at line 100 col 23 changed to p_L
\* Parameter x of procedure Entry_sentinel at line 134 col 26 changed to x_
\* Parameter y of procedure Entry_sentinel at line 134 col 28 changed to y_
\* Parameter z of procedure Entry_sentinel at line 134 col 30 changed to z_
\* Parameter func of procedure Entry_sentinel at line 134 col 32 changed to func_
\* Parameter x of procedure Exit_sentinel at line 152 col 25 changed to x_E
\* Parameter y of procedure Exit_sentinel at line 152 col 27 changed to y_E
\* Parameter z of procedure Exit_sentinel at line 152 col 29 changed to z_E
\* Parameter x of procedure Uobject_code at line 183 col 24 changed to x_U
\* Parameter y of procedure Uobject_code at line 183 col 27 changed to y_U
\* Parameter z of procedure Uobject_code at line 183 col 30 changed to z_U
\* Parameter x of procedure Uobject_code_c_func at line 236 col 31 changed to x_Uo
\* Parameter y of procedure Uobject_code_c_func at line 236 col 34 changed to y_Uo
\* Parameter z of procedure Uobject_code_c_func at line 236 col 37 changed to z_Uo
\* Parameter x of procedure Uobject_code_casm_func at line 288 col 34 changed to x_Uob
\* Parameter y of procedure Uobject_code_casm_func at line 288 col 37 changed to y_Uob
\* Parameter z of procedure Uobject_code_casm_func at line 288 col 40 changed to z_Uob
\* Parameter x of procedure Uobject_code_legacy_func at line 338 col 36 changed to x_Uobj
CONSTANT defaultInitValue
VARIABLES cpu, Cpu, memory, cfi, Pc_src, pc, stack, Pc, p_, p_C, p_L, x_, y_, 
          z_, func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, y_U, z_U, 
          Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
          Uobject_code_legacy_funcs_, Uobjects, In_uobj, Uobj_finished, x_Uo, 
          y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
          Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, 
          z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, 
          Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc, x_Uobj, 
          y, z, x

vars == << cpu, Cpu, memory, cfi, Pc_src, pc, stack, Pc, p_, p_C, p_L, x_, y_, 
           z_, func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, y_U, z_U, 
           Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
           Uobject_code_legacy_funcs_, Uobjects, In_uobj, Uobj_finished, x_Uo, 
           y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
           Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, 
           y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, 
           Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc, x_Uobj, 
           y, z, x >>

Init == (* Global variables *)
        /\ cpu = MAXCPUS
        /\ Cpu = [cp \in 1..MAXCPUS |->
                   [Id |-> cp,
                    Pc |-> 0,
                    Pr |-> 0,
                    Shared_cpustate |-> [r \in 1..3 |-> 0],
                    Legacy_cpustate |-> [r \in 1..3 |-> 0],
                    Res_cpustate |-> [m \in 1..MAXUOBJCOLLECTIONS |->
                        [n \in 1..MAXUOBJSWITHINCOLLECTION |-> {}]
                    ]
                   ]
                 ]
        /\ memory = [Mem_legacy |-> 0,
                     Mem_global |-> 0,
                     memuobjcollection |-> [co \in 1..MAXUOBJCOLLECTIONS |->
                       [Uobject_stack |-> [s \in (1..MAXCPUS) \X (1..MAXUOBJCOLLECTIONSTACKSIZE) |-> {}],
                        memuobj |-> [o \in 1..MAXUOBJSWITHINCOLLECTION |->
                          [
                    
                    
                    
                    
                    
                    
                    
                    
                           Mem |-> 0]
                         ]
                       ]
                      ]
                    ]
        /\ cfi = TRUE
        /\ Pc_src = 0
        (* Procedure CFI_observer *)
        /\ Pc = defaultInitValue
        /\ p_ = defaultInitValue
        (* Procedure Cpu_process *)
        /\ p_C = defaultInitValue
        (* Procedure Legacy_code *)
        /\ p_L = defaultInitValue
        (* Procedure Entry_sentinel *)
        /\ x_ = defaultInitValue
        /\ y_ = defaultInitValue
        /\ z_ = defaultInitValue
        /\ func_ = defaultInitValue
        (* Procedure Exit_sentinel *)
        /\ x_E = defaultInitValue
        /\ y_E = defaultInitValue
        /\ z_E = defaultInitValue
        /\ func = defaultInitValue
        (* Procedure Uobjcollection_code *)
        /\ p = defaultInitValue
        /\ c = defaultInitValue
        /\ saved_pc = defaultInitValue
        (* Procedure Uobject_code *)
        /\ x_U = defaultInitValue
        /\ y_U = defaultInitValue
        /\ z_U = defaultInitValue
        /\ Uobject_code_c_funcs_ = func_set
        /\ Uobject_code_casm_funcs_ = func_set
        /\ Uobject_code_legacy_funcs_ = func_set
        /\ Uobjects = {1..MAXUOBJSWITHINCOLLECTION}
        /\ In_uobj = FALSE
        /\ Uobj_finished = FALSE
        (* Procedure Uobject_code_c_func *)
        /\ x_Uo = defaultInitValue
        /\ y_Uo = defaultInitValue
        /\ z_Uo = defaultInitValue
        /\ Uobject_code_c_funcs_U = func_set
        /\ Uobject_code_casm_funcs_U = func_set
        /\ Uobject_code_legacy_funcs_U = func_set
        /\ cfunc_finished = defaultInitValue
        /\ in_cfunc = defaultInitValue
        (* Procedure Uobject_code_casm_func *)
        /\ x_Uob = defaultInitValue
        /\ y_Uob = defaultInitValue
        /\ z_Uob = defaultInitValue
        /\ Uobject_code_c_funcs = func_set
        /\ Uobject_code_casm_funcs = func_set
        /\ Uobject_code_legacy_funcs = func_set
        /\ casmfunc_finished = defaultInitValue
        /\ in_casmfunc = defaultInitValue
        (* Procedure Uobject_code_legacy_func *)
        /\ x_Uobj = defaultInitValue
        /\ y = defaultInitValue
        /\ z = defaultInitValue
        (* Procedure device_process *)
        /\ x = defaultInitValue
        /\ stack = << >>
        /\ pc = "Loop"

Start_ == /\ pc = "Start_"
          /\ IF (Pc = LEGACY /\ Cpu[p_].Pc = UBER) \/ (Pc = UBER /\ Cpu[p_].Pc = LEGACY)
                THEN /\ cfi' = FALSE
                ELSE /\ TRUE
                     /\ cfi' = cfi
          /\ pc' = Head(stack).pc
          /\ Pc' = Head(stack).Pc
          /\ p_' = Head(stack).p_
          /\ stack' = Tail(stack)
          /\ UNCHANGED << cpu, Cpu, memory, Pc_src, p_C, p_L, x_, y_, z_, 
                          func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, y_U, 
                          z_U, Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                          Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                          Uobj_finished, x_Uo, y_Uo, z_Uo, 
                          Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                          Uobject_code_legacy_funcs_U, cfunc_finished, 
                          in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                          Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                          casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

CFI_observer == Start_

Start_C == /\ pc = "Start_C"
           /\ \/ /\ Cpu' = [Cpu EXCEPT ![p_C].Pr = LEGACY]
                 /\ Pc_src' = LEGACY
                 /\ pc' = "Call"
                 /\ UNCHANGED <<stack, p, c, saved_pc>>
              \/ /\ \E col \in 1..MAXUOBJCOLLECTIONS:
                      /\ Cpu' = [Cpu EXCEPT ![p_C].Pr = UBER]
                      /\ Pc_src' = LEGACY
                      /\ /\ c' = col
                         /\ p' = p_C
                         /\ saved_pc' = Pc_src'
                         /\ stack' = << [ procedure |->  "Uobjcollection_code",
                                          pc        |->  "Observe_uber",
                                          p         |->  p,
                                          c         |->  c,
                                          saved_pc  |->  saved_pc ] >>
                                      \o stack
                      /\ pc' = "Start_U"
           /\ UNCHANGED << cpu, memory, cfi, Pc, p_, p_C, p_L, x_, y_, z_, 
                           func_, x_E, y_E, z_E, func, x_U, y_U, z_U, 
                           Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                           Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                           Uobj_finished, x_Uo, y_Uo, z_Uo, 
                           Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                           Uobject_code_legacy_funcs_U, cfunc_finished, 
                           in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                           Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                           casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Call == /\ pc = "Call"
        /\ /\ p_L' = p_C
           /\ stack' = << [ procedure |->  "Legacy_code",
                            pc        |->  "Observe_legacy",
                            p_L       |->  p_L ] >>
                        \o stack
        /\ pc' = "Start_L"
        /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, Pc, p_, p_C, x_, y_, z_, 
                        func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, y_U, 
                        z_U, Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                        Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                        Uobj_finished, x_Uo, y_Uo, z_Uo, 
                        Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                        Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, 
                        x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                        Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                        casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Observe_legacy == /\ pc = "Observe_legacy"
                  /\ /\ Pc' = Pc_src
                     /\ p_' = p_C
                     /\ stack' = << [ procedure |->  "CFI_observer",
                                      pc        |->  Head(stack).pc,
                                      Pc        |->  Pc,
                                      p_        |->  p_ ] >>
                                  \o Tail(stack)
                  /\ pc' = "Start_"
                  /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, p_C, p_L, x_, 
                                  y_, z_, func_, x_E, y_E, z_E, func, p, c, 
                                  saved_pc, x_U, y_U, z_U, 
                                  Uobject_code_c_funcs_, 
                                  Uobject_code_casm_funcs_, 
                                  Uobject_code_legacy_funcs_, Uobjects, 
                                  In_uobj, Uobj_finished, x_Uo, y_Uo, z_Uo, 
                                  Uobject_code_c_funcs_U, 
                                  Uobject_code_casm_funcs_U, 
                                  Uobject_code_legacy_funcs_U, cfunc_finished, 
                                  in_cfunc, x_Uob, y_Uob, z_Uob, 
                                  Uobject_code_c_funcs, 
                                  Uobject_code_casm_funcs, 
                                  Uobject_code_legacy_funcs, casmfunc_finished, 
                                  in_casmfunc, x_Uobj, y, z, x >>

Observe_uber == /\ pc = "Observe_uber"
                /\ /\ Pc' = Pc_src
                   /\ p_' = p_C
                   /\ stack' = << [ procedure |->  "CFI_observer",
                                    pc        |->  "After_branching",
                                    Pc        |->  Pc,
                                    p_        |->  p_ ] >>
                                \o stack
                /\ pc' = "Start_"
                /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, p_C, p_L, x_, 
                                y_, z_, func_, x_E, y_E, z_E, func, p, c, 
                                saved_pc, x_U, y_U, z_U, Uobject_code_c_funcs_, 
                                Uobject_code_casm_funcs_, 
                                Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                                Uobj_finished, x_Uo, y_Uo, z_Uo, 
                                Uobject_code_c_funcs_U, 
                                Uobject_code_casm_funcs_U, 
                                Uobject_code_legacy_funcs_U, cfunc_finished, 
                                in_cfunc, x_Uob, y_Uob, z_Uob, 
                                Uobject_code_c_funcs, Uobject_code_casm_funcs, 
                                Uobject_code_legacy_funcs, casmfunc_finished, 
                                in_casmfunc, x_Uobj, y, z, x >>

After_branching == /\ pc = "After_branching"
                   /\ pc' = Head(stack).pc
                   /\ p_C' = Head(stack).p_C
                   /\ stack' = Tail(stack)
                   /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, Pc, p_, p_L, 
                                   x_, y_, z_, func_, x_E, y_E, z_E, func, p, 
                                   c, saved_pc, x_U, y_U, z_U, 
                                   Uobject_code_c_funcs_, 
                                   Uobject_code_casm_funcs_, 
                                   Uobject_code_legacy_funcs_, Uobjects, 
                                   In_uobj, Uobj_finished, x_Uo, y_Uo, z_Uo, 
                                   Uobject_code_c_funcs_U, 
                                   Uobject_code_casm_funcs_U, 
                                   Uobject_code_legacy_funcs_U, cfunc_finished, 
                                   in_cfunc, x_Uob, y_Uob, z_Uob, 
                                   Uobject_code_c_funcs, 
                                   Uobject_code_casm_funcs, 
                                   Uobject_code_legacy_funcs, 
                                   casmfunc_finished, in_casmfunc, x_Uobj, y, 
                                   z, x >>

Cpu_process == Start_C \/ Call \/ Observe_legacy \/ Observe_uber
                  \/ After_branching

Start_L == /\ pc = "Start_L"
           /\ Cpu' = [Cpu EXCEPT ![p_L].Pc = LEGACY]
           /\ pc' = "Loop_"
           /\ UNCHANGED << cpu, memory, cfi, Pc_src, stack, Pc, p_, p_C, p_L, 
                           x_, y_, z_, func_, x_E, y_E, z_E, func, p, c, 
                           saved_pc, x_U, y_U, z_U, Uobject_code_c_funcs_, 
                           Uobject_code_casm_funcs_, 
                           Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                           Uobj_finished, x_Uo, y_Uo, z_Uo, 
                           Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                           Uobject_code_legacy_funcs_U, cfunc_finished, 
                           in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                           Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                           casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Loop_ == /\ pc = "Loop_"
         /\ \/ /\ Pc_src' = LEGACY
               /\ \E coll \in 1..MAXUOBJCOLLECTIONS:
                    /\ /\ func_' = FALSE
                       /\ stack' = << [ procedure |->  "Entry_sentinel",
                                        pc        |->  "Obs_uO",
                                        x_        |->  x_,
                                        y_        |->  y_,
                                        z_        |->  z_,
                                        func_     |->  func_ ] >>
                                    \o stack
                       /\ x_' = p_L
                       /\ y_' = coll
                       /\ z_' = Pc_src'
                    /\ pc' = "Start_E"
               /\ UNCHANGED <<Cpu, memory, p_L>>
            \/ /\ TRUE
               /\ pc' = "Loop_"
               /\ UNCHANGED <<Cpu, memory, Pc_src, stack, p_L, x_, y_, z_, func_>>
            \/ /\ memory' = [memory EXCEPT !.Mem_legacy = LEGACY]
               /\ TRUE
               /\ pc' = "Loop_"
               /\ UNCHANGED <<Cpu, Pc_src, stack, p_L, x_, y_, z_, func_>>
            \/ /\ \E pr \in 1..MAXCPUS:
                    \E r \in {1,2,3}:
                      Cpu' = [Cpu EXCEPT ![pr].Shared_cpustate[r] = LEGACY]
               /\ pc' = "Loop_"
               /\ UNCHANGED <<memory, Pc_src, stack, p_L, x_, y_, z_, func_>>
            \/ /\ \E pr \in 1..MAXCPUS:
                    \E r \in {1,2,3}:
                      Cpu' = [Cpu EXCEPT ![pr].Legacy_cpustate[r] = LEGACY]
               /\ pc' = "Loop_"
               /\ UNCHANGED <<memory, Pc_src, stack, p_L, x_, y_, z_, func_>>
            \/ /\ pc' = Head(stack).pc
               /\ p_L' = Head(stack).p_L
               /\ stack' = Tail(stack)
               /\ UNCHANGED <<Cpu, memory, Pc_src, x_, y_, z_, func_>>
         /\ UNCHANGED << cpu, cfi, Pc, p_, p_C, x_E, y_E, z_E, func, p, c, 
                         saved_pc, x_U, y_U, z_U, Uobject_code_c_funcs_, 
                         Uobject_code_casm_funcs_, Uobject_code_legacy_funcs_, 
                         Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_Uo, 
                         Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                         Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, 
                         x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                         Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                         casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Obs_uO == /\ pc = "Obs_uO"
          /\ /\ Pc' = Pc_src
             /\ p_' = p_L
             /\ stack' = << [ procedure |->  "CFI_observer",
                              pc        |->  "Loop_",
                              Pc        |->  Pc,
                              p_        |->  p_ ] >>
                          \o stack
          /\ pc' = "Start_"
          /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, p_C, p_L, x_, y_, z_, 
                          func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, y_U, 
                          z_U, Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                          Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                          Uobj_finished, x_Uo, y_Uo, z_Uo, 
                          Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                          Uobject_code_legacy_funcs_U, cfunc_finished, 
                          in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                          Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                          casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Legacy_code == Start_L \/ Loop_ \/ Obs_uO

Start_E == /\ pc = "Start_E"
           /\ Cpu' = [Cpu EXCEPT ![x_].Pc = SENTINEL]
           /\ Pc_src' = SENTINEL
           /\ pc' = "Privilege_up"
           /\ UNCHANGED << cpu, memory, cfi, stack, Pc, p_, p_C, p_L, x_, y_, 
                           z_, func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, 
                           y_U, z_U, Uobject_code_c_funcs_, 
                           Uobject_code_casm_funcs_, 
                           Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                           Uobj_finished, x_Uo, y_Uo, z_Uo, 
                           Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                           Uobject_code_legacy_funcs_U, cfunc_finished, 
                           in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                           Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                           casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Privilege_up == /\ pc = "Privilege_up"
                /\ Cpu' = [Cpu EXCEPT ![x_].Pr = UBER]
                /\ IF func_
                      THEN /\ /\ stack' = << [ procedure |->  "Uobject_code_c_func",
                                               pc        |->  "Obs_",
                                               Uobject_code_c_funcs_U |->  Uobject_code_c_funcs_U,
                                               Uobject_code_casm_funcs_U |->  Uobject_code_casm_funcs_U,
                                               Uobject_code_legacy_funcs_U |->  Uobject_code_legacy_funcs_U,
                                               cfunc_finished |->  cfunc_finished,
                                               in_cfunc  |->  in_cfunc,
                                               x_Uo      |->  x_Uo,
                                               y_Uo      |->  y_Uo,
                                               z_Uo      |->  z_Uo ] >>
                                           \o stack
                              /\ x_Uo' = x_
                              /\ y_Uo' = y_
                              /\ z_Uo' = z_
                           /\ Uobject_code_c_funcs_U' = func_set
                           /\ Uobject_code_casm_funcs_U' = func_set
                           /\ Uobject_code_legacy_funcs_U' = func_set
                           /\ cfunc_finished' = defaultInitValue
                           /\ in_cfunc' = defaultInitValue
                           /\ pc' = "Start_Uob"
                           /\ UNCHANGED << p, c, saved_pc >>
                      ELSE /\ /\ c' = y_
                              /\ p' = x_
                              /\ saved_pc' = LEGACY
                              /\ stack' = << [ procedure |->  "Uobjcollection_code",
                                               pc        |->  "Obs_",
                                               p         |->  p,
                                               c         |->  c,
                                               saved_pc  |->  saved_pc ] >>
                                           \o stack
                           /\ pc' = "Start_U"
                           /\ UNCHANGED << x_Uo, y_Uo, z_Uo, 
                                           Uobject_code_c_funcs_U, 
                                           Uobject_code_casm_funcs_U, 
                                           Uobject_code_legacy_funcs_U, 
                                           cfunc_finished, in_cfunc >>
                /\ UNCHANGED << cpu, memory, cfi, Pc_src, Pc, p_, p_C, p_L, x_, 
                                y_, z_, func_, x_E, y_E, z_E, func, x_U, y_U, 
                                z_U, Uobject_code_c_funcs_, 
                                Uobject_code_casm_funcs_, 
                                Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                                Uobj_finished, x_Uob, y_Uob, z_Uob, 
                                Uobject_code_c_funcs, Uobject_code_casm_funcs, 
                                Uobject_code_legacy_funcs, casmfunc_finished, 
                                in_casmfunc, x_Uobj, y, z, x >>

Obs_ == /\ pc = "Obs_"
        /\ /\ Pc' = Pc_src
           /\ p_' = p
           /\ stack' = << [ procedure |->  "CFI_observer",
                            pc        |->  "End_",
                            Pc        |->  Pc,
                            p_        |->  p_ ] >>
                        \o stack
        /\ pc' = "Start_"
        /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, p_C, p_L, x_, y_, z_, 
                        func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, y_U, 
                        z_U, Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                        Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                        Uobj_finished, x_Uo, y_Uo, z_Uo, 
                        Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                        Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, 
                        x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                        Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                        casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

End_ == /\ pc = "End_"
        /\ pc' = Head(stack).pc
        /\ x_' = Head(stack).x_
        /\ y_' = Head(stack).y_
        /\ z_' = Head(stack).z_
        /\ func_' = Head(stack).func_
        /\ stack' = Tail(stack)
        /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, Pc, p_, p_C, p_L, x_E, 
                        y_E, z_E, func, p, c, saved_pc, x_U, y_U, z_U, 
                        Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                        Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                        Uobj_finished, x_Uo, y_Uo, z_Uo, 
                        Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                        Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, 
                        x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                        Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                        casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Entry_sentinel == Start_E \/ Privilege_up \/ Obs_ \/ End_

Start_Ex == /\ pc = "Start_Ex"
            /\ Cpu' = [Cpu EXCEPT ![x_E].Pc = SENTINEL]
            /\ Pc_src' = SENTINEL
            /\ pc' = "Privilege_down"
            /\ UNCHANGED << cpu, memory, cfi, stack, Pc, p_, p_C, p_L, x_, y_, 
                            z_, func_, x_E, y_E, z_E, func, p, c, saved_pc, 
                            x_U, y_U, z_U, Uobject_code_c_funcs_, 
                            Uobject_code_casm_funcs_, 
                            Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                            Uobj_finished, x_Uo, y_Uo, z_Uo, 
                            Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                            Uobject_code_legacy_funcs_U, cfunc_finished, 
                            in_cfunc, x_Uob, y_Uob, z_Uob, 
                            Uobject_code_c_funcs, Uobject_code_casm_funcs, 
                            Uobject_code_legacy_funcs, casmfunc_finished, 
                            in_casmfunc, x_Uobj, y, z, x >>

Privilege_down == /\ pc = "Privilege_down"
                  /\ Cpu' = [Cpu EXCEPT ![x_E].Pr = LEGACY]
                  /\ IF func
                        THEN /\ /\ stack' = << [ procedure |->  "Uobject_code_legacy_func",
                                                 pc        |->  "Obs_E",
                                                 x_Uobj    |->  x_Uobj,
                                                 y         |->  y,
                                                 z         |->  z ] >>
                                             \o stack
                                /\ x_Uobj' = x_E
                                /\ y' = y_E
                                /\ z' = z_E
                             /\ pc' = "Start"
                             /\ p_L' = p_L
                        ELSE /\ /\ p_L' = x_E
                                /\ stack' = << [ procedure |->  "Legacy_code",
                                                 pc        |->  "Obs_E",
                                                 p_L       |->  p_L ] >>
                                             \o stack
                             /\ pc' = "Start_L"
                             /\ UNCHANGED << x_Uobj, y, z >>
                  /\ UNCHANGED << cpu, memory, cfi, Pc_src, Pc, p_, p_C, x_, 
                                  y_, z_, func_, x_E, y_E, z_E, func, p, c, 
                                  saved_pc, x_U, y_U, z_U, 
                                  Uobject_code_c_funcs_, 
                                  Uobject_code_casm_funcs_, 
                                  Uobject_code_legacy_funcs_, Uobjects, 
                                  In_uobj, Uobj_finished, x_Uo, y_Uo, z_Uo, 
                                  Uobject_code_c_funcs_U, 
                                  Uobject_code_casm_funcs_U, 
                                  Uobject_code_legacy_funcs_U, cfunc_finished, 
                                  in_cfunc, x_Uob, y_Uob, z_Uob, 
                                  Uobject_code_c_funcs, 
                                  Uobject_code_casm_funcs, 
                                  Uobject_code_legacy_funcs, casmfunc_finished, 
                                  in_casmfunc, x >>

Obs_E == /\ pc = "Obs_E"
         /\ /\ Pc' = Pc_src
            /\ p_' = p
            /\ stack' = << [ procedure |->  "CFI_observer",
                             pc        |->  "End_E",
                             Pc        |->  Pc,
                             p_        |->  p_ ] >>
                         \o stack
         /\ pc' = "Start_"
         /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, p_C, p_L, x_, y_, z_, 
                         func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, y_U, 
                         z_U, Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                         Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                         Uobj_finished, x_Uo, y_Uo, z_Uo, 
                         Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                         Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, 
                         x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                         Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                         casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

End_E == /\ pc = "End_E"
         /\ pc' = Head(stack).pc
         /\ x_E' = Head(stack).x_E
         /\ y_E' = Head(stack).y_E
         /\ z_E' = Head(stack).z_E
         /\ func' = Head(stack).func
         /\ stack' = Tail(stack)
         /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, Pc, p_, p_C, p_L, x_, 
                         y_, z_, func_, p, c, saved_pc, x_U, y_U, z_U, 
                         Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                         Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                         Uobj_finished, x_Uo, y_Uo, z_Uo, 
                         Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                         Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, 
                         x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                         Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                         casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Exit_sentinel == Start_Ex \/ Privilege_down \/ Obs_E \/ End_E

Start_U == /\ pc = "Start_U"
           /\ Cpu' = [Cpu EXCEPT ![p].Pc = UBER]
           /\ \E o \in 1..MAXUOBJCOLLECTIONS:
                /\ /\ stack' = << [ procedure |->  "Uobject_code",
                                    pc        |->  "Return",
                                    Uobject_code_c_funcs_ |->  Uobject_code_c_funcs_,
                                    Uobject_code_casm_funcs_ |->  Uobject_code_casm_funcs_,
                                    Uobject_code_legacy_funcs_ |->  Uobject_code_legacy_funcs_,
                                    Uobjects  |->  Uobjects,
                                    In_uobj   |->  In_uobj,
                                    Uobj_finished |->  Uobj_finished,
                                    x_U       |->  x_U,
                                    y_U       |->  y_U,
                                    z_U       |->  z_U ] >>
                                \o stack
                   /\ x_U' = p
                   /\ y_U' = c
                   /\ z_U' = o
                /\ Uobject_code_c_funcs_' = func_set
                /\ Uobject_code_casm_funcs_' = func_set
                /\ Uobject_code_legacy_funcs_' = func_set
                /\ Uobjects' = {1..MAXUOBJSWITHINCOLLECTION}
                /\ In_uobj' = FALSE
                /\ Uobj_finished' = FALSE
                /\ pc' = "Start_Uo"
           /\ UNCHANGED << cpu, memory, cfi, Pc_src, Pc, p_, p_C, p_L, x_, y_, 
                           z_, func_, x_E, y_E, z_E, func, p, c, saved_pc, 
                           x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, 
                           Uobject_code_casm_funcs_U, 
                           Uobject_code_legacy_funcs_U, cfunc_finished, 
                           in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                           Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                           casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Return == /\ pc = "Return"
          /\ Cpu' = [Cpu EXCEPT ![p].Pc = saved_pc]
          /\ pc' = Head(stack).pc
          /\ p' = Head(stack).p
          /\ c' = Head(stack).c
          /\ saved_pc' = Head(stack).saved_pc
          /\ stack' = Tail(stack)
          /\ UNCHANGED << cpu, memory, cfi, Pc_src, Pc, p_, p_C, p_L, x_, y_, 
                          z_, func_, x_E, y_E, z_E, func, x_U, y_U, z_U, 
                          Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                          Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                          Uobj_finished, x_Uo, y_Uo, z_Uo, 
                          Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                          Uobject_code_legacy_funcs_U, cfunc_finished, 
                          in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                          Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                          casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Uobjcollection_code == Start_U \/ Return

Start_Uo == /\ pc = "Start_Uo"
            /\ IF ~In_uobj
                  THEN /\ Pc_src' = UBER
                       /\ pc' = "Loop_U"
                  ELSE /\ pc' = "Uobj_finished_assign"
                       /\ UNCHANGED Pc_src
            /\ UNCHANGED << cpu, Cpu, memory, cfi, stack, Pc, p_, p_C, p_L, x_, 
                            y_, z_, func_, x_E, y_E, z_E, func, p, c, saved_pc, 
                            x_U, y_U, z_U, Uobject_code_c_funcs_, 
                            Uobject_code_casm_funcs_, 
                            Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                            Uobj_finished, x_Uo, y_Uo, z_Uo, 
                            Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                            Uobject_code_legacy_funcs_U, cfunc_finished, 
                            in_cfunc, x_Uob, y_Uob, z_Uob, 
                            Uobject_code_c_funcs, Uobject_code_casm_funcs, 
                            Uobject_code_legacy_funcs, casmfunc_finished, 
                            in_casmfunc, x_Uobj, y, z, x >>

Loop_U == /\ pc = "Loop_U"
          /\ IF ~Uobj_finished
                THEN /\ \/ /\ /\ stack' = << [ procedure |->  "Uobject_code_c_func",
                                               pc        |->  "Loop_U",
                                               Uobject_code_c_funcs_U |->  Uobject_code_c_funcs_U,
                                               Uobject_code_casm_funcs_U |->  Uobject_code_casm_funcs_U,
                                               Uobject_code_legacy_funcs_U |->  Uobject_code_legacy_funcs_U,
                                               cfunc_finished |->  cfunc_finished,
                                               in_cfunc  |->  in_cfunc,
                                               x_Uo      |->  x_Uo,
                                               y_Uo      |->  y_Uo,
                                               z_Uo      |->  z_Uo ] >>
                                           \o stack
                              /\ x_Uo' = x_U
                              /\ y_Uo' = y_U
                              /\ z_Uo' = z_U
                           /\ Uobject_code_c_funcs_U' = func_set
                           /\ Uobject_code_casm_funcs_U' = func_set
                           /\ Uobject_code_legacy_funcs_U' = func_set
                           /\ cfunc_finished' = defaultInitValue
                           /\ in_cfunc' = defaultInitValue
                           /\ pc' = "Start_Uob"
                           /\ UNCHANGED <<memory, x_E, y_E, z_E, func, Uobj_finished, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                        \/ /\ /\ stack' = << [ procedure |->  "Uobject_code_casm_func",
                                               pc        |->  "Loop_U",
                                               Uobject_code_c_funcs |->  Uobject_code_c_funcs,
                                               Uobject_code_casm_funcs |->  Uobject_code_casm_funcs,
                                               Uobject_code_legacy_funcs |->  Uobject_code_legacy_funcs,
                                               casmfunc_finished |->  casmfunc_finished,
                                               in_casmfunc |->  in_casmfunc,
                                               x_Uob     |->  x_Uob,
                                               y_Uob     |->  y_Uob,
                                               z_Uob     |->  z_Uob ] >>
                                           \o stack
                              /\ x_Uob' = x_U
                              /\ y_Uob' = y_U
                              /\ z_Uob' = z_U
                           /\ Uobject_code_c_funcs' = func_set
                           /\ Uobject_code_casm_funcs' = func_set
                           /\ Uobject_code_legacy_funcs' = func_set
                           /\ casmfunc_finished' = defaultInitValue
                           /\ in_casmfunc' = defaultInitValue
                           /\ pc' = "Start_Uobj"
                           /\ UNCHANGED <<memory, x_E, y_E, z_E, func, Uobj_finished, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc>>
                        \/ /\ /\ func' = TRUE
                              /\ stack' = << [ procedure |->  "Exit_sentinel",
                                               pc        |->  "Obs_U",
                                               x_E       |->  x_E,
                                               y_E       |->  y_E,
                                               z_E       |->  z_E,
                                               func      |->  func ] >>
                                           \o stack
                              /\ x_E' = x_U
                              /\ y_E' = y_U
                              /\ z_E' = Pc_src
                           /\ pc' = "Start_Ex"
                           /\ UNCHANGED <<memory, Uobj_finished, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                        \/ /\ TRUE
                           /\ pc' = "Loop_U"
                           /\ UNCHANGED <<memory, stack, x_E, y_E, z_E, func, Uobj_finished, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                        \/ /\ memory' = [memory EXCEPT !.memuobjcollection[y_U].memuobj[z_U].Mem = z_U]
                           /\ pc' = "Loop_U"
                           /\ UNCHANGED <<stack, x_E, y_E, z_E, func, Uobj_finished, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                        \/ /\ TRUE
                           /\ pc' = "Loop_U"
                           /\ UNCHANGED <<memory, stack, x_E, y_E, z_E, func, Uobj_finished, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                        \/ /\ Uobj_finished' = TRUE
                           /\ pc' = "Loop_U"
                           /\ UNCHANGED <<memory, stack, x_E, y_E, z_E, func, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                ELSE /\ pc' = "Uobj_finished_assign"
                     /\ UNCHANGED << memory, stack, x_E, y_E, z_E, func, 
                                     Uobj_finished, x_Uo, y_Uo, z_Uo, 
                                     Uobject_code_c_funcs_U, 
                                     Uobject_code_casm_funcs_U, 
                                     Uobject_code_legacy_funcs_U, 
                                     cfunc_finished, in_cfunc, x_Uob, y_Uob, 
                                     z_Uob, Uobject_code_c_funcs, 
                                     Uobject_code_casm_funcs, 
                                     Uobject_code_legacy_funcs, 
                                     casmfunc_finished, in_casmfunc >>
          /\ UNCHANGED << cpu, Cpu, cfi, Pc_src, Pc, p_, p_C, p_L, x_, y_, z_, 
                          func_, p, c, saved_pc, x_U, y_U, z_U, 
                          Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                          Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                          x_Uobj, y, z, x >>

Obs_U == /\ pc = "Obs_U"
         /\ /\ Pc' = Pc_src
            /\ p_' = x_U
            /\ stack' = << [ procedure |->  "CFI_observer",
                             pc        |->  "Loop_U",
                             Pc        |->  Pc,
                             p_        |->  p_ ] >>
                         \o stack
         /\ pc' = "Start_"
         /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, p_C, p_L, x_, y_, z_, 
                         func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, y_U, 
                         z_U, Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                         Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                         Uobj_finished, x_Uo, y_Uo, z_Uo, 
                         Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                         Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, 
                         x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                         Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                         casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Uobj_finished_assign == /\ pc = "Uobj_finished_assign"
                        /\ Uobj_finished' = FALSE
                        /\ In_uobj' = FALSE
                        /\ Cpu' = [Cpu EXCEPT ![x_U].Pc = 0]
                        /\ pc' = "End_U"
                        /\ UNCHANGED << cpu, memory, cfi, Pc_src, stack, Pc, 
                                        p_, p_C, p_L, x_, y_, z_, func_, x_E, 
                                        y_E, z_E, func, p, c, saved_pc, x_U, 
                                        y_U, z_U, Uobject_code_c_funcs_, 
                                        Uobject_code_casm_funcs_, 
                                        Uobject_code_legacy_funcs_, Uobjects, 
                                        x_Uo, y_Uo, z_Uo, 
                                        Uobject_code_c_funcs_U, 
                                        Uobject_code_casm_funcs_U, 
                                        Uobject_code_legacy_funcs_U, 
                                        cfunc_finished, in_cfunc, x_Uob, y_Uob, 
                                        z_Uob, Uobject_code_c_funcs, 
                                        Uobject_code_casm_funcs, 
                                        Uobject_code_legacy_funcs, 
                                        casmfunc_finished, in_casmfunc, x_Uobj, 
                                        y, z, x >>

End_U == /\ pc = "End_U"
         /\ pc' = Head(stack).pc
         /\ Uobject_code_c_funcs_' = Head(stack).Uobject_code_c_funcs_
         /\ Uobject_code_casm_funcs_' = Head(stack).Uobject_code_casm_funcs_
         /\ Uobject_code_legacy_funcs_' = Head(stack).Uobject_code_legacy_funcs_
         /\ Uobjects' = Head(stack).Uobjects
         /\ In_uobj' = Head(stack).In_uobj
         /\ Uobj_finished' = Head(stack).Uobj_finished
         /\ x_U' = Head(stack).x_U
         /\ y_U' = Head(stack).y_U
         /\ z_U' = Head(stack).z_U
         /\ stack' = Tail(stack)
         /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, Pc, p_, p_C, p_L, x_, 
                         y_, z_, func_, x_E, y_E, z_E, func, p, c, saved_pc, 
                         x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, 
                         Uobject_code_casm_funcs_U, 
                         Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, 
                         x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                         Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                         casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Uobject_code == Start_Uo \/ Loop_U \/ Obs_U \/ Uobj_finished_assign
                   \/ End_U

Start_Uob == /\ pc = "Start_Uob"
             /\ IF ~in_cfunc
                   THEN /\ Pc_src' = UBER
                        /\ pc' = "Loop_Uo"
                   ELSE /\ pc' = "Cfunc_finished_assign"
                        /\ UNCHANGED Pc_src
             /\ UNCHANGED << cpu, Cpu, memory, cfi, stack, Pc, p_, p_C, p_L, 
                             x_, y_, z_, func_, x_E, y_E, z_E, func, p, c, 
                             saved_pc, x_U, y_U, z_U, Uobject_code_c_funcs_, 
                             Uobject_code_casm_funcs_, 
                             Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                             Uobj_finished, x_Uo, y_Uo, z_Uo, 
                             Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                             Uobject_code_legacy_funcs_U, cfunc_finished, 
                             in_cfunc, x_Uob, y_Uob, z_Uob, 
                             Uobject_code_c_funcs, Uobject_code_casm_funcs, 
                             Uobject_code_legacy_funcs, casmfunc_finished, 
                             in_casmfunc, x_Uobj, y, z, x >>

Loop_Uo == /\ pc = "Loop_Uo"
           /\ IF ~cfunc_finished
                 THEN /\ \/ /\ /\ stack' = << [ procedure |->  "Uobject_code_c_func",
                                                pc        |->  "Loop_Uo",
                                                Uobject_code_c_funcs_U |->  Uobject_code_c_funcs_U,
                                                Uobject_code_casm_funcs_U |->  Uobject_code_casm_funcs_U,
                                                Uobject_code_legacy_funcs_U |->  Uobject_code_legacy_funcs_U,
                                                cfunc_finished |->  cfunc_finished,
                                                in_cfunc  |->  in_cfunc,
                                                x_Uo      |->  x_Uo,
                                                y_Uo      |->  y_Uo,
                                                z_Uo      |->  z_Uo ] >>
                                            \o stack
                               /\ x_Uo' = x_Uo
                               /\ y_Uo' = y_Uo
                               /\ z_Uo' = z_Uo
                            /\ Uobject_code_c_funcs_U' = func_set
                            /\ Uobject_code_casm_funcs_U' = func_set
                            /\ Uobject_code_legacy_funcs_U' = func_set
                            /\ cfunc_finished' = defaultInitValue
                            /\ in_cfunc' = defaultInitValue
                            /\ pc' = "Start_Uob"
                            /\ UNCHANGED <<memory, x_E, y_E, z_E, func, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                         \/ /\ /\ stack' = << [ procedure |->  "Uobject_code_casm_func",
                                                pc        |->  "Loop_Uo",
                                                Uobject_code_c_funcs |->  Uobject_code_c_funcs,
                                                Uobject_code_casm_funcs |->  Uobject_code_casm_funcs,
                                                Uobject_code_legacy_funcs |->  Uobject_code_legacy_funcs,
                                                casmfunc_finished |->  casmfunc_finished,
                                                in_casmfunc |->  in_casmfunc,
                                                x_Uob     |->  x_Uob,
                                                y_Uob     |->  y_Uob,
                                                z_Uob     |->  z_Uob ] >>
                                            \o stack
                               /\ x_Uob' = x_Uo
                               /\ y_Uob' = y_Uo
                               /\ z_Uob' = z_Uo
                            /\ Uobject_code_c_funcs' = func_set
                            /\ Uobject_code_casm_funcs' = func_set
                            /\ Uobject_code_legacy_funcs' = func_set
                            /\ casmfunc_finished' = defaultInitValue
                            /\ in_casmfunc' = defaultInitValue
                            /\ pc' = "Start_Uobj"
                            /\ UNCHANGED <<memory, x_E, y_E, z_E, func, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc>>
                         \/ /\ /\ func' = TRUE
                               /\ stack' = << [ procedure |->  "Exit_sentinel",
                                                pc        |->  "Obs_Uo",
                                                x_E       |->  x_E,
                                                y_E       |->  y_E,
                                                z_E       |->  z_E,
                                                func      |->  func ] >>
                                            \o stack
                               /\ x_E' = x_Uo
                               /\ y_E' = y_Uo
                               /\ z_E' = Pc_src
                            /\ pc' = "Start_Ex"
                            /\ UNCHANGED <<memory, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                         \/ /\ TRUE
                            /\ pc' = "Loop_Uo"
                            /\ UNCHANGED <<memory, stack, x_E, y_E, z_E, func, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                         \/ /\ memory' = [memory EXCEPT !.memuobjcollection[y_Uo].memuobj[z_Uo].Mem = z_Uo]
                            /\ pc' = "Loop_Uo"
                            /\ UNCHANGED <<stack, x_E, y_E, z_E, func, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                         \/ /\ TRUE
                            /\ pc' = "Loop_Uo"
                            /\ UNCHANGED <<memory, stack, x_E, y_E, z_E, func, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                         \/ /\ cfunc_finished' = TRUE
                            /\ pc' = "Loop_Uo"
                            /\ UNCHANGED <<memory, stack, x_E, y_E, z_E, func, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                 ELSE /\ pc' = "Cfunc_finished_assign"
                      /\ UNCHANGED << memory, stack, x_E, y_E, z_E, func, x_Uo, 
                                      y_Uo, z_Uo, Uobject_code_c_funcs_U, 
                                      Uobject_code_casm_funcs_U, 
                                      Uobject_code_legacy_funcs_U, 
                                      cfunc_finished, in_cfunc, x_Uob, y_Uob, 
                                      z_Uob, Uobject_code_c_funcs, 
                                      Uobject_code_casm_funcs, 
                                      Uobject_code_legacy_funcs, 
                                      casmfunc_finished, in_casmfunc >>
           /\ UNCHANGED << cpu, Cpu, cfi, Pc_src, Pc, p_, p_C, p_L, x_, y_, z_, 
                           func_, p, c, saved_pc, x_U, y_U, z_U, 
                           Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                           Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                           Uobj_finished, x_Uobj, y, z, x >>

Obs_Uo == /\ pc = "Obs_Uo"
          /\ /\ Pc' = Pc_src
             /\ p_' = x_Uo
             /\ stack' = << [ procedure |->  "CFI_observer",
                              pc        |->  "Loop_Uo",
                              Pc        |->  Pc,
                              p_        |->  p_ ] >>
                          \o stack
          /\ pc' = "Start_"
          /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, p_C, p_L, x_, y_, z_, 
                          func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, y_U, 
                          z_U, Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                          Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                          Uobj_finished, x_Uo, y_Uo, z_Uo, 
                          Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                          Uobject_code_legacy_funcs_U, cfunc_finished, 
                          in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                          Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                          casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Cfunc_finished_assign == /\ pc = "Cfunc_finished_assign"
                         /\ cfunc_finished' = FALSE
                         /\ in_cfunc' = FALSE
                         /\ Cpu' = [Cpu EXCEPT ![x_Uo].Pc = 0]
                         /\ pc' = "End_Uo"
                         /\ UNCHANGED << cpu, memory, cfi, Pc_src, stack, Pc, 
                                         p_, p_C, p_L, x_, y_, z_, func_, x_E, 
                                         y_E, z_E, func, p, c, saved_pc, x_U, 
                                         y_U, z_U, Uobject_code_c_funcs_, 
                                         Uobject_code_casm_funcs_, 
                                         Uobject_code_legacy_funcs_, Uobjects, 
                                         In_uobj, Uobj_finished, x_Uo, y_Uo, 
                                         z_Uo, Uobject_code_c_funcs_U, 
                                         Uobject_code_casm_funcs_U, 
                                         Uobject_code_legacy_funcs_U, x_Uob, 
                                         y_Uob, z_Uob, Uobject_code_c_funcs, 
                                         Uobject_code_casm_funcs, 
                                         Uobject_code_legacy_funcs, 
                                         casmfunc_finished, in_casmfunc, 
                                         x_Uobj, y, z, x >>

End_Uo == /\ pc = "End_Uo"
          /\ pc' = Head(stack).pc
          /\ Uobject_code_c_funcs_U' = Head(stack).Uobject_code_c_funcs_U
          /\ Uobject_code_casm_funcs_U' = Head(stack).Uobject_code_casm_funcs_U
          /\ Uobject_code_legacy_funcs_U' = Head(stack).Uobject_code_legacy_funcs_U
          /\ cfunc_finished' = Head(stack).cfunc_finished
          /\ in_cfunc' = Head(stack).in_cfunc
          /\ x_Uo' = Head(stack).x_Uo
          /\ y_Uo' = Head(stack).y_Uo
          /\ z_Uo' = Head(stack).z_Uo
          /\ stack' = Tail(stack)
          /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, Pc, p_, p_C, p_L, x_, 
                          y_, z_, func_, x_E, y_E, z_E, func, p, c, saved_pc, 
                          x_U, y_U, z_U, Uobject_code_c_funcs_, 
                          Uobject_code_casm_funcs_, Uobject_code_legacy_funcs_, 
                          Uobjects, In_uobj, Uobj_finished, x_Uob, y_Uob, 
                          z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, 
                          Uobject_code_legacy_funcs, casmfunc_finished, 
                          in_casmfunc, x_Uobj, y, z, x >>

Uobject_code_c_func == Start_Uob \/ Loop_Uo \/ Obs_Uo
                          \/ Cfunc_finished_assign \/ End_Uo

Start_Uobj == /\ pc = "Start_Uobj"
              /\ IF ~in_casmfunc
                    THEN /\ Pc_src' = UBER
                         /\ pc' = "Loop_Uob"
                    ELSE /\ pc' = "End_Uob"
                         /\ UNCHANGED Pc_src
              /\ UNCHANGED << cpu, Cpu, memory, cfi, stack, Pc, p_, p_C, p_L, 
                              x_, y_, z_, func_, x_E, y_E, z_E, func, p, c, 
                              saved_pc, x_U, y_U, z_U, Uobject_code_c_funcs_, 
                              Uobject_code_casm_funcs_, 
                              Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                              Uobj_finished, x_Uo, y_Uo, z_Uo, 
                              Uobject_code_c_funcs_U, 
                              Uobject_code_casm_funcs_U, 
                              Uobject_code_legacy_funcs_U, cfunc_finished, 
                              in_cfunc, x_Uob, y_Uob, z_Uob, 
                              Uobject_code_c_funcs, Uobject_code_casm_funcs, 
                              Uobject_code_legacy_funcs, casmfunc_finished, 
                              in_casmfunc, x_Uobj, y, z, x >>

Loop_Uob == /\ pc = "Loop_Uob"
            /\ IF ~casmfunc_finished
                  THEN /\ \/ /\ /\ stack' = << [ procedure |->  "Uobject_code_c_func",
                                                 pc        |->  "Loop_Uob",
                                                 Uobject_code_c_funcs_U |->  Uobject_code_c_funcs_U,
                                                 Uobject_code_casm_funcs_U |->  Uobject_code_casm_funcs_U,
                                                 Uobject_code_legacy_funcs_U |->  Uobject_code_legacy_funcs_U,
                                                 cfunc_finished |->  cfunc_finished,
                                                 in_cfunc  |->  in_cfunc,
                                                 x_Uo      |->  x_Uo,
                                                 y_Uo      |->  y_Uo,
                                                 z_Uo      |->  z_Uo ] >>
                                             \o stack
                                /\ x_Uo' = x_Uob
                                /\ y_Uo' = y_Uob
                                /\ z_Uo' = z_Uob
                             /\ Uobject_code_c_funcs_U' = func_set
                             /\ Uobject_code_casm_funcs_U' = func_set
                             /\ Uobject_code_legacy_funcs_U' = func_set
                             /\ cfunc_finished' = defaultInitValue
                             /\ in_cfunc' = defaultInitValue
                             /\ pc' = "Start_Uob"
                             /\ UNCHANGED <<memory, x_E, y_E, z_E, func, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                          \/ /\ /\ stack' = << [ procedure |->  "Uobject_code_casm_func",
                                                 pc        |->  "Loop_Uob",
                                                 Uobject_code_c_funcs |->  Uobject_code_c_funcs,
                                                 Uobject_code_casm_funcs |->  Uobject_code_casm_funcs,
                                                 Uobject_code_legacy_funcs |->  Uobject_code_legacy_funcs,
                                                 casmfunc_finished |->  casmfunc_finished,
                                                 in_casmfunc |->  in_casmfunc,
                                                 x_Uob     |->  x_Uob,
                                                 y_Uob     |->  y_Uob,
                                                 z_Uob     |->  z_Uob ] >>
                                             \o stack
                                /\ x_Uob' = x_Uob
                                /\ y_Uob' = y_Uob
                                /\ z_Uob' = z_Uob
                             /\ Uobject_code_c_funcs' = func_set
                             /\ Uobject_code_casm_funcs' = func_set
                             /\ Uobject_code_legacy_funcs' = func_set
                             /\ casmfunc_finished' = defaultInitValue
                             /\ in_casmfunc' = defaultInitValue
                             /\ pc' = "Start_Uobj"
                             /\ UNCHANGED <<memory, x_E, y_E, z_E, func, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc>>
                          \/ /\ /\ func' = TRUE
                                /\ stack' = << [ procedure |->  "Exit_sentinel",
                                                 pc        |->  "Obs",
                                                 x_E       |->  x_E,
                                                 y_E       |->  y_E,
                                                 z_E       |->  z_E,
                                                 func      |->  func ] >>
                                             \o stack
                                /\ x_E' = x_Uob
                                /\ y_E' = y_Uob
                                /\ z_E' = Pc_src
                             /\ pc' = "Start_Ex"
                             /\ UNCHANGED <<memory, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                          \/ /\ TRUE
                             /\ pc' = "Loop_Uob"
                             /\ UNCHANGED <<memory, stack, x_E, y_E, z_E, func, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                          \/ /\ memory' = [memory EXCEPT !.memuobjcollection[y_Uob].memuobj[z_Uob].Mem = z_Uob]
                             /\ pc' = "Loop_Uob"
                             /\ UNCHANGED <<stack, x_E, y_E, z_E, func, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                          \/ /\ TRUE
                             /\ pc' = "Loop_Uob"
                             /\ UNCHANGED <<memory, stack, x_E, y_E, z_E, func, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, casmfunc_finished, in_casmfunc>>
                          \/ /\ casmfunc_finished' = TRUE
                             /\ pc' = "Loop_Uob"
                             /\ UNCHANGED <<memory, stack, x_E, y_E, z_E, func, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, Uobject_code_casm_funcs, Uobject_code_legacy_funcs, in_casmfunc>>
                       /\ Cpu' = Cpu
                  ELSE /\ casmfunc_finished' = FALSE
                       /\ in_casmfunc' = FALSE
                       /\ Cpu' = [Cpu EXCEPT ![x_Uob].Pc = 0]
                       /\ pc' = "End_Uob"
                       /\ UNCHANGED << memory, stack, x_E, y_E, z_E, func, 
                                       x_Uo, y_Uo, z_Uo, 
                                       Uobject_code_c_funcs_U, 
                                       Uobject_code_casm_funcs_U, 
                                       Uobject_code_legacy_funcs_U, 
                                       cfunc_finished, in_cfunc, x_Uob, y_Uob, 
                                       z_Uob, Uobject_code_c_funcs, 
                                       Uobject_code_casm_funcs, 
                                       Uobject_code_legacy_funcs >>
            /\ UNCHANGED << cpu, cfi, Pc_src, Pc, p_, p_C, p_L, x_, y_, z_, 
                            func_, p, c, saved_pc, x_U, y_U, z_U, 
                            Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                            Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                            Uobj_finished, x_Uobj, y, z, x >>

Obs == /\ pc = "Obs"
       /\ /\ Pc' = Pc_src
          /\ p_' = x_Uob
          /\ stack' = << [ procedure |->  "CFI_observer",
                           pc        |->  "Loop_Uob",
                           Pc        |->  Pc,
                           p_        |->  p_ ] >>
                       \o stack
       /\ pc' = "Start_"
       /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, p_C, p_L, x_, y_, z_, 
                       func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, y_U, 
                       z_U, Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                       Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                       Uobj_finished, x_Uo, y_Uo, z_Uo, Uobject_code_c_funcs_U, 
                       Uobject_code_casm_funcs_U, Uobject_code_legacy_funcs_U, 
                       cfunc_finished, in_cfunc, x_Uob, y_Uob, z_Uob, 
                       Uobject_code_c_funcs, Uobject_code_casm_funcs, 
                       Uobject_code_legacy_funcs, casmfunc_finished, 
                       in_casmfunc, x_Uobj, y, z, x >>

End_Uob == /\ pc = "End_Uob"
           /\ pc' = Head(stack).pc
           /\ Uobject_code_c_funcs' = Head(stack).Uobject_code_c_funcs
           /\ Uobject_code_casm_funcs' = Head(stack).Uobject_code_casm_funcs
           /\ Uobject_code_legacy_funcs' = Head(stack).Uobject_code_legacy_funcs
           /\ casmfunc_finished' = Head(stack).casmfunc_finished
           /\ in_casmfunc' = Head(stack).in_casmfunc
           /\ x_Uob' = Head(stack).x_Uob
           /\ y_Uob' = Head(stack).y_Uob
           /\ z_Uob' = Head(stack).z_Uob
           /\ stack' = Tail(stack)
           /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, Pc, p_, p_C, p_L, x_, 
                           y_, z_, func_, x_E, y_E, z_E, func, p, c, saved_pc, 
                           x_U, y_U, z_U, Uobject_code_c_funcs_, 
                           Uobject_code_casm_funcs_, 
                           Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                           Uobj_finished, x_Uo, y_Uo, z_Uo, 
                           Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                           Uobject_code_legacy_funcs_U, cfunc_finished, 
                           in_cfunc, x_Uobj, y, z, x >>

Uobject_code_casm_func == Start_Uobj \/ Loop_Uob \/ Obs \/ End_Uob

Start == /\ pc = "Start"
         /\ memory' = [memory EXCEPT !.memuobjcollection[y].uobject_sssa[x_Uobj].sp = Cpu[x_Uobj].sp]
         /\ pc' = "Memory_assign"
         /\ UNCHANGED << cpu, Cpu, cfi, Pc_src, stack, Pc, p_, p_C, p_L, x_, 
                         y_, z_, func_, x_E, y_E, z_E, func, p, c, saved_pc, 
                         x_U, y_U, z_U, Uobject_code_c_funcs_, 
                         Uobject_code_casm_funcs_, Uobject_code_legacy_funcs_, 
                         Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_Uo, 
                         Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                         Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, 
                         x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                         Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                         casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Memory_assign == /\ pc = "Memory_assign"
                 /\ memory' = [memory EXCEPT !.memuobjcollection[y].uobject_sssa[x_Uobj].lr = Cpu[x_Uobj].lr]
                 /\ pc' = "Memory_assign_pc"
                 /\ UNCHANGED << cpu, Cpu, cfi, Pc_src, stack, Pc, p_, p_C, 
                                 p_L, x_, y_, z_, func_, x_E, y_E, z_E, func, 
                                 p, c, saved_pc, x_U, y_U, z_U, 
                                 Uobject_code_c_funcs_, 
                                 Uobject_code_casm_funcs_, 
                                 Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                                 Uobj_finished, x_Uo, y_Uo, z_Uo, 
                                 Uobject_code_c_funcs_U, 
                                 Uobject_code_casm_funcs_U, 
                                 Uobject_code_legacy_funcs_U, cfunc_finished, 
                                 in_cfunc, x_Uob, y_Uob, z_Uob, 
                                 Uobject_code_c_funcs, Uobject_code_casm_funcs, 
                                 Uobject_code_legacy_funcs, casmfunc_finished, 
                                 in_casmfunc, x_Uobj, y, z, x >>

Memory_assign_pc == /\ pc = "Memory_assign_pc"
                    /\ memory' = [memory EXCEPT !.memuobjcollection[y].uobject_sssa[x_Uobj].Pc = z]
                    /\ Cpu' = [Cpu EXCEPT ![x_Uobj].Lr = 0]
                    /\ pc' = "Cpu_assign"
                    /\ UNCHANGED << cpu, cfi, Pc_src, stack, Pc, p_, p_C, p_L, 
                                    x_, y_, z_, func_, x_E, y_E, z_E, func, p, 
                                    c, saved_pc, x_U, y_U, z_U, 
                                    Uobject_code_c_funcs_, 
                                    Uobject_code_casm_funcs_, 
                                    Uobject_code_legacy_funcs_, Uobjects, 
                                    In_uobj, Uobj_finished, x_Uo, y_Uo, z_Uo, 
                                    Uobject_code_c_funcs_U, 
                                    Uobject_code_casm_funcs_U, 
                                    Uobject_code_legacy_funcs_U, 
                                    cfunc_finished, in_cfunc, x_Uob, y_Uob, 
                                    z_Uob, Uobject_code_c_funcs, 
                                    Uobject_code_casm_funcs, 
                                    Uobject_code_legacy_funcs, 
                                    casmfunc_finished, in_casmfunc, x_Uobj, y, 
                                    z, x >>

Cpu_assign == /\ pc = "Cpu_assign"
              /\ Cpu' = [Cpu EXCEPT ![x_Uobj].Pc = LEGACY]
              /\ pc' = "Cpu_assign_pc"
              /\ UNCHANGED << cpu, memory, cfi, Pc_src, stack, Pc, p_, p_C, 
                              p_L, x_, y_, z_, func_, x_E, y_E, z_E, func, p, 
                              c, saved_pc, x_U, y_U, z_U, 
                              Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                              Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                              Uobj_finished, x_Uo, y_Uo, z_Uo, 
                              Uobject_code_c_funcs_U, 
                              Uobject_code_casm_funcs_U, 
                              Uobject_code_legacy_funcs_U, cfunc_finished, 
                              in_cfunc, x_Uob, y_Uob, z_Uob, 
                              Uobject_code_c_funcs, Uobject_code_casm_funcs, 
                              Uobject_code_legacy_funcs, casmfunc_finished, 
                              in_casmfunc, x_Uobj, y, z, x >>

Cpu_assign_pc == /\ pc = "Cpu_assign_pc"
                 /\ Cpu' = [Cpu EXCEPT ![x_Uobj].Pc = memory.memuobjcollection[y].uobject_sssa[x_Uobj].Pc]
                 /\ pc' = "End"
                 /\ UNCHANGED << cpu, memory, cfi, Pc_src, stack, Pc, p_, p_C, 
                                 p_L, x_, y_, z_, func_, x_E, y_E, z_E, func, 
                                 p, c, saved_pc, x_U, y_U, z_U, 
                                 Uobject_code_c_funcs_, 
                                 Uobject_code_casm_funcs_, 
                                 Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                                 Uobj_finished, x_Uo, y_Uo, z_Uo, 
                                 Uobject_code_c_funcs_U, 
                                 Uobject_code_casm_funcs_U, 
                                 Uobject_code_legacy_funcs_U, cfunc_finished, 
                                 in_cfunc, x_Uob, y_Uob, z_Uob, 
                                 Uobject_code_c_funcs, Uobject_code_casm_funcs, 
                                 Uobject_code_legacy_funcs, casmfunc_finished, 
                                 in_casmfunc, x_Uobj, y, z, x >>

End == /\ pc = "End"
       /\ pc' = Head(stack).pc
       /\ x_Uobj' = Head(stack).x_Uobj
       /\ y' = Head(stack).y
       /\ z' = Head(stack).z
       /\ stack' = Tail(stack)
       /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, Pc, p_, p_C, p_L, x_, y_, 
                       z_, func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, 
                       y_U, z_U, Uobject_code_c_funcs_, 
                       Uobject_code_casm_funcs_, Uobject_code_legacy_funcs_, 
                       Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_Uo, 
                       Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                       Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, 
                       x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                       Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                       casmfunc_finished, in_casmfunc, x >>

Uobject_code_legacy_func == Start \/ Memory_assign \/ Memory_assign_pc
                               \/ Cpu_assign \/ Cpu_assign_pc \/ End

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
          /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, Pc, p_, p_C, p_L, x_, 
                          y_, z_, func_, x_E, y_E, z_E, func, p, c, saved_pc, 
                          x_U, y_U, z_U, Uobject_code_c_funcs_, 
                          Uobject_code_casm_funcs_, Uobject_code_legacy_funcs_, 
                          Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_Uo, 
                          Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                          Uobject_code_legacy_funcs_U, cfunc_finished, 
                          in_cfunc, x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                          Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                          casmfunc_finished, in_casmfunc, x_Uobj, y, z >>

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
        /\ UNCHANGED << cpu, Cpu, memory, cfi, Pc_src, Pc, p_, p_L, x_, y_, z_, 
                        func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, y_U, 
                        z_U, Uobject_code_c_funcs_, Uobject_code_casm_funcs_, 
                        Uobject_code_legacy_funcs_, Uobjects, In_uobj, 
                        Uobj_finished, x_Uo, y_Uo, z_Uo, 
                        Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                        Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, 
                        x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                        Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                        casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

Dec == /\ pc = "Dec"
       /\ cpu' = cpu - 1
       /\ pc' = "Loop"
       /\ UNCHANGED << Cpu, memory, cfi, Pc_src, stack, Pc, p_, p_C, p_L, x_, 
                       y_, z_, func_, x_E, y_E, z_E, func, p, c, saved_pc, x_U, 
                       y_U, z_U, Uobject_code_c_funcs_, 
                       Uobject_code_casm_funcs_, Uobject_code_legacy_funcs_, 
                       Uobjects, In_uobj, Uobj_finished, x_Uo, y_Uo, z_Uo, 
                       Uobject_code_c_funcs_U, Uobject_code_casm_funcs_U, 
                       Uobject_code_legacy_funcs_U, cfunc_finished, in_cfunc, 
                       x_Uob, y_Uob, z_Uob, Uobject_code_c_funcs, 
                       Uobject_code_casm_funcs, Uobject_code_legacy_funcs, 
                       casmfunc_finished, in_casmfunc, x_Uobj, y, z, x >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == CFI_observer \/ Cpu_process \/ Legacy_code \/ Entry_sentinel
           \/ Exit_sentinel \/ Uobjcollection_code \/ Uobject_code
           \/ Uobject_code_c_func \/ Uobject_code_casm_func
           \/ Uobject_code_legacy_func \/ device_process \/ Loop \/ Dec
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2aa3801b5bd109715aa154c527bd110b

(*Mem_Integrity == [](\A c1 \in 1..MAXUOBJCOLLECTIONS: \A o \in 1..MAXUOBJSWITHINCOLLECTION: 
                    memory.memuobjcollection[c1].memuobjs[o].Mem = o)*)
MI_initial == \A c1 \in 1..MAXUOBJCOLLECTIONS: \A o \in 1..MAXUOBJSWITHINCOLLECTION: 
                    memory.memuobjcollection[c1].memuobjs[o].Mem = o
(*CFI == [](\A p1 \in 1..MAXCPUS: Buffer(Cpu[p1].Pc = LEGACY, Cpu[p1].Pc = SENTINEL, Cpu[p1].Pc = UBER) /\
                                Buffer(Cpu[p1].Pc = UBER, Cpu[p1].Pc = SENTINEL, Cpu[p1].Pc = LEGACY))*)
CFI_initial == cfi = TRUE

=============================================================================
\* Modification History
\* Last modified Wed Jan 15 11:53:18 PST 2021 by mjmccall
\* Created Thu Dec 17 08:07:51 PST 2020 by mjmccall
