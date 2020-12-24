-------------------------------- MODULE toy --------------------------------
EXTENDS TLC, Sequences, Integers
CONSTANTS MAXCPUS, MAXUOBJCOLLECTIONS, MAXUOBJSWITHINCOLLECTION, MAXUOBJCOLLECTIONSTACKSIZE, MAXUOBJDEVMMIO,
            func_set, maxvars
E(n) == IF n \in MAXCPUS THEN TRUE ELSE FALSE
R(n) == 1..n
LocalSets == SUBSET {1,2,3,4,5,6,7,8}\*1..maxvars

Mem_Safety == [](\A c \in 1..MAXUOBJCOLLECTIONS: \A o \in 1..MAXUOBJSWITHINCOLLECTION: 
                    memory.memuobjcollection[c].memuobjs[o].Local = o)
CF_Integrity_1 == [](\A l \in 1..MAXCPUS: ~((Cpu[l].Pc = leg ~> Cpu[l].Pc = uber) \/ (Cpu[l].Pc = uber ~> Cpu[l].Pc = leg)) \* express next, not leads to
CF_Integrity_2 == [](\A l \in 1..MAXCPUS: ((Cpu[l].Pc = leg ~> Cpu[l].Pc = uber) => Cpu[l].Pc = leg ~> Cpu[l].Pc = sent /\
                    (Cpu[l].Pc = uber ~> Cpu[l].Pc = leg) => Cpu[l].Pc = leg ~> Cpu[l].Pc = sent)
\*Mem_Integrity == []()

(* --algorithm execution
variables cpu = MAXCPUS,
          collection = 1,
          object = 1,
    (**)Cpu = [l \in 1..MAXCPUS |->
              [id |-> l,
               Pc |-> 1,
               Sp |-> 1,
               Shared_cpustate |-> {},\*<<1,2,3>>,
               Legacy_cpustate |-> {},\*<<4,5,6>>,
               Res_cpustate |-> [m \in 1..MAXUOBJCOLLECTIONS |->
                 [n \in 1..MAXUOBJSWITHINCOLLECTION |-> {}
          ]]]],(**)
    \*cpu = [x \in 1..MAXCPUS |-> [id : 0, pop : [y \in R(5) |-> z]]];
    (*memory = [Mem_legacy |-> {},
              memuobjcollection |-> [c \in 1..MAXUOBJCOLLECTIONS |->
                [Uobject_stack |-> [s \in (1..MAXCPUS) \X (1..MAXUOBJCOLLECTIONSTACKSIZE) |-> {}],
                 memuobjs |-> [o \in 1..MAXUOBJSWITHINCOLLECTION |-> [Local : LocalSets]
                   (*[Uobj_ssa : {[ssa \in 1..MAXCPUS |-> {}]},
                    Uobj_code : {},
                    Uobj_data : {},
                    Uobj_dmadata : {},
                    Uobj_devmmio : [dev \in 1..MAXUOBJDEVMMIO |-> {}],
                    Global : <<>>,
                    Local : LocalSets,
                    Device : <<>>,
                    System : <<>>]*)
                  ]
                ]
               ]
             ];*)
             
    memory = [Mem_legacy |-> 0,
              memuobjcollection |-> [c \in 1..MAXUOBJCOLLECTIONS |->
                [Uobject_stack |-> [s \in (1..MAXCPUS) \X (1..MAXUOBJCOLLECTIONSTACKSIZE) |-> {}],
                 memuobjs |-> [o \in 1..MAXUOBJSWITHINCOLLECTION |->
                   [Uobj_ssa |-> [ssa \in 1..MAXCPUS |-> {}],
                    Uobj_code |-> {},
                    Uobj_data |-> {},
                    Uobj_dmadata |-> {},
                    Uobj_devmmio |-> [dev \in 1..MAXUOBJDEVMMIO |-> {}],
                    Global |-> 0,
                    Local |-> o,
                    Device |-> 0,
                    System |-> 0]
                  ]
                ]
               ]
             ];
             
    (*mem_stacks = [Globals |-> {},
                  ]*)
    
    (*mem_test = [memuobjcollection |-> [c \in 1..MAXUOBJCOLLECTIONS |->
                [memuobjs |-> [o \in 1..MAXUOBJSWITHINCOLLECTION |->
                   [exists |-> [v \in 1..maxvars |-> {0,1}],
                   numvars |-> 0..maxvars,
                   vars |-> << c*100 + o, 0..(0..maxvars)>>]
                  ]
                ]
               ]
             ];*)
             
procedure Push_locals(S) begin
Start:
    \*memory.memuobjcollection := memory.memuobjcollection;
    memory.memuobjcollection[collection].memuobjs[object].Local := Append(memory.memuobjcollection[collection].memuobjs[object].Local, S);
    return;
end procedure;

procedure Pop_locals() begin
Start:
    \*memory := memory;
    memory.memuobjcollection[collection].memuobjs[object].Local := Head(memory.memuobjcollection[collection].memuobjs[object].Local);
    return;
end procedure;             
             
procedure Cpu_process(x) begin
Start:
    either
        call Legacy_code(x);
        return;
    or
        with obj \in 1..MAXUOBJCOLLECTIONS do
            call Uobjcollection_code(x, obj(*1..MAXUOBJCOLLECTIONS*)) (*?*);
        end with;
After_branching:
        return;
    end either;
end procedure;

procedure Legacy_code(x) begin
Start:
    Cpu[x].Pc := leg;
Loop:
    while TRUE do
        either
            call Uobjcollection_code(x, 1..MAXUOBJCOLLECTIONS); \* should be done with with {}
        or
            \*Execute code from memory.mem_legacy[]
            skip;
        or 
            \*Read/write to memory.mem_legacy[]
            memory.mem_legacy := -1;
            skip;
        or  
            \*Read/write to cpu[x].shared_cpustate[]
            cpu[x:1..MAXCPUS].shared_cpustate[r:{1,2,3}] := -1;
            skip;
        or  
            \*Read/write to cpu[x].legacy_cpustate[] 
            skip;
        or  
            return; 
        end either;
    end while;
end procedure;

procedure Sentinel(x,y) begin
Start:
    Cpu[x].Pc := leg;
    call Uobjcollection_code(x, y);
end procedure;
 

procedure Uobjcollection_code(x, y) begin
Start:
    Cpu[x].Pc := uber;
    call Uobject_code(x, y, 1..MAXUOBJSWITHINCOLLECTION);
Return:
    Cpu[x].Pc := 0;\*pc_pre_uobjectcollection_code;
Cpu_assign:
    Cpu[x].Sp := 0;\*sp_pre_uobjectcollection_code;
    return;
end procedure;

procedure Uobject_code(x, y, z)
    variables Uobject_code_c_func = func_set,\*{f1..fn}, \* are these in these sets, or equal to these sets
        Uobject_code_casm_func = func_set,\*{c1..cn}, 
        Uobject_code_legacy_func = func_set,\*{l1..ln},
        Uobjects = {1..MAXUOBJSWITHINCOLLECTION(*?MAXUOBJS*)}, 
        In_uobj = FALSE,
        Uobj_finished = FALSE; 
    begin
\*Push:
\*    call Push_locals(<<>>);
Start:
    if ~In_uobj then
Loop:
        while ~Uobj_finished do
            either
                with f \in Uobject_code_c_func do
                    Cpu[x].Pc :=  f; \*\in Uobject_code_c_func; \* try all?
                end with;
            or 
                with c \in Uobject_code_casm_func do
                Cpu[x].Pc :=  c;\* \in Uobject_code_casm_func;
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
                Uobj_finished := TRUE;
            end either;
        end while;
    end if;
\*Pop:
\*    call Pop_locals();
Uobj_finished_assign:
    Uobj_finished := FALSE;
    In_uobj := FALSE;
    Cpu[x].Pc := 0;\*pc_pre_uobject_code;
Cpu_assign:
    Cpu[x].Sp := 0;\*sp_pre_uobject_code;
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
                with c \in Uobject_code_casm_func do
                Cpu[x].Pc :=  c;\* \in Uobject_code_casm_func;
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
    Cpu[x].pc := 0;\*pc_pre_cfunc_code;
Cpu_assign: 
    Cpu[x].Sp := 0;\*sp_pre_cfunc_code;
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
                with c \in Uobject_code_casm_func do
                Cpu[x].Pc :=  c;\* \in Uobject_code_casm_func;
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
        Cpu[x].pc := 0;\*pc_pre_casmfunc_code;
Cpu_assign:
        Cpu[x].Sp := 0;\*sp_pre_casmfunc_code;
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
Resumelegacy:
    Cpu[x].Sp := memory.memuobjcollection[y].uobject_sssa[x].sp;
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
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-d32cc5aa317445d3ee9f51b9a94c69a5
\* Label Start of procedure Push_locals at line 82 col 5 changed to Start_
\* Label Start of procedure Pop_locals at line 89 col 5 changed to Start_P
\* Label Start of procedure Cpu_process at line 95 col 5 changed to Start_C
\* Label Start of procedure Legacy_code at line 109 col 5 changed to Start_L
\* Label Loop of procedure Legacy_code at line 111 col 5 changed to Loop_
\* Label Start of procedure Sentinel at line 136 col 5 changed to Start_S
\* Label Start of procedure Uobjcollection_code at line 143 col 5 changed to Start_U
\* Label Cpu_assign of procedure Uobjcollection_code at line 148 col 5 changed to Cpu_assign_
\* Label Start of procedure Uobject_code at line 163 col 5 changed to Start_Uo
\* Label Loop of procedure Uobject_code at line 165 col 9 changed to Loop_U
\* Label Cpu_assign of procedure Uobject_code at line 199 col 5 changed to Cpu_assign_U
\* Label Start of procedure Uobject_code_c_func at line 207 col 5 changed to Start_Uob
\* Label Loop of procedure Uobject_code_c_func at line 209 col 9 changed to Loop_Uo
\* Label Cpu_assign of procedure Uobject_code_c_func at line 241 col 5 changed to Cpu_assign_Uo
\* Label Start of procedure Uobject_code_casm_func at line 250 col 5 changed to Start_Uobj
\* Label Loop of procedure Uobject_code_casm_func at line 252 col 9 changed to Loop_Uob
\* Label Cpu_assign of procedure Uobject_code_casm_func at line 282 col 9 changed to Cpu_assign_Uob
\* Label Loop of procedure device_process at line 307 col 5 changed to Loop_d
\* Procedure Uobject_code_c_func at line 203 col 1 changed to Uobject_code_c_func_
\* Procedure Uobject_code_casm_func at line 246 col 1 changed to Uobject_code_casm_func_
\* Procedure Uobject_code_legacy_func at line 288 col 1 changed to Uobject_code_legacy_func_
\* Parameter x of procedure Cpu_process at line 93 col 23 changed to x_
\* Parameter x of procedure Legacy_code at line 107 col 23 changed to x_L
\* Parameter x of procedure Sentinel at line 134 col 20 changed to x_S
\* Parameter y of procedure Sentinel at line 134 col 22 changed to y_
\* Parameter x of procedure Uobjcollection_code at line 141 col 31 changed to x_U
\* Parameter y of procedure Uobjcollection_code at line 141 col 34 changed to y_U
\* Parameter x of procedure Uobject_code at line 152 col 24 changed to x_Uo
\* Parameter y of procedure Uobject_code at line 152 col 27 changed to y_Uo
\* Parameter z of procedure Uobject_code at line 152 col 30 changed to z_
\* Parameter x of procedure Uobject_code_c_func at line 203 col 31 changed to x_Uob
\* Parameter y of procedure Uobject_code_c_func at line 203 col 34 changed to y_Uob
\* Parameter z of procedure Uobject_code_c_func at line 203 col 37 changed to z_U
\* Parameter x of procedure Uobject_code_casm_func at line 246 col 34 changed to x_Uobj
\* Parameter y of procedure Uobject_code_casm_func at line 246 col 37 changed to y_Uobj
\* Parameter z of procedure Uobject_code_casm_func at line 246 col 40 changed to z_Uo
\* Parameter x of procedure Uobject_code_legacy_func at line 288 col 36 changed to x_Uobje
CONSTANT defaultInitValue
VARIABLES cpu, collection, object, Cpu, memory, pc, stack, S, x_, x_L, x_S, 
          y_, x_U, y_U, x_Uo, y_Uo, z_, Uobject_code_c_func, 
          Uobject_code_casm_func, Uobject_code_legacy_func, Uobjects, In_uobj, 
          Uobj_finished, x_Uob, y_Uob, z_U, cfunc_finished, in_cfunc, x_Uobj, 
          y_Uobj, z_Uo, casmfunc_finished, in_casmfunc, x_Uobje, y, z, x

vars == << cpu, collection, object, Cpu, memory, pc, stack, S, x_, x_L, x_S, 
           y_, x_U, y_U, x_Uo, y_Uo, z_, Uobject_code_c_func, 
           Uobject_code_casm_func, Uobject_code_legacy_func, Uobjects, 
           In_uobj, Uobj_finished, x_Uob, y_Uob, z_U, cfunc_finished, 
           in_cfunc, x_Uobj, y_Uobj, z_Uo, casmfunc_finished, in_casmfunc, 
           x_Uobje, y, z, x >>

Init == (* Global variables *)
        /\ cpu = MAXCPUS
        /\ collection = 1
        /\ object = 1
        /\ Cpu =     [l \in 1..MAXCPUS |->
                     [id |-> l,
                      Pc |-> 1,
                      Sp |-> 1,
                      Shared_cpustate |-> {},
                      Legacy_cpustate |-> {},
                      Res_cpustate |-> [m \in 1..MAXUOBJCOLLECTIONS |->
                        [n \in 1..MAXUOBJSWITHINCOLLECTION |-> {}
                 ]]]]
        /\ memory = [Mem_legacy |-> 0,
                     memuobjcollection |-> [c \in 1..MAXUOBJCOLLECTIONS |->
                       [Uobject_stack |-> [s \in (1..MAXCPUS) \X (1..MAXUOBJCOLLECTIONSTACKSIZE) |-> {}],
                        memuobjs |-> [o \in 1..MAXUOBJSWITHINCOLLECTION |->
                          [Uobj_ssa |-> [ssa \in 1..MAXCPUS |-> {}],
                           Uobj_code |-> {},
                           Uobj_data |-> {},
                           Uobj_dmadata |-> {},
                           Uobj_devmmio |-> [dev \in 1..MAXUOBJDEVMMIO |-> {}],
                           Global |-> 0,
                           Local |-> o,
                           Device |-> 0,
                           System |-> 0]
                         ]
                       ]
                      ]
                    ]
        (* Procedure Push_locals *)
        /\ S = defaultInitValue
        (* Procedure Cpu_process *)
        /\ x_ = defaultInitValue
        (* Procedure Legacy_code *)
        /\ x_L = defaultInitValue
        (* Procedure Sentinel *)
        /\ x_S = defaultInitValue
        /\ y_ = defaultInitValue
        (* Procedure Uobjcollection_code *)
        /\ x_U = defaultInitValue
        /\ y_U = defaultInitValue
        (* Procedure Uobject_code *)
        /\ x_Uo = defaultInitValue
        /\ y_Uo = defaultInitValue
        /\ z_ = defaultInitValue
        /\ Uobject_code_c_func = func_set
        /\ Uobject_code_casm_func = func_set
        /\ Uobject_code_legacy_func = func_set
        /\ Uobjects = {1..MAXUOBJSWITHINCOLLECTION             }
        /\ In_uobj = FALSE
        /\ Uobj_finished = FALSE
        (* Procedure Uobject_code_c_func_ *)
        /\ x_Uob = defaultInitValue
        /\ y_Uob = defaultInitValue
        /\ z_U = defaultInitValue
        /\ cfunc_finished = defaultInitValue
        /\ in_cfunc = defaultInitValue
        (* Procedure Uobject_code_casm_func_ *)
        /\ x_Uobj = defaultInitValue
        /\ y_Uobj = defaultInitValue
        /\ z_Uo = defaultInitValue
        /\ casmfunc_finished = defaultInitValue
        /\ in_casmfunc = defaultInitValue
        (* Procedure Uobject_code_legacy_func_ *)
        /\ x_Uobje = defaultInitValue
        /\ y = defaultInitValue
        /\ z = defaultInitValue
        (* Procedure device_process *)
        /\ x = defaultInitValue
        /\ stack = << >>
        /\ pc = "Loop"

Start_ == /\ pc = "Start_"
          /\ memory' = [memory EXCEPT !.memuobjcollection[collection].memuobjs[object].Local = Append(memory.memuobjcollection[collection].memuobjs[object].Local, S)]
          /\ pc' = Head(stack).pc
          /\ S' = Head(stack).S
          /\ stack' = Tail(stack)
          /\ UNCHANGED << cpu, collection, object, Cpu, x_, x_L, x_S, y_, x_U, 
                          y_U, x_Uo, y_Uo, z_, Uobject_code_c_func, 
                          Uobject_code_casm_func, Uobject_code_legacy_func, 
                          Uobjects, In_uobj, Uobj_finished, x_Uob, y_Uob, z_U, 
                          cfunc_finished, in_cfunc, x_Uobj, y_Uobj, z_Uo, 
                          casmfunc_finished, in_casmfunc, x_Uobje, y, z, x >>

Push_locals == Start_

Start_P == /\ pc = "Start_P"
           /\ memory' = [memory EXCEPT !.memuobjcollection[collection].memuobjs[object].Local = Head(memory.memuobjcollection[collection].memuobjs[object].Local)]
           /\ pc' = Head(stack).pc
           /\ stack' = Tail(stack)
           /\ UNCHANGED << cpu, collection, object, Cpu, S, x_, x_L, x_S, y_, 
                           x_U, y_U, x_Uo, y_Uo, z_, Uobject_code_c_func, 
                           Uobject_code_casm_func, Uobject_code_legacy_func, 
                           Uobjects, In_uobj, Uobj_finished, x_Uob, y_Uob, z_U, 
                           cfunc_finished, in_cfunc, x_Uobj, y_Uobj, z_Uo, 
                           casmfunc_finished, in_casmfunc, x_Uobje, y, z, x >>

Pop_locals == Start_P

Start_C == /\ pc = "Start_C"
           /\ \/ /\ /\ stack' = << [ procedure |->  "Legacy_code",
                                     pc        |->  Head(stack).pc,
                                     x_L       |->  x_L ] >>
                                 \o Tail(stack)
                    /\ x_L' = x_
                 /\ pc' = "Start_L"
                 /\ UNCHANGED <<x_U, y_U>>
              \/ /\ \E obj \in 1..MAXUOBJCOLLECTIONS:
                      /\ /\ stack' = << [ procedure |->  "Uobjcollection_code",
                                          pc        |->  "After_branching",
                                          x_U       |->  x_U,
                                          y_U       |->  y_U ] >>
                                      \o stack
                         /\ x_U' = x_
                         /\ y_U' = obj
                      /\ pc' = "Start_U"
                 /\ x_L' = x_L
           /\ UNCHANGED << cpu, collection, object, Cpu, memory, S, x_, x_S, 
                           y_, x_Uo, y_Uo, z_, Uobject_code_c_func, 
                           Uobject_code_casm_func, Uobject_code_legacy_func, 
                           Uobjects, In_uobj, Uobj_finished, x_Uob, y_Uob, z_U, 
                           cfunc_finished, in_cfunc, x_Uobj, y_Uobj, z_Uo, 
                           casmfunc_finished, in_casmfunc, x_Uobje, y, z, x >>

After_branching == /\ pc = "After_branching"
                   /\ pc' = Head(stack).pc
                   /\ x_' = Head(stack).x_
                   /\ stack' = Tail(stack)
                   /\ UNCHANGED << cpu, collection, object, Cpu, memory, S, 
                                   x_L, x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                                   Uobject_code_c_func, Uobject_code_casm_func, 
                                   Uobject_code_legacy_func, Uobjects, In_uobj, 
                                   Uobj_finished, x_Uob, y_Uob, z_U, 
                                   cfunc_finished, in_cfunc, x_Uobj, y_Uobj, 
                                   z_Uo, casmfunc_finished, in_casmfunc, 
                                   x_Uobje, y, z, x >>

Cpu_process == Start_C \/ After_branching

Start_L == /\ pc = "Start_L"
           /\ Cpu' = [Cpu EXCEPT ![x_L].Pc = leg]
           /\ pc' = "Loop_"
           /\ UNCHANGED << cpu, collection, object, memory, stack, S, x_, x_L, 
                           x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                           Uobject_code_c_func, Uobject_code_casm_func, 
                           Uobject_code_legacy_func, Uobjects, In_uobj, 
                           Uobj_finished, x_Uob, y_Uob, z_U, cfunc_finished, 
                           in_cfunc, x_Uobj, y_Uobj, z_Uo, casmfunc_finished, 
                           in_casmfunc, x_Uobje, y, z, x >>

Loop_ == /\ pc = "Loop_"
         /\ \/ /\ /\ stack' = << [ procedure |->  "Uobjcollection_code",
                                   pc        |->  "Loop_",
                                   x_U       |->  x_U,
                                   y_U       |->  y_U ] >>
                               \o stack
                  /\ x_U' = x_L
                  /\ y_U' = 1..MAXUOBJCOLLECTIONS
               /\ pc' = "Start_U"
               /\ UNCHANGED <<cpu, memory, x_L>>
            \/ /\ TRUE
               /\ pc' = "Loop_"
               /\ UNCHANGED <<cpu, memory, stack, x_L, x_U, y_U>>
            \/ /\ memory' = [memory EXCEPT !.mem_legacy = -1]
               /\ TRUE
               /\ pc' = "Loop_"
               /\ UNCHANGED <<cpu, stack, x_L, x_U, y_U>>
            \/ /\ cpu' = [cpu EXCEPT ![x:1..MAXCPUS].shared_cpustate[r:{1,2,3}] = -1]
               /\ TRUE
               /\ pc' = "Loop_"
               /\ UNCHANGED <<memory, stack, x_L, x_U, y_U>>
            \/ /\ TRUE
               /\ pc' = "Loop_"
               /\ UNCHANGED <<cpu, memory, stack, x_L, x_U, y_U>>
            \/ /\ pc' = Head(stack).pc
               /\ x_L' = Head(stack).x_L
               /\ stack' = Tail(stack)
               /\ UNCHANGED <<cpu, memory, x_U, y_U>>
         /\ UNCHANGED << collection, object, Cpu, S, x_, x_S, y_, x_Uo, y_Uo, 
                         z_, Uobject_code_c_func, Uobject_code_casm_func, 
                         Uobject_code_legacy_func, Uobjects, In_uobj, 
                         Uobj_finished, x_Uob, y_Uob, z_U, cfunc_finished, 
                         in_cfunc, x_Uobj, y_Uobj, z_Uo, casmfunc_finished, 
                         in_casmfunc, x_Uobje, y, z, x >>

Legacy_code == Start_L \/ Loop_

Start_S == /\ pc = "Start_S"
           /\ Cpu' = [Cpu EXCEPT ![x_S].Pc = leg]
           /\ /\ stack' = << [ procedure |->  "Uobjcollection_code",
                               pc        |->  "Error",
                               x_U       |->  x_U,
                               y_U       |->  y_U ] >>
                           \o stack
              /\ x_U' = x_S
              /\ y_U' = y_
           /\ pc' = "Start_U"
           /\ UNCHANGED << cpu, collection, object, memory, S, x_, x_L, x_S, 
                           y_, x_Uo, y_Uo, z_, Uobject_code_c_func, 
                           Uobject_code_casm_func, Uobject_code_legacy_func, 
                           Uobjects, In_uobj, Uobj_finished, x_Uob, y_Uob, z_U, 
                           cfunc_finished, in_cfunc, x_Uobj, y_Uobj, z_Uo, 
                           casmfunc_finished, in_casmfunc, x_Uobje, y, z, x >>

Sentinel == Start_S

Start_U == /\ pc = "Start_U"
           /\ Cpu' = [Cpu EXCEPT ![x_U].Pc = uber]
           /\ /\ stack' = << [ procedure |->  "Uobject_code",
                               pc        |->  "Return",
                               Uobject_code_c_func |->  Uobject_code_c_func,
                               Uobject_code_casm_func |->  Uobject_code_casm_func,
                               Uobject_code_legacy_func |->  Uobject_code_legacy_func,
                               Uobjects  |->  Uobjects,
                               In_uobj   |->  In_uobj,
                               Uobj_finished |->  Uobj_finished,
                               x_Uo      |->  x_Uo,
                               y_Uo      |->  y_Uo,
                               z_        |->  z_ ] >>
                           \o stack
              /\ x_Uo' = x_U
              /\ y_Uo' = y_U
              /\ z_' = 1..MAXUOBJSWITHINCOLLECTION
           /\ Uobject_code_c_func' = func_set
           /\ Uobject_code_casm_func' = func_set
           /\ Uobject_code_legacy_func' = func_set
           /\ Uobjects' = {1..MAXUOBJSWITHINCOLLECTION             }
           /\ In_uobj' = FALSE
           /\ Uobj_finished' = FALSE
           /\ pc' = "Start_Uo"
           /\ UNCHANGED << cpu, collection, object, memory, S, x_, x_L, x_S, 
                           y_, x_U, y_U, x_Uob, y_Uob, z_U, cfunc_finished, 
                           in_cfunc, x_Uobj, y_Uobj, z_Uo, casmfunc_finished, 
                           in_casmfunc, x_Uobje, y, z, x >>

Return == /\ pc = "Return"
          /\ Cpu' = [Cpu EXCEPT ![x_U].Pc = 0]
          /\ pc' = "Cpu_assign_"
          /\ UNCHANGED << cpu, collection, object, memory, stack, S, x_, x_L, 
                          x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                          Uobject_code_c_func, Uobject_code_casm_func, 
                          Uobject_code_legacy_func, Uobjects, In_uobj, 
                          Uobj_finished, x_Uob, y_Uob, z_U, cfunc_finished, 
                          in_cfunc, x_Uobj, y_Uobj, z_Uo, casmfunc_finished, 
                          in_casmfunc, x_Uobje, y, z, x >>

Cpu_assign_ == /\ pc = "Cpu_assign_"
               /\ Cpu' = [Cpu EXCEPT ![x_U].Sp = 0]
               /\ pc' = Head(stack).pc
               /\ x_U' = Head(stack).x_U
               /\ y_U' = Head(stack).y_U
               /\ stack' = Tail(stack)
               /\ UNCHANGED << cpu, collection, object, memory, S, x_, x_L, 
                               x_S, y_, x_Uo, y_Uo, z_, Uobject_code_c_func, 
                               Uobject_code_casm_func, 
                               Uobject_code_legacy_func, Uobjects, In_uobj, 
                               Uobj_finished, x_Uob, y_Uob, z_U, 
                               cfunc_finished, in_cfunc, x_Uobj, y_Uobj, z_Uo, 
                               casmfunc_finished, in_casmfunc, x_Uobje, y, z, 
                               x >>

Uobjcollection_code == Start_U \/ Return \/ Cpu_assign_

Start_Uo == /\ pc = "Start_Uo"
            /\ IF ~In_uobj
                  THEN /\ pc' = "Loop_U"
                  ELSE /\ pc' = "Uobj_finished_assign"
            /\ UNCHANGED << cpu, collection, object, Cpu, memory, stack, S, x_, 
                            x_L, x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                            Uobject_code_c_func, Uobject_code_casm_func, 
                            Uobject_code_legacy_func, Uobjects, In_uobj, 
                            Uobj_finished, x_Uob, y_Uob, z_U, cfunc_finished, 
                            in_cfunc, x_Uobj, y_Uobj, z_Uo, casmfunc_finished, 
                            in_casmfunc, x_Uobje, y, z, x >>

Loop_U == /\ pc = "Loop_U"
          /\ IF ~Uobj_finished
                THEN /\ \/ /\ \E f \in Uobject_code_c_func:
                                Cpu' = [Cpu EXCEPT ![x_Uo].Pc = f]
                           /\ UNCHANGED Uobj_finished
                        \/ /\ \E c \in Uobject_code_casm_func:
                                Cpu' = [Cpu EXCEPT ![x_Uo].Pc = c]
                           /\ UNCHANGED Uobj_finished
                        \/ /\ \E l \in Uobject_code_legacy_func:
                                Cpu' = [Cpu EXCEPT ![x_Uo].Pc = l]
                           /\ UNCHANGED Uobj_finished
                        \/ /\ TRUE
                           /\ UNCHANGED <<Cpu, Uobj_finished>>
                        \/ /\ TRUE
                           /\ UNCHANGED <<Cpu, Uobj_finished>>
                        \/ /\ TRUE
                           /\ UNCHANGED <<Cpu, Uobj_finished>>
                        \/ /\ Uobj_finished' = TRUE
                           /\ Cpu' = Cpu
                     /\ pc' = "Loop_U"
                ELSE /\ pc' = "Uobj_finished_assign"
                     /\ UNCHANGED << Cpu, Uobj_finished >>
          /\ UNCHANGED << cpu, collection, object, memory, stack, S, x_, x_L, 
                          x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                          Uobject_code_c_func, Uobject_code_casm_func, 
                          Uobject_code_legacy_func, Uobjects, In_uobj, x_Uob, 
                          y_Uob, z_U, cfunc_finished, in_cfunc, x_Uobj, y_Uobj, 
                          z_Uo, casmfunc_finished, in_casmfunc, x_Uobje, y, z, 
                          x >>

Uobj_finished_assign == /\ pc = "Uobj_finished_assign"
                        /\ Uobj_finished' = FALSE
                        /\ In_uobj' = FALSE
                        /\ Cpu' = [Cpu EXCEPT ![x_Uo].Pc = 0]
                        /\ pc' = "Cpu_assign_U"
                        /\ UNCHANGED << cpu, collection, object, memory, stack, 
                                        S, x_, x_L, x_S, y_, x_U, y_U, x_Uo, 
                                        y_Uo, z_, Uobject_code_c_func, 
                                        Uobject_code_casm_func, 
                                        Uobject_code_legacy_func, Uobjects, 
                                        x_Uob, y_Uob, z_U, cfunc_finished, 
                                        in_cfunc, x_Uobj, y_Uobj, z_Uo, 
                                        casmfunc_finished, in_casmfunc, 
                                        x_Uobje, y, z, x >>

Cpu_assign_U == /\ pc = "Cpu_assign_U"
                /\ Cpu' = [Cpu EXCEPT ![x_Uo].Sp = 0]
                /\ pc' = Head(stack).pc
                /\ Uobject_code_c_func' = Head(stack).Uobject_code_c_func
                /\ Uobject_code_casm_func' = Head(stack).Uobject_code_casm_func
                /\ Uobject_code_legacy_func' = Head(stack).Uobject_code_legacy_func
                /\ Uobjects' = Head(stack).Uobjects
                /\ In_uobj' = Head(stack).In_uobj
                /\ Uobj_finished' = Head(stack).Uobj_finished
                /\ x_Uo' = Head(stack).x_Uo
                /\ y_Uo' = Head(stack).y_Uo
                /\ z_' = Head(stack).z_
                /\ stack' = Tail(stack)
                /\ UNCHANGED << cpu, collection, object, memory, S, x_, x_L, 
                                x_S, y_, x_U, y_U, x_Uob, y_Uob, z_U, 
                                cfunc_finished, in_cfunc, x_Uobj, y_Uobj, z_Uo, 
                                casmfunc_finished, in_casmfunc, x_Uobje, y, z, 
                                x >>

Uobject_code == Start_Uo \/ Loop_U \/ Uobj_finished_assign \/ Cpu_assign_U

Start_Uob == /\ pc = "Start_Uob"
             /\ IF ~in_cfunc
                   THEN /\ pc' = "Loop_Uo"
                   ELSE /\ pc' = "Cfunc_finished_assign"
             /\ UNCHANGED << cpu, collection, object, Cpu, memory, stack, S, 
                             x_, x_L, x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                             Uobject_code_c_func, Uobject_code_casm_func, 
                             Uobject_code_legacy_func, Uobjects, In_uobj, 
                             Uobj_finished, x_Uob, y_Uob, z_U, cfunc_finished, 
                             in_cfunc, x_Uobj, y_Uobj, z_Uo, casmfunc_finished, 
                             in_casmfunc, x_Uobje, y, z, x >>

Loop_Uo == /\ pc = "Loop_Uo"
           /\ IF ~cfunc_finished
                 THEN /\ \/ /\ \E f \in Uobject_code_c_func:
                                 Cpu' = [Cpu EXCEPT ![x_Uob].Pc = f]
                            /\ UNCHANGED cfunc_finished
                         \/ /\ \E c \in Uobject_code_casm_func:
                                 Cpu' = [Cpu EXCEPT ![x_Uob].Pc = c]
                            /\ UNCHANGED cfunc_finished
                         \/ /\ \E l \in Uobject_code_legacy_func:
                                 Cpu' = [Cpu EXCEPT ![x_Uob].Pc = l]
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
           /\ UNCHANGED << cpu, collection, object, memory, stack, S, x_, x_L, 
                           x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                           Uobject_code_c_func, Uobject_code_casm_func, 
                           Uobject_code_legacy_func, Uobjects, In_uobj, 
                           Uobj_finished, x_Uob, y_Uob, z_U, in_cfunc, x_Uobj, 
                           y_Uobj, z_Uo, casmfunc_finished, in_casmfunc, 
                           x_Uobje, y, z, x >>

Cfunc_finished_assign == /\ pc = "Cfunc_finished_assign"
                         /\ cfunc_finished' = FALSE
                         /\ in_cfunc' = FALSE
                         /\ Cpu' = [Cpu EXCEPT ![x_Uob].pc = 0]
                         /\ pc' = "Cpu_assign_Uo"
                         /\ UNCHANGED << cpu, collection, object, memory, 
                                         stack, S, x_, x_L, x_S, y_, x_U, y_U, 
                                         x_Uo, y_Uo, z_, Uobject_code_c_func, 
                                         Uobject_code_casm_func, 
                                         Uobject_code_legacy_func, Uobjects, 
                                         In_uobj, Uobj_finished, x_Uob, y_Uob, 
                                         z_U, x_Uobj, y_Uobj, z_Uo, 
                                         casmfunc_finished, in_casmfunc, 
                                         x_Uobje, y, z, x >>

Cpu_assign_Uo == /\ pc = "Cpu_assign_Uo"
                 /\ Cpu' = [Cpu EXCEPT ![x_Uob].Sp = 0]
                 /\ pc' = "Error"
                 /\ UNCHANGED << cpu, collection, object, memory, stack, S, x_, 
                                 x_L, x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                                 Uobject_code_c_func, Uobject_code_casm_func, 
                                 Uobject_code_legacy_func, Uobjects, In_uobj, 
                                 Uobj_finished, x_Uob, y_Uob, z_U, 
                                 cfunc_finished, in_cfunc, x_Uobj, y_Uobj, 
                                 z_Uo, casmfunc_finished, in_casmfunc, x_Uobje, 
                                 y, z, x >>

Uobject_code_c_func_ == Start_Uob \/ Loop_Uo \/ Cfunc_finished_assign
                           \/ Cpu_assign_Uo

Start_Uobj == /\ pc = "Start_Uobj"
              /\ IF ~in_casmfunc
                    THEN /\ pc' = "Loop_Uob"
                    ELSE /\ pc' = "Error"
              /\ UNCHANGED << cpu, collection, object, Cpu, memory, stack, S, 
                              x_, x_L, x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                              Uobject_code_c_func, Uobject_code_casm_func, 
                              Uobject_code_legacy_func, Uobjects, In_uobj, 
                              Uobj_finished, x_Uob, y_Uob, z_U, cfunc_finished, 
                              in_cfunc, x_Uobj, y_Uobj, z_Uo, 
                              casmfunc_finished, in_casmfunc, x_Uobje, y, z, x >>

Loop_Uob == /\ pc = "Loop_Uob"
            /\ IF ~casmfunc_finished
                  THEN /\ \/ /\ \E f \in Uobject_code_c_func:
                                  Cpu' = [Cpu EXCEPT ![x_Uobj].Pc = f]
                             /\ UNCHANGED casmfunc_finished
                          \/ /\ \E c \in Uobject_code_casm_func:
                                  Cpu' = [Cpu EXCEPT ![x_Uobj].Pc = c]
                             /\ UNCHANGED casmfunc_finished
                          \/ /\ \E l \in Uobject_code_legacy_func:
                                  Cpu' = [Cpu EXCEPT ![x_Uobj].Pc = l]
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
                       /\ Cpu' = [Cpu EXCEPT ![x_Uobj].pc = 0]
                       /\ pc' = "Cpu_assign_Uob"
            /\ UNCHANGED << cpu, collection, object, memory, stack, S, x_, x_L, 
                            x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                            Uobject_code_c_func, Uobject_code_casm_func, 
                            Uobject_code_legacy_func, Uobjects, In_uobj, 
                            Uobj_finished, x_Uob, y_Uob, z_U, cfunc_finished, 
                            in_cfunc, x_Uobj, y_Uobj, z_Uo, x_Uobje, y, z, x >>

Cpu_assign_Uob == /\ pc = "Cpu_assign_Uob"
                  /\ Cpu' = [Cpu EXCEPT ![x_Uobj].Sp = 0]
                  /\ pc' = "Error"
                  /\ UNCHANGED << cpu, collection, object, memory, stack, S, 
                                  x_, x_L, x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                                  Uobject_code_c_func, Uobject_code_casm_func, 
                                  Uobject_code_legacy_func, Uobjects, In_uobj, 
                                  Uobj_finished, x_Uob, y_Uob, z_U, 
                                  cfunc_finished, in_cfunc, x_Uobj, y_Uobj, 
                                  z_Uo, casmfunc_finished, in_casmfunc, 
                                  x_Uobje, y, z, x >>

Uobject_code_casm_func_ == Start_Uobj \/ Loop_Uob \/ Cpu_assign_Uob

Start == /\ pc = "Start"
         /\ memory' = [memory EXCEPT !.memuobjcollection[y].uobject_sssa[x_Uobje].sp = Cpu[x_Uobje].sp]
         /\ pc' = "Memory_assign"
         /\ UNCHANGED << cpu, collection, object, Cpu, stack, S, x_, x_L, x_S, 
                         y_, x_U, y_U, x_Uo, y_Uo, z_, Uobject_code_c_func, 
                         Uobject_code_casm_func, Uobject_code_legacy_func, 
                         Uobjects, In_uobj, Uobj_finished, x_Uob, y_Uob, z_U, 
                         cfunc_finished, in_cfunc, x_Uobj, y_Uobj, z_Uo, 
                         casmfunc_finished, in_casmfunc, x_Uobje, y, z, x >>

Memory_assign == /\ pc = "Memory_assign"
                 /\ memory' = [memory EXCEPT !.memuobjcollection[y].uobject_sssa[x_Uobje].lr = Cpu[x_Uobje].lr]
                 /\ pc' = "Memory_assign_pc"
                 /\ UNCHANGED << cpu, collection, object, Cpu, stack, S, x_, 
                                 x_L, x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                                 Uobject_code_c_func, Uobject_code_casm_func, 
                                 Uobject_code_legacy_func, Uobjects, In_uobj, 
                                 Uobj_finished, x_Uob, y_Uob, z_U, 
                                 cfunc_finished, in_cfunc, x_Uobj, y_Uobj, 
                                 z_Uo, casmfunc_finished, in_casmfunc, x_Uobje, 
                                 y, z, x >>

Memory_assign_pc == /\ pc = "Memory_assign_pc"
                    /\ memory' = [memory EXCEPT !.memuobjcollection[y].uobject_sssa[x_Uobje].pc = 0]
                    /\ Cpu' = [Cpu EXCEPT ![x_Uobje].Lr = 0]
                    /\ pc' = "Cpu_assign"
                    /\ UNCHANGED << cpu, collection, object, stack, S, x_, x_L, 
                                    x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                                    Uobject_code_c_func, 
                                    Uobject_code_casm_func, 
                                    Uobject_code_legacy_func, Uobjects, 
                                    In_uobj, Uobj_finished, x_Uob, y_Uob, z_U, 
                                    cfunc_finished, in_cfunc, x_Uobj, y_Uobj, 
                                    z_Uo, casmfunc_finished, in_casmfunc, 
                                    x_Uobje, y, z, x >>

Cpu_assign == /\ pc = "Cpu_assign"
              /\ Cpu' = [Cpu EXCEPT ![x_Uobje].Pc = 0]
              /\ pc' = "Resumelegacy"
              /\ UNCHANGED << cpu, collection, object, memory, stack, S, x_, 
                              x_L, x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                              Uobject_code_c_func, Uobject_code_casm_func, 
                              Uobject_code_legacy_func, Uobjects, In_uobj, 
                              Uobj_finished, x_Uob, y_Uob, z_U, cfunc_finished, 
                              in_cfunc, x_Uobj, y_Uobj, z_Uo, 
                              casmfunc_finished, in_casmfunc, x_Uobje, y, z, x >>

Resumelegacy == /\ pc = "Resumelegacy"
                /\ Cpu' = [Cpu EXCEPT ![x_Uobje].Sp = memory.memuobjcollection[y].uobject_sssa[x_Uobje].sp]
                /\ pc' = "Cpu_assign_pc"
                /\ UNCHANGED << cpu, collection, object, memory, stack, S, x_, 
                                x_L, x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                                Uobject_code_c_func, Uobject_code_casm_func, 
                                Uobject_code_legacy_func, Uobjects, In_uobj, 
                                Uobj_finished, x_Uob, y_Uob, z_U, 
                                cfunc_finished, in_cfunc, x_Uobj, y_Uobj, z_Uo, 
                                casmfunc_finished, in_casmfunc, x_Uobje, y, z, 
                                x >>

Cpu_assign_pc == /\ pc = "Cpu_assign_pc"
                 /\ Cpu' = [Cpu EXCEPT ![x_Uobje].Pc = memory.memuobjcollection[y].uobject_sssa[x_Uobje].pc]
                 /\ pc' = "Error"
                 /\ UNCHANGED << cpu, collection, object, memory, stack, S, x_, 
                                 x_L, x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                                 Uobject_code_c_func, Uobject_code_casm_func, 
                                 Uobject_code_legacy_func, Uobjects, In_uobj, 
                                 Uobj_finished, x_Uob, y_Uob, z_U, 
                                 cfunc_finished, in_cfunc, x_Uobj, y_Uobj, 
                                 z_Uo, casmfunc_finished, in_casmfunc, x_Uobje, 
                                 y, z, x >>

Uobject_code_legacy_func_ == Start \/ Memory_assign \/ Memory_assign_pc
                                \/ Cpu_assign \/ Resumelegacy
                                \/ Cpu_assign_pc

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
          /\ UNCHANGED << cpu, collection, object, Cpu, memory, S, x_, x_L, 
                          x_S, y_, x_U, y_U, x_Uo, y_Uo, z_, 
                          Uobject_code_c_func, Uobject_code_casm_func, 
                          Uobject_code_legacy_func, Uobjects, In_uobj, 
                          Uobj_finished, x_Uob, y_Uob, z_U, cfunc_finished, 
                          in_cfunc, x_Uobj, y_Uobj, z_Uo, casmfunc_finished, 
                          in_casmfunc, x_Uobje, y, z >>

device_process == Loop_d

Loop == /\ pc = "Loop"
        /\ IF cpu > 0
              THEN /\ /\ stack' = << [ procedure |->  "Cpu_process",
                                       pc        |->  "Dec",
                                       x_        |->  x_ ] >>
                                   \o stack
                      /\ x_' = cpu
                   /\ pc' = "Start_C"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << stack, x_ >>
        /\ UNCHANGED << cpu, collection, object, Cpu, memory, S, x_L, x_S, y_, 
                        x_U, y_U, x_Uo, y_Uo, z_, Uobject_code_c_func, 
                        Uobject_code_casm_func, Uobject_code_legacy_func, 
                        Uobjects, In_uobj, Uobj_finished, x_Uob, y_Uob, z_U, 
                        cfunc_finished, in_cfunc, x_Uobj, y_Uobj, z_Uo, 
                        casmfunc_finished, in_casmfunc, x_Uobje, y, z, x >>

Dec == /\ pc = "Dec"
       /\ cpu' = cpu - 1
       /\ pc' = "Loop"
       /\ UNCHANGED << collection, object, Cpu, memory, stack, S, x_, x_L, x_S, 
                       y_, x_U, y_U, x_Uo, y_Uo, z_, Uobject_code_c_func, 
                       Uobject_code_casm_func, Uobject_code_legacy_func, 
                       Uobjects, In_uobj, Uobj_finished, x_Uob, y_Uob, z_U, 
                       cfunc_finished, in_cfunc, x_Uobj, y_Uobj, z_Uo, 
                       casmfunc_finished, in_casmfunc, x_Uobje, y, z, x >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Push_locals \/ Pop_locals \/ Cpu_process \/ Legacy_code \/ Sentinel
           \/ Uobjcollection_code \/ Uobject_code \/ Uobject_code_c_func_
           \/ Uobject_code_casm_func_ \/ Uobject_code_legacy_func_
           \/ device_process \/ Loop \/ Dec
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a6a112fc2a7d9d58571fe9f96e2417b9

=============================================================================
\* Modification History
\* Last modified Thu Dec 17 05:25:22 PST 2020 by mjmccall
\* Created Thu Aug 20 05:23:36 PDT 2020 by mjmccall
