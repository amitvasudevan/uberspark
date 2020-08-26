-------------------------------- MODULE toy --------------------------------
EXTENDS TLC, Sequences, Integers
CONSTANTS MAXCPUS, MAXUOBJCOLLECTIONS, MAXUOBJSWITHINCOLLECTION, MAXUOBJCOLLECTIONSTACKSIZE, MAXUOBJDEVMMIO 
E(n) == IF n \in MAXCPUS THEN TRUE ELSE FALSE
R(n) == 1..n

(* --algorithm execution
variables cpus = MAXCPUS,
    (**)Cpu = [x \in 1..MAXCPUS |->
              [id |-> x,
               Pc |-> 1,
               Sp |-> 1,
               Shared_cpustate |-> <<1,2,3>>,
               Legacy_cpustate |-> <<4,5,6>>,
               uobjcoll_cpustate |-> [y \in 1..MAXUOBJCOLLECTIONS |->
                 [z \in 1..MAXUOBJSWITHINCOLLECTION |-> {}
          ]]]],(**)
    \*cpu = [x \in 1..MAXCPUS |-> [id : 0, pop : [y \in R(5) |-> z]]];
    memory = [memuobjs \in 1..MAXUOBJSWITHINCOLLECTION |->
                [Uobj_ssa : 1..MAXCPUS,
                 Uobj_code : {},
                 Uobj_data : {},
                 Uobj_dmadata : {},
                 Uobj_devmmio : 1..MAXUOBJDEVMMIO]]

procedure Cpu_process(x) begin
Start:
    either
        call Legacy_code(x);
        return;
    or
        with y \in 1..MAXUOBJCOLLECTIONS do
            call Uobjcollection_code(x, y(*1..MAXUOBJCOLLECTIONS*)) (*?*);
        end with;
After_branching:
        return;
    end either;
end procedure;

procedure Legacy_code(x) begin
Start:
    while TRUE do
        either
            call Uobjcollection_code(x, 1..MAXUOBJCOLLECTIONS);
        or
            \*Execute code from memory.mem_legacy[]
            skip;
        or 
            \*Read/write to memory.mem_legacy[]
            skip;
        or  
            \*Read/write to cpu[x].shared_cpustate[]  
            skip;
        or  
            \*Read/write to cpu[x].legacy_cpustate[] 
            skip;
        or  
            return; 
        end either;
    end while;
end procedure;

procedure Uobjcollection_code(x, y) begin
Start:
    call Uobject_code(x, y, 1..MAXUOBJSWITHINCOLLECTION);
Return:
    Cpu[x].Pc := pc_pre_uobjectcollection_code;
Cpu_assign:
    Cpu[x].Sp := sp_pre_uobjectcollection_code;
end procedure;

procedure Uobject_code(x, y, z)
    variables Uobject_code_c_func = {f1..fn}, 
        Uobject_code_casm_func = {c1..cn}, 
        Uobject_code_legacy_funcLegacy_funcs = {l1..ln}; 
        Uobjects = {1..MAXUOBJS}, 
        In_uobj = FALSE,
        Uobj_finished = FALSE; 
    begin
Start:
    if ~in_uobj then
Loop:
        while ~uobj_finished do
            either
                Cpu[x].Pc :=  f \in uobject_code_c_func; 
            or 
                Cpu[x].Pc :=  c \in uobject_code_casm_func; 
            or  
                Cpu[x].Pc := l \in uobject_code_legacy_func; 
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
Uobj_finished_assign:
    Uobj_finished := FALSE;
    In_uobj := FALSE;
    Cpu[x].pc := pc_pre_uobject_code;
Cpu_assign:
    Cpu[x].Sp := sp_pre_uobject_code;
end procedure;

procedure Uobject_code_c_func(x, y, z)
    variables cfunc_finished, in_cfunc (*??*);
    begin
Start:
    if ~in_cfunc then
Loop:
        while ~cfunc_finished do 
            either
                Cpu[x].Pc :=  f \in uobject_code_c_func; 
            or 
                Cpu[x].Pc :=  c \in uobject_code_casm_func; 
            or  
                Cpu[x].pc := l \in uobject_code_legacy_func; 
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
    Cpu[x].pc := pc_pre_cfunc_code;
Cpu_assign: 
    Cpu[x].Sp := sp_pre_cfunc_code;
end procedure;

procedure Uobject_code_casm_func(x, y, z)
    variable casmfunc_finished, in_casmfunc (*??*);
    begin
Start: 
    if ~in_casmfunc then
Loop:
        while ~casmfunc_finished do
            either
                Cpu[x].Pc :=  f \in uobject_code_c_func; 
            or
                Cpu[x].Pc :=  c \in uobject_code_casm_func; 
            or
                Cpu[x].pc := l \in uobject_code_legacy_func;
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
        Cpu[x].pc := pc_pre_casmfunc_code;
Cpu_assign:
        Cpu[x].Sp := sp_pre_casmfunc_code;
    end if;
end procedure;

procedure Uobject_code_legacy_func(x,y,z) begin
Start:
    memory.memuobjcollection[y].uobject_sssa[x].sp := cpu[x].sp;
Memory_assign:
    memory.memuobjcollection[y].uobject_sssa[x].lr := cpu[x].lr;
Memory_assign_pc:
    memory.memuobjcollection[y].uobject_sssa[x].pc := pc_pre_legacy_func;
    Cpu[x].Lr := resumelegacy;
Cpu_assign:
    Cpu[x].Pc := legacy_code;
Resumelegacy:
    Cpu[x].Sp := memory.memuobjcollection[y].uobject_sssa[x].sp;
Cpu_assign_pc:
    Cpu[x].Pc := memory.memuobjcollection[y].uobject_sssa[x].pc;
end procedure;

begin
Loop:
while cpus > 0 do
    cpus := cpus - 1;
end while;

end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e80592a8f5fea872069aa806ca50a1d1
\* Label Start of procedure Cpu_process at line 28 col 5 changed to Start_
\* Label Start of procedure Legacy_code at line 42 col 5 changed to Start_L
\* Label Start of procedure Uobjcollection_code at line 65 col 5 changed to Start_U
\* Label Cpu_assign of procedure Uobjcollection_code at line 69 col 5 changed to Cpu_assign_
\* Label Start of procedure Uobject_code at line 81 col 5 changed to Start_Uo
\* Label Loop of procedure Uobject_code at line 83 col 9 changed to Loop_
\* Label Cpu_assign of procedure Uobject_code at line 109 col 5 changed to Cpu_assign_U
\* Label Start of procedure Uobject_code_c_func at line 116 col 5 changed to Start_Uob
\* Label Loop of procedure Uobject_code_c_func at line 118 col 9 changed to Loop_U
\* Label Cpu_assign of procedure Uobject_code_c_func at line 144 col 5 changed to Cpu_assign_Uo
\* Label Start of procedure Uobject_code_casm_func at line 151 col 5 changed to Start_Uobj
\* Label Loop of procedure Uobject_code_casm_func at line 153 col 9 changed to Loop_Uo
\* Label Cpu_assign of procedure Uobject_code_casm_func at line 177 col 9 changed to Cpu_assign_Uob
\* Procedure Uobject_code_c_func at line 112 col 1 changed to Uobject_code_c_func_
\* Procedure Uobject_code_casm_func at line 147 col 1 changed to Uobject_code_casm_func_
\* Parameter x of procedure Cpu_process at line 26 col 23 changed to x_
\* Parameter x of procedure Legacy_code at line 40 col 23 changed to x_L
\* Parameter x of procedure Uobjcollection_code at line 63 col 31 changed to x_U
\* Parameter y of procedure Uobjcollection_code at line 63 col 34 changed to y_
\* Parameter x of procedure Uobject_code at line 72 col 24 changed to x_Uo
\* Parameter y of procedure Uobject_code at line 72 col 27 changed to y_U
\* Parameter z of procedure Uobject_code at line 72 col 30 changed to z_
\* Parameter x of procedure Uobject_code_c_func at line 112 col 31 changed to x_Uob
\* Parameter y of procedure Uobject_code_c_func at line 112 col 34 changed to y_Uo
\* Parameter z of procedure Uobject_code_c_func at line 112 col 37 changed to z_U
\* Parameter x of procedure Uobject_code_casm_func at line 147 col 34 changed to x_Uobj
\* Parameter y of procedure Uobject_code_casm_func at line 147 col 37 changed to y_Uob
\* Parameter z of procedure Uobject_code_casm_func at line 147 col 40 changed to z_Uo
CONSTANT defaultInitValue
VARIABLES cpus, Cpu, memory, pc, stack, x_, x_L, x_U, y_, x_Uo, y_U, z_, 
          Uobject_code_c_func, Uobject_code_casm_func, 
          Uobject_code_legacy_funcLegacy_funcs, Uobjects, In_uobj, 
          Uobj_finished, x_Uob, y_Uo, z_U, cfunc_finished, in_cfunc, x_Uobj, 
          y_Uob, z_Uo, casmfunc_finished, in_casmfunc, x, y, z

vars == << cpus, Cpu, memory, pc, stack, x_, x_L, x_U, y_, x_Uo, y_U, z_, 
           Uobject_code_c_func, Uobject_code_casm_func, 
           Uobject_code_legacy_funcLegacy_funcs, Uobjects, In_uobj, 
           Uobj_finished, x_Uob, y_Uo, z_U, cfunc_finished, in_cfunc, x_Uobj, 
           y_Uob, z_Uo, casmfunc_finished, in_casmfunc, x, y, z >>

Init == (* Global variables *)
        /\ cpus = MAXCPUS
        /\ Cpu =     [x \in 1..MAXCPUS |->
                     [id |-> x,
                      Pc |-> 1,
                      Sp |-> 1,
                      Shared_cpustate |-> <<1,2,3>>,
                      Legacy_cpustate |-> <<4,5,6>>,
                      uobjcoll_cpustate |-> [y \in 1..MAXUOBJCOLLECTIONS |->
                        [z \in 1..MAXUOBJSWITHINCOLLECTION |-> {}
                 ]]]]
        /\ memory = [memuobjs \in 1..MAXUOBJSWITHINCOLLECTION |->
                       [Uobj_ssa : 1..MAXCPUS,
                        Uobj_code : {},
                        Uobj_data : {},
                        Uobj_dmadata : {},
                        Uobj_devmmio : 1..MAXUOBJDEVMMIO]]
        (* Procedure Cpu_process *)
        /\ x_ = defaultInitValue
        (* Procedure Legacy_code *)
        /\ x_L = defaultInitValue
        (* Procedure Uobjcollection_code *)
        /\ x_U = defaultInitValue
        /\ y_ = defaultInitValue
        (* Procedure Uobject_code *)
        /\ x_Uo = defaultInitValue
        /\ y_U = defaultInitValue
        /\ z_ = defaultInitValue
        /\ Uobject_code_c_func = {f1..fn}
        /\ Uobject_code_casm_func = {c1..cn}
        /\ Uobject_code_legacy_funcLegacy_funcs = {l1..ln}
        /\ Uobjects = {1..MAXUOBJS}
        /\ In_uobj = FALSE
        /\ Uobj_finished = FALSE
        (* Procedure Uobject_code_c_func_ *)
        /\ x_Uob = defaultInitValue
        /\ y_Uo = defaultInitValue
        /\ z_U = defaultInitValue
        /\ cfunc_finished = defaultInitValue
        /\ in_cfunc = defaultInitValue
        (* Procedure Uobject_code_casm_func_ *)
        /\ x_Uobj = defaultInitValue
        /\ y_Uob = defaultInitValue
        /\ z_Uo = defaultInitValue
        /\ casmfunc_finished = defaultInitValue
        /\ in_casmfunc = defaultInitValue
        (* Procedure Uobject_code_legacy_func *)
        /\ x = defaultInitValue
        /\ y = defaultInitValue
        /\ z = defaultInitValue
        /\ stack = << >>
        /\ pc = "Loop"

Start_ == /\ pc = "Start_"
          /\ \/ /\ /\ stack' = << [ procedure |->  "Legacy_code",
                                    pc        |->  Head(stack).pc,
                                    x_L       |->  x_L ] >>
                                \o Tail(stack)
                   /\ x_L' = x_
                /\ pc' = "Start_L"
                /\ UNCHANGED <<x_U, y_>>
             \/ /\ \E y \in 1..MAXUOBJCOLLECTIONS:
                     /\ /\ stack' = << [ procedure |->  "Uobjcollection_code",
                                         pc        |->  "After_branching",
                                         x_U       |->  x_U,
                                         y_        |->  y_ ] >>
                                     \o stack
                        /\ x_U' = x_
                        /\ y_' = y
                     /\ pc' = "Start_U"
                /\ x_L' = x_L
          /\ UNCHANGED << cpus, Cpu, memory, x_, x_Uo, y_U, z_, 
                          Uobject_code_c_func, Uobject_code_casm_func, 
                          Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                          In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, 
                          cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, 
                          casmfunc_finished, in_casmfunc, x, y, z >>

After_branching == /\ pc = "After_branching"
                   /\ pc' = Head(stack).pc
                   /\ x_' = Head(stack).x_
                   /\ stack' = Tail(stack)
                   /\ UNCHANGED << cpus, Cpu, memory, x_L, x_U, y_, x_Uo, y_U, 
                                   z_, Uobject_code_c_func, 
                                   Uobject_code_casm_func, 
                                   Uobject_code_legacy_funcLegacy_funcs, 
                                   Uobjects, In_uobj, Uobj_finished, x_Uob, 
                                   y_Uo, z_U, cfunc_finished, in_cfunc, x_Uobj, 
                                   y_Uob, z_Uo, casmfunc_finished, in_casmfunc, 
                                   x, y, z >>

Cpu_process == Start_ \/ After_branching

Start_L == /\ pc = "Start_L"
           /\ \/ /\ /\ stack' = << [ procedure |->  "Uobjcollection_code",
                                     pc        |->  "Start_L",
                                     x_U       |->  x_U,
                                     y_        |->  y_ ] >>
                                 \o stack
                    /\ x_U' = x_L
                    /\ y_' = 1..MAXUOBJCOLLECTIONS
                 /\ pc' = "Start_U"
                 /\ x_L' = x_L
              \/ /\ TRUE
                 /\ pc' = "Start_L"
                 /\ UNCHANGED <<stack, x_L, x_U, y_>>
              \/ /\ TRUE
                 /\ pc' = "Start_L"
                 /\ UNCHANGED <<stack, x_L, x_U, y_>>
              \/ /\ TRUE
                 /\ pc' = "Start_L"
                 /\ UNCHANGED <<stack, x_L, x_U, y_>>
              \/ /\ TRUE
                 /\ pc' = "Start_L"
                 /\ UNCHANGED <<stack, x_L, x_U, y_>>
              \/ /\ pc' = Head(stack).pc
                 /\ x_L' = Head(stack).x_L
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED <<x_U, y_>>
           /\ UNCHANGED << cpus, Cpu, memory, x_, x_Uo, y_U, z_, 
                           Uobject_code_c_func, Uobject_code_casm_func, 
                           Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                           In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, 
                           cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, 
                           casmfunc_finished, in_casmfunc, x, y, z >>

Legacy_code == Start_L

Start_U == /\ pc = "Start_U"
           /\ /\ stack' = << [ procedure |->  "Uobject_code",
                               pc        |->  "Return",
                               Uobject_code_c_func |->  Uobject_code_c_func,
                               Uobject_code_casm_func |->  Uobject_code_casm_func,
                               Uobject_code_legacy_funcLegacy_funcs |->  Uobject_code_legacy_funcLegacy_funcs,
                               Uobjects  |->  Uobjects,
                               In_uobj   |->  In_uobj,
                               Uobj_finished |->  Uobj_finished,
                               x_Uo      |->  x_Uo,
                               y_U       |->  y_U,
                               z_        |->  z_ ] >>
                           \o stack
              /\ x_Uo' = x_U
              /\ y_U' = y_
              /\ z_' = 1..MAXUOBJSWITHINCOLLECTION
           /\ Uobject_code_c_func' = {f1..fn}
           /\ Uobject_code_casm_func' = {c1..cn}
           /\ Uobject_code_legacy_funcLegacy_funcs' = {l1..ln}
           /\ Uobjects' = {1..MAXUOBJS}
           /\ In_uobj' = FALSE
           /\ Uobj_finished' = FALSE
           /\ pc' = "Start_Uo"
           /\ UNCHANGED << cpus, Cpu, memory, x_, x_L, x_U, y_, x_Uob, y_Uo, 
                           z_U, cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, 
                           casmfunc_finished, in_casmfunc, x, y, z >>

Return == /\ pc = "Return"
          /\ Cpu' = [Cpu EXCEPT ![x_U].Pc = pc_pre_uobjectcollection_code]
          /\ pc' = "Cpu_assign_"
          /\ UNCHANGED << cpus, memory, stack, x_, x_L, x_U, y_, x_Uo, y_U, z_, 
                          Uobject_code_c_func, Uobject_code_casm_func, 
                          Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                          In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, 
                          cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, 
                          casmfunc_finished, in_casmfunc, x, y, z >>

Cpu_assign_ == /\ pc = "Cpu_assign_"
               /\ Cpu' = [Cpu EXCEPT ![x_U].Sp = sp_pre_uobjectcollection_code]
               /\ pc' = "Error"
               /\ UNCHANGED << cpus, memory, stack, x_, x_L, x_U, y_, x_Uo, 
                               y_U, z_, Uobject_code_c_func, 
                               Uobject_code_casm_func, 
                               Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                               In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, 
                               cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, 
                               casmfunc_finished, in_casmfunc, x, y, z >>

Uobjcollection_code == Start_U \/ Return \/ Cpu_assign_

Start_Uo == /\ pc = "Start_Uo"
            /\ IF ~in_uobj
                  THEN /\ pc' = "Loop_"
                  ELSE /\ pc' = "Uobj_finished_assign"
            /\ UNCHANGED << cpus, Cpu, memory, stack, x_, x_L, x_U, y_, x_Uo, 
                            y_U, z_, Uobject_code_c_func, 
                            Uobject_code_casm_func, 
                            Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                            In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, 
                            cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, 
                            casmfunc_finished, in_casmfunc, x, y, z >>

Loop_ == /\ pc = "Loop_"
         /\ IF ~uobj_finished
               THEN /\ \/ /\ Cpu' = [Cpu EXCEPT ![x_Uo].Pc = f \in uobject_code_c_func]
                          /\ UNCHANGED Uobj_finished
                       \/ /\ Cpu' = [Cpu EXCEPT ![x_Uo].Pc = c \in uobject_code_casm_func]
                          /\ UNCHANGED Uobj_finished
                       \/ /\ Cpu' = [Cpu EXCEPT ![x_Uo].Pc = l \in uobject_code_legacy_func]
                          /\ UNCHANGED Uobj_finished
                       \/ /\ TRUE
                          /\ UNCHANGED <<Cpu, Uobj_finished>>
                       \/ /\ TRUE
                          /\ UNCHANGED <<Cpu, Uobj_finished>>
                       \/ /\ TRUE
                          /\ UNCHANGED <<Cpu, Uobj_finished>>
                       \/ /\ Uobj_finished' = TRUE
                          /\ Cpu' = Cpu
                    /\ pc' = "Loop_"
               ELSE /\ pc' = "Uobj_finished_assign"
                    /\ UNCHANGED << Cpu, Uobj_finished >>
         /\ UNCHANGED << cpus, memory, stack, x_, x_L, x_U, y_, x_Uo, y_U, z_, 
                         Uobject_code_c_func, Uobject_code_casm_func, 
                         Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                         In_uobj, x_Uob, y_Uo, z_U, cfunc_finished, in_cfunc, 
                         x_Uobj, y_Uob, z_Uo, casmfunc_finished, in_casmfunc, 
                         x, y, z >>

Uobj_finished_assign == /\ pc = "Uobj_finished_assign"
                        /\ Uobj_finished' = FALSE
                        /\ In_uobj' = FALSE
                        /\ Cpu' = [Cpu EXCEPT ![x_Uo].pc = pc_pre_uobject_code]
                        /\ pc' = "Cpu_assign_U"
                        /\ UNCHANGED << cpus, memory, stack, x_, x_L, x_U, y_, 
                                        x_Uo, y_U, z_, Uobject_code_c_func, 
                                        Uobject_code_casm_func, 
                                        Uobject_code_legacy_funcLegacy_funcs, 
                                        Uobjects, x_Uob, y_Uo, z_U, 
                                        cfunc_finished, in_cfunc, x_Uobj, 
                                        y_Uob, z_Uo, casmfunc_finished, 
                                        in_casmfunc, x, y, z >>

Cpu_assign_U == /\ pc = "Cpu_assign_U"
                /\ Cpu' = [Cpu EXCEPT ![x_Uo].Sp = sp_pre_uobject_code]
                /\ pc' = "Error"
                /\ UNCHANGED << cpus, memory, stack, x_, x_L, x_U, y_, x_Uo, 
                                y_U, z_, Uobject_code_c_func, 
                                Uobject_code_casm_func, 
                                Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                                In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, 
                                cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, 
                                casmfunc_finished, in_casmfunc, x, y, z >>

Uobject_code == Start_Uo \/ Loop_ \/ Uobj_finished_assign \/ Cpu_assign_U

Start_Uob == /\ pc = "Start_Uob"
             /\ IF ~in_cfunc
                   THEN /\ pc' = "Loop_U"
                   ELSE /\ pc' = "Cfunc_finished_assign"
             /\ UNCHANGED << cpus, Cpu, memory, stack, x_, x_L, x_U, y_, x_Uo, 
                             y_U, z_, Uobject_code_c_func, 
                             Uobject_code_casm_func, 
                             Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                             In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, 
                             cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, 
                             casmfunc_finished, in_casmfunc, x, y, z >>

Loop_U == /\ pc = "Loop_U"
          /\ IF ~cfunc_finished
                THEN /\ \/ /\ Cpu' = [Cpu EXCEPT ![x_Uob].Pc = f \in uobject_code_c_func]
                           /\ UNCHANGED cfunc_finished
                        \/ /\ Cpu' = [Cpu EXCEPT ![x_Uob].Pc = c \in uobject_code_casm_func]
                           /\ UNCHANGED cfunc_finished
                        \/ /\ Cpu' = [Cpu EXCEPT ![x_Uob].pc = l \in uobject_code_legacy_func]
                           /\ UNCHANGED cfunc_finished
                        \/ /\ TRUE
                           /\ UNCHANGED <<Cpu, cfunc_finished>>
                        \/ /\ TRUE
                           /\ UNCHANGED <<Cpu, cfunc_finished>>
                        \/ /\ TRUE
                           /\ UNCHANGED <<Cpu, cfunc_finished>>
                        \/ /\ cfunc_finished' = TRUE
                           /\ Cpu' = Cpu
                     /\ pc' = "Loop_U"
                ELSE /\ pc' = "Cfunc_finished_assign"
                     /\ UNCHANGED << Cpu, cfunc_finished >>
          /\ UNCHANGED << cpus, memory, stack, x_, x_L, x_U, y_, x_Uo, y_U, z_, 
                          Uobject_code_c_func, Uobject_code_casm_func, 
                          Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                          In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, in_cfunc, 
                          x_Uobj, y_Uob, z_Uo, casmfunc_finished, in_casmfunc, 
                          x, y, z >>

Cfunc_finished_assign == /\ pc = "Cfunc_finished_assign"
                         /\ cfunc_finished' = FALSE
                         /\ in_cfunc' = FALSE
                         /\ Cpu' = [Cpu EXCEPT ![x_Uob].pc = pc_pre_cfunc_code]
                         /\ pc' = "Cpu_assign_Uo"
                         /\ UNCHANGED << cpus, memory, stack, x_, x_L, x_U, y_, 
                                         x_Uo, y_U, z_, Uobject_code_c_func, 
                                         Uobject_code_casm_func, 
                                         Uobject_code_legacy_funcLegacy_funcs, 
                                         Uobjects, In_uobj, Uobj_finished, 
                                         x_Uob, y_Uo, z_U, x_Uobj, y_Uob, z_Uo, 
                                         casmfunc_finished, in_casmfunc, x, y, 
                                         z >>

Cpu_assign_Uo == /\ pc = "Cpu_assign_Uo"
                 /\ Cpu' = [Cpu EXCEPT ![x_Uob].Sp = sp_pre_cfunc_code]
                 /\ pc' = "Error"
                 /\ UNCHANGED << cpus, memory, stack, x_, x_L, x_U, y_, x_Uo, 
                                 y_U, z_, Uobject_code_c_func, 
                                 Uobject_code_casm_func, 
                                 Uobject_code_legacy_funcLegacy_funcs, 
                                 Uobjects, In_uobj, Uobj_finished, x_Uob, y_Uo, 
                                 z_U, cfunc_finished, in_cfunc, x_Uobj, y_Uob, 
                                 z_Uo, casmfunc_finished, in_casmfunc, x, y, z >>

Uobject_code_c_func_ == Start_Uob \/ Loop_U \/ Cfunc_finished_assign
                           \/ Cpu_assign_Uo

Start_Uobj == /\ pc = "Start_Uobj"
              /\ IF ~in_casmfunc
                    THEN /\ pc' = "Loop_Uo"
                    ELSE /\ pc' = "Error"
              /\ UNCHANGED << cpus, Cpu, memory, stack, x_, x_L, x_U, y_, x_Uo, 
                              y_U, z_, Uobject_code_c_func, 
                              Uobject_code_casm_func, 
                              Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                              In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, 
                              cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, 
                              casmfunc_finished, in_casmfunc, x, y, z >>

Loop_Uo == /\ pc = "Loop_Uo"
           /\ IF ~casmfunc_finished
                 THEN /\ \/ /\ Cpu' = [Cpu EXCEPT ![x_Uobj].Pc = f \in uobject_code_c_func]
                            /\ UNCHANGED casmfunc_finished
                         \/ /\ Cpu' = [Cpu EXCEPT ![x_Uobj].Pc = c \in uobject_code_casm_func]
                            /\ UNCHANGED casmfunc_finished
                         \/ /\ Cpu' = [Cpu EXCEPT ![x_Uobj].pc = l \in uobject_code_legacy_func]
                            /\ UNCHANGED casmfunc_finished
                         \/ /\ TRUE
                            /\ UNCHANGED <<Cpu, casmfunc_finished>>
                         \/ /\ TRUE
                            /\ UNCHANGED <<Cpu, casmfunc_finished>>
                         \/ /\ TRUE
                            /\ UNCHANGED <<Cpu, casmfunc_finished>>
                         \/ /\ casmfunc_finished' = TRUE
                            /\ Cpu' = Cpu
                      /\ pc' = "Loop_Uo"
                      /\ UNCHANGED in_casmfunc
                 ELSE /\ casmfunc_finished' = FALSE
                      /\ in_casmfunc' = FALSE
                      /\ Cpu' = [Cpu EXCEPT ![x_Uobj].pc = pc_pre_casmfunc_code]
                      /\ pc' = "Cpu_assign_Uob"
           /\ UNCHANGED << cpus, memory, stack, x_, x_L, x_U, y_, x_Uo, y_U, 
                           z_, Uobject_code_c_func, Uobject_code_casm_func, 
                           Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                           In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, 
                           cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, x, y, 
                           z >>

Cpu_assign_Uob == /\ pc = "Cpu_assign_Uob"
                  /\ Cpu' = [Cpu EXCEPT ![x_Uobj].Sp = sp_pre_casmfunc_code]
                  /\ pc' = "Error"
                  /\ UNCHANGED << cpus, memory, stack, x_, x_L, x_U, y_, x_Uo, 
                                  y_U, z_, Uobject_code_c_func, 
                                  Uobject_code_casm_func, 
                                  Uobject_code_legacy_funcLegacy_funcs, 
                                  Uobjects, In_uobj, Uobj_finished, x_Uob, 
                                  y_Uo, z_U, cfunc_finished, in_cfunc, x_Uobj, 
                                  y_Uob, z_Uo, casmfunc_finished, in_casmfunc, 
                                  x, y, z >>

Uobject_code_casm_func_ == Start_Uobj \/ Loop_Uo \/ Cpu_assign_Uob

Start == /\ pc = "Start"
         /\ memory' = [memory EXCEPT !.memuobjcollection[y].uobject_sssa[x].sp = cpu[x].sp]
         /\ pc' = "Memory_assign"
         /\ UNCHANGED << cpus, Cpu, stack, x_, x_L, x_U, y_, x_Uo, y_U, z_, 
                         Uobject_code_c_func, Uobject_code_casm_func, 
                         Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                         In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, 
                         cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, 
                         casmfunc_finished, in_casmfunc, x, y, z >>

Memory_assign == /\ pc = "Memory_assign"
                 /\ memory' = [memory EXCEPT !.memuobjcollection[y].uobject_sssa[x].lr = cpu[x].lr]
                 /\ pc' = "Memory_assign_pc"
                 /\ UNCHANGED << cpus, Cpu, stack, x_, x_L, x_U, y_, x_Uo, y_U, 
                                 z_, Uobject_code_c_func, 
                                 Uobject_code_casm_func, 
                                 Uobject_code_legacy_funcLegacy_funcs, 
                                 Uobjects, In_uobj, Uobj_finished, x_Uob, y_Uo, 
                                 z_U, cfunc_finished, in_cfunc, x_Uobj, y_Uob, 
                                 z_Uo, casmfunc_finished, in_casmfunc, x, y, z >>

Memory_assign_pc == /\ pc = "Memory_assign_pc"
                    /\ memory' = [memory EXCEPT !.memuobjcollection[y].uobject_sssa[x].pc = pc_pre_legacy_func]
                    /\ Cpu' = [Cpu EXCEPT ![x].Lr = resumelegacy]
                    /\ pc' = "Cpu_assign"
                    /\ UNCHANGED << cpus, stack, x_, x_L, x_U, y_, x_Uo, y_U, 
                                    z_, Uobject_code_c_func, 
                                    Uobject_code_casm_func, 
                                    Uobject_code_legacy_funcLegacy_funcs, 
                                    Uobjects, In_uobj, Uobj_finished, x_Uob, 
                                    y_Uo, z_U, cfunc_finished, in_cfunc, 
                                    x_Uobj, y_Uob, z_Uo, casmfunc_finished, 
                                    in_casmfunc, x, y, z >>

Cpu_assign == /\ pc = "Cpu_assign"
              /\ Cpu' = [Cpu EXCEPT ![x].Pc = legacy_code]
              /\ pc' = "Resumelegacy"
              /\ UNCHANGED << cpus, memory, stack, x_, x_L, x_U, y_, x_Uo, y_U, 
                              z_, Uobject_code_c_func, Uobject_code_casm_func, 
                              Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                              In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, 
                              cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, 
                              casmfunc_finished, in_casmfunc, x, y, z >>

Resumelegacy == /\ pc = "Resumelegacy"
                /\ Cpu' = [Cpu EXCEPT ![x].Sp = memory.memuobjcollection[y].uobject_sssa[x].sp]
                /\ pc' = "Cpu_assign_pc"
                /\ UNCHANGED << cpus, memory, stack, x_, x_L, x_U, y_, x_Uo, 
                                y_U, z_, Uobject_code_c_func, 
                                Uobject_code_casm_func, 
                                Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                                In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, 
                                cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, 
                                casmfunc_finished, in_casmfunc, x, y, z >>

Cpu_assign_pc == /\ pc = "Cpu_assign_pc"
                 /\ Cpu' = [Cpu EXCEPT ![x].Pc = memory.memuobjcollection[y].uobject_sssa[x].pc]
                 /\ pc' = "Error"
                 /\ UNCHANGED << cpus, memory, stack, x_, x_L, x_U, y_, x_Uo, 
                                 y_U, z_, Uobject_code_c_func, 
                                 Uobject_code_casm_func, 
                                 Uobject_code_legacy_funcLegacy_funcs, 
                                 Uobjects, In_uobj, Uobj_finished, x_Uob, y_Uo, 
                                 z_U, cfunc_finished, in_cfunc, x_Uobj, y_Uob, 
                                 z_Uo, casmfunc_finished, in_casmfunc, x, y, z >>

Uobject_code_legacy_func == Start \/ Memory_assign \/ Memory_assign_pc
                               \/ Cpu_assign \/ Resumelegacy
                               \/ Cpu_assign_pc

Loop == /\ pc = "Loop"
        /\ IF cpus > 0
              THEN /\ cpus' = cpus - 1
                   /\ pc' = "Loop"
              ELSE /\ pc' = "Done"
                   /\ cpus' = cpus
        /\ UNCHANGED << Cpu, memory, stack, x_, x_L, x_U, y_, x_Uo, y_U, z_, 
                        Uobject_code_c_func, Uobject_code_casm_func, 
                        Uobject_code_legacy_funcLegacy_funcs, Uobjects, 
                        In_uobj, Uobj_finished, x_Uob, y_Uo, z_U, 
                        cfunc_finished, in_cfunc, x_Uobj, y_Uob, z_Uo, 
                        casmfunc_finished, in_casmfunc, x, y, z >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Cpu_process \/ Legacy_code \/ Uobjcollection_code \/ Uobject_code
           \/ Uobject_code_c_func_ \/ Uobject_code_casm_func_
           \/ Uobject_code_legacy_func \/ Loop
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-0d9af0226865b07194dc01668462226e

=============================================================================
\* Modification History
\* Last modified Wed Aug 26 05:59:56 PDT 2020 by mjmccall
\* Created Thu Aug 20 05:23:36 PDT 2020 by mjmccall
