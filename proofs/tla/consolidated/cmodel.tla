---- MODULE cmodel ----
EXTENDS TLC, Sequences, Integers
CONSTANTS MAXUOBJCOLLECTIONS, MAXUOBJSWITHINCOLLECTION

CONSTANTS MAX_TLB_ENTRIES (* ADD *)

MAXCPUS == 2

LEGACY == 1
SENTINEL == 2
UBER == 3

LOAD == 1
STORE == 2
LEGLOAD == 3
LEGSTORE == 4
CS == 5

(* ADD-START *)
(* ADD-END *)

(* ADD-START *)
TLB_TYPE_NONE     == 0
TLB_TYPE_SENTINEL == 1
TLB_TYPE_UOBJCOLL == 2
TLB_TYPE_LEGACY   == 3
TLB_TYPE_INITMETHOD_ENTRYSENTINEL  == 4
TLB_TYPE_PUBLICMETHOD_ENTRYSENTINEL == 5
TLB_TYPE_RESUMEMETHOD_ENTRYSENTINEL == 6


TLB_OP_READ    == 1
TLB_OP_WRITE   == 2
TLB_OP_EXECUTE == 3

PRIVILEGE_LEVEL_UOBJCOLL == 0
PRIVILEGE_LEVEL_LEGACY   == 3

MEM_SIZE == 268435456 \*0x10000000 = 256MB

\* the following are defined assuming a total physical memory of // 0x10000000 = 256MB



UOBJCOLL_SENTINEL_PHYSICAL_ADDR_BASE    == 0 \*0x000000006
UOBJCOLL_SENTINEL_PHYSICAL_ADDR_SIZE    == 393216 \* 0x00060000

UOBJCOLL_INITMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_BASE == 0
UOBJCOLL_INITMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_SIZE == 131072

UOBJCOLL_PUBLICMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_BASE == 131072
UOBJCOLL_PUBLICMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_SIZE == 131072

UOBJCOLL_RESUMEMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_BASE == 262144
UOBJCOLL_RESUMEMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_SIZE == 131072

UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_BASE == 393216 \* 0x00060000
UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_SIZE == 16777216 \* 0x01000000
LEGACY_PHYSICAL_ADDR_BASE               == 17170432 \*0x01060000
LEGACY_PHYSICAL_ADDR_SIZE               == 251265024 \*0x0EFA0000

(* the following are defined assuming a 32-bit linear addressing space 
 that permits addressing from 0x00000000 through 0xFFFFFFFF 
 note the following addresses are initialized to non-overlapping 
 and can be part of either first stage page-tables, second stage page-tables 
 or even regular segmentation
*)

UOBJCOLL_SENTINEL_LINEAR_ADDR_BASE    == 268435456 \*0x10000000
UOBJCOLL_SENTINEL_LINEAR_ADDR_SIZE    == 393216 \*0x00060000

UOBJCOLL_INITMETHOD_ENTRYSENTINEL_LINEAR_ADDR_BASE == 268435456 \* 0x10000000
UOBJCOLL_INITMETHOD_ENTRYSENTINEL_LINEAR_ADDR_SIZE == 131072 \* 0x00020000

UOBJCOLL_PUBLICMETHOD_ENTRYSENTINEL_LINEAR_ADDR_BASE == 268566528 \* 0x10020000
UOBJCOLL_PUBLICMETHOD_ENTRYSENTINEL_LINEAR_ADDR_SIZE == 131072 \* 0x00020000

UOBJCOLL_RESUMEMETHOD_ENTRYSENTINEL_LINEAR_ADDR_BASE == 268697600 \* 0x10040000
UOBJCOLL_RESUMEMETHOD_ENTRYSENTINEL_LINEAR_ADDR_SIZE == 131072 \* 0x00020000

UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE == 268828672 \* 0x10060000
UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE == 16777216 \* 0x01000000

LEGACY_LINEAR_ADDR_BASE == 285605888 \* 0x11060000
LEGACY_LINEAR_ADDR_SIZE == 251265024 \* 0x0EFA0000


nondet_u8  == 0
nondet_u32 == {0,1,2,3}

(* ADD-END *)


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
    memory_load_return = 0,
    x_memory_load_return = 0, (* ADD *)
    
    (* ADD-START *)
    tlb = [entry \in 0..MAX_TLB_ENTRIES-1 |->
                    [linear_addr_base |-> 0,
                     linear_addr_size |-> 0,
                     physical_addr_base |-> 0,
                     physical_addr_size |-> 0,
                     rpl |-> 0, \* requestor_privilege_level
                     op_mask |-> 0]], \*logical OR of TLB_OP_READ, TLB_OP_WRITE and/or TLB_OP_EXECUTE u32 type; //can be one of TLB_TYPE_SENTINEL, TLB_TYPE_UOBJCOLL, TLB_TYPE_LEGACY
         tlb_type_return = 0, (* TODO: Make sure this have write/read atomicity *)
         tlb_lookup_return = 0,
         memory_paddr = 0(*[address \in 0..268435456|-> 0]*)
        \* perhaps convert this into a scalar variable so writing to it denotes write to memory store
        \* and reading from it denotes reading from physical memory store
         
         \*addr \in nondet_u32;
    
    (* ADD-END *)
    
    ;

(*
    low-level memory load operation
    p = CPU index, c = uobjcoll index, o = uobject index, l = boolean which
    is true if legacy code, else false
*)
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

(*
    low-level memory store operation
    p = CPU index, c = uobjcoll index, o = uobject index, l = boolean which
    is true if legacy code, else false
    val = value to be stored
*)
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



(* ADD-START *)
procedure tlb_init() begin
Start:
    tlb[0].linear_addr_base := UOBJCOLL_SENTINEL_LINEAR_ADDR_BASE;
TLB_0:
    tlb[0].linear_addr_size := UOBJCOLL_SENTINEL_LINEAR_ADDR_SIZE;
TLB_1:
    tlb[0].physical_addr_base := UOBJCOLL_SENTINEL_PHYSICAL_ADDR_BASE;
TLB_2:
    tlb[0].physical_addr_size := UOBJCOLL_SENTINEL_PHYSICAL_ADDR_SIZE;
TLB_3:
    tlb[0].rpl := PRIVILEGE_LEVEL_LEGACY;
TLB_4:    
    tlb[0].op_mask := {TLB_OP_READ, TLB_OP_EXECUTE}; \* TLB_OP_READ | TLB_OP_EXECUTE;
TLB_5:    
    tlb[0].type := TLB_TYPE_SENTINEL;

TLB_6:
    tlb[1].linear_addr_base := UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE;
TLB_7:    
    tlb[1].linear_addr_size := UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE;
TLB_8:    
    tlb[1].physical_addr_base := UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_BASE;
TLB_9:    
    tlb[1].physical_addr_size := UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_SIZE;
TLB_10:    
    tlb[1].rpl := PRIVILEGE_LEVEL_UOBJCOLL;
TLB_11:    
    tlb[1].op_mask := {TLB_OP_READ, TLB_OP_WRITE, TLB_OP_EXECUTE}; \* TLB_OP_READ | TLB_OP_WRITE | TLB_OP_EXECUTE;
TLB_12:    
    tlb[1].type := TLB_TYPE_UOBJCOLL;

TLB_13:
    tlb[2].linear_addr_base := LEGACY_LINEAR_ADDR_BASE;
TLB_14:    
    tlb[2].linear_addr_size := LEGACY_LINEAR_ADDR_SIZE;
TLB_15:    
    tlb[2].physical_addr_base := LEGACY_PHYSICAL_ADDR_BASE;
TLB_16:    
    tlb[2].physical_addr_size := LEGACY_PHYSICAL_ADDR_SIZE;
TLB_17:    
    tlb[2].rpl := PRIVILEGE_LEVEL_LEGACY;
TLB_18:    
    tlb[2].op_mask := {TLB_OP_READ, TLB_OP_WRITE, TLB_OP_EXECUTE}; \* TLB_OP_READ | TLB_OP_WRITE | TLB_OP_EXECUTE;
TLB_19:    
    tlb[2].type := TLB_TYPE_LEGACY;
    return;
end procedure;

\* get the TLB type for a given address, return TLB_TYPE_NONE if we // did not find an entry for the given addr
procedure tlb_type(addr)
    variables tlb_type_i = 0;
    begin
Loop:
    while tlb_type_i < MAX_TLB_ENTRIES do
        if addr > tlb[tlb_type_i].linear_addr_base /\ addr <= (tlb[tlb_type_i].linear_addr_base + tlb[tlb_type_i].linear_addr_size) then
            tlb_type_return := tlb[tlb_type_i].type;
            return;
        end if;
Inc:
        tlb_type_i := tlb_type_i + 1;
    end while;
    tlb_type_return := TLB_TYPE_NONE;
    return;
end procedure;

\* lookup TLB for a given address, current privilege level, and action (read, write or execute) // return true and the physical address if successful, else false
procedure tlb_lookup(addr, cpl, tlb_op_mask)
    variables tlb_lookup_i = 0;
    begin
Loop:
    while tlb_lookup_i < MAX_TLB_ENTRIES do
        if addr > tlb[tlb_lookup_i].linear_addr_base /\ addr <= (tlb[tlb_lookup_i].linear_addr_base + tlb[tlb_lookup_i].linear_addr_size) /\ tlb[tlb_lookup_i].rpl = cpl /\ tlb[tlb_lookup_i].op_mask \in tlb_op_mask  then
            tlb_lookup_return := <<TRUE, tlb[tlb_lookup_i].physical_addr_base + (addr - tlb[tlb_lookup_i].linear_addr_base)>>;
            return;
        end if;
Inc:
        tlb_lookup_i := tlb_lookup_i + 1;
    end while;
    tlb_lookup_return := <<FALSE, 0>>;
    return;
end procedure;

(* the following two likely need to be folded into existing memory_load
and memory_store procedure definitions. they use a scalar variable approach
where the vetted addr passed is simply discarded and a value is instead
written to or read from a scalar variable *)

\* the physical addr has been vetted by the TLB translation
procedure x_memory_load(addr) begin
Start:
    x_memory_load_return := memory_paddr(*[addr]*);
    return;
end procedure;

\* the physical addr has been vetted by the TLB translation
procedure x_memory_store(addr, val) begin
Start:
    memory_paddr(*[addr]*) := val;
    return;
end procedure;


procedure cpu_read(addr, level) (* TODO: added privilege level*)
    variables status, paddr, tmp;
    begin
Start:
    call tlb_lookup(addr, level, TLB_OP_READ); \* returns true if successful lookup
Return:    
    status := tlb_lookup_return[1];
    paddr := tlb_lookup_return[2];
    if status then
        call x_memory_load(paddr);
Ret_load:
        tmp := x_memory_load_return;
    else
        skip; \* call cpu_halt(); \* error in lookup
    end if;
End:
    return;
end procedure;


procedure cpu_write(addr, level) begin (* TODO: added privilege level*)
Start:
    call tlb_lookup(addr, level, TLB_OP_WRITE); \* returns true if successful lookup
Return:
    status := tlb_lookup_return[1];
    paddr := tlb_lookup_return[2];
    if status then
        tmp := nondet_u8;
        call x_memory_store(paddr, tmp);
    else
        skip; \* call cpu_halt(); \* error in lookup
    end if;
End:
    return;
end procedure;

procedure cpu_execute(addr, level) (* TODO: added privilege level*)
    variables type, status, paddr;
    begin
Start:
    call tlb_type(addr);
Return:
    type := tlb_type_return;
    call tlb_lookup(addr, level, TLB_OP_EXECUTE);
Ret_lookup:
    status := tlb_lookup_return[1];
    paddr := tlb_lookup_return[2];
    if status then
        if type = TLB_TYPE_SENTINEL then
            skip; \* call sentinel();   (* TODO: Represent sentinel *)
        else
            skip; \* call cpu_halt();
        end if;
    else
        skip; \* call cpu_halt(); \* error in lookup
    end if;
End:
    return;
end procedure;


(* ADD-END *)


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

            (* ADD-START *)
            (* TBD: we have the convert the above three calls to 
            call uobjcollection_code, memory_load and memory_store to follow the following
            pattern for reads, writes and executes; the call uobjcollection_code will
            then happen within cpu_execute *)
            with case \in nondet_u32, rand_addr \in nondet_u32 do
                \*case := case % 4;
                if case = 0 then
                    call cpu_read(rand_addr, PRIVILEGE_LEVEL_LEGACY);
                elsif case = 1 then 
                    call cpu_write(rand_addr, PRIVILEGE_LEVEL_LEGACY);
                elsif case = 2 then
                    call cpu_execute(rand_addr, PRIVILEGE_LEVEL_LEGACY);
                else
                    skip; \* call cpu_halt();
                end if;
            end with;
            (* ADD-END *)
            
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

\* BEGIN TRANSLATION (chksum(pcal) = "32aae2f3" /\ chksum(tla) = "95ab5986")
\* Label Start of procedure memory_load at line 153 col 1 changed to Start_
\* Label Start of procedure memory_store at line 178 col 1 changed to Start_m
\* Label Start of procedure tlb_init at line 200 col 5 changed to Start_t
\* Label Loop of procedure tlb_type at line 251 col 5 changed to Loop_
\* Label Inc of procedure tlb_type at line 257 col 9 changed to Inc_
\* Label Loop of procedure tlb_lookup at line 268 col 5 changed to Loop_t
\* Label Start of procedure x_memory_load at line 288 col 5 changed to Start_x
\* Label Start of procedure x_memory_store at line 295 col 5 changed to Start_x_
\* Label Start of procedure cpu_read at line 304 col 5 changed to Start_c
\* Label Return of procedure cpu_read at line 306 col 5 changed to Return_
\* Label End of procedure cpu_read at line 316 col 5 changed to End_
\* Label Start of procedure cpu_write at line 322 col 5 changed to Start_cp
\* Label Return of procedure cpu_write at line 324 col 5 changed to Return_c
\* Label End of procedure cpu_write at line 333 col 5 changed to End_c
\* Label Start of procedure cpu_execute at line 340 col 5 changed to Start_cpu
\* Label Return of procedure cpu_execute at line 342 col 5 changed to Return_cp
\* Label End of procedure cpu_execute at line 357 col 5 changed to End_cp
\* Label Start of procedure Cpu_process at line 372 col 5 changed to Start_C
\* Label Call of procedure Cpu_process at line 378 col 9 changed to Call_
\* Label Start of procedure Legacy_code at line 398 col 5 changed to Start_L
\* Label Start of procedure Uobjcollection_code at line 451 col 5 changed to Start_U
\* Label Start of procedure Uobject_code at line 471 col 5 changed to Start_Uo
\* Label End of procedure Uobject_code at line 507 col 5 changed to End_U
\* Label A of process one at line 526 col 5 changed to A_
\* Procedure variable status of procedure cpu_read at line 301 col 15 changed to status_
\* Procedure variable paddr of procedure cpu_read at line 301 col 23 changed to paddr_
\* Procedure variable collection of procedure Cpu_process at line 369 col 15 changed to collection_
\* Parameter p of procedure memory_load at line 151 col 23 changed to p_
\* Parameter c of procedure memory_load at line 151 col 26 changed to c_
\* Parameter o of procedure memory_load at line 151 col 29 changed to o_
\* Parameter l of procedure memory_load at line 151 col 32 changed to l_
\* Parameter p of procedure memory_store at line 176 col 24 changed to p_m
\* Parameter c of procedure memory_store at line 176 col 27 changed to c_m
\* Parameter o of procedure memory_store at line 176 col 30 changed to o_m
\* Parameter val of procedure memory_store at line 176 col 36 changed to val_
\* Parameter addr of procedure tlb_type at line 247 col 20 changed to addr_
\* Parameter addr of procedure tlb_lookup at line 264 col 22 changed to addr_t
\* Parameter addr of procedure x_memory_load at line 286 col 25 changed to addr_x
\* Parameter addr of procedure x_memory_store at line 293 col 26 changed to addr_x_
\* Parameter addr of procedure cpu_read at line 300 col 20 changed to addr_c
\* Parameter level of procedure cpu_read at line 300 col 26 changed to level_
\* Parameter addr of procedure cpu_write at line 320 col 21 changed to addr_cp
\* Parameter level of procedure cpu_write at line 320 col 27 changed to level_c
\* Parameter p of procedure Cpu_process at line 368 col 23 changed to p_C
\* Parameter p of procedure Legacy_code at line 394 col 23 changed to p_L
\* Parameter saved_pc of procedure Legacy_code at line 394 col 26 changed to saved_pc_
\* Parameter p of procedure Uobjcollection_code at line 449 col 31 changed to p_U
\* Parameter c of procedure Uobjcollection_code at line 449 col 34 changed to c_U
\* Parameter saved_pc of procedure Uobjcollection_code at line 449 col 37 changed to saved_pc_U
\* Parameter p of procedure Uobject_code at line 466 col 24 changed to p_Uo
\* Parameter saved_pc of procedure Uobject_code at line 466 col 33 changed to saved_pc_Uo
CONSTANT defaultInitValue
VARIABLES Cpu, memory, call_stack, memory_load_return, x_memory_load_return, 
          tlb, tlb_type_return, tlb_lookup_return, memory_paddr, pc, stack, 
          p_, c_, o_, l_, p_m, c_m, o_m, l, val_, addr_, tlb_type_i, addr_t, 
          cpl, tlb_op_mask, tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
          level_, status_, paddr_, tmp, addr_cp, level_c, addr, level, type, 
          status, paddr, p_C, collection_, p_L, saved_pc_, collection, p_U, 
          c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, Uobj_finished, p, 
          saved_pc

vars == << Cpu, memory, call_stack, memory_load_return, x_memory_load_return, 
           tlb, tlb_type_return, tlb_lookup_return, memory_paddr, pc, stack, 
           p_, c_, o_, l_, p_m, c_m, o_m, l, val_, addr_, tlb_type_i, addr_t, 
           cpl, tlb_op_mask, tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
           level_, status_, paddr_, tmp, addr_cp, level_c, addr, level, type, 
           status, paddr, p_C, collection_, p_L, saved_pc_, collection, p_U, 
           c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, Uobj_finished, 
           p, saved_pc >>

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
        /\ x_memory_load_return = 0
        /\ tlb = [entry \in 0..MAX_TLB_ENTRIES-1 |->
                           [linear_addr_base |-> 0,
                            linear_addr_size |-> 0,
                            physical_addr_base |-> 0,
                            physical_addr_size |-> 0,
                            rpl |-> 0,
                            op_mask |-> 0]]
        /\ tlb_type_return = 0
        /\ tlb_lookup_return = 0
        /\ memory_paddr = 0
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
        /\ val_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure tlb_type *)
        /\ addr_ = [ self \in ProcSet |-> defaultInitValue]
        /\ tlb_type_i = [ self \in ProcSet |-> 0]
        (* Procedure tlb_lookup *)
        /\ addr_t = [ self \in ProcSet |-> defaultInitValue]
        /\ cpl = [ self \in ProcSet |-> defaultInitValue]
        /\ tlb_op_mask = [ self \in ProcSet |-> defaultInitValue]
        /\ tlb_lookup_i = [ self \in ProcSet |-> 0]
        (* Procedure x_memory_load *)
        /\ addr_x = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure x_memory_store *)
        /\ addr_x_ = [ self \in ProcSet |-> defaultInitValue]
        /\ val = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure cpu_read *)
        /\ addr_c = [ self \in ProcSet |-> defaultInitValue]
        /\ level_ = [ self \in ProcSet |-> defaultInitValue]
        /\ status_ = [ self \in ProcSet |-> defaultInitValue]
        /\ paddr_ = [ self \in ProcSet |-> defaultInitValue]
        /\ tmp = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure cpu_write *)
        /\ addr_cp = [ self \in ProcSet |-> defaultInitValue]
        /\ level_c = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure cpu_execute *)
        /\ addr = [ self \in ProcSet |-> defaultInitValue]
        /\ level = [ self \in ProcSet |-> defaultInitValue]
        /\ type = [ self \in ProcSet |-> defaultInitValue]
        /\ status = [ self \in ProcSet |-> defaultInitValue]
        /\ paddr = [ self \in ProcSet |-> defaultInitValue]
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
                                x_memory_load_return, tlb, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, stack, p_, c_, 
                                o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                level_, status_, paddr_, tmp, addr_cp, level_c, 
                                addr, level, type, status, paddr, p_C, 
                                collection_, p_L, saved_pc_, collection, p_U, 
                                c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                In_uobj, Uobj_finished, p, saved_pc >>

Load_Legacy(self) == /\ pc[self] = "Load_Legacy"
                     /\ Cpu' = [Cpu EXCEPT ![p_[self]].Pc[2] = LEGLOAD]
                     /\ memory_load_return' = memory.Mem_legacy
                     /\ pc' = [pc EXCEPT ![self] = "LL_Done"]
                     /\ UNCHANGED << memory, call_stack, x_memory_load_return, 
                                     tlb, tlb_type_return, tlb_lookup_return, 
                                     memory_paddr, stack, p_, c_, o_, l_, p_m, 
                                     c_m, o_m, l, val_, addr_, tlb_type_i, 
                                     addr_t, cpl, tlb_op_mask, tlb_lookup_i, 
                                     addr_x, addr_x_, val, addr_c, level_, 
                                     status_, paddr_, tmp, addr_cp, level_c, 
                                     addr, level, type, status, paddr, p_C, 
                                     collection_, p_L, saved_pc_, collection, 
                                     p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                     saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                     saved_pc >>

LL_Done(self) == /\ pc[self] = "LL_Done"
                 /\ Cpu' = [Cpu EXCEPT ![p_[self]].Pc[2] = 0]
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ p_' = [p_ EXCEPT ![self] = Head(stack[self]).p_]
                 /\ c_' = [c_ EXCEPT ![self] = Head(stack[self]).c_]
                 /\ o_' = [o_ EXCEPT ![self] = Head(stack[self]).o_]
                 /\ l_' = [l_ EXCEPT ![self] = Head(stack[self]).l_]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << memory, call_stack, memory_load_return, 
                                 x_memory_load_return, tlb, tlb_type_return, 
                                 tlb_lookup_return, memory_paddr, p_m, c_m, 
                                 o_m, l, val_, addr_, tlb_type_i, addr_t, cpl, 
                                 tlb_op_mask, tlb_lookup_i, addr_x, addr_x_, 
                                 val, addr_c, level_, status_, paddr_, tmp, 
                                 addr_cp, level_c, addr, level, type, status, 
                                 paddr, p_C, collection_, p_L, saved_pc_, 
                                 collection, p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                 saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                 saved_pc >>

Load(self) == /\ pc[self] = "Load"
              /\ Cpu' = [Cpu EXCEPT ![p_[self]].Pc[2] = LOAD]
              /\ memory_load_return' = memory.Mem_uobjcollection[c_[self]].memuobj[o_[self]].uobj_local_data
              /\ pc' = [pc EXCEPT ![self] = "L_Done"]
              /\ UNCHANGED << memory, call_stack, x_memory_load_return, tlb, 
                              tlb_type_return, tlb_lookup_return, memory_paddr, 
                              stack, p_, c_, o_, l_, p_m, c_m, o_m, l, val_, 
                              addr_, tlb_type_i, addr_t, cpl, tlb_op_mask, 
                              tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                              level_, status_, paddr_, tmp, addr_cp, level_c, 
                              addr, level, type, status, paddr, p_C, 
                              collection_, p_L, saved_pc_, collection, p_U, 
                              c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                              In_uobj, Uobj_finished, p, saved_pc >>

L_Done(self) == /\ pc[self] = "L_Done"
                /\ Cpu' = [Cpu EXCEPT ![p_[self]].Pc[2] = 0]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ p_' = [p_ EXCEPT ![self] = Head(stack[self]).p_]
                /\ c_' = [c_ EXCEPT ![self] = Head(stack[self]).c_]
                /\ o_' = [o_ EXCEPT ![self] = Head(stack[self]).o_]
                /\ l_' = [l_ EXCEPT ![self] = Head(stack[self]).l_]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, p_m, c_m, o_m, 
                                l, val_, addr_, tlb_type_i, addr_t, cpl, 
                                tlb_op_mask, tlb_lookup_i, addr_x, addr_x_, 
                                val, addr_c, level_, status_, paddr_, tmp, 
                                addr_cp, level_c, addr, level, type, status, 
                                paddr, p_C, collection_, p_L, saved_pc_, 
                                collection, p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                saved_pc >>

memory_load(self) == Start_(self) \/ Load_Legacy(self) \/ LL_Done(self)
                        \/ Load(self) \/ L_Done(self)

Start_m(self) == /\ pc[self] = "Start_m"
                 /\ IF l[self]
                       THEN /\ pc' = [pc EXCEPT ![self] = "Store_Legacy"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Store"]
                 /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                 x_memory_load_return, tlb, tlb_type_return, 
                                 tlb_lookup_return, memory_paddr, stack, p_, 
                                 c_, o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                 tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                 tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                 level_, status_, paddr_, tmp, addr_cp, 
                                 level_c, addr, level, type, status, paddr, 
                                 p_C, collection_, p_L, saved_pc_, collection, 
                                 p_U, c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                 In_uobj, Uobj_finished, p, saved_pc >>

Store_Legacy(self) == /\ pc[self] = "Store_Legacy"
                      /\ Cpu' = [Cpu EXCEPT ![p_m[self]].Pc[2] = LEGSTORE]
                      /\ memory' = [memory EXCEPT !.Mem_legacy = val_[self]]
                      /\ pc' = [pc EXCEPT ![self] = "LS_Done"]
                      /\ UNCHANGED << call_stack, memory_load_return, 
                                      x_memory_load_return, tlb, 
                                      tlb_type_return, tlb_lookup_return, 
                                      memory_paddr, stack, p_, c_, o_, l_, p_m, 
                                      c_m, o_m, l, val_, addr_, tlb_type_i, 
                                      addr_t, cpl, tlb_op_mask, tlb_lookup_i, 
                                      addr_x, addr_x_, val, addr_c, level_, 
                                      status_, paddr_, tmp, addr_cp, level_c, 
                                      addr, level, type, status, paddr, p_C, 
                                      collection_, p_L, saved_pc_, collection, 
                                      p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                      saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                      saved_pc >>

LS_Done(self) == /\ pc[self] = "LS_Done"
                 /\ Cpu' = [Cpu EXCEPT ![p_m[self]].Pc[2] = 0]
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ p_m' = [p_m EXCEPT ![self] = Head(stack[self]).p_m]
                 /\ c_m' = [c_m EXCEPT ![self] = Head(stack[self]).c_m]
                 /\ o_m' = [o_m EXCEPT ![self] = Head(stack[self]).o_m]
                 /\ l' = [l EXCEPT ![self] = Head(stack[self]).l]
                 /\ val_' = [val_ EXCEPT ![self] = Head(stack[self]).val_]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << memory, call_stack, memory_load_return, 
                                 x_memory_load_return, tlb, tlb_type_return, 
                                 tlb_lookup_return, memory_paddr, p_, c_, o_, 
                                 l_, addr_, tlb_type_i, addr_t, cpl, 
                                 tlb_op_mask, tlb_lookup_i, addr_x, addr_x_, 
                                 val, addr_c, level_, status_, paddr_, tmp, 
                                 addr_cp, level_c, addr, level, type, status, 
                                 paddr, p_C, collection_, p_L, saved_pc_, 
                                 collection, p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                 saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                 saved_pc >>

Store(self) == /\ pc[self] = "Store"
               /\ Cpu' = [Cpu EXCEPT ![p_m[self]].Pc[2] = STORE]
               /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c_m[self]].memuobj[o_m[self]].uobj_local_data = val_[self]]
               /\ pc' = [pc EXCEPT ![self] = "S_Done"]
               /\ UNCHANGED << call_stack, memory_load_return, 
                               x_memory_load_return, tlb, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, stack, p_, c_, 
                               o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                               tlb_type_i, addr_t, cpl, tlb_op_mask, 
                               tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                               level_, status_, paddr_, tmp, addr_cp, level_c, 
                               addr, level, type, status, paddr, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

S_Done(self) == /\ pc[self] = "S_Done"
                /\ Cpu' = [Cpu EXCEPT ![p_m[self]].Pc[2] = 0]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ p_m' = [p_m EXCEPT ![self] = Head(stack[self]).p_m]
                /\ c_m' = [c_m EXCEPT ![self] = Head(stack[self]).c_m]
                /\ o_m' = [o_m EXCEPT ![self] = Head(stack[self]).o_m]
                /\ l' = [l EXCEPT ![self] = Head(stack[self]).l]
                /\ val_' = [val_ EXCEPT ![self] = Head(stack[self]).val_]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, p_, c_, o_, 
                                l_, addr_, tlb_type_i, addr_t, cpl, 
                                tlb_op_mask, tlb_lookup_i, addr_x, addr_x_, 
                                val, addr_c, level_, status_, paddr_, tmp, 
                                addr_cp, level_c, addr, level, type, status, 
                                paddr, p_C, collection_, p_L, saved_pc_, 
                                collection, p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                saved_pc >>

memory_store(self) == Start_m(self) \/ Store_Legacy(self) \/ LS_Done(self)
                         \/ Store(self) \/ S_Done(self)

Start_t(self) == /\ pc[self] = "Start_t"
                 /\ tlb' = [tlb EXCEPT ![0].linear_addr_base = UOBJCOLL_SENTINEL_LINEAR_ADDR_BASE]
                 /\ pc' = [pc EXCEPT ![self] = "TLB_0"]
                 /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                 x_memory_load_return, tlb_type_return, 
                                 tlb_lookup_return, memory_paddr, stack, p_, 
                                 c_, o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                 tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                 tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                 level_, status_, paddr_, tmp, addr_cp, 
                                 level_c, addr, level, type, status, paddr, 
                                 p_C, collection_, p_L, saved_pc_, collection, 
                                 p_U, c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                 In_uobj, Uobj_finished, p, saved_pc >>

TLB_0(self) == /\ pc[self] = "TLB_0"
               /\ tlb' = [tlb EXCEPT ![0].linear_addr_size = UOBJCOLL_SENTINEL_LINEAR_ADDR_SIZE]
               /\ pc' = [pc EXCEPT ![self] = "TLB_1"]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, stack, p_, c_, 
                               o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                               tlb_type_i, addr_t, cpl, tlb_op_mask, 
                               tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                               level_, status_, paddr_, tmp, addr_cp, level_c, 
                               addr, level, type, status, paddr, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

TLB_1(self) == /\ pc[self] = "TLB_1"
               /\ tlb' = [tlb EXCEPT ![0].physical_addr_base = UOBJCOLL_SENTINEL_PHYSICAL_ADDR_BASE]
               /\ pc' = [pc EXCEPT ![self] = "TLB_2"]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, stack, p_, c_, 
                               o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                               tlb_type_i, addr_t, cpl, tlb_op_mask, 
                               tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                               level_, status_, paddr_, tmp, addr_cp, level_c, 
                               addr, level, type, status, paddr, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

TLB_2(self) == /\ pc[self] = "TLB_2"
               /\ tlb' = [tlb EXCEPT ![0].physical_addr_size = UOBJCOLL_SENTINEL_PHYSICAL_ADDR_SIZE]
               /\ pc' = [pc EXCEPT ![self] = "TLB_3"]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, stack, p_, c_, 
                               o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                               tlb_type_i, addr_t, cpl, tlb_op_mask, 
                               tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                               level_, status_, paddr_, tmp, addr_cp, level_c, 
                               addr, level, type, status, paddr, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

TLB_3(self) == /\ pc[self] = "TLB_3"
               /\ tlb' = [tlb EXCEPT ![0].rpl = PRIVILEGE_LEVEL_LEGACY]
               /\ pc' = [pc EXCEPT ![self] = "TLB_4"]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, stack, p_, c_, 
                               o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                               tlb_type_i, addr_t, cpl, tlb_op_mask, 
                               tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                               level_, status_, paddr_, tmp, addr_cp, level_c, 
                               addr, level, type, status, paddr, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

TLB_4(self) == /\ pc[self] = "TLB_4"
               /\ tlb' = [tlb EXCEPT ![0].op_mask = {TLB_OP_READ, TLB_OP_EXECUTE}]
               /\ pc' = [pc EXCEPT ![self] = "TLB_5"]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, stack, p_, c_, 
                               o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                               tlb_type_i, addr_t, cpl, tlb_op_mask, 
                               tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                               level_, status_, paddr_, tmp, addr_cp, level_c, 
                               addr, level, type, status, paddr, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

TLB_5(self) == /\ pc[self] = "TLB_5"
               /\ tlb' = [tlb EXCEPT ![0].type = TLB_TYPE_SENTINEL]
               /\ pc' = [pc EXCEPT ![self] = "TLB_6"]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, stack, p_, c_, 
                               o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                               tlb_type_i, addr_t, cpl, tlb_op_mask, 
                               tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                               level_, status_, paddr_, tmp, addr_cp, level_c, 
                               addr, level, type, status, paddr, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

TLB_6(self) == /\ pc[self] = "TLB_6"
               /\ tlb' = [tlb EXCEPT ![1].linear_addr_base = UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE]
               /\ pc' = [pc EXCEPT ![self] = "TLB_7"]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, stack, p_, c_, 
                               o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                               tlb_type_i, addr_t, cpl, tlb_op_mask, 
                               tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                               level_, status_, paddr_, tmp, addr_cp, level_c, 
                               addr, level, type, status, paddr, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

TLB_7(self) == /\ pc[self] = "TLB_7"
               /\ tlb' = [tlb EXCEPT ![1].linear_addr_size = UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE]
               /\ pc' = [pc EXCEPT ![self] = "TLB_8"]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, stack, p_, c_, 
                               o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                               tlb_type_i, addr_t, cpl, tlb_op_mask, 
                               tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                               level_, status_, paddr_, tmp, addr_cp, level_c, 
                               addr, level, type, status, paddr, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

TLB_8(self) == /\ pc[self] = "TLB_8"
               /\ tlb' = [tlb EXCEPT ![1].physical_addr_base = UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_BASE]
               /\ pc' = [pc EXCEPT ![self] = "TLB_9"]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, stack, p_, c_, 
                               o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                               tlb_type_i, addr_t, cpl, tlb_op_mask, 
                               tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                               level_, status_, paddr_, tmp, addr_cp, level_c, 
                               addr, level, type, status, paddr, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

TLB_9(self) == /\ pc[self] = "TLB_9"
               /\ tlb' = [tlb EXCEPT ![1].physical_addr_size = UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_SIZE]
               /\ pc' = [pc EXCEPT ![self] = "TLB_10"]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, stack, p_, c_, 
                               o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                               tlb_type_i, addr_t, cpl, tlb_op_mask, 
                               tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                               level_, status_, paddr_, tmp, addr_cp, level_c, 
                               addr, level, type, status, paddr, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

TLB_10(self) == /\ pc[self] = "TLB_10"
                /\ tlb' = [tlb EXCEPT ![1].rpl = PRIVILEGE_LEVEL_UOBJCOLL]
                /\ pc' = [pc EXCEPT ![self] = "TLB_11"]
                /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, stack, p_, c_, 
                                o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                level_, status_, paddr_, tmp, addr_cp, level_c, 
                                addr, level, type, status, paddr, p_C, 
                                collection_, p_L, saved_pc_, collection, p_U, 
                                c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                In_uobj, Uobj_finished, p, saved_pc >>

TLB_11(self) == /\ pc[self] = "TLB_11"
                /\ tlb' = [tlb EXCEPT ![1].op_mask = {TLB_OP_READ, TLB_OP_WRITE, TLB_OP_EXECUTE}]
                /\ pc' = [pc EXCEPT ![self] = "TLB_12"]
                /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, stack, p_, c_, 
                                o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                level_, status_, paddr_, tmp, addr_cp, level_c, 
                                addr, level, type, status, paddr, p_C, 
                                collection_, p_L, saved_pc_, collection, p_U, 
                                c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                In_uobj, Uobj_finished, p, saved_pc >>

TLB_12(self) == /\ pc[self] = "TLB_12"
                /\ tlb' = [tlb EXCEPT ![1].type = TLB_TYPE_UOBJCOLL]
                /\ pc' = [pc EXCEPT ![self] = "TLB_13"]
                /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, stack, p_, c_, 
                                o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                level_, status_, paddr_, tmp, addr_cp, level_c, 
                                addr, level, type, status, paddr, p_C, 
                                collection_, p_L, saved_pc_, collection, p_U, 
                                c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                In_uobj, Uobj_finished, p, saved_pc >>

TLB_13(self) == /\ pc[self] = "TLB_13"
                /\ tlb' = [tlb EXCEPT ![2].linear_addr_base = LEGACY_LINEAR_ADDR_BASE]
                /\ pc' = [pc EXCEPT ![self] = "TLB_14"]
                /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, stack, p_, c_, 
                                o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                level_, status_, paddr_, tmp, addr_cp, level_c, 
                                addr, level, type, status, paddr, p_C, 
                                collection_, p_L, saved_pc_, collection, p_U, 
                                c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                In_uobj, Uobj_finished, p, saved_pc >>

TLB_14(self) == /\ pc[self] = "TLB_14"
                /\ tlb' = [tlb EXCEPT ![2].linear_addr_size = LEGACY_LINEAR_ADDR_SIZE]
                /\ pc' = [pc EXCEPT ![self] = "TLB_15"]
                /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, stack, p_, c_, 
                                o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                level_, status_, paddr_, tmp, addr_cp, level_c, 
                                addr, level, type, status, paddr, p_C, 
                                collection_, p_L, saved_pc_, collection, p_U, 
                                c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                In_uobj, Uobj_finished, p, saved_pc >>

TLB_15(self) == /\ pc[self] = "TLB_15"
                /\ tlb' = [tlb EXCEPT ![2].physical_addr_base = LEGACY_PHYSICAL_ADDR_BASE]
                /\ pc' = [pc EXCEPT ![self] = "TLB_16"]
                /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, stack, p_, c_, 
                                o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                level_, status_, paddr_, tmp, addr_cp, level_c, 
                                addr, level, type, status, paddr, p_C, 
                                collection_, p_L, saved_pc_, collection, p_U, 
                                c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                In_uobj, Uobj_finished, p, saved_pc >>

TLB_16(self) == /\ pc[self] = "TLB_16"
                /\ tlb' = [tlb EXCEPT ![2].physical_addr_size = LEGACY_PHYSICAL_ADDR_SIZE]
                /\ pc' = [pc EXCEPT ![self] = "TLB_17"]
                /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, stack, p_, c_, 
                                o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                level_, status_, paddr_, tmp, addr_cp, level_c, 
                                addr, level, type, status, paddr, p_C, 
                                collection_, p_L, saved_pc_, collection, p_U, 
                                c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                In_uobj, Uobj_finished, p, saved_pc >>

TLB_17(self) == /\ pc[self] = "TLB_17"
                /\ tlb' = [tlb EXCEPT ![2].rpl = PRIVILEGE_LEVEL_LEGACY]
                /\ pc' = [pc EXCEPT ![self] = "TLB_18"]
                /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, stack, p_, c_, 
                                o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                level_, status_, paddr_, tmp, addr_cp, level_c, 
                                addr, level, type, status, paddr, p_C, 
                                collection_, p_L, saved_pc_, collection, p_U, 
                                c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                In_uobj, Uobj_finished, p, saved_pc >>

TLB_18(self) == /\ pc[self] = "TLB_18"
                /\ tlb' = [tlb EXCEPT ![2].op_mask = {TLB_OP_READ, TLB_OP_WRITE, TLB_OP_EXECUTE}]
                /\ pc' = [pc EXCEPT ![self] = "TLB_19"]
                /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, stack, p_, c_, 
                                o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                level_, status_, paddr_, tmp, addr_cp, level_c, 
                                addr, level, type, status, paddr, p_C, 
                                collection_, p_L, saved_pc_, collection, p_U, 
                                c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                In_uobj, Uobj_finished, p, saved_pc >>

TLB_19(self) == /\ pc[self] = "TLB_19"
                /\ tlb' = [tlb EXCEPT ![2].type = TLB_TYPE_LEGACY]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, p_, c_, o_, 
                                l_, p_m, c_m, o_m, l, val_, addr_, tlb_type_i, 
                                addr_t, cpl, tlb_op_mask, tlb_lookup_i, addr_x, 
                                addr_x_, val, addr_c, level_, status_, paddr_, 
                                tmp, addr_cp, level_c, addr, level, type, 
                                status, paddr, p_C, collection_, p_L, 
                                saved_pc_, collection, p_U, c_U, saved_pc_U, 
                                p_Uo, c, o, saved_pc_Uo, In_uobj, 
                                Uobj_finished, p, saved_pc >>

tlb_init(self) == Start_t(self) \/ TLB_0(self) \/ TLB_1(self)
                     \/ TLB_2(self) \/ TLB_3(self) \/ TLB_4(self)
                     \/ TLB_5(self) \/ TLB_6(self) \/ TLB_7(self)
                     \/ TLB_8(self) \/ TLB_9(self) \/ TLB_10(self)
                     \/ TLB_11(self) \/ TLB_12(self) \/ TLB_13(self)
                     \/ TLB_14(self) \/ TLB_15(self) \/ TLB_16(self)
                     \/ TLB_17(self) \/ TLB_18(self) \/ TLB_19(self)

Loop_(self) == /\ pc[self] = "Loop_"
               /\ IF tlb_type_i[self] < MAX_TLB_ENTRIES
                     THEN /\ IF addr_[self] > tlb[tlb_type_i[self]].linear_addr_base /\ addr_[self] <= (tlb[tlb_type_i[self]].linear_addr_base + tlb[tlb_type_i[self]].linear_addr_size)
                                THEN /\ tlb_type_return' = tlb[tlb_type_i[self]].type
                                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ tlb_type_i' = [tlb_type_i EXCEPT ![self] = Head(stack[self]).tlb_type_i]
                                     /\ addr_' = [addr_ EXCEPT ![self] = Head(stack[self]).addr_]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "Inc_"]
                                     /\ UNCHANGED << tlb_type_return, stack, 
                                                     addr_, tlb_type_i >>
                     ELSE /\ tlb_type_return' = TLB_TYPE_NONE
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ tlb_type_i' = [tlb_type_i EXCEPT ![self] = Head(stack[self]).tlb_type_i]
                          /\ addr_' = [addr_ EXCEPT ![self] = Head(stack[self]).addr_]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb, tlb_lookup_return, 
                               memory_paddr, p_, c_, o_, l_, p_m, c_m, o_m, l, 
                               val_, addr_t, cpl, tlb_op_mask, tlb_lookup_i, 
                               addr_x, addr_x_, val, addr_c, level_, status_, 
                               paddr_, tmp, addr_cp, level_c, addr, level, 
                               type, status, paddr, p_C, collection_, p_L, 
                               saved_pc_, collection, p_U, c_U, saved_pc_U, 
                               p_Uo, c, o, saved_pc_Uo, In_uobj, Uobj_finished, 
                               p, saved_pc >>

Inc_(self) == /\ pc[self] = "Inc_"
              /\ tlb_type_i' = [tlb_type_i EXCEPT ![self] = tlb_type_i[self] + 1]
              /\ pc' = [pc EXCEPT ![self] = "Loop_"]
              /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                              x_memory_load_return, tlb, tlb_type_return, 
                              tlb_lookup_return, memory_paddr, stack, p_, c_, 
                              o_, l_, p_m, c_m, o_m, l, val_, addr_, addr_t, 
                              cpl, tlb_op_mask, tlb_lookup_i, addr_x, addr_x_, 
                              val, addr_c, level_, status_, paddr_, tmp, 
                              addr_cp, level_c, addr, level, type, status, 
                              paddr, p_C, collection_, p_L, saved_pc_, 
                              collection, p_U, c_U, saved_pc_U, p_Uo, c, o, 
                              saved_pc_Uo, In_uobj, Uobj_finished, p, saved_pc >>

tlb_type(self) == Loop_(self) \/ Inc_(self)

Loop_t(self) == /\ pc[self] = "Loop_t"
                /\ IF tlb_lookup_i[self] < MAX_TLB_ENTRIES
                      THEN /\ IF addr_t[self] > tlb[tlb_lookup_i[self]].linear_addr_base /\ addr_t[self] <= (tlb[tlb_lookup_i[self]].linear_addr_base + tlb[tlb_lookup_i[self]].linear_addr_size) /\ tlb[tlb_lookup_i[self]].rpl = cpl[self] /\ tlb[tlb_lookup_i[self]].op_mask \in tlb_op_mask[self]
                                 THEN /\ tlb_lookup_return' = <<TRUE, tlb[tlb_lookup_i[self]].physical_addr_base + (addr_t[self] - tlb[tlb_lookup_i[self]].linear_addr_base)>>
                                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                      /\ tlb_lookup_i' = [tlb_lookup_i EXCEPT ![self] = Head(stack[self]).tlb_lookup_i]
                                      /\ addr_t' = [addr_t EXCEPT ![self] = Head(stack[self]).addr_t]
                                      /\ cpl' = [cpl EXCEPT ![self] = Head(stack[self]).cpl]
                                      /\ tlb_op_mask' = [tlb_op_mask EXCEPT ![self] = Head(stack[self]).tlb_op_mask]
                                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "Inc"]
                                      /\ UNCHANGED << tlb_lookup_return, stack, 
                                                      addr_t, cpl, tlb_op_mask, 
                                                      tlb_lookup_i >>
                      ELSE /\ tlb_lookup_return' = <<FALSE, 0>>
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ tlb_lookup_i' = [tlb_lookup_i EXCEPT ![self] = Head(stack[self]).tlb_lookup_i]
                           /\ addr_t' = [addr_t EXCEPT ![self] = Head(stack[self]).addr_t]
                           /\ cpl' = [cpl EXCEPT ![self] = Head(stack[self]).cpl]
                           /\ tlb_op_mask' = [tlb_op_mask EXCEPT ![self] = Head(stack[self]).tlb_op_mask]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb, tlb_type_return, 
                                memory_paddr, p_, c_, o_, l_, p_m, c_m, o_m, l, 
                                val_, addr_, tlb_type_i, addr_x, addr_x_, val, 
                                addr_c, level_, status_, paddr_, tmp, addr_cp, 
                                level_c, addr, level, type, status, paddr, p_C, 
                                collection_, p_L, saved_pc_, collection, p_U, 
                                c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                In_uobj, Uobj_finished, p, saved_pc >>

Inc(self) == /\ pc[self] = "Inc"
             /\ tlb_lookup_i' = [tlb_lookup_i EXCEPT ![self] = tlb_lookup_i[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "Loop_t"]
             /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                             x_memory_load_return, tlb, tlb_type_return, 
                             tlb_lookup_return, memory_paddr, stack, p_, c_, 
                             o_, l_, p_m, c_m, o_m, l, val_, addr_, tlb_type_i, 
                             addr_t, cpl, tlb_op_mask, addr_x, addr_x_, val, 
                             addr_c, level_, status_, paddr_, tmp, addr_cp, 
                             level_c, addr, level, type, status, paddr, p_C, 
                             collection_, p_L, saved_pc_, collection, p_U, c_U, 
                             saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, 
                             Uobj_finished, p, saved_pc >>

tlb_lookup(self) == Loop_t(self) \/ Inc(self)

Start_x(self) == /\ pc[self] = "Start_x"
                 /\ x_memory_load_return' = memory_paddr
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ addr_x' = [addr_x EXCEPT ![self] = Head(stack[self]).addr_x]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                 tlb, tlb_type_return, tlb_lookup_return, 
                                 memory_paddr, p_, c_, o_, l_, p_m, c_m, o_m, 
                                 l, val_, addr_, tlb_type_i, addr_t, cpl, 
                                 tlb_op_mask, tlb_lookup_i, addr_x_, val, 
                                 addr_c, level_, status_, paddr_, tmp, addr_cp, 
                                 level_c, addr, level, type, status, paddr, 
                                 p_C, collection_, p_L, saved_pc_, collection, 
                                 p_U, c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                 In_uobj, Uobj_finished, p, saved_pc >>

x_memory_load(self) == Start_x(self)

Start_x_(self) == /\ pc[self] = "Start_x_"
                  /\ memory_paddr' = val[self]
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ addr_x_' = [addr_x_ EXCEPT ![self] = Head(stack[self]).addr_x_]
                  /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                  x_memory_load_return, tlb, tlb_type_return, 
                                  tlb_lookup_return, p_, c_, o_, l_, p_m, c_m, 
                                  o_m, l, val_, addr_, tlb_type_i, addr_t, cpl, 
                                  tlb_op_mask, tlb_lookup_i, addr_x, addr_c, 
                                  level_, status_, paddr_, tmp, addr_cp, 
                                  level_c, addr, level, type, status, paddr, 
                                  p_C, collection_, p_L, saved_pc_, collection, 
                                  p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                  saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                  saved_pc >>

x_memory_store(self) == Start_x_(self)

Start_c(self) == /\ pc[self] = "Start_c"
                 /\ /\ addr_t' = [addr_t EXCEPT ![self] = addr_c[self]]
                    /\ cpl' = [cpl EXCEPT ![self] = level_[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "tlb_lookup",
                                                             pc        |->  "Return_",
                                                             tlb_lookup_i |->  tlb_lookup_i[self],
                                                             addr_t    |->  addr_t[self],
                                                             cpl       |->  cpl[self],
                                                             tlb_op_mask |->  tlb_op_mask[self] ] >>
                                                         \o stack[self]]
                    /\ tlb_op_mask' = [tlb_op_mask EXCEPT ![self] = TLB_OP_READ]
                 /\ tlb_lookup_i' = [tlb_lookup_i EXCEPT ![self] = 0]
                 /\ pc' = [pc EXCEPT ![self] = "Loop_t"]
                 /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                 x_memory_load_return, tlb, tlb_type_return, 
                                 tlb_lookup_return, memory_paddr, p_, c_, o_, 
                                 l_, p_m, c_m, o_m, l, val_, addr_, tlb_type_i, 
                                 addr_x, addr_x_, val, addr_c, level_, status_, 
                                 paddr_, tmp, addr_cp, level_c, addr, level, 
                                 type, status, paddr, p_C, collection_, p_L, 
                                 saved_pc_, collection, p_U, c_U, saved_pc_U, 
                                 p_Uo, c, o, saved_pc_Uo, In_uobj, 
                                 Uobj_finished, p, saved_pc >>

Return_(self) == /\ pc[self] = "Return_"
                 /\ status_' = [status_ EXCEPT ![self] = tlb_lookup_return[1]]
                 /\ paddr_' = [paddr_ EXCEPT ![self] = tlb_lookup_return[2]]
                 /\ IF status_'[self]
                       THEN /\ /\ addr_x' = [addr_x EXCEPT ![self] = paddr_'[self]]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "x_memory_load",
                                                                        pc        |->  "Ret_load",
                                                                        addr_x    |->  addr_x[self] ] >>
                                                                    \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "Start_x"]
                       ELSE /\ TRUE
                            /\ pc' = [pc EXCEPT ![self] = "End_"]
                            /\ UNCHANGED << stack, addr_x >>
                 /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                 x_memory_load_return, tlb, tlb_type_return, 
                                 tlb_lookup_return, memory_paddr, p_, c_, o_, 
                                 l_, p_m, c_m, o_m, l, val_, addr_, tlb_type_i, 
                                 addr_t, cpl, tlb_op_mask, tlb_lookup_i, 
                                 addr_x_, val, addr_c, level_, tmp, addr_cp, 
                                 level_c, addr, level, type, status, paddr, 
                                 p_C, collection_, p_L, saved_pc_, collection, 
                                 p_U, c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                 In_uobj, Uobj_finished, p, saved_pc >>

Ret_load(self) == /\ pc[self] = "Ret_load"
                  /\ tmp' = [tmp EXCEPT ![self] = x_memory_load_return]
                  /\ pc' = [pc EXCEPT ![self] = "End_"]
                  /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                  x_memory_load_return, tlb, tlb_type_return, 
                                  tlb_lookup_return, memory_paddr, stack, p_, 
                                  c_, o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                  tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                  tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                  level_, status_, paddr_, addr_cp, level_c, 
                                  addr, level, type, status, paddr, p_C, 
                                  collection_, p_L, saved_pc_, collection, p_U, 
                                  c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                  In_uobj, Uobj_finished, p, saved_pc >>

End_(self) == /\ pc[self] = "End_"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ status_' = [status_ EXCEPT ![self] = Head(stack[self]).status_]
              /\ paddr_' = [paddr_ EXCEPT ![self] = Head(stack[self]).paddr_]
              /\ tmp' = [tmp EXCEPT ![self] = Head(stack[self]).tmp]
              /\ addr_c' = [addr_c EXCEPT ![self] = Head(stack[self]).addr_c]
              /\ level_' = [level_ EXCEPT ![self] = Head(stack[self]).level_]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                              x_memory_load_return, tlb, tlb_type_return, 
                              tlb_lookup_return, memory_paddr, p_, c_, o_, l_, 
                              p_m, c_m, o_m, l, val_, addr_, tlb_type_i, 
                              addr_t, cpl, tlb_op_mask, tlb_lookup_i, addr_x, 
                              addr_x_, val, addr_cp, level_c, addr, level, 
                              type, status, paddr, p_C, collection_, p_L, 
                              saved_pc_, collection, p_U, c_U, saved_pc_U, 
                              p_Uo, c, o, saved_pc_Uo, In_uobj, Uobj_finished, 
                              p, saved_pc >>

cpu_read(self) == Start_c(self) \/ Return_(self) \/ Ret_load(self)
                     \/ End_(self)

Start_cp(self) == /\ pc[self] = "Start_cp"
                  /\ /\ addr_t' = [addr_t EXCEPT ![self] = addr_cp[self]]
                     /\ cpl' = [cpl EXCEPT ![self] = level_c[self]]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "tlb_lookup",
                                                              pc        |->  "Return_c",
                                                              tlb_lookup_i |->  tlb_lookup_i[self],
                                                              addr_t    |->  addr_t[self],
                                                              cpl       |->  cpl[self],
                                                              tlb_op_mask |->  tlb_op_mask[self] ] >>
                                                          \o stack[self]]
                     /\ tlb_op_mask' = [tlb_op_mask EXCEPT ![self] = TLB_OP_WRITE]
                  /\ tlb_lookup_i' = [tlb_lookup_i EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = "Loop_t"]
                  /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                  x_memory_load_return, tlb, tlb_type_return, 
                                  tlb_lookup_return, memory_paddr, p_, c_, o_, 
                                  l_, p_m, c_m, o_m, l, val_, addr_, 
                                  tlb_type_i, addr_x, addr_x_, val, addr_c, 
                                  level_, status_, paddr_, tmp, addr_cp, 
                                  level_c, addr, level, type, status, paddr, 
                                  p_C, collection_, p_L, saved_pc_, collection, 
                                  p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                  saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                  saved_pc >>

Return_c(self) == /\ pc[self] = "Return_c"
                  /\ status' = [status EXCEPT ![self] = tlb_lookup_return[1]]
                  /\ paddr' = [paddr EXCEPT ![self] = tlb_lookup_return[2]]
                  /\ IF status'[self]
                        THEN /\ tmp' = [tmp EXCEPT ![self] = nondet_u8]
                             /\ /\ addr_x_' = [addr_x_ EXCEPT ![self] = paddr'[self]]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "x_memory_store",
                                                                         pc        |->  "End_c",
                                                                         addr_x_   |->  addr_x_[self],
                                                                         val       |->  val[self] ] >>
                                                                     \o stack[self]]
                                /\ val' = [val EXCEPT ![self] = tmp'[self]]
                             /\ pc' = [pc EXCEPT ![self] = "Start_x_"]
                        ELSE /\ TRUE
                             /\ pc' = [pc EXCEPT ![self] = "End_c"]
                             /\ UNCHANGED << stack, addr_x_, val, tmp >>
                  /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                  x_memory_load_return, tlb, tlb_type_return, 
                                  tlb_lookup_return, memory_paddr, p_, c_, o_, 
                                  l_, p_m, c_m, o_m, l, val_, addr_, 
                                  tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                  tlb_lookup_i, addr_x, addr_c, level_, 
                                  status_, paddr_, addr_cp, level_c, addr, 
                                  level, type, p_C, collection_, p_L, 
                                  saved_pc_, collection, p_U, c_U, saved_pc_U, 
                                  p_Uo, c, o, saved_pc_Uo, In_uobj, 
                                  Uobj_finished, p, saved_pc >>

End_c(self) == /\ pc[self] = "End_c"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ addr_cp' = [addr_cp EXCEPT ![self] = Head(stack[self]).addr_cp]
               /\ level_c' = [level_c EXCEPT ![self] = Head(stack[self]).level_c]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, p_, c_, o_, l_, 
                               p_m, c_m, o_m, l, val_, addr_, tlb_type_i, 
                               addr_t, cpl, tlb_op_mask, tlb_lookup_i, addr_x, 
                               addr_x_, val, addr_c, level_, status_, paddr_, 
                               tmp, addr, level, type, status, paddr, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

cpu_write(self) == Start_cp(self) \/ Return_c(self) \/ End_c(self)

Start_cpu(self) == /\ pc[self] = "Start_cpu"
                   /\ /\ addr_' = [addr_ EXCEPT ![self] = addr[self]]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "tlb_type",
                                                               pc        |->  "Return_cp",
                                                               tlb_type_i |->  tlb_type_i[self],
                                                               addr_     |->  addr_[self] ] >>
                                                           \o stack[self]]
                   /\ tlb_type_i' = [tlb_type_i EXCEPT ![self] = 0]
                   /\ pc' = [pc EXCEPT ![self] = "Loop_"]
                   /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                   x_memory_load_return, tlb, tlb_type_return, 
                                   tlb_lookup_return, memory_paddr, p_, c_, o_, 
                                   l_, p_m, c_m, o_m, l, val_, addr_t, cpl, 
                                   tlb_op_mask, tlb_lookup_i, addr_x, addr_x_, 
                                   val, addr_c, level_, status_, paddr_, tmp, 
                                   addr_cp, level_c, addr, level, type, status, 
                                   paddr, p_C, collection_, p_L, saved_pc_, 
                                   collection, p_U, c_U, saved_pc_U, p_Uo, c, 
                                   o, saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                   saved_pc >>

Return_cp(self) == /\ pc[self] = "Return_cp"
                   /\ type' = [type EXCEPT ![self] = tlb_type_return]
                   /\ /\ addr_t' = [addr_t EXCEPT ![self] = addr[self]]
                      /\ cpl' = [cpl EXCEPT ![self] = level[self]]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "tlb_lookup",
                                                               pc        |->  "Ret_lookup",
                                                               tlb_lookup_i |->  tlb_lookup_i[self],
                                                               addr_t    |->  addr_t[self],
                                                               cpl       |->  cpl[self],
                                                               tlb_op_mask |->  tlb_op_mask[self] ] >>
                                                           \o stack[self]]
                      /\ tlb_op_mask' = [tlb_op_mask EXCEPT ![self] = TLB_OP_EXECUTE]
                   /\ tlb_lookup_i' = [tlb_lookup_i EXCEPT ![self] = 0]
                   /\ pc' = [pc EXCEPT ![self] = "Loop_t"]
                   /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                   x_memory_load_return, tlb, tlb_type_return, 
                                   tlb_lookup_return, memory_paddr, p_, c_, o_, 
                                   l_, p_m, c_m, o_m, l, val_, addr_, 
                                   tlb_type_i, addr_x, addr_x_, val, addr_c, 
                                   level_, status_, paddr_, tmp, addr_cp, 
                                   level_c, addr, level, status, paddr, p_C, 
                                   collection_, p_L, saved_pc_, collection, 
                                   p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                   saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                   saved_pc >>

Ret_lookup(self) == /\ pc[self] = "Ret_lookup"
                    /\ status' = [status EXCEPT ![self] = tlb_lookup_return[1]]
                    /\ paddr' = [paddr EXCEPT ![self] = tlb_lookup_return[2]]
                    /\ IF status'[self]
                          THEN /\ IF type[self] = TLB_TYPE_SENTINEL
                                     THEN /\ TRUE
                                     ELSE /\ TRUE
                          ELSE /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "End_cp"]
                    /\ UNCHANGED << Cpu, memory, call_stack, 
                                    memory_load_return, x_memory_load_return, 
                                    tlb, tlb_type_return, tlb_lookup_return, 
                                    memory_paddr, stack, p_, c_, o_, l_, p_m, 
                                    c_m, o_m, l, val_, addr_, tlb_type_i, 
                                    addr_t, cpl, tlb_op_mask, tlb_lookup_i, 
                                    addr_x, addr_x_, val, addr_c, level_, 
                                    status_, paddr_, tmp, addr_cp, level_c, 
                                    addr, level, type, p_C, collection_, p_L, 
                                    saved_pc_, collection, p_U, c_U, 
                                    saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                    In_uobj, Uobj_finished, p, saved_pc >>

End_cp(self) == /\ pc[self] = "End_cp"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ type' = [type EXCEPT ![self] = Head(stack[self]).type]
                /\ status' = [status EXCEPT ![self] = Head(stack[self]).status]
                /\ paddr' = [paddr EXCEPT ![self] = Head(stack[self]).paddr]
                /\ addr' = [addr EXCEPT ![self] = Head(stack[self]).addr]
                /\ level' = [level EXCEPT ![self] = Head(stack[self]).level]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, p_, c_, o_, 
                                l_, p_m, c_m, o_m, l, val_, addr_, tlb_type_i, 
                                addr_t, cpl, tlb_op_mask, tlb_lookup_i, addr_x, 
                                addr_x_, val, addr_c, level_, status_, paddr_, 
                                tmp, addr_cp, level_c, p_C, collection_, p_L, 
                                saved_pc_, collection, p_U, c_U, saved_pc_U, 
                                p_Uo, c, o, saved_pc_Uo, In_uobj, 
                                Uobj_finished, p, saved_pc >>

cpu_execute(self) == Start_cpu(self) \/ Return_cp(self) \/ Ret_lookup(self)
                        \/ End_cp(self)

Start_C(self) == /\ pc[self] = "Start_C"
                 /\ \E col \in 1..MAXUOBJCOLLECTIONS:
                      collection_' = [collection_ EXCEPT ![self] = col]
                 /\ \/ /\ Cpu' = [Cpu EXCEPT ![p_C[self]].Pr = LEGACY]
                       /\ pc' = [pc EXCEPT ![self] = "Call_"]
                    \/ /\ Cpu' = [Cpu EXCEPT ![p_C[self]].Pr = UBER]
                       /\ pc' = [pc EXCEPT ![self] = "Collection"]
                 /\ UNCHANGED << memory, call_stack, memory_load_return, 
                                 x_memory_load_return, tlb, tlb_type_return, 
                                 tlb_lookup_return, memory_paddr, stack, p_, 
                                 c_, o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                 tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                 tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                 level_, status_, paddr_, tmp, addr_cp, 
                                 level_c, addr, level, type, status, paddr, 
                                 p_C, p_L, saved_pc_, collection, p_U, c_U, 
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
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, p_, c_, o_, l_, 
                               p_m, c_m, o_m, l, val_, addr_, tlb_type_i, 
                               addr_t, cpl, tlb_op_mask, tlb_lookup_i, addr_x, 
                               addr_x_, val, addr_c, level_, status_, paddr_, 
                               tmp, addr_cp, level_c, addr, level, type, 
                               status, paddr, p_C, p_U, c_U, saved_pc_U, p_Uo, 
                               c, o, saved_pc_Uo, In_uobj, Uobj_finished, p, 
                               saved_pc >>

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
                    /\ UNCHANGED << memory, call_stack, memory_load_return, 
                                    x_memory_load_return, tlb, tlb_type_return, 
                                    tlb_lookup_return, memory_paddr, p_, c_, 
                                    o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                    tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                    tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                    level_, status_, paddr_, tmp, addr_cp, 
                                    level_c, addr, level, type, status, paddr, 
                                    p_C, collection_, p_L, saved_pc_, 
                                    collection, p_Uo, c, o, saved_pc_Uo, 
                                    In_uobj, Uobj_finished, p, saved_pc >>

After_branching(self) == /\ pc[self] = "After_branching"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ collection_' = [collection_ EXCEPT ![self] = Head(stack[self]).collection_]
                         /\ p_C' = [p_C EXCEPT ![self] = Head(stack[self]).p_C]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << Cpu, memory, call_stack, 
                                         memory_load_return, 
                                         x_memory_load_return, tlb, 
                                         tlb_type_return, tlb_lookup_return, 
                                         memory_paddr, p_, c_, o_, l_, p_m, 
                                         c_m, o_m, l, val_, addr_, tlb_type_i, 
                                         addr_t, cpl, tlb_op_mask, 
                                         tlb_lookup_i, addr_x, addr_x_, val, 
                                         addr_c, level_, status_, paddr_, tmp, 
                                         addr_cp, level_c, addr, level, type, 
                                         status, paddr, p_L, saved_pc_, 
                                         collection, p_U, c_U, saved_pc_U, 
                                         p_Uo, c, o, saved_pc_Uo, In_uobj, 
                                         Uobj_finished, p, saved_pc >>

Cpu_process(self) == Start_C(self) \/ Call_(self) \/ Collection(self)
                        \/ After_branching(self)

Start_L(self) == /\ pc[self] = "Start_L"
                 /\ Cpu' = [Cpu EXCEPT ![p_L[self]].Pc[1] = LEGACY]
                 /\ pc' = [pc EXCEPT ![self] = "Loop"]
                 /\ UNCHANGED << memory, call_stack, memory_load_return, 
                                 x_memory_load_return, tlb, tlb_type_return, 
                                 tlb_lookup_return, memory_paddr, stack, p_, 
                                 c_, o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                 tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                 tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                 level_, status_, paddr_, tmp, addr_cp, 
                                 level_c, addr, level, type, status, paddr, 
                                 p_C, collection_, p_L, saved_pc_, collection, 
                                 p_U, c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
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
                    /\ UNCHANGED <<p_, c_, o_, l_, p_m, c_m, o_m, l, val_, addr_c, level_, status_, paddr_, tmp, addr_cp, level_c, addr, level, type, status, paddr, p_L, saved_pc_, collection>>
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
                    /\ UNCHANGED <<Cpu, call_stack, p_m, c_m, o_m, l, val_, addr_c, level_, status_, paddr_, tmp, addr_cp, level_c, addr, level, type, status, paddr, p_L, saved_pc_, collection, p_U, c_U, saved_pc_U>>
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
                                                                val_      |->  val_[self] ] >>
                                                            \o stack[self]]
                       /\ val_' = [val_ EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "Start_m"]
                    /\ UNCHANGED <<Cpu, call_stack, p_, c_, o_, l_, addr_c, level_, status_, paddr_, tmp, addr_cp, level_c, addr, level, type, status, paddr, p_L, saved_pc_, collection, p_U, c_U, saved_pc_U>>
                 \/ /\ \E case \in nondet_u32:
                         \E rand_addr \in nondet_u32:
                           IF case = 0
                              THEN /\ /\ addr_c' = [addr_c EXCEPT ![self] = rand_addr]
                                      /\ level_' = [level_ EXCEPT ![self] = PRIVILEGE_LEVEL_LEGACY]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "cpu_read",
                                                                               pc        |->  "Loop",
                                                                               status_   |->  status_[self],
                                                                               paddr_    |->  paddr_[self],
                                                                               tmp       |->  tmp[self],
                                                                               addr_c    |->  addr_c[self],
                                                                               level_    |->  level_[self] ] >>
                                                                           \o stack[self]]
                                   /\ status_' = [status_ EXCEPT ![self] = defaultInitValue]
                                   /\ paddr_' = [paddr_ EXCEPT ![self] = defaultInitValue]
                                   /\ tmp' = [tmp EXCEPT ![self] = defaultInitValue]
                                   /\ pc' = [pc EXCEPT ![self] = "Start_c"]
                                   /\ UNCHANGED << addr_cp, level_c, addr, 
                                                   level, type, status, paddr >>
                              ELSE /\ IF case = 1
                                         THEN /\ /\ addr_cp' = [addr_cp EXCEPT ![self] = rand_addr]
                                                 /\ level_c' = [level_c EXCEPT ![self] = PRIVILEGE_LEVEL_LEGACY]
                                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "cpu_write",
                                                                                          pc        |->  "Loop",
                                                                                          addr_cp   |->  addr_cp[self],
                                                                                          level_c   |->  level_c[self] ] >>
                                                                                      \o stack[self]]
                                              /\ pc' = [pc EXCEPT ![self] = "Start_cp"]
                                              /\ UNCHANGED << addr, level, 
                                                              type, status, 
                                                              paddr >>
                                         ELSE /\ IF case = 2
                                                    THEN /\ /\ addr' = [addr EXCEPT ![self] = rand_addr]
                                                            /\ level' = [level EXCEPT ![self] = PRIVILEGE_LEVEL_LEGACY]
                                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "cpu_execute",
                                                                                                     pc        |->  "Loop",
                                                                                                     type      |->  type[self],
                                                                                                     status    |->  status[self],
                                                                                                     paddr     |->  paddr[self],
                                                                                                     addr      |->  addr[self],
                                                                                                     level     |->  level[self] ] >>
                                                                                                 \o stack[self]]
                                                         /\ type' = [type EXCEPT ![self] = defaultInitValue]
                                                         /\ status' = [status EXCEPT ![self] = defaultInitValue]
                                                         /\ paddr' = [paddr EXCEPT ![self] = defaultInitValue]
                                                         /\ pc' = [pc EXCEPT ![self] = "Start_cpu"]
                                                    ELSE /\ TRUE
                                                         /\ pc' = [pc EXCEPT ![self] = "Loop"]
                                                         /\ UNCHANGED << stack, 
                                                                         addr, 
                                                                         level, 
                                                                         type, 
                                                                         status, 
                                                                         paddr >>
                                              /\ UNCHANGED << addr_cp, level_c >>
                                   /\ UNCHANGED << addr_c, level_, status_, 
                                                   paddr_, tmp >>
                    /\ UNCHANGED <<Cpu, call_stack, p_, c_, o_, l_, p_m, c_m, o_m, l, val_, p_L, saved_pc_, collection, p_U, c_U, saved_pc_U>>
                 \/ /\ Cpu' = [Cpu EXCEPT ![p_L[self]].Pc[1] = saved_pc_[self]]
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ collection' = [collection EXCEPT ![self] = Head(stack[self]).collection]
                    /\ p_L' = [p_L EXCEPT ![self] = Head(stack[self]).p_L]
                    /\ saved_pc_' = [saved_pc_ EXCEPT ![self] = Head(stack[self]).saved_pc_]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED <<call_stack, p_, c_, o_, l_, p_m, c_m, o_m, l, val_, addr_c, level_, status_, paddr_, tmp, addr_cp, level_c, addr, level, type, status, paddr, p_U, c_U, saved_pc_U>>
              /\ UNCHANGED << memory, memory_load_return, x_memory_load_return, 
                              tlb, tlb_type_return, tlb_lookup_return, 
                              memory_paddr, addr_, tlb_type_i, addr_t, cpl, 
                              tlb_op_mask, tlb_lookup_i, addr_x, addr_x_, val, 
                              p_C, collection_, p_Uo, c, o, saved_pc_Uo, 
                              In_uobj, Uobj_finished, p, saved_pc >>

Legacy_code(self) == Start_L(self) \/ Loop(self)

Start_U(self) == /\ pc[self] = "Start_U"
                 /\ Cpu' = [Cpu EXCEPT ![p_U[self]].Pc[1] = UBER]
                 /\ pc' = [pc EXCEPT ![self] = "Call"]
                 /\ UNCHANGED << memory, call_stack, memory_load_return, 
                                 x_memory_load_return, tlb, tlb_type_return, 
                                 tlb_lookup_return, memory_paddr, stack, p_, 
                                 c_, o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                 tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                 tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                 level_, status_, paddr_, tmp, addr_cp, 
                                 level_c, addr, level, type, status, paddr, 
                                 p_C, collection_, p_L, saved_pc_, collection, 
                                 p_U, c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
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
              /\ UNCHANGED << memory, call_stack, memory_load_return, 
                              x_memory_load_return, tlb, tlb_type_return, 
                              tlb_lookup_return, memory_paddr, p_, c_, o_, l_, 
                              p_m, c_m, o_m, l, val_, addr_, tlb_type_i, 
                              addr_t, cpl, tlb_op_mask, tlb_lookup_i, addr_x, 
                              addr_x_, val, addr_c, level_, status_, paddr_, 
                              tmp, addr_cp, level_c, addr, level, type, status, 
                              paddr, p_C, collection_, p_L, saved_pc_, 
                              collection, p_U, c_U, saved_pc_U, p, saved_pc >>

Return(self) == /\ pc[self] = "Return"
                /\ Cpu' = [Cpu EXCEPT ![p_U[self]].Pc[1] = saved_pc_U[self]]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ p_U' = [p_U EXCEPT ![self] = Head(stack[self]).p_U]
                /\ c_U' = [c_U EXCEPT ![self] = Head(stack[self]).c_U]
                /\ saved_pc_U' = [saved_pc_U EXCEPT ![self] = Head(stack[self]).saved_pc_U]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << memory, call_stack, memory_load_return, 
                                x_memory_load_return, tlb, tlb_type_return, 
                                tlb_lookup_return, memory_paddr, p_, c_, o_, 
                                l_, p_m, c_m, o_m, l, val_, addr_, tlb_type_i, 
                                addr_t, cpl, tlb_op_mask, tlb_lookup_i, addr_x, 
                                addr_x_, val, addr_c, level_, status_, paddr_, 
                                tmp, addr_cp, level_c, addr, level, type, 
                                status, paddr, p_C, collection_, p_L, 
                                saved_pc_, collection, p_Uo, c, o, saved_pc_Uo, 
                                In_uobj, Uobj_finished, p, saved_pc >>

Uobjcollection_code(self) == Start_U(self) \/ Call(self) \/ Return(self)

Start_Uo(self) == /\ pc[self] = "Start_Uo"
                  /\ memory.Mem_uobjcollection[c[self]].memuobj[o[self]].lock = 0
                  /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c[self]].memuobj[o[self]].lock = 1]
                  /\ IF ~In_uobj[self]
                        THEN /\ Cpu' = [Cpu EXCEPT ![p_Uo[self]].Pc[1] = UBER]
                             /\ pc' = [pc EXCEPT ![self] = "CS_Start"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "CS_Unlock"]
                             /\ Cpu' = Cpu
                  /\ UNCHANGED << call_stack, memory_load_return, 
                                  x_memory_load_return, tlb, tlb_type_return, 
                                  tlb_lookup_return, memory_paddr, stack, p_, 
                                  c_, o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                  tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                  tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                  level_, status_, paddr_, tmp, addr_cp, 
                                  level_c, addr, level, type, status, paddr, 
                                  p_C, collection_, p_L, saved_pc_, collection, 
                                  p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                  saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                  saved_pc >>

CS_Start(self) == /\ pc[self] = "CS_Start"
                  /\ Cpu' = [Cpu EXCEPT ![p_Uo[self]].Pc[2] = CS]
                  /\ pc' = [pc EXCEPT ![self] = "CS_Loop"]
                  /\ UNCHANGED << memory, call_stack, memory_load_return, 
                                  x_memory_load_return, tlb, tlb_type_return, 
                                  tlb_lookup_return, memory_paddr, stack, p_, 
                                  c_, o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                  tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                  tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                  level_, status_, paddr_, tmp, addr_cp, 
                                  level_c, addr, level, type, status, paddr, 
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
                 /\ UNCHANGED << Cpu, memory, memory_load_return, 
                                 x_memory_load_return, tlb, tlb_type_return, 
                                 tlb_lookup_return, memory_paddr, p_, c_, o_, 
                                 l_, p_m, c_m, o_m, l, val_, addr_, tlb_type_i, 
                                 addr_t, cpl, tlb_op_mask, tlb_lookup_i, 
                                 addr_x, addr_x_, val, addr_c, level_, status_, 
                                 paddr_, tmp, addr_cp, level_c, addr, level, 
                                 type, status, paddr, p_C, collection_, p_L, 
                                 saved_pc_, collection, p_U, c_U, saved_pc_U, 
                                 p_Uo, c, o, saved_pc_Uo, In_uobj, 
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
                                 x_memory_load_return, tlb, tlb_type_return, 
                                 tlb_lookup_return, memory_paddr, p_m, c_m, 
                                 o_m, l, val_, addr_, tlb_type_i, addr_t, cpl, 
                                 tlb_op_mask, tlb_lookup_i, addr_x, addr_x_, 
                                 val, addr_c, level_, status_, paddr_, tmp, 
                                 addr_cp, level_c, addr, level, type, status, 
                                 paddr, p_C, collection_, p_L, saved_pc_, 
                                 collection, p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                 saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                 saved_pc >>

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
                                                              val_      |->  val_[self] ] >>
                                                          \o stack[self]]
                     /\ val_' = [val_ EXCEPT ![self] = 0]
                  /\ pc' = [pc EXCEPT ![self] = "Start_m"]
                  /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                                  x_memory_load_return, tlb, tlb_type_return, 
                                  tlb_lookup_return, memory_paddr, p_, c_, o_, 
                                  l_, addr_, tlb_type_i, addr_t, cpl, 
                                  tlb_op_mask, tlb_lookup_i, addr_x, addr_x_, 
                                  val, addr_c, level_, status_, paddr_, tmp, 
                                  addr_cp, level_c, addr, level, type, status, 
                                  paddr, p_C, collection_, p_L, saved_pc_, 
                                  collection, p_U, c_U, saved_pc_U, p_Uo, c, o, 
                                  saved_pc_Uo, In_uobj, Uobj_finished, p, 
                                  saved_pc >>

CS_Exit(self) == /\ pc[self] = "CS_Exit"
                 /\ Cpu' = [Cpu EXCEPT ![p_Uo[self]].Pc[2] = 0]
                 /\ Uobj_finished' = [Uobj_finished EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "CS_Loop"]
                 /\ UNCHANGED << memory, call_stack, memory_load_return, 
                                 x_memory_load_return, tlb, tlb_type_return, 
                                 tlb_lookup_return, memory_paddr, stack, p_, 
                                 c_, o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                 tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                 tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                 level_, status_, paddr_, tmp, addr_cp, 
                                 level_c, addr, level, type, status, paddr, 
                                 p_C, collection_, p_L, saved_pc_, collection, 
                                 p_U, c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                                 In_uobj, p, saved_pc >>

CS_Unlock(self) == /\ pc[self] = "CS_Unlock"
                   /\ memory' = [memory EXCEPT !.Mem_uobjcollection[c[self]].memuobj[o[self]].lock = 0]
                   /\ Uobj_finished' = [Uobj_finished EXCEPT ![self] = FALSE]
                   /\ In_uobj' = [In_uobj EXCEPT ![self] = FALSE]
                   /\ Cpu' = [Cpu EXCEPT ![p_Uo[self]].Pc[1] = saved_pc_Uo[self]]
                   /\ pc' = [pc EXCEPT ![self] = "End_U"]
                   /\ UNCHANGED << call_stack, memory_load_return, 
                                   x_memory_load_return, tlb, tlb_type_return, 
                                   tlb_lookup_return, memory_paddr, stack, p_, 
                                   c_, o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                                   tlb_type_i, addr_t, cpl, tlb_op_mask, 
                                   tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                                   level_, status_, paddr_, tmp, addr_cp, 
                                   level_c, addr, level, type, status, paddr, 
                                   p_C, collection_, p_L, saved_pc_, 
                                   collection, p_U, c_U, saved_pc_U, p_Uo, c, 
                                   o, saved_pc_Uo, p, saved_pc >>

End_U(self) == /\ pc[self] = "End_U"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ In_uobj' = [In_uobj EXCEPT ![self] = Head(stack[self]).In_uobj]
               /\ Uobj_finished' = [Uobj_finished EXCEPT ![self] = Head(stack[self]).Uobj_finished]
               /\ p_Uo' = [p_Uo EXCEPT ![self] = Head(stack[self]).p_Uo]
               /\ c' = [c EXCEPT ![self] = Head(stack[self]).c]
               /\ o' = [o EXCEPT ![self] = Head(stack[self]).o]
               /\ saved_pc_Uo' = [saved_pc_Uo EXCEPT ![self] = Head(stack[self]).saved_pc_Uo]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, p_, c_, o_, l_, 
                               p_m, c_m, o_m, l, val_, addr_, tlb_type_i, 
                               addr_t, cpl, tlb_op_mask, tlb_lookup_i, addr_x, 
                               addr_x_, val, addr_c, level_, status_, paddr_, 
                               tmp, addr_cp, level_c, addr, level, type, 
                               status, paddr, p_C, collection_, p_L, saved_pc_, 
                               collection, p_U, c_U, saved_pc_U, p, saved_pc >>

Uobject_code(self) == Start_Uo(self) \/ CS_Start(self) \/ CS_Loop(self)
                         \/ CS_Read(self) \/ CS_Write(self)
                         \/ CS_Exit(self) \/ CS_Unlock(self) \/ End_U(self)

Start(self) == /\ pc[self] = "Start"
               /\ Cpu' = [Cpu EXCEPT ![p[self]].Pc[1] = LEGACY]
               /\ pc' = [pc EXCEPT ![self] = "End"]
               /\ UNCHANGED << memory, call_stack, memory_load_return, 
                               x_memory_load_return, tlb, tlb_type_return, 
                               tlb_lookup_return, memory_paddr, stack, p_, c_, 
                               o_, l_, p_m, c_m, o_m, l, val_, addr_, 
                               tlb_type_i, addr_t, cpl, tlb_op_mask, 
                               tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                               level_, status_, paddr_, tmp, addr_cp, level_c, 
                               addr, level, type, status, paddr, p_C, 
                               collection_, p_L, saved_pc_, collection, p_U, 
                               c_U, saved_pc_U, p_Uo, c, o, saved_pc_Uo, 
                               In_uobj, Uobj_finished, p, saved_pc >>

End(self) == /\ pc[self] = "End"
             /\ Cpu' = [Cpu EXCEPT ![p[self]].Pc[1] = saved_pc[self]]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
             /\ saved_pc' = [saved_pc EXCEPT ![self] = Head(stack[self]).saved_pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << memory, call_stack, memory_load_return, 
                             x_memory_load_return, tlb, tlb_type_return, 
                             tlb_lookup_return, memory_paddr, p_, c_, o_, l_, 
                             p_m, c_m, o_m, l, val_, addr_, tlb_type_i, addr_t, 
                             cpl, tlb_op_mask, tlb_lookup_i, addr_x, addr_x_, 
                             val, addr_c, level_, status_, paddr_, tmp, 
                             addr_cp, level_c, addr, level, type, status, 
                             paddr, p_C, collection_, p_L, saved_pc_, 
                             collection, p_U, c_U, saved_pc_U, p_Uo, c, o, 
                             saved_pc_Uo, In_uobj, Uobj_finished >>

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
      /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                      x_memory_load_return, tlb, tlb_type_return, 
                      tlb_lookup_return, memory_paddr, p_, c_, o_, l_, p_m, 
                      c_m, o_m, l, val_, addr_, tlb_type_i, addr_t, cpl, 
                      tlb_op_mask, tlb_lookup_i, addr_x, addr_x_, val, addr_c, 
                      level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                      level, type, status, paddr, p_L, saved_pc_, collection, 
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
     /\ UNCHANGED << Cpu, memory, call_stack, memory_load_return, 
                     x_memory_load_return, tlb, tlb_type_return, 
                     tlb_lookup_return, memory_paddr, p_, c_, o_, l_, p_m, c_m, 
                     o_m, l, val_, addr_, tlb_type_i, addr_t, cpl, tlb_op_mask, 
                     tlb_lookup_i, addr_x, addr_x_, val, addr_c, level_, 
                     status_, paddr_, tmp, addr_cp, level_c, addr, level, type, 
                     status, paddr, p_L, saved_pc_, collection, p_U, c_U, 
                     saved_pc_U, p_Uo, c, o, saved_pc_Uo, In_uobj, 
                     Uobj_finished, p, saved_pc >>

two == A

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two
           \/ (\E self \in ProcSet:  \/ memory_load(self) \/ memory_store(self)
                                     \/ tlb_init(self) \/ tlb_type(self)
                                     \/ tlb_lookup(self) \/ x_memory_load(self)
                                     \/ x_memory_store(self) \/ cpu_read(self)
                                     \/ cpu_write(self) \/ cpu_execute(self)
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

