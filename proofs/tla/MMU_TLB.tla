---------------------------- MODULE MMU_TLB ----------------------------
EXTENDS Sequences, Integers
CONSTANTS MAX_TLB_ENTRIES
\*#define  MAX_TLB_ENTRIES 3

TLB_TYPE_NONE     == 0
TLB_TYPE_SENTINEL == 1
TLB_TYPE_UOBJCOLL == 2
TLB_TYPE_LEGACY   == 3

TLB_OP_READ    == 1
TLB_OP_WRITE   == 2
TLB_OP_EXECUTE == 3

PRIVILEGE_LEVEL_UOBJCOLL == 0
PRIVILEGE_LEVEL_LEGACY   == 3

MEM_SIZE == 268435456 \*0x10000000 = 256MB

\* the following are defined assuming a total physical memory of // 0x10000000 = 256MB

UOBJCOLL_SENTINEL_PHYSICAL_ADDR_BASE    == 0 \*0x00000000
UOBJCOLL_SENTINEL_PHYSICAL_ADDR_SIZE    == 131072 \* 0x00020000
UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_BASE == 8192 \* 0x00002000
UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_SIZE == 16777216 \* 0x01000000
LEGACY_PHYSICAL_ADDR_BASE               == 16777216 \*0x01000000
LEGACY_PHYSICAL_ADDR_SIZE               == 251658240 \*0x0F000000

\* the following are defined assuming a 32-bit linear addressing space // that permits addressing from 0x00000000 through 0xFFFFFFFF // note the following addresses are initialized to non-overlapping // and can be part of either first stage page-tables, second stage page-tables // or even regular segmentation

UOBJCOLL_SENTINEL_LINEAR_ADDR_BASE    == 268435456 \*0x10000000
UOBJCOLL_SENTINEL_LINEAR_ADDR_SIZE    == 268566528 \*0x10020000
UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE == 268566528 \*0x10002000
UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE == 285212672 \*0x11000000
LEGACY_LINEAR_ADDR_BASE               == 285212672 \*0x11000000
LEGACY_LINEAR_ADDR_SIZE               == 520093696 \*0x1F000000

nondet_u8  == 0
nondet_u32 == {0,1,2,3}

(* --algorithm execution
variables tlb = [entry \in 0..MAX_TLB_ENTRIES-1 |->
                    [linear_addr_base |-> 0,
                     linear_addr_size |-> 0,
                     physical_addr_base |-> 0,
                     physical_addr_size |-> 0,
                     rpl |-> 0, \* requestor_privilege_level
                     op_mask |-> 0]], \*logical OR of TLB_OP_READ, TLB_OP_WRITE and/or TLB_OP_EXECUTE u32 type; //can be one of TLB_TYPE_SENTINEL, TLB_TYPE_UOBJCOLL, TLB_TYPE_LEGACY
         tlb_type_return = 0, (* TODO: Make sure this have write/read atomicity *)
         tlb_lookup_return,
         memory_load_return,
         memory = [address \in 0..268435456|-> 0];
         
         \*addr \in nondet_u32;
         
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
    variables i = 0;
    begin
Loop:
    while i < MAX_TLB_ENTRIES do
        if addr > tlb[i].linear_addr_base /\ addr <= (tlb[i].linear_addr_base + tlb[i].linear_addr_size) then
            tlb_type_return := tlb[i].type;
            return;
        end if;
Inc:
        i := i + 1;
    end while;
    tlb_type_return := TLB_TYPE_NONE;
    return;
end procedure;

\* lookup TLB for a given address, current privilege level, and action (read, write or execute) // return true and the physical address if successful, else false
procedure tlb_lookup(addr, cpl, tlb_op_mask)
    variables i = 0;
    begin
Loop:
    while i < MAX_TLB_ENTRIES do
        if addr > tlb[i].linear_addr_base /\ addr <= (tlb[i].linear_addr_base + tlb[i].linear_addr_size) /\ tlb[i].rpl = cpl /\ tlb[i].op_mask \in tlb_op_mask  then
            tlb_lookup_return := <<TRUE, tlb[i].physical_addr_base + (addr - tlb[i].linear_addr_base)>>;
            return;
        end if;
Inc:
        i := i + 1;
    end while;
    tlb_lookup_return := <<FALSE, 0>>;
    return;
end procedure;

procedure memory_load(addr) begin
Start:
    memory_load_return := memory[addr];
    return;
end procedure;

procedure memory_store(addr, val) begin
Start:
    memory[addr] := val;
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
        call memory_load(paddr);
Ret_load:
        tmp := memory_load_return;
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
        call memory_store(paddr, tmp);
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

\* legacy_code ()
begin
Loop:
while TRUE do
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
end while;

end algorithm *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-53847e9b8c4619bbe14028c86ce2292d
\* Label Start of procedure tlb_init at line 58 col 5 changed to Start_
\* Label Loop of procedure tlb_type at line 109 col 5 changed to Loop_
\* Label Inc of procedure tlb_type at line 115 col 9 changed to Inc_
\* Label Loop of procedure tlb_lookup at line 126 col 5 changed to Loop_t
\* Label Start of procedure memory_load at line 140 col 5 changed to Start_m
\* Label Start of procedure memory_store at line 146 col 5 changed to Start_me
\* Label Start of procedure cpu_read at line 154 col 5 changed to Start_c
\* Label Return of procedure cpu_read at line 156 col 5 changed to Return_
\* Label End of procedure cpu_read at line 166 col 5 changed to End_
\* Label Start of procedure cpu_write at line 171 col 5 changed to Start_cp
\* Label Return of procedure cpu_write at line 173 col 5 changed to Return_c
\* Label End of procedure cpu_write at line 182 col 5 changed to End_c
\* Procedure variable i of procedure tlb_type at line 106 col 15 changed to i_
\* Procedure variable status of procedure cpu_read at line 151 col 15 changed to status_
\* Procedure variable paddr of procedure cpu_read at line 151 col 23 changed to paddr_
\* Parameter addr of procedure tlb_type at line 105 col 20 changed to addr_
\* Parameter addr of procedure tlb_lookup at line 122 col 22 changed to addr_t
\* Parameter addr of procedure memory_load at line 138 col 23 changed to addr_m
\* Parameter addr of procedure memory_store at line 144 col 24 changed to addr_me
\* Parameter addr of procedure cpu_read at line 150 col 20 changed to addr_c
\* Parameter level of procedure cpu_read at line 150 col 26 changed to level_
\* Parameter addr of procedure cpu_write at line 169 col 21 changed to addr_cp
\* Parameter level of procedure cpu_write at line 169 col 27 changed to level_c
CONSTANT defaultInitValue
VARIABLES tlb, tlb_type_return, tlb_lookup_return, memory_load_return, memory, 
          pc, stack, addr_, i_, addr_t, cpl, tlb_op_mask, i, addr_m, addr_me, 
          val, addr_c, level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
          level, type, status, paddr

vars == << tlb, tlb_type_return, tlb_lookup_return, memory_load_return, 
           memory, pc, stack, addr_, i_, addr_t, cpl, tlb_op_mask, i, addr_m, 
           addr_me, val, addr_c, level_, status_, paddr_, tmp, addr_cp, 
           level_c, addr, level, type, status, paddr >>

Init == (* Global variables *)
        /\ tlb = [entry \in 0..MAX_TLB_ENTRIES-1 |->
                     [linear_addr_base |-> 0,
                      linear_addr_size |-> 0,
                      physical_addr_base |-> 0,
                      physical_addr_size |-> 0,
                      rpl |-> 0,
                      op_mask |-> 0]]
        /\ tlb_type_return = 0
        /\ tlb_lookup_return = defaultInitValue
        /\ memory_load_return = defaultInitValue
        /\ memory = [address \in 0..268435456|-> 0]
        (* Procedure tlb_type *)
        /\ addr_ = defaultInitValue
        /\ i_ = 0
        (* Procedure tlb_lookup *)
        /\ addr_t = defaultInitValue
        /\ cpl = defaultInitValue
        /\ tlb_op_mask = defaultInitValue
        /\ i = 0
        (* Procedure memory_load *)
        /\ addr_m = defaultInitValue
        (* Procedure memory_store *)
        /\ addr_me = defaultInitValue
        /\ val = defaultInitValue
        (* Procedure cpu_read *)
        /\ addr_c = defaultInitValue
        /\ level_ = defaultInitValue
        /\ status_ = defaultInitValue
        /\ paddr_ = defaultInitValue
        /\ tmp = defaultInitValue
        (* Procedure cpu_write *)
        /\ addr_cp = defaultInitValue
        /\ level_c = defaultInitValue
        (* Procedure cpu_execute *)
        /\ addr = defaultInitValue
        /\ level = defaultInitValue
        /\ type = defaultInitValue
        /\ status = defaultInitValue
        /\ paddr = defaultInitValue
        /\ stack = << >>
        /\ pc = "Loop"

Start_ == /\ pc = "Start_"
          /\ tlb' = [tlb EXCEPT ![0].linear_addr_base = UOBJCOLL_SENTINEL_LINEAR_ADDR_BASE]
          /\ pc' = "TLB_0"
          /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                          memory_load_return, memory, stack, addr_, i_, addr_t, 
                          cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                          level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                          level, type, status, paddr >>

TLB_0 == /\ pc = "TLB_0"
         /\ tlb' = [tlb EXCEPT ![0].linear_addr_size = UOBJCOLL_SENTINEL_LINEAR_ADDR_SIZE]
         /\ pc' = "TLB_1"
         /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                         memory_load_return, memory, stack, addr_, i_, addr_t, 
                         cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                         level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                         level, type, status, paddr >>

TLB_1 == /\ pc = "TLB_1"
         /\ tlb' = [tlb EXCEPT ![0].physical_addr_base = UOBJCOLL_SENTINEL_PHYSICAL_ADDR_BASE]
         /\ pc' = "TLB_2"
         /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                         memory_load_return, memory, stack, addr_, i_, addr_t, 
                         cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                         level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                         level, type, status, paddr >>

TLB_2 == /\ pc = "TLB_2"
         /\ tlb' = [tlb EXCEPT ![0].physical_addr_size = UOBJCOLL_SENTINEL_PHYSICAL_ADDR_SIZE]
         /\ pc' = "TLB_3"
         /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                         memory_load_return, memory, stack, addr_, i_, addr_t, 
                         cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                         level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                         level, type, status, paddr >>

TLB_3 == /\ pc = "TLB_3"
         /\ tlb' = [tlb EXCEPT ![0].rpl = PRIVILEGE_LEVEL_LEGACY]
         /\ pc' = "TLB_4"
         /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                         memory_load_return, memory, stack, addr_, i_, addr_t, 
                         cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                         level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                         level, type, status, paddr >>

TLB_4 == /\ pc = "TLB_4"
         /\ tlb' = [tlb EXCEPT ![0].op_mask = {TLB_OP_READ, TLB_OP_EXECUTE}]
         /\ pc' = "TLB_5"
         /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                         memory_load_return, memory, stack, addr_, i_, addr_t, 
                         cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                         level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                         level, type, status, paddr >>

TLB_5 == /\ pc = "TLB_5"
         /\ tlb' = [tlb EXCEPT ![0].type = TLB_TYPE_SENTINEL]
         /\ pc' = "TLB_6"
         /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                         memory_load_return, memory, stack, addr_, i_, addr_t, 
                         cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                         level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                         level, type, status, paddr >>

TLB_6 == /\ pc = "TLB_6"
         /\ tlb' = [tlb EXCEPT ![1].linear_addr_base = UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE]
         /\ pc' = "TLB_7"
         /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                         memory_load_return, memory, stack, addr_, i_, addr_t, 
                         cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                         level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                         level, type, status, paddr >>

TLB_7 == /\ pc = "TLB_7"
         /\ tlb' = [tlb EXCEPT ![1].linear_addr_size = UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE]
         /\ pc' = "TLB_8"
         /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                         memory_load_return, memory, stack, addr_, i_, addr_t, 
                         cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                         level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                         level, type, status, paddr >>

TLB_8 == /\ pc = "TLB_8"
         /\ tlb' = [tlb EXCEPT ![1].physical_addr_base = UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_BASE]
         /\ pc' = "TLB_9"
         /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                         memory_load_return, memory, stack, addr_, i_, addr_t, 
                         cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                         level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                         level, type, status, paddr >>

TLB_9 == /\ pc = "TLB_9"
         /\ tlb' = [tlb EXCEPT ![1].physical_addr_size = UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_SIZE]
         /\ pc' = "TLB_10"
         /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                         memory_load_return, memory, stack, addr_, i_, addr_t, 
                         cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                         level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                         level, type, status, paddr >>

TLB_10 == /\ pc = "TLB_10"
          /\ tlb' = [tlb EXCEPT ![1].rpl = PRIVILEGE_LEVEL_UOBJCOLL]
          /\ pc' = "TLB_11"
          /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                          memory_load_return, memory, stack, addr_, i_, addr_t, 
                          cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                          level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                          level, type, status, paddr >>

TLB_11 == /\ pc = "TLB_11"
          /\ tlb' = [tlb EXCEPT ![1].op_mask = {TLB_OP_READ, TLB_OP_WRITE, TLB_OP_EXECUTE}]
          /\ pc' = "TLB_12"
          /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                          memory_load_return, memory, stack, addr_, i_, addr_t, 
                          cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                          level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                          level, type, status, paddr >>

TLB_12 == /\ pc = "TLB_12"
          /\ tlb' = [tlb EXCEPT ![1].type = TLB_TYPE_UOBJCOLL]
          /\ pc' = "TLB_13"
          /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                          memory_load_return, memory, stack, addr_, i_, addr_t, 
                          cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                          level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                          level, type, status, paddr >>

TLB_13 == /\ pc = "TLB_13"
          /\ tlb' = [tlb EXCEPT ![2].linear_addr_base = LEGACY_LINEAR_ADDR_BASE]
          /\ pc' = "TLB_14"
          /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                          memory_load_return, memory, stack, addr_, i_, addr_t, 
                          cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                          level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                          level, type, status, paddr >>

TLB_14 == /\ pc = "TLB_14"
          /\ tlb' = [tlb EXCEPT ![2].linear_addr_size = LEGACY_LINEAR_ADDR_SIZE]
          /\ pc' = "TLB_15"
          /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                          memory_load_return, memory, stack, addr_, i_, addr_t, 
                          cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                          level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                          level, type, status, paddr >>

TLB_15 == /\ pc = "TLB_15"
          /\ tlb' = [tlb EXCEPT ![2].physical_addr_base = LEGACY_PHYSICAL_ADDR_BASE]
          /\ pc' = "TLB_16"
          /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                          memory_load_return, memory, stack, addr_, i_, addr_t, 
                          cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                          level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                          level, type, status, paddr >>

TLB_16 == /\ pc = "TLB_16"
          /\ tlb' = [tlb EXCEPT ![2].physical_addr_size = LEGACY_PHYSICAL_ADDR_SIZE]
          /\ pc' = "TLB_17"
          /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                          memory_load_return, memory, stack, addr_, i_, addr_t, 
                          cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                          level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                          level, type, status, paddr >>

TLB_17 == /\ pc = "TLB_17"
          /\ tlb' = [tlb EXCEPT ![2].rpl = PRIVILEGE_LEVEL_LEGACY]
          /\ pc' = "TLB_18"
          /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                          memory_load_return, memory, stack, addr_, i_, addr_t, 
                          cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                          level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                          level, type, status, paddr >>

TLB_18 == /\ pc = "TLB_18"
          /\ tlb' = [tlb EXCEPT ![2].op_mask = {TLB_OP_READ, TLB_OP_WRITE, TLB_OP_EXECUTE}]
          /\ pc' = "TLB_19"
          /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                          memory_load_return, memory, stack, addr_, i_, addr_t, 
                          cpl, tlb_op_mask, i, addr_m, addr_me, val, addr_c, 
                          level_, status_, paddr_, tmp, addr_cp, level_c, addr, 
                          level, type, status, paddr >>

TLB_19 == /\ pc = "TLB_19"
          /\ tlb' = [tlb EXCEPT ![2].type = TLB_TYPE_LEGACY]
          /\ pc' = Head(stack).pc
          /\ stack' = Tail(stack)
          /\ UNCHANGED << tlb_type_return, tlb_lookup_return, 
                          memory_load_return, memory, addr_, i_, addr_t, cpl, 
                          tlb_op_mask, i, addr_m, addr_me, val, addr_c, level_, 
                          status_, paddr_, tmp, addr_cp, level_c, addr, level, 
                          type, status, paddr >>

tlb_init == Start_ \/ TLB_0 \/ TLB_1 \/ TLB_2 \/ TLB_3 \/ TLB_4 \/ TLB_5
               \/ TLB_6 \/ TLB_7 \/ TLB_8 \/ TLB_9 \/ TLB_10 \/ TLB_11
               \/ TLB_12 \/ TLB_13 \/ TLB_14 \/ TLB_15 \/ TLB_16 \/ TLB_17
               \/ TLB_18 \/ TLB_19

Loop_ == /\ pc = "Loop_"
         /\ IF i_ < MAX_TLB_ENTRIES
               THEN /\ IF addr_ > tlb[i_].linear_addr_base /\ addr_ <= (tlb[i_].linear_addr_base + tlb[i_].linear_addr_size)
                          THEN /\ tlb_type_return' = tlb[i_].type
                               /\ pc' = Head(stack).pc
                               /\ i_' = Head(stack).i_
                               /\ addr_' = Head(stack).addr_
                               /\ stack' = Tail(stack)
                          ELSE /\ pc' = "Inc_"
                               /\ UNCHANGED << tlb_type_return, stack, addr_, 
                                               i_ >>
               ELSE /\ tlb_type_return' = TLB_TYPE_NONE
                    /\ pc' = Head(stack).pc
                    /\ i_' = Head(stack).i_
                    /\ addr_' = Head(stack).addr_
                    /\ stack' = Tail(stack)
         /\ UNCHANGED << tlb, tlb_lookup_return, memory_load_return, memory, 
                         addr_t, cpl, tlb_op_mask, i, addr_m, addr_me, val, 
                         addr_c, level_, status_, paddr_, tmp, addr_cp, 
                         level_c, addr, level, type, status, paddr >>

Inc_ == /\ pc = "Inc_"
        /\ i_' = i_ + 1
        /\ pc' = "Loop_"
        /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                        memory_load_return, memory, stack, addr_, addr_t, cpl, 
                        tlb_op_mask, i, addr_m, addr_me, val, addr_c, level_, 
                        status_, paddr_, tmp, addr_cp, level_c, addr, level, 
                        type, status, paddr >>

tlb_type == Loop_ \/ Inc_

Loop_t == /\ pc = "Loop_t"
          /\ IF i < MAX_TLB_ENTRIES
                THEN /\ IF addr_t > tlb[i].linear_addr_base /\ addr_t <= (tlb[i].linear_addr_base + tlb[i].linear_addr_size) /\ tlb[i].rpl = cpl /\ tlb[i].op_mask \in tlb_op_mask
                           THEN /\ tlb_lookup_return' = <<TRUE, tlb[i].physical_addr_base + (addr_t - tlb[i].linear_addr_base)>>
                                /\ pc' = Head(stack).pc
                                /\ i' = Head(stack).i
                                /\ addr_t' = Head(stack).addr_t
                                /\ cpl' = Head(stack).cpl
                                /\ tlb_op_mask' = Head(stack).tlb_op_mask
                                /\ stack' = Tail(stack)
                           ELSE /\ pc' = "Inc"
                                /\ UNCHANGED << tlb_lookup_return, stack, 
                                                addr_t, cpl, tlb_op_mask, i >>
                ELSE /\ tlb_lookup_return' = <<FALSE, 0>>
                     /\ pc' = Head(stack).pc
                     /\ i' = Head(stack).i
                     /\ addr_t' = Head(stack).addr_t
                     /\ cpl' = Head(stack).cpl
                     /\ tlb_op_mask' = Head(stack).tlb_op_mask
                     /\ stack' = Tail(stack)
          /\ UNCHANGED << tlb, tlb_type_return, memory_load_return, memory, 
                          addr_, i_, addr_m, addr_me, val, addr_c, level_, 
                          status_, paddr_, tmp, addr_cp, level_c, addr, level, 
                          type, status, paddr >>

Inc == /\ pc = "Inc"
       /\ i' = i + 1
       /\ pc' = "Loop_t"
       /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                       memory_load_return, memory, stack, addr_, i_, addr_t, 
                       cpl, tlb_op_mask, addr_m, addr_me, val, addr_c, level_, 
                       status_, paddr_, tmp, addr_cp, level_c, addr, level, 
                       type, status, paddr >>

tlb_lookup == Loop_t \/ Inc

Start_m == /\ pc = "Start_m"
           /\ memory_load_return' = memory[addr_m]
           /\ pc' = Head(stack).pc
           /\ addr_m' = Head(stack).addr_m
           /\ stack' = Tail(stack)
           /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, memory, 
                           addr_, i_, addr_t, cpl, tlb_op_mask, i, addr_me, 
                           val, addr_c, level_, status_, paddr_, tmp, addr_cp, 
                           level_c, addr, level, type, status, paddr >>

memory_load == Start_m

Start_me == /\ pc = "Start_me"
            /\ memory' = [memory EXCEPT ![addr_me] = val]
            /\ pc' = Head(stack).pc
            /\ addr_me' = Head(stack).addr_me
            /\ val' = Head(stack).val
            /\ stack' = Tail(stack)
            /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                            memory_load_return, addr_, i_, addr_t, cpl, 
                            tlb_op_mask, i, addr_m, addr_c, level_, status_, 
                            paddr_, tmp, addr_cp, level_c, addr, level, type, 
                            status, paddr >>

memory_store == Start_me

Start_c == /\ pc = "Start_c"
           /\ /\ addr_t' = addr_c
              /\ cpl' = level_
              /\ stack' = << [ procedure |->  "tlb_lookup",
                               pc        |->  "Return_",
                               i         |->  i,
                               addr_t    |->  addr_t,
                               cpl       |->  cpl,
                               tlb_op_mask |->  tlb_op_mask ] >>
                           \o stack
              /\ tlb_op_mask' = TLB_OP_READ
           /\ i' = 0
           /\ pc' = "Loop_t"
           /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                           memory_load_return, memory, addr_, i_, addr_m, 
                           addr_me, val, addr_c, level_, status_, paddr_, tmp, 
                           addr_cp, level_c, addr, level, type, status, paddr >>

Return_ == /\ pc = "Return_"
           /\ status_' = tlb_lookup_return[1]
           /\ paddr_' = tlb_lookup_return[2]
           /\ IF status_'
                 THEN /\ /\ addr_m' = paddr_'
                         /\ stack' = << [ procedure |->  "memory_load",
                                          pc        |->  "Ret_load",
                                          addr_m    |->  addr_m ] >>
                                      \o stack
                      /\ pc' = "Start_m"
                 ELSE /\ TRUE
                      /\ pc' = "End_"
                      /\ UNCHANGED << stack, addr_m >>
           /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                           memory_load_return, memory, addr_, i_, addr_t, cpl, 
                           tlb_op_mask, i, addr_me, val, addr_c, level_, tmp, 
                           addr_cp, level_c, addr, level, type, status, paddr >>

Ret_load == /\ pc = "Ret_load"
            /\ tmp' = memory_load_return
            /\ pc' = "End_"
            /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                            memory_load_return, memory, stack, addr_, i_, 
                            addr_t, cpl, tlb_op_mask, i, addr_m, addr_me, val, 
                            addr_c, level_, status_, paddr_, addr_cp, level_c, 
                            addr, level, type, status, paddr >>

End_ == /\ pc = "End_"
        /\ pc' = Head(stack).pc
        /\ status_' = Head(stack).status_
        /\ paddr_' = Head(stack).paddr_
        /\ tmp' = Head(stack).tmp
        /\ addr_c' = Head(stack).addr_c
        /\ level_' = Head(stack).level_
        /\ stack' = Tail(stack)
        /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                        memory_load_return, memory, addr_, i_, addr_t, cpl, 
                        tlb_op_mask, i, addr_m, addr_me, val, addr_cp, level_c, 
                        addr, level, type, status, paddr >>

cpu_read == Start_c \/ Return_ \/ Ret_load \/ End_

Start_cp == /\ pc = "Start_cp"
            /\ /\ addr_t' = addr_cp
               /\ cpl' = level_c
               /\ stack' = << [ procedure |->  "tlb_lookup",
                                pc        |->  "Return_c",
                                i         |->  i,
                                addr_t    |->  addr_t,
                                cpl       |->  cpl,
                                tlb_op_mask |->  tlb_op_mask ] >>
                            \o stack
               /\ tlb_op_mask' = TLB_OP_WRITE
            /\ i' = 0
            /\ pc' = "Loop_t"
            /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                            memory_load_return, memory, addr_, i_, addr_m, 
                            addr_me, val, addr_c, level_, status_, paddr_, tmp, 
                            addr_cp, level_c, addr, level, type, status, paddr >>

Return_c == /\ pc = "Return_c"
            /\ status' = tlb_lookup_return[1]
            /\ paddr' = tlb_lookup_return[2]
            /\ IF status'
                  THEN /\ tmp' = nondet_u8
                       /\ /\ addr_me' = paddr'
                          /\ stack' = << [ procedure |->  "memory_store",
                                           pc        |->  "End_c",
                                           addr_me   |->  addr_me,
                                           val       |->  val ] >>
                                       \o stack
                          /\ val' = tmp'
                       /\ pc' = "Start_me"
                  ELSE /\ TRUE
                       /\ pc' = "End_c"
                       /\ UNCHANGED << stack, addr_me, val, tmp >>
            /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                            memory_load_return, memory, addr_, i_, addr_t, cpl, 
                            tlb_op_mask, i, addr_m, addr_c, level_, status_, 
                            paddr_, addr_cp, level_c, addr, level, type >>

End_c == /\ pc = "End_c"
         /\ pc' = Head(stack).pc
         /\ addr_cp' = Head(stack).addr_cp
         /\ level_c' = Head(stack).level_c
         /\ stack' = Tail(stack)
         /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                         memory_load_return, memory, addr_, i_, addr_t, cpl, 
                         tlb_op_mask, i, addr_m, addr_me, val, addr_c, level_, 
                         status_, paddr_, tmp, addr, level, type, status, 
                         paddr >>

cpu_write == Start_cp \/ Return_c \/ End_c

Start == /\ pc = "Start"
         /\ /\ addr_' = addr
            /\ stack' = << [ procedure |->  "tlb_type",
                             pc        |->  "Return",
                             i_        |->  i_,
                             addr_     |->  addr_ ] >>
                         \o stack
         /\ i_' = 0
         /\ pc' = "Loop_"
         /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                         memory_load_return, memory, addr_t, cpl, tlb_op_mask, 
                         i, addr_m, addr_me, val, addr_c, level_, status_, 
                         paddr_, tmp, addr_cp, level_c, addr, level, type, 
                         status, paddr >>

Return == /\ pc = "Return"
          /\ type' = tlb_type_return
          /\ /\ addr_t' = addr
             /\ cpl' = level
             /\ stack' = << [ procedure |->  "tlb_lookup",
                              pc        |->  "Ret_lookup",
                              i         |->  i,
                              addr_t    |->  addr_t,
                              cpl       |->  cpl,
                              tlb_op_mask |->  tlb_op_mask ] >>
                          \o stack
             /\ tlb_op_mask' = TLB_OP_EXECUTE
          /\ i' = 0
          /\ pc' = "Loop_t"
          /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                          memory_load_return, memory, addr_, i_, addr_m, 
                          addr_me, val, addr_c, level_, status_, paddr_, tmp, 
                          addr_cp, level_c, addr, level, status, paddr >>

Ret_lookup == /\ pc = "Ret_lookup"
              /\ status' = tlb_lookup_return[1]
              /\ paddr' = tlb_lookup_return[2]
              /\ IF status'
                    THEN /\ IF type = TLB_TYPE_SENTINEL
                               THEN /\ TRUE
                               ELSE /\ TRUE
                    ELSE /\ TRUE
              /\ pc' = "End"
              /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                              memory_load_return, memory, stack, addr_, i_, 
                              addr_t, cpl, tlb_op_mask, i, addr_m, addr_me, 
                              val, addr_c, level_, status_, paddr_, tmp, 
                              addr_cp, level_c, addr, level, type >>

End == /\ pc = "End"
       /\ pc' = Head(stack).pc
       /\ type' = Head(stack).type
       /\ status' = Head(stack).status
       /\ paddr' = Head(stack).paddr
       /\ addr' = Head(stack).addr
       /\ level' = Head(stack).level
       /\ stack' = Tail(stack)
       /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                       memory_load_return, memory, addr_, i_, addr_t, cpl, 
                       tlb_op_mask, i, addr_m, addr_me, val, addr_c, level_, 
                       status_, paddr_, tmp, addr_cp, level_c >>

cpu_execute == Start \/ Return \/ Ret_lookup \/ End

Loop == /\ pc = "Loop"
        /\ \E case \in nondet_u32:
             \E rand_addr \in nondet_u32:
               IF case = 0
                  THEN /\ /\ addr_c' = rand_addr
                          /\ level_' = PRIVILEGE_LEVEL_LEGACY
                          /\ stack' = << [ procedure |->  "cpu_read",
                                           pc        |->  "Loop",
                                           status_   |->  status_,
                                           paddr_    |->  paddr_,
                                           tmp       |->  tmp,
                                           addr_c    |->  addr_c,
                                           level_    |->  level_ ] >>
                                       \o stack
                       /\ status_' = defaultInitValue
                       /\ paddr_' = defaultInitValue
                       /\ tmp' = defaultInitValue
                       /\ pc' = "Start_c"
                       /\ UNCHANGED << addr_cp, level_c, addr, level, type, 
                                       status, paddr >>
                  ELSE /\ IF case = 1
                             THEN /\ /\ addr_cp' = rand_addr
                                     /\ level_c' = PRIVILEGE_LEVEL_LEGACY
                                     /\ stack' = << [ procedure |->  "cpu_write",
                                                      pc        |->  "Loop",
                                                      addr_cp   |->  addr_cp,
                                                      level_c   |->  level_c ] >>
                                                  \o stack
                                  /\ pc' = "Start_cp"
                                  /\ UNCHANGED << addr, level, type, status, 
                                                  paddr >>
                             ELSE /\ IF case = 2
                                        THEN /\ /\ addr' = rand_addr
                                                /\ level' = PRIVILEGE_LEVEL_LEGACY
                                                /\ stack' = << [ procedure |->  "cpu_execute",
                                                                 pc        |->  "Loop",
                                                                 type      |->  type,
                                                                 status    |->  status,
                                                                 paddr     |->  paddr,
                                                                 addr      |->  addr,
                                                                 level     |->  level ] >>
                                                             \o stack
                                             /\ type' = defaultInitValue
                                             /\ status' = defaultInitValue
                                             /\ paddr' = defaultInitValue
                                             /\ pc' = "Start"
                                        ELSE /\ TRUE
                                             /\ pc' = "Loop"
                                             /\ UNCHANGED << stack, addr, 
                                                             level, type, 
                                                             status, paddr >>
                                  /\ UNCHANGED << addr_cp, level_c >>
                       /\ UNCHANGED << addr_c, level_, status_, paddr_, tmp >>
        /\ UNCHANGED << tlb, tlb_type_return, tlb_lookup_return, 
                        memory_load_return, memory, addr_, i_, addr_t, cpl, 
                        tlb_op_mask, i, addr_m, addr_me, val >>

Next == tlb_init \/ tlb_type \/ tlb_lookup \/ memory_load \/ memory_store
           \/ cpu_read \/ cpu_write \/ cpu_execute \/ Loop

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-8256ce3e49cf7a125569bd2bee7fd9c3


=============================================================================
\* Modification History
\* Last modified Thu Dec 24 07:13:25 PST 2020 by mjmccall
\* Created Thu Dec 17 08:07:51 PST 2020 by mjmccall
