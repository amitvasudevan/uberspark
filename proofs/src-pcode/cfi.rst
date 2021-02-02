// CFI pseudo-code for modeling
// based on CFI invariants in the overleaf paper: https://www.overleaf.com/project/5da730cfe6041d000118ad29
// paper sections 1.8.2, 1.8.3 and 1.8.4
// author: amit vasudevan <amitvasudevan@acm.org>


//------------------------------------------------------------------------------------------------------
// the following are common functions brought in from tlb_model.rst and enhanced for CFI
// TBD: we need to merge logic of these functions from tlb_model.rst and this file (cfi.rst) eventually
//------------------------------------------------------------------------------------------------------

#define MAX_TLB_ENTRIES 5

#define TLB_TYPE_NONE       0
#define TLB_TYPE_INITMETHOD_ENTRYSENTINEL   1
#define TLB_TYPE_PUBLICMETHOD_ENTRYSENTINEL   2
#define TLB_TYPE_RESUMEMETHOD_ENTRYSENTINEL   3
#define TLB_TYPE_UOBJCOLL   4
#define TLB_TYPE_LEGACY     5

#define TLB_OP_READ         1
#define TLB_OP_WRITE        2
#define TLB_OP_EXECUTE      3

#define PRIVILEGE_LEVEL_UOBJCOLL 0
#define PRIVILEGE_LEVEL_LEGACY  3


// the following are defined assuming a total physical memory of
// 0x10000000 = 256MB

#define UOBJCOLL_INITMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_BASE 0x00000000
#define UOBJCOLL_INITMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_SIZE 0x00020000

#define UOBJCOLL_PUBLICMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_BASE 0x00020000
#define UOBJCOLL_PUBLICMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_SIZE 0x00020000

#define UOBJCOLL_RESUMEMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_BASE 0x00040000
#define UOBJCOLL_RESUMEMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_SIZE 0x00020000

#define UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_BASE 0x00060000
#define UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_SIZE 0x01000000

#define LEGACY_PHYSICAL_ADDR_BASE 0x01000000
#define LEGACY_PHYSICAL_ADDR_SIZE 0x0F000000

// the following are defined assuming a 32-bit linear addressing space
// that permits addressing from 0x00000000 through 0xFFFFFFFF
// note the following addresses are initialized to non-overlapping
// and can be part of either first stage page-tables, second stage page-tables
// or even regular segmentation

#define UOBJCOLL_INITMETHOD_ENTRYSENTINEL_LINEAR_ADDR_BASE 0x10000000
#define UOBJCOLL_INITMETHOD_ENTRYSENTINEL_LINEAR_ADDR_SIZE 0x00020000

#define UOBJCOLL_PUBLICMETHOD_ENTRYSENTINEL_LINEAR_ADDR_BASE 0x10020000
#define UOBJCOLL_PUBLICMETHOD_ENTRYSENTINEL_LINEAR_ADDR_SIZE 0x00020000

#define UOBJCOLL_RESUMEMETHOD_ENTRYSENTINEL_LINEAR_ADDR_BASE 0x10040000
#define UOBJCOLL_RESUMEMETHOD_ENTRYSENTINEL_LINEAR_ADDR_SIZE 0x00020000

#define UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE 0x10060000
#define UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE 0x11000000

#define LEGACY_LINEAR_ADDR_BASE 0x11000000
#define LEGACY_LINEAR_ADDR_SIZE 0x1F000000


// cpu state; see section 1.4.2 in overleaf paper for definitions of the fields
struct {
    u32 cpu_cpl;
    u32 cpu_sp;
    u32 cpu_id;
    u32 cpu_pc;
} cpu_state_t;

cpu_state_t cpu_state;


struct {

    u32 linear_addr_base;
    u32 linear_addr_size;

    u32 physical_addr_base;
    u32 physical_addr_size;
    
    u32 requestor_privilege_level;
    
    u32 op_mask;    //logical OR of TLB_OP_READ, TLB_OP_WRITE and/or TLB_OP_EXECUTE
    u32 type; //can be one of TLB_TYPE_SENTINEL, TLB_TYPE_UOBJCOLL, TLB_TYPE_LEGACY

} tlb[MAX_TLB_ENTRIES]

tlb_init(){
    tlb[0].linear_addr_base = UOBJCOLL_INITMETHOD_ENTRYSENTINEL_LINEAR_ADDR_BASE;
    tlb[0].linear_addr_size = UOBJCOLL_INITMETHOD_ENTRYSENTINEL_LINEAR_ADDR_SIZE;
    tlb[0].physical_addr_base = UOBJCOLL_INITMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_BASE;
    tlb[0].physical_addr_size = UOBJCOLL_INITMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_SIZE;
    tlb[0].rpl = PRIVILEGE_LEVEL_LEGACY; 
    tlb[0].op_mask = TLB_OP_READ | TLB_OP_EXECUTE;
    tlb[0].type = TLB_TYPE_INITMETHOD_ENTRYSENTINEL;

    tlb[1].linear_addr_base = UOBJCOLL_PUBLICMETHOD_ENTRYSENTINEL_LINEAR_ADDR_BASE;
    tlb[1].linear_addr_size = UOBJCOLL_PUBLICMETHOD_ENTRYSENTINEL_LINEAR_ADDR_SIZE;
    tlb[1].physical_addr_base = UOBJCOLL_PUBLICMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_BASE;
    tlb[1].physical_addr_size = UOBJCOLL_PUBLICMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_SIZE;
    tlb[1].rpl = PRIVILEGE_LEVEL_LEGACY; 
    tlb[1].op_mask = TLB_OP_READ | TLB_OP_EXECUTE;
    tlb[1].type = TLB_TYPE_PUBLICMETHOD_ENTRYSENTINEL;

    tlb[2].linear_addr_base = UOBJCOLL_RESUMEMETHOD_ENTRYSENTINEL_LINEAR_ADDR_BASE;
    tlb[2].linear_addr_size = UOBJCOLL_RESUMEMETHOD_ENTRYSENTINEL_LINEAR_ADDR_SIZE;
    tlb[2].physical_addr_base = UOBJCOLL_RESUMEMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_BASE;
    tlb[2].physical_addr_size = UOBJCOLL_RESUMEMETHOD_ENTRYSENTINEL_PHYSICAL_ADDR_SIZE;
    tlb[2].rpl = PRIVILEGE_LEVEL_LEGACY; 
    tlb[2].op_mask = TLB_OP_READ | TLB_OP_EXECUTE;
    tlb[2].type = TLB_TYPE_RESUMEMETHOD_ENTRYSENTINEL;

    tlb[3].linear_addr_base = UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE;
    tlb[3].linear_addr_size = UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE;
    tlb[3].physical_addr_base = UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_BASE;
    tlb[3].physical_addr_size = UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_SIZE;
    tlb[3].rpl = PRIVILEGE_LEVEL_UOBJCOLL; 
    tlb[3].op_mask = TLB_OP_READ | TLB_OP_WRITE | TLB_OP_EXECUTE;
    tlb[3].type = TLB_TYPE_UOBJCOLL;

    tlb[4].linear_addr_base = LEGACY_LINEAR_ADDR_BASE;
    tlb[4].linear_addr_size = LEGACY_LINEAR_ADDR_SIZE;
    tlb[4].physical_addr_base = LEGACY_PHYSICAL_ADDR_BASE;
    tlb[4].physical_addr_size = LEGACY_PHYSICAL_ADDR_SIZE;
    tlb[4].rpl = PRIVILEGE_LEVEL_LEGACY; 
    tlb[4].op_mask = TLB_OP_READ | TLB_OP_WRITE | TLB_OP_EXECUTE;
    tlb[4].type = TLB_TYPE_LEGACY;    
}


// get the TLB type for a given address, return TLB_TYPE_NONE if we 
// did not find an entry for the given addr
tlb_type(addr){
    u32 i;

    for(i=0; i < MAX_TLB_ENTRIES; i++){
        if (addr > tlb[i].linear_addr_base && addr <= (tlb[i].linear_addr_base + 
                                            tlb[i].linear_addr_size))
            return tlb[i].type;
    }

    return TLB_TYPE_NONE;
}

// lookup TLB for a given address, current privilege level, and action (read, write or execute)
// return true and the physical address if successful, else false
tlb_lookup(addr, cpl, tlb_op_mask){

    u32 i;

    for(i=0; i < MAX_TLB_ENTRIES; i++){
        if (addr > tlb[i].linear_addr_base && addr <= (tlb[i].linear_addr_base + 
                                            tlb[i].linear_addr_size)
            && tlb[i].rpl == cpl 
            && tlb[i].op_mask &  tlb_op_mask )
            return (true, tlb[i].physical_addr_base + (addr - tlb[i].linear_addr_base));
    }

    (false, 0)
}


cpu_execute(u32 addr, u32 cpl){
    type= tlb_type(addr);    //returns tlb type for addr
    
    (status, paddr) = tlb_lookup(addr, cpl, TLB_OP_EXECUTE); //returns true if successful lookup 

    if(status)
        if(type == TLB_TYPE_INITMETHOD_ENTRYSENTINEL)
            uobjcoll_initmethod_entrysentinel();
        else if(type == TLB_TYPE_PUBLICMETHOD_ENTRYSENTINEL)
            uobjcoll_publicmethod_entrysentinel();
        else if(type == TLB_TYPE_RESUMEMETHOD_ENTRYSENTINEL)
            uobjcoll_resumemethod_entrysentinel();
        else
            cpu_halt();
    else
        cpu_halt(); //error in lookup
}


legacy_code () {
    cpu_cpl = PRIVILEGE_LEVEL_LEGACY;

    while(true){
        switch(nondet_u32() mod 4){
            case 0:
                addr = nondet_u32();
                cpu_read(addr, cpl);
                break;
            case 1:
                addr = nondet_u32();
                cpu_write(addr, cpl);
                break;
            case 2:
                addr = nondet_u32();
                cpu_execute(addr, cpl);
                break;
            case 3:
                cpu_halt();
        }
    }

}


//------------------------------------------------------------------------------------------------------
// CFI modeling specific functions below
// currently models invariants in overleaf paper section 1.8.2
//------------------------------------------------------------------------------------------------------

//NB: when cpu_cpl (CPU privilege level) is set to PRIVILEGE_LEVEL_UOBJCOLL we directly address
//variables that belong within the  UOBJCOLL_NONSENTINEL_{PHYSICAL/LINEAR}_ADDR_BASE to
//UOBJCOLL_NONSENTINEL_{PHYSICAL/LINEAR}_ADDR_SIZE. 
//TBD: in principle we can convert all these direct memory refereces to go via cpu_read function (in tlb_model.rst)

#define UOBJCOLL_MAX_STACKSIZE_PER_CPU  4096
#define MAX_CPUS    1

//for definitions of the fields see section 1.4.2 in the overleaf paper
struct {
    bool legacy_call;
    bool interrupted;
    u8 stack[MAX_CPUS][UOBJCOLL_MAX_STACKSIZE_PER_CPU];
    u8 cpu_sp[MAX_CPUS];
    u8 cpu_pc[MAX_CPUS];
} uobjcoll_ssa_t;

uobjcoll_ssa_t uobjcoll_ssa;


uobjcoll_initmethod_entrysentinel(){
    cpu_state.cpu_cpl = PRIVILEGE_LEVEL_UOBJCOLL;

    if (uobjcoll_ssa.legacy_call == false && uobjcoll_ssa.interrupted == false) {

        //setup uobjcoll execution stack
        cpu_state.cpu_sp = &uobj_ssa.stack[cpu_state.cpu_id].stack[UOBJCOLL_MAX_STACKSIZE_PER_CPU];

        uobjcoll_initmethod();

    }

}

uobjcoll_publicmethod_entrysentinel(){

    cpu_state.cpu_cpl = PRIVILEGE_LEVEL_UOBJCOLL;

    if (uobjcoll_ssa.legacy_call == false && uobjcoll_ssa.interrupted == false) {
        //setup uobjcoll execution stack
        cpu_state.cpu_sp = &uobj_ssa.stack[cpu_state.cpu_id].stack[UOBJCOLL_MAX_STACKSIZE_PER_CPU];

        uobjcoll_publicmethod();
    }
}

uobjcoll_resumemethod_entrysentinel(){

    cpu_state.cpu_cpl = PRIVILEGE_LEVEL_UOBJCOLL;

    if (uobjcoll_ssa.legacy_call == true){
        cpu_pc = uobj_ssa.cpu_pc[cpu_state.cpu_id];
        cpu_sp = uobj_ssa.cpu_sp[cpu_state.cpu_id];
    }

}

legacy_code_exit_sentinel(){

   uobj_ssa.cpu_pc[cpu_state.cpu_id] = cpu_state.cpu_pc;
   uobj_ssa.cpu_sp[cpu_state.cpu_id] = cpu_state.cpu_sp;

   uobjcoll_ssa.legacy_call = true;

   cpu_state.cpu_cpl = PRIVILEGE_LEVEL_LEGACY;
   legacy_code();
}


uobjcoll_initmethod(){

    while(true){
        switch(nondet_u32() mod 5){
            case 0:
                //TBD: scope it down to uobj data segment reads
                addr = nondet_u32(UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE, UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE);
                cpu_read(addr, cpl);
                break;
            case 1:
                //TBD: scope it down to uobj data segment writes
                addr = nondet_u32(UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE, UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE);
                cpu_write(addr, cpl);
                break;
            case 2:
                //TBD: scope it down to uobj code segment executes
                addr = nondet_u32(UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE, UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE);
                cpu_execute(addr, cpl);
                break;
            case 3:
                cpu_halt();
            case 4:
                //TBD: bring this in via cpu_execute(addr, cpl)
                legacy_code_exit_sentinel();
        }
    }

}

uobjcoll_publicmethod(){

    while(true){
        switch(nondet_u32() mod 5){
            case 0:
                //TBD: scope it down to uobj data segment reads
                addr = nondet_u32(UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE, UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE);
                cpu_read(addr, cpl);
                break;
            case 1:
                //TBD: scope it down to uobj data segment writes
                addr = nondet_u32(UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE, UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE);
                cpu_write(addr, cpl);
                break;
            case 2:
                //TBD: scope it down to uobj code segment executes
                addr = nondet_u32(UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE, UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE);
                cpu_execute(addr, cpl);
                break;
            case 3:
                cpu_halt();
            case 4:
                //TBD: bring this in via cpu_execute(addr, cpl)
                legacy_code_exit_sentinel();
        }
    }

}