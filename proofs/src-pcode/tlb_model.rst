#define MAX_TLB_ENTRIES 3

#define TLB_TYPE_NONE       0
#define TLB_TYPE_SENTINEL   1
#define TLB_TYPE_UOBJCOLL   2
#define TLB_TYPE_LEGACY     3

#define TLB_OP_READ         1
#define TLB_OP_WRITE        2
#define TLB_OP_EXECUTE      3

#define PRIVILEGE_LEVEL_UOBJCOLL 0
#define PRIVILEGE_LEVEL_LEGACY  3


// the following are defined assuming a total physical memory of
// 0x10000000 = 256MB

#define UOBJCOLL_SENTINEL_PHYSICAL_ADDR_BASE 0x00000000
#define UOBJCOLL_SENTINEL_PHYSICAL_ADDR_SIZE 0x00020000

#define UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_BASE 0x00002000
#define UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_SIZE 0x01000000

#define LEGACY_PHYSICAL_ADDR_BASE 0x01000000
#define LEGACY_PHYSICAL_ADDR_SIZE 0x0F000000

// the following are defined assuming a 32-bit linear addressing space
// that permits addressing from 0x00000000 through 0xFFFFFFFF
// note the following addresses are initialized to non-overlapping
// and can be part of either first stage page-tables, second stage page-tables
// or even regular segmentation

#define UOBJCOLL_SENTINEL_LINEAR_ADDR_BASE 0x10000000
#define UOBJCOLL_SENTINEL_LINEAR_ADDR_SIZE 0x10020000

#define UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE 0x10002000
#define UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE 0x11000000

#define LEGACY_LINEAR_ADDR_BASE 0x11000000
#define LEGACY_LINEAR_ADDR_SIZE 0x1F000000


//current CPU privilege level register
u32 cpu_cpl;


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
    tlb[0].linear_addr_base = UOBJCOLL_SENTINEL_LINEAR_ADDR_BASE;
    tlb[0].linear_addr_size = UOBJCOLL_SENTINEL_LINEAR_ADDR_SIZE;
    tlb[0].physical_addr_base = UOBJCOLL_SENTINEL_PHYSICAL_ADDR_BASE;
    tlb[0].physical_addr_size = UOBJCOLL_SENTINEL_PHYSICAL_ADDR_SIZE;
    tlb[0].rpl = PRIVILEGE_LEVEL_LEGACY; 
    tlb[0].op_mask = TLB_OP_READ | TLB_OP_EXECUTE;
    tlb[0].type = TLB_TYPE_SENTINEL;

    tlb[1].linear_addr_base = UOBJCOLL_NONSENTINEL_LINEAR_ADDR_BASE;
    tlb[1].linear_addr_size = UOBJCOLL_NONSENTINEL_LINEAR_ADDR_SIZE;
    tlb[1].physical_addr_base = UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_BASE;
    tlb[1].physical_addr_size = UOBJCOLL_NONSENTINEL_PHYSICAL_ADDR_SIZE;
    tlb[0].rpl = PRIVILEGE_LEVEL_UOBJCOLL; 
    tlb[0].op_mask = TLB_OP_READ | TLB_OP_WRITE | TLB_OP_EXECUTE;
    tlb[1].type = TLB_TYPE_UOBJCOLL;

    tlb[2].linear_addr_base = LEGACY_LINEAR_ADDR_BASE;
    tlb[2].linear_addr_size = LEGACY_LINEAR_ADDR_SIZE;
    tlb[2].physical_addr_base = LEGACY_PHYSICAL_ADDR_BASE;
    tlb[2].physical_addr_size = LEGACY_PHYSICAL_ADDR_SIZE;
    tlb[0].rpl = PRIVILEGE_LEVEL_LEGACY; 
    tlb[0].op_mask = TLB_OP_READ | TLB_OP_WRITE | TLB_OP_EXECUTE;
    tlb[2].type = TLB_TYPE_LEGACY;    
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


cpu_read(u32 addr, u32 cpl){
    (status, paddr) = tlb_lookup(addr, cpl, TLB_OP_READ); //returns true if successful lookup 

    if(status)
        tmp = memory_load(paddr);
    else
        cpu_halt(); //error in lookup
}

cpu_write(u32 addr, u32 cpl){

    (status, paddr) = tlb_lookup(addr, cpl, TLB_OP_WRITE); //returns true if successful lookup 

    if(status){
        tmp = nondet_u8();
        memory_store(paddr, tmp);
    }else
        cpu_halt(); //error in lookup
}

cpu_execute(u32 addr, u32 cpl){
    type= tlb_type(addr);    //returns tlb type for addr
    
    (status, paddr) = tlb_lookup(addr, cpl, TLB_OP_EXECUTE); //returns true if successful lookup 

    if(status)
        if(type == TLB_TYPE_SENTINEL)
            sentinel();
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

    



}