//constant definitions
#define MAXCPUS 8
#define MAXUOBJCOLLECTIONS 8
#define MAXUOBJSWITHINCOLLECTION 8

#define MAXUOBJCOLLECTIONSTACKSIZE 4096
#define MAXUOBJDEVMMIO 8


// types/records for cpu and memory
//note: device end points are either part of memory or cpu
Struct {
	Id; //unique cpu identifier
	Pc; //cpu program counter pointing to next instruction to be executed
	Sp; //cpu stack pointer pointing to next location in memory for stack operations
	Shared_cpustate[]; //shared cpu state (e.g., general purpose reigisters)
	Legacy_cpustate[];// cpu state that can be accessed by legacy code
	
	Struct{
		Struct{
			Res_cpustate[]; //cpu state that can only be accessed by this uobj
		} uobj_cpustate[MAXUOBJSWITHINCOLLECTION];
	}uobjcoll_cpustate[MAXUOBJCOLLECTIONS];
	
}cpu[MAXCPUS];


Struct {
	Mem_legacy[]; //byte addressable array of legacy memory
	
	Struct {
		Struct {
			Uobj_ssa[MAXCPUS][]; //state save area
			Uobj_code[]; //uobject code
			Uobj_data[]; //uobject data
			Uobj_dmadata[]; //uobject dmadata
			Uobj_devmmio[MAXUOBJDEVMMIO][]; //uobject device end-point pads
		} memuobjs[MAXUOBJSWITHINCOLLECTION]; 
		
		Uobject_stack[MAXCPUS][MAXUOBJCOLLECTIONSTACKSIZE];  //uobject collection stack; one per CPU
	}memuobjcollection[MAXUOBJCOLLECTIONS];

}memory;


//execution processes
Cpu_process(x):  where x is 1 to MAXCPUS-1
	1. Legacy_code(x)
	2. halt
	or
	3. Uobjcollection_code(1..MAXUOBJCOLLECTIONS)
	4. halt


//x = cpu id
Legacy_code(x)
	1. do
		a. Call uobjcollection_code(x, 1..MAXUOBJCOLLECTIONS); add a restriction parameter
		b. Or
		c. Execute code from memory.mem_legacy[]
		d. or
		e. Read/write to memory.mem_legacy[]
		f. Or 
		g. Read/write to cpu[x].shared_cpustate[] 
		h. or 
		i. Read/write to cpu[x].legacy_cpustate[]
		j. Or 
		k. Halt/powerdown
	2. While (true)

//x = cpu id
//y = uobj collection index
Uobjcollection_code(x, y)
	1. Uobject_code(x, y, 1..MAXUOBJSWITHINCOLLECTION); add a restiction parameter
	2. Cpu[x].pc = pc_pre_uobjectcollection_code
	3. Cpu[x].Sp= sp_pre_uobjectcollection_code
	

//x = cpu id
//y = uobjcollection index
//z = uobject index within given collection index
uobject_code(x, y, z)
	 vars: 
		a. Uobject_code_c_func={f1…fn}
		b. Uobject_code_casm_func={c1..cn}
		c. Uobject_code_legacy_funcLegacy_funcs={l1..ln}
		d. Uobjects= {1..MAXUOBJS}
		e. In_uobj=false
		f. Uobj_finished=false
		
	Code: 
		a. If !in_uobj then 
		b. Do
			i. Cpu[x].Pc =  f in uobject_code_c_func
			ii. Or
			iii. Cpu[x].Pc =  c in uobject_code_casm_func
			iv. Or 
			v. Cpu[x].pc = l in uobject_code_legacy_func
			vi. Or
			vii. Read/write cpu[x].uobjcoll_cpustate[y].uobj_cpustate[z].res_cpustate[]
			viii. or
			ix. Read/write memory.memuobjcollection[y].memuobj[z].uobj_data
			x. Or
			xi. Read/write memory.memuobjcollection[y].uobject_stack[x][] within extent of local_frame
			xii. Or
			xiii. Uobj_finished=true
		c. While(uobj_finished)
		d. Uobj_finished=false
		e. In_uobj=false
		f. Cpu[x].pc = pc_pre_uobject_code
		g. Cpu[x].Sp= sp_pre_uobject_code


Uobject_code_c_func (x, y, z):
	1. If !in_cfunc then 
	2. Do
		a. Cpu[x].Pc =  f in uobject_code_c_func
		b. Or
		c. Cpu[x].Pc =  c in uobject_code_casm_func
		d. Or 
		e. Cpu[x].pc = l in uobject_code_legacy_func
		f. Or
		g. Read/write cpu[x].uobjcoll_cpustate[y].uobj_cpustate[z].res_cpustate[]
		h. or
		i. Read/write memory.memuobjcollection[y].memuobj[z].uobj_data
		j. Or
		k. Read/write memory.memuobjcollection[y].uobject_stack[x][] within extent of local_frame
		l. Or
		m. cfunc_finished=true
	3. While(cfunc_finished)
	4. cfunc_finished=false
	5. In_cfunc=false
	6. Cpu[x].pc = pc_pre_cfunc_code
	7. Cpu[x].Sp= sp_pre_cfunc_code

Uobject_code_casm_func (x, y, z):
	1. If !in_casmfunc then 
	2. Do
		a. Cpu[x].Pc =  f in uobject_code_c_func
		b. Or
		c. Cpu[x].Pc =  c in uobject_code_casm_func
		d. Or 
		e. Cpu[x].pc = l in uobject_code_legacy_func
		f. Or
		g. Read/write cpu[x].uobjcoll_cpustate[y].uobj_cpustate[z].res_cpustate[]
		h. or
		i. Read/write memory.memuobjcollection[y].memuobj[z].uobj_data
		j. Or
		k. Read/write memory.memuobjcollection[y].uobject_stack[x][] within extent of local_frame
		l. Or
		m. casmfunc_finished=true
	3. While(casmfunc_finished)
	4. casmfunc_finished=false
	5. In_casmfunc=false
	6. Cpu[x].pc = pc_pre_casmfunc_code
	7. Cpu[x].Sp= sp_pre_casmfunc_code


Uobject_code_legacy_func(x,y,z):
	1. memory.memuobjcollection[y].uobject_sssa[x].sp = cpu[x].sp
	2. memory.memuobjcollection[y].uobject_sssa[x].lr = cpu[x].lr
	3. memory.memuobjcollection[y].uobject_sssa[x].pc = pc_pre_legacy_func
	4. Cpu[x].lr = resumelegacy
	5. Cpu[x].pc = legacy code
	6. Resumelegacy: 
	7. Cpu[x].sp=memory.memuobjcollection[y].uobject_sssa[x].sp
	8. Cpu[x].pc = memory.memuobjcollection[y].uobject_sssa[x].pc

	
//added 9/1/2020
//device execution processes
device_process(x):  where x is 1 to MAXUOBJDEVMMIO-1
	1. do
		a. read from memory.memuobjcollection[(1..MAXUOBJCOLLECTIONS)].memuobj[(1..MAXUOBJSWITHINCOLLECTION)].uobj_dmadata[]
		b. or
		c. write to memory.memuobjcollection[(1..MAXUOBJCOLLECTIONS)].memuobj[(1..MAXUOBJSWITHINCOLLECTION)].uobj_dmadata[]
		d. or
		e. halt
	2. while (true)

	

Notes
	1. Enforcement for legacy_code happens via hardware capabilities or SFI
	2. Enforcement for uobjcollction_code and uobject code happens via software verification, hardware 
       capabilites and/or SFI
	3. We need to come up with memory safety, memory integrity and control-flow integrity description based 
       on this model semantics and prove them
	4. Then we use frama-c to discharge invariants that the model relies upon
	5. invariants can be discharged via:
		i. 		assumption on hardware (PAH) 
		ii. 	assumption on another uobject (PAU)
		iii. 	obligations on uobject (POU)

//added 9/1/2020
device/DMA Notes
	1. the definition of device_process(x) above assumes that the read and write statements within can be 
		discharged via PAH, PAU and/or POU
		ii. for example on intel x86 platforms there is vt-d dma page tables that can be setup to enforce such read
			and write invariants. the page tables become part of a special dma uobject that ensures the appropriate
			mappings
		iii. another example arm platform like rpi3, there is a dma controller device that can be setup with dma
			 control blocks to read/write to memory. so in this case there is a dma uobj that has exclusive control of
			 the dma controller device endpoint and is able to check the control blocks to ensure that they only
			 point to uobj_dmadata[] regions


