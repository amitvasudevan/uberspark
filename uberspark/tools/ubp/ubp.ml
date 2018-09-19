(*
	frama-c plugin for blueprint conformance
	author: amit vasudevan (amitvasudevan@acm.org)
*)
(* open Umfcommon *)
open Uslog
open Libusmf
open Sys
open Str


(*
module Self = Plugin.Register
	(struct
		let name = "US blueprint conformance"
		let shortname = "ubp"
		let help = "UberSpark blueprint conformance plugin"
	end)


module Cmdopt_slabsfile = Self.String
	(struct
		let option_name = "-umf-uobjlist"
		let default = ""
		let arg_name = "uobjlist-file"
		let help = "uobj list file"
	end)

module Cmdopt_outputdir_sentinelstubs = Self.String
	(struct
		let option_name = "-umf-outdirsentinelstubs"
		let default = ""
		let arg_name = "outdirsentinelstubs"
		let help = "output directory for uobj sentinel stubs"
	end)



module Cmdopt_maxincldevlistentries = Self.String
	(struct
		let option_name = "-umf-maxincldevlistentries"
		let default = ""
		let arg_name = "max-incldevlistentries"
		let help = "total number of INCL device list entries"
	end)

module Cmdopt_maxexcldevlistentries = Self.String
	(struct
		let option_name = "-umf-maxexcldevlistentries"
		let default = ""
		let arg_name = "max-excldevlistentries"
		let help = "total number of EXCL device list entries"
	end)

module Cmdopt_maxmemoffsetentries = Self.String
	(struct
		let option_name = "-umf-maxmemoffsetentries"
		let default = ""
		let arg_name = "max-memoffsetentries"
		let help = "total number of MEMOFFSET entries"
	end)

module Cmdopt_memoffsets = Self.False
	(struct
		let option_name = "-umf-memoffsets"
		(* let default = false *)
		let help = "when on (off by default), include absolute memory offsets in MEMOFFSETS list"
	end)
*)

(*
	**************************************************************************
	global variables
	**************************************************************************
*)

(*	command line inputs *)
let g_slabsfile = ref "";;	(* argv 0 *)
let g_outputdir_sentinelstubs = ref "";; (* argv 1 *)
let g_maxincldevlistentries = ref 0;;  (* argv 2 *)
let g_maxexcldevlistentries = ref 0;;  (* argv 3 *)
let g_maxmemoffsetentries = ref 0;; (* argv 4 *)
let g_memoffsets = ref false;; (*argv 5 *)

(* other global variables *)
let g_rootdir = ref "";;


(*
let ubp_process_cmdline () =
	g_slabsfile := Cmdopt_slabsfile.get();
	g_outputdir_sentinelstubs := Cmdopt_outputdir_sentinelstubs.get();
	g_maxincldevlistentries := int_of_string (Cmdopt_maxincldevlistentries.get());
	g_maxexcldevlistentries := int_of_string (Cmdopt_maxexcldevlistentries.get());
	g_maxmemoffsetentries := int_of_string (Cmdopt_maxmemoffsetentries.get());
	if Cmdopt_memoffsets.get() then g_memoffsets := true else g_memoffsets := false;

	
	Self.result "g_slabsfile=%s\n" !g_slabsfile;
	Self.result "g_outputdir_sentinelstubs=%s\n" !g_outputdir_sentinelstubs;
	Self.result "g_maxincldevlistentries=%d\n" !g_maxincldevlistentries;
	Self.result "g_maxexcldevlistentries=%d\n" !g_maxexcldevlistentries;
	Self.result "g_maxmemoffsetentries=%d\n" !g_maxmemoffsetentries;
	Self.result "g_memoffsets=%b\n" !g_memoffsets;
	()
*)


let ubp_process_cmdline () =
	let len = Array.length Sys.argv in
		Uslog.logf "umfparse" Uslog.Info "cmdline len=%u" len;

		if len = 7 then
	    	begin
					g_slabsfile := Sys.argv.(1);
					g_outputdir_sentinelstubs := Sys.argv.(2);
					g_maxincldevlistentries := int_of_string (Sys.argv.(3));
					g_maxexcldevlistentries := int_of_string (Sys.argv.(4));
					g_maxmemoffsetentries := int_of_string (Sys.argv.(5));
					if int_of_string (Sys.argv.(6)) = 1 then g_memoffsets := true else g_memoffsets := false;

					Uslog.logf "ubp" Uslog.Info "g_slabsfile=%s\n" !g_slabsfile;
					Uslog.logf "ubp" Uslog.Info "g_outputdir_sentinelstubs=%s\n" !g_outputdir_sentinelstubs;
					Uslog.logf "ubp" Uslog.Info "g_maxincldevlistentries=%d\n" !g_maxincldevlistentries;
					Uslog.logf "ubp" Uslog.Info "g_maxexcldevlistentries=%d\n" !g_maxexcldevlistentries;
					Uslog.logf "ubp" Uslog.Info "g_maxmemoffsetentries=%d\n" !g_maxmemoffsetentries;
					Uslog.logf "ubp" Uslog.Info "g_memoffsets=%b\n" !g_memoffsets;

				end
		else
				begin
					Uslog.logf "ubp" Uslog.Info "ubp_process_cmdline: Insufficient Parameters!";
					ignore(exit 1);
				end
		;

()


let ubp_outputsentinelstubforslab sentinelstubsdir slabname slabid =
	let sstubfilename = (sentinelstubsdir ^  slabname ^ "_sstub.ag.v.c") in 
	let assertstring = ref "" in
	let oc = open_out sstubfilename in
	
	(* compute assert string *) 
	if (Hashtbl.mem Libusmf.slab_idtocalleemask slabid) then
		assertstring := "(sp->src_slabid == " ^ (string_of_int slabid) ^ " && ( " ^ (Printf.sprintf "0x%08xUL " (Hashtbl.find Libusmf.slab_idtocalleemask slabid)) ^ " & (1UL << sp->dst_slabid)))"
	else
		assertstring := "1"
	;				

	Printf.fprintf oc  "\n/* autogenerated XMHF blue print conformance sentinel stub file */";
	Printf.fprintf oc  "\n/* author: amit vasudevan (amitvasudevan@acm.org) */";
	Printf.fprintf oc  "\n\n";
	Printf.fprintf oc  "#include <xmhf.h>\r\n";
	Printf.fprintf oc  "#include <xmhf-debug.h>\r\n";
	Printf.fprintf oc  "#include <xmhfgeec.h>\r\n";
	Printf.fprintf oc  "\n\n";
	Printf.fprintf oc  "#include <xc.h>\r\n";
    Printf.fprintf oc  "#include <%s.h>\r\n" slabname;
	Printf.fprintf oc  "\n\n";

	Printf.fprintf oc  "void __slab_callsentinel(slab_params_t *sp){\r\n";

	Printf.fprintf oc  "  /*@assert %s ; */\r\n" !assertstring;

	Printf.fprintf oc  "}\r\n";

	close_out oc;
	()




let ubp_outputsentinelstubs () =
	let i = ref 0 in
	
	while (!i < !Libusmf.g_totalslabs) do
		if (compare (Hashtbl.find Libusmf.slab_idtotype !i) "VfT_SLAB") = 0 then
			ubp_outputsentinelstubforslab !g_outputdir_sentinelstubs (Hashtbl.find Libusmf.slab_idtoname !i) !i
		;
	    i := !i + 1;
	done;
	()


(*	
let run () =
	Self.result "Generating blueprint conformance sentinel stubs...\n";
	ubp_process_cmdline ();

	g_rootdir := (Filename.dirname !g_slabsfile) ^ "/";
	Self.result "g_rootdir=%s\n" !g_rootdir;

	umfcommon_init !g_slabsfile !g_memoffsets !g_rootdir;
	Self.result "g_totalslabs=%d \n" !g_totalslabs;
	
	ubp_outputsentinelstubs ();
	
	Self.result "Done.\n";
	()


let () = Db.Main.extend run

*)

let main () =
	Uslog.current_level := Uslog.ord Uslog.Info;

	Uslog.logf "ubp" Uslog.Info "Generating blueprint conformance sentinel stubs...\n";
	ubp_process_cmdline ();

	g_rootdir := (Filename.dirname !g_slabsfile) ^ "/";
	Uslog.logf "ubp" Uslog.Info "g_rootdir=%s\n" !g_rootdir;

	Libusmf.usmf_maxincldevlistentries := !g_maxincldevlistentries;  
	Libusmf.usmf_maxexcldevlistentries := !g_maxexcldevlistentries; 
	Libusmf.usmf_maxmemoffsetentries := !g_maxmemoffsetentries;

(*	Libusmf.usmf_initialize !g_slabsfile !g_memoffsets !g_rootdir;*)
	Libusmf.usmf_parse_uobj_list !g_slabsfile !g_rootdir;
	Libusmf.usmf_parse_uobjs !g_memoffsets;

	Uslog.logf "ubp" Uslog.Info "g_totalslabs=%d \n" !Libusmf.g_totalslabs;
	
	ubp_outputsentinelstubs ();
	
	Uslog.logf "ubp" Uslog.Info "Done.\n";

;;

		
main ();;





