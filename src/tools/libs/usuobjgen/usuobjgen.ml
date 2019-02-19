(*------------------------------------------------------------------------------
	uberSpark uberobject support module generation interface
	author: amit vasudevan (amitvasudevan@acm.org)
------------------------------------------------------------------------------*)

open Usconfig
open Uslog
open Usmanifest
open Usextbinutils

module Usuobjgen =
	struct

	let log_tag = "Usuobjgen";;


	let generate_linker_script 
		(fname : string)
		(sections_hashtbl : (string, Usextbinutils.ld_section_info_t) Hashtbl.t)
 		: string =
		
		let linker_script_filename = (fname ^ ".lscript") in
		let oc = open_out linker_script_filename in
			Printf.fprintf oc "\n/* autogenerated uberSpark linker script */";
			Printf.fprintf oc "\n/* author: amit vasudevan (amitvasudevan@acm.org) */";
			Printf.fprintf oc "\n";
			Printf.fprintf oc "\n";
			Printf.fprintf oc "\nOUTPUT_ARCH(\"i386\")";
			Printf.fprintf oc "\n";
			Printf.fprintf oc "\nMEMORY";
			Printf.fprintf oc "\n{";
	
			Hashtbl.iter (fun key (x:Usextbinutils.ld_section_info_t)  ->
				(* new section memory *)
				Printf.fprintf oc "\n %s (%s) : ORIGIN = 0x%08x, LENGTH = 0x%08x"
					("mem_" ^ x.s_name)
					( x.s_attribute ^ "ail") (x.s_origin) (x.s_length);
			)  sections_hashtbl;
					
			Printf.fprintf oc "\n}";
			Printf.fprintf oc "\n";
			
			Printf.fprintf oc "\nSECTIONS";
			Printf.fprintf oc "\n{";
			Printf.fprintf oc "\n";
	
			
			Hashtbl.iter (fun key (x:Usextbinutils.ld_section_info_t)  ->
				(* new section *)
				Printf.fprintf oc "\n	. = 0x%08x;" x.s_origin;
		    Printf.fprintf oc "\n %s : {" x.s_name;
				List.iter (fun subsection ->
					    Printf.fprintf oc "\n *(%s)" subsection;
				) x.s_subsection_list;
				Printf.fprintf oc "\n . = 0x%08x;" x.s_length; 
		    Printf.fprintf oc "\n	} >mem_%s =0x9090" x.s_name;
		    Printf.fprintf oc "\n";
			) sections_hashtbl;
	
			Printf.fprintf oc "\n";
			Printf.fprintf oc "\n	/* this is to cause the link to fail if there is";
			Printf.fprintf oc "\n	* anything we didn't explicitly place.";
			Printf.fprintf oc "\n	* when this does cause link to fail, temporarily comment";
			Printf.fprintf oc "\n	* this part out to see what sections end up in the output";
			Printf.fprintf oc "\n	* which are not handled above, and handle them.";
			Printf.fprintf oc "\n	*/";
			Printf.fprintf oc "\n	/DISCARD/ : {";
			Printf.fprintf oc "\n	*(*)";
			Printf.fprintf oc "\n	}";
			Printf.fprintf oc "\n}";
			Printf.fprintf oc "\n";
																																																																																																																									
			close_out oc;
			(linker_script_filename)
	;;
																
																																																																								
																																																																																																																																												
																																																																																																																																																																																																																																																																																				
	end