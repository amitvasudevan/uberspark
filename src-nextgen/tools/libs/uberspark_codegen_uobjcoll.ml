(*===========================================================================*)
(*===========================================================================*)
(*	uberSpark codegen interface for uberobject collection            		 *)
(*	implementation															 *)
(*	author: amit vasudevan (amitvasudevan@acm.org)							 *)
(*===========================================================================*)
(*===========================================================================*)


(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(* type definitions *)
(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)

type sentinel_info_t =
{
	mutable f_type          : string; 	
    mutable fn_name          : string;
    mutable f_secname       : string;
	mutable code_template		    : string;
	mutable library_code_template  	    : string;	
	mutable sizeof_code_template   : int;	
	mutable fn_address          : int;
    mutable f_pm_addr       : int;
};;





(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(* interface definitions *)
(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)


(*--------------------------------------------------------------------------*)
(* generate sentinel code *)
(*--------------------------------------------------------------------------*)
let generate_sentinel_code	
    (output_filename : string)
    ?(output_banner = "uobjcoll/uobj sentinel code")
	(pm_sentinel_list : sentinel_info_t list)
    : bool	= 

    let retval = ref false in
    
    Uberspark_logger.log ~lvl:Uberspark_logger.Debug "%s: length of pm_sentinel_list=%u" 
        __LOC__ (List.length pm_sentinel_list);
    let oc = open_out output_filename in
        Printf.fprintf oc "\n/* --- this file is autogenerated --- */";
        Printf.fprintf oc "\n/* %s */" output_banner;
        Printf.fprintf oc "\n/* author: amit vasudevan (amitvasudevan@acm.org) */";
        Printf.fprintf oc "\n";
        Printf.fprintf oc "\n";
        Printf.fprintf oc "\n/* --- sentinel code follows --- */";
        Printf.fprintf oc "\n";
        Printf.fprintf oc "\n";

        List.iter (fun (sinfo_entry : sentinel_info_t)  ->

            Printf.fprintf oc "\n";
            Printf.fprintf oc "\n";
            Printf.fprintf oc "\n/* sentinel canonical name: %s */" sinfo_entry.fn_name;
            Printf.fprintf oc "\n.section %s" sinfo_entry.f_secname;
            (*Printf.fprintf oc "\n.global %s" sinfo_entry.fn_name;
            Printf.fprintf oc "\n%s:" sinfo_entry.fn_name;
            *)
            let tcode = Str.global_replace (Str.regexp "PUBLICMETHOD_ADDR") (Printf.sprintf "0x%08x" sinfo_entry.f_pm_addr) sinfo_entry.code_template in
            let tcode_1 = Str.global_replace (Str.regexp "SENTINEL_SIZE") (Printf.sprintf "0x%08x" sinfo_entry.sizeof_code_template) tcode in
            Printf.fprintf oc "\n%s" tcode_1;
            Printf.fprintf oc "\n";
            Printf.fprintf oc "\n";

        ) pm_sentinel_list;

    close_out oc;	

    retval := true;
    (!retval)
;;



(*--------------------------------------------------------------------------*)
(* generate sentinel (legacy) library code *)
(*--------------------------------------------------------------------------*)
let generate_sentinel_libcode	
    (output_filename : string)
    ?(output_banner = "uobjcoll/uobj legacy code public methods interface library")
	(canonical_publicmethods_sentinels_hashtbl : ((string, int)  Hashtbl.t) )
    (sentinel_libcode : string)
    (sentinel_libcode_section_name : string)
    : bool	= 

    let retval = ref false in
    
    Uberspark_logger.log ~lvl:Uberspark_logger.Debug "%s: length of canonical_publicmethods_sentinels_hashtbl=%u" 
        __LOC__ (Hashtbl.length canonical_publicmethods_sentinels_hashtbl);
    let oc = open_out output_filename in
        Printf.fprintf oc "\n/* --- this file is autogenerated --- */";
        Printf.fprintf oc "\n/* %s */" output_banner;
        Printf.fprintf oc "\n/* author: amit vasudevan (amitvasudevan@acm.org) */";
        Printf.fprintf oc "\n";
        Printf.fprintf oc "\n";
        Printf.fprintf oc "\n/* --- uobjcoll/uobj legacy code public methods interface code follows --- */";
        Printf.fprintf oc "\n";
        Printf.fprintf oc "\n";

        Hashtbl.iter (fun canonical_public_method pm_addr  ->

            Printf.fprintf oc "\n";
            Printf.fprintf oc "\n";
            Printf.fprintf oc "\n.section %s" sentinel_libcode_section_name;
            Printf.fprintf oc "\n.global %s" canonical_public_method;
            Printf.fprintf oc "\n%s:" canonical_public_method;
            let tcode = Str.global_replace (Str.regexp "PUBLICMETHOD_SENTINEL_ADDR") (string_of_int pm_addr) sentinel_libcode in
            Printf.fprintf oc "\n%s" tcode;
            Printf.fprintf oc "\n";
            Printf.fprintf oc "\n";

        ) canonical_publicmethods_sentinels_hashtbl;

    close_out oc;	

    retval := true;
    (!retval)
;;





(*--------------------------------------------------------------------------*)
(* generate uobj binary image section mapping *)
(*--------------------------------------------------------------------------*)
let generate_uobj_binary_image_section_mapping	
    (output_filename : string)
    ?(output_banner = "uobj collection uobj binary image section mapping source")
	(uobjcoll_uobjinfo_list : Defs.Basedefs.uobjinfo_t list)
    : bool	= 
        let retval = ref false in
        
        Uberspark_logger.log ~lvl:Uberspark_logger.Debug "uobjcoll_uobjinfo_list length=%u" (List.length uobjcoll_uobjinfo_list);
        let oc = open_out output_filename in
            Printf.fprintf oc "\n/* --- this file is autogenerated --- */";
            Printf.fprintf oc "\n/* %s */" output_banner;
            Printf.fprintf oc "\n/* author: amit vasudevan (amitvasudevan@acm.org) */";
            Printf.fprintf oc "\n";
            Printf.fprintf oc "\n";
            Printf.fprintf oc "\n/* --- uobj binary image section definitions follow --- */";
            Printf.fprintf oc "\n";
            
            List.iter ( fun (uobjinfo_entry : Defs.Basedefs.uobjinfo_t) ->
                Printf.fprintf oc "\n";
                Printf.fprintf oc "\n.section .section_uobj_%s" uobjinfo_entry.f_uobj_name;
                Printf.fprintf oc "\n.incbin \"%s\"" ("./" ^ uobjinfo_entry.f_uobj_name ^ "/" ^ Uberspark_namespace.namespace_uobj_build_dir ^ "/" ^ Uberspark_namespace.namespace_uobj_binary_flat_image_filename);
                Printf.fprintf oc "\n";
            ) uobjcoll_uobjinfo_list;

            Printf.fprintf oc "\n";
            Printf.fprintf oc "\n/* --- end of uobj binary image section definitions --- */";
            Printf.fprintf oc "\n";

        close_out oc;	

        retval := true;
        (!retval)
;;


(*--------------------------------------------------------------------------*)
(* generate uobj linker script *)
(*--------------------------------------------------------------------------*)
let generate_linker_script 
    (output_filename : string)
    (binary_origin : int)
    (binary_size : int)
    (sections_list : (string * Defs.Basedefs.section_info_t) list ) 
    : bool   =

    let oc = open_out output_filename in
        Printf.fprintf oc "\n/* autogenerated uberSpark uobj collection linker script */";
        Printf.fprintf oc "\n/* author: amit vasudevan (amitvasudevan@acm.org) */";
        Printf.fprintf oc "\n";
        Printf.fprintf oc "\n";
        Printf.fprintf oc "\n";
        Printf.fprintf oc "\n";

        (* generate MEMORY information *)
        Printf.fprintf oc "\nMEMORY";
        Printf.fprintf oc "\n{";

        Printf.fprintf oc "\n %s (%s) : ORIGIN = 0x%08x, LENGTH = 0x%08x"
            ("mem_uobjcoll")
            ( "rw" ^ "ail") (binary_origin) (binary_size);

		(*List.iter (fun (key, (x:Defs.Basedefs.section_info_t))  ->
                (* new section memory *)
                Printf.fprintf oc "\n %s (%s) : ORIGIN = 0x%08x, LENGTH = 0x%08x"
                    ("mem_" ^ x.fn_name)
                    ( "rw" ^ "ail") (x.usbinformat.f_addr_start) (x.usbinformat.f_size);
        ) sections_list;
        *)

        Printf.fprintf oc "\n}";
        Printf.fprintf oc "\n";

        (* . = . + LEN - 1 *)

        (* generate SECTIONS information *)            
        Printf.fprintf oc "\nSECTIONS";
        Printf.fprintf oc "\n{";
        Printf.fprintf oc "\n";

   (*     List.iter ( fun ( (key:string), (section_info:Defs.Basedefs.section_info_t)) ->

                        Printf.fprintf oc "\n %s : {" section_info.fn_name;
                        List.iter (fun subsection ->
                                    Printf.fprintf oc "\n *(%s)" subsection;
                        ) section_info.f_subsection_list;
                        Printf.fprintf oc "\n . = ORIGIN(%s) + LENGTH(%s) - 1;" ("mem_" ^ section_info.fn_name) ("mem_" ^ section_info.fn_name);
                        Printf.fprintf oc "\n BYTE(0xAA)";
                        Printf.fprintf oc "\n	} >%s =0x9090" ("mem_" ^ section_info.fn_name);
                        Printf.fprintf oc "\n";

        ) sections_list;
    *)

         List.iter ( fun ( (key:string), (section_info:Defs.Basedefs.section_info_t)) ->

                        Printf.fprintf oc "\n %s : {" section_info.fn_name;
                        List.iter (fun subsection ->
                                    Printf.fprintf oc "\n *(%s)" subsection;
                        ) section_info.f_subsection_list;
                        Printf.fprintf oc "\n . = . + 0x%08x - 1;" section_info.usbinformat.f_size;
                        Printf.fprintf oc "\n BYTE(0xAA)";
                        Printf.fprintf oc "\n	} >mem_uobjcoll =0x9090";
                        Printf.fprintf oc "\n";

        ) sections_list;
    

        

        (* Printf.fprintf oc "\n"; *)
        (* Printf.fprintf oc "\n	/* this is to cause the link to fail if there is"; *)
        (* Printf.fprintf oc "\n	* anything we didn't explicitly place."; *)
        (* Printf.fprintf oc "\n	* when this does cause link to fail, temporarily comment"; *)
        (* Printf.fprintf oc "\n	* this part out to see what sections end up in the output"; *)
        (* Printf.fprintf oc "\n	* which are not handled above, and handle them."; *)
        (* Printf.fprintf oc "\n	*/"; *)
        (* Printf.fprintf oc "\n	/DISCARD/ : {"; *)
        (* Printf.fprintf oc "\n	* ( * ) "; *)
        (* Printf.fprintf oc "\n	}"; *)

        Printf.fprintf oc "\n}";
        Printf.fprintf oc "\n";

                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                
        close_out oc;
        (true)
;;

(*--------------------------------------------------------------------------*)
(* generate uobjcoll top-level include header *)
(*--------------------------------------------------------------------------*)
let generate_top_level_include_header 
    (output_filename : string)
    (configdefs_verbatim : bool)
    (configdefs_assoc_list : ((string * Uberspark_manifest.Uobjcoll.json_node_uberspark_uobjcoll_configdefs_t) list) ) 
    : unit   =

    let oc = open_out output_filename in
        Printf.fprintf oc "\n/* überSpark üobjcoll top-level include header */";
        Printf.fprintf oc "\n/* this file is auto-generated, __do not edit__ */";
        Printf.fprintf oc "\n";
        Printf.fprintf oc "\n";

        (* generate configuration definitions *)
    	List.iter ( fun ( (name : string) , (entry : Uberspark_manifest.Uobjcoll.json_node_uberspark_uobjcoll_configdefs_t) ) -> 

            if entry.value = "@@TRUE@@" then begin
                if configdefs_verbatim = true then begin
                    Printf.fprintf oc "\n#define %s" name;
                end else begin
                    Printf.fprintf oc "\n#define __UBERSPARK_UOBJCOLL_CONFIGDEF_%s__" (String.uppercase name);
                end;
            end else if entry.value = "@@FALSE@@" then begin
                if configdefs_verbatim = true then begin
                    Printf.fprintf oc "\n//#define %s" name;
                end else begin
                    Printf.fprintf oc "\n//#define __UBERSPARK_UOBJCOLL_CONFIGDEF_%s__" (String.uppercase name);
                end;
            end else begin
                if configdefs_verbatim = true then begin
                    Printf.fprintf oc "\n#define %s %s" name entry.value;
                end else begin
                    Printf.fprintf oc "\n#define __UBERSPARK_UOBJCOLL_CONFIGDEF_%s__ %s" (String.uppercase name) entry.value;
                end;
            end;
           
		) configdefs_assoc_list;

        Printf.fprintf oc "\n";
        Printf.fprintf oc "\n";


        Printf.fprintf oc "\n#ifndef __ASSEMBLY__";

        (* define C types/externs *)

        Printf.fprintf oc "\n#endif //__ASSEMBLY__";


        Printf.fprintf oc "\n";
        Printf.fprintf oc "\n";

        close_out oc;
        ()
;;
	


