(*
	uberSpark bridge module
	author: amit vasudevan (amitvasudevan@acm.org)
*)
open Unix
open Yojson

type bridge_hdr_t = {
	mutable btype : string;
	mutable execname: string;
	mutable path: string;
	mutable params: string list;
	mutable extexecname: string;
	mutable devenv: string;
	mutable arch: string;
	mutable cpu: string;
	mutable version: string;
	mutable namespace: string;
}
;;

type cc_bridge_t = { 
	mutable hdr : bridge_hdr_t;
	mutable params_prefix_to_obj: string;
	mutable params_prefix_to_asm: string;
	mutable params_prefix_to_output: string;
};;


let hdr_type = ref "";;
let hdr_namespace = ref "";;
let hdr_platform = ref "";;
let hdr_arch = ref "";;
let hdr_cpu = ref "";;


let cc_bridge_settings : cc_bridge_t = {
	hdr = { btype = "";
			execname = "";
			path = "";
			params = [];
			extexecname = "";
			devenv = "";
			arch = "";
			cpu = "";
			version = "";
			namespace = "";
	};
	params_prefix_to_obj = "";
	params_prefix_to_asm = "";
	params_prefix_to_output = "";
};;

let cc_bridge_settings_loaded = ref false;;


let json_list_to_string_list
	json_list = 
	
	let ret_str_list = ref [] in
		List.iter (fun (x) ->
			ret_str_list := !ret_str_list @ [ (Yojson.Basic.Util.to_string x) ];
		) json_list;

	(!ret_str_list)
;;



let load_from_file 
	(bridge_ns_json_file : string)
	: bool =
	let retval = ref false in
	Uberspark_logger.log "bridge_ns_json_file=%s" bridge_ns_json_file;

	try
		let bridge_json = Yojson.Basic.from_file bridge_ns_json_file in
		(*parse header*)
		let bridge_json_hdr = Yojson.Basic.Util.member "hdr" bridge_json in
			hdr_type := Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "type" bridge_json_hdr);
			hdr_namespace := Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "namespace" bridge_json_hdr);
			hdr_platform := Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "platform" bridge_json_hdr);
			hdr_arch := Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "arch" bridge_json_hdr);
			hdr_cpu := Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "cpu" bridge_json_hdr);
			(* TBD: sanity check header *)
		

		(* parse cc-bridge if found *)
		let cc_bridge_json = Yojson.Basic.Util.member "cc-bridge" bridge_json in
		if (cc_bridge_json <> `Null) then
			begin
				let cc_bridge_json_hdr = Yojson.Basic.Util.member "hdr" cc_bridge_json in
					cc_bridge_settings.hdr.btype <-	Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "btype" cc_bridge_json_hdr);
					cc_bridge_settings.hdr.execname <-	Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "execname" cc_bridge_json_hdr);
					cc_bridge_settings.hdr.path <-	Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "path" cc_bridge_json_hdr);
					cc_bridge_settings.hdr.params <-	json_list_to_string_list ( Yojson.Basic.Util.to_list (Yojson.Basic.Util.member "params" cc_bridge_json_hdr));
					cc_bridge_settings.hdr.extexecname <-	Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "extexecname" cc_bridge_json_hdr);
					cc_bridge_settings.hdr.devenv <-	Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "devenv" cc_bridge_json_hdr);
					cc_bridge_settings.hdr.arch <-	Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "arch" cc_bridge_json_hdr);
					cc_bridge_settings.hdr.cpu <-	Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "cpu" cc_bridge_json_hdr);
					cc_bridge_settings.hdr.version <-	Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "version" cc_bridge_json_hdr);
					cc_bridge_settings.hdr.namespace <-	Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "namespace" cc_bridge_json_hdr);

				cc_bridge_settings.params_prefix_to_obj <- Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "params_prefix_to_obj" cc_bridge_json);
				cc_bridge_settings.params_prefix_to_asm <- Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "params_prefix_to_asm" cc_bridge_json);
				cc_bridge_settings.params_prefix_to_output <- Yojson.Basic.Util.to_string (Yojson.Basic.Util.member "params_prefix_to_output" cc_bridge_json);
			
				cc_bridge_settings_loaded := true;
			end
		;

		
		retval := true;							
	with Yojson.Json_error s -> 
		Uberspark_logger.log ~lvl:Uberspark_logger.Error "%s" s;
		retval := false;
	;
					
	(!retval)
;;

let load 
	(bridge_ns : string)
	: bool =
	let bridge_ns_json_path = Uberspark_config.namespace_root ^ bridge_ns ^ "/uberspark-bridge.json" in
		(load_from_file bridge_ns_json_path)
;;


let dump
	(bridge_ns : string)
	(output_file_name : string)
	=
	let bridge_ns_json_path = Uberspark_config.namespace_root ^ bridge_ns ^ "/uberspark-bridge.json" in
	Uberspark_osservices.file_copy bridge_ns_json_path output_file_name;
	()
;;


let store_settings_to_namespace
	(bridgetypes: string list )
	: unit =

	List.iter (fun (x) ->
		match x with 
		| "cc-bridge" ->
			let output_bridge_ns_path = Uberspark_config.namespace_root ^ "/" ^ 
								Uberspark_config.namespace_bridges_cc_bridge ^ "/" ^
								cc_bridge_settings.hdr.namespace in 
			let output_bridge_json_file = output_bridge_ns_path ^ "/uberspark-bridge.json" in
			
			(* make the namespace directory *)
			Uberspark_logger.log "Directory: %s" output_bridge_ns_path;
			Uberspark_osservices.mkdir_v2 ~parent:true output_bridge_ns_path (`Octal 0o0777);

			let oc = open_out output_bridge_json_file in
				Printf.fprintf oc "\n/* --- this file is autogenerated --- */";
				Printf.fprintf oc "\n/* uberSpark bridge definition file */";
				Printf.fprintf oc "\n";
				Printf.fprintf oc "\n";
				Printf.fprintf oc "\n{";
				Printf.fprintf oc "\n\t\"hdr\":{";
				Printf.fprintf oc "\n\t\t\"type\" : \"%s\"," !hdr_type;
				Printf.fprintf oc "\n\t\t\"namespace\" : \"%s\"," !hdr_namespace;
				Printf.fprintf oc "\n\t\t\"platform\" : \"%s\"," !hdr_platform;
				Printf.fprintf oc "\n\t\t\"arch\" : \"%s\"," !hdr_arch;
				Printf.fprintf oc "\n\t\t\"cpu\" : \"%s\"" !hdr_cpu;
				Printf.fprintf oc "\n\t},";
				Printf.fprintf oc "\n";
				Printf.fprintf oc "\n\t\"cc-bridge\":{";
				Printf.fprintf oc "\n\t\t\"hdr\":{";
				Printf.fprintf oc "\n\t\t\t\"btype\" : \"%s\"," cc_bridge_settings.hdr.btype;
				Printf.fprintf oc "\n\t\t\t\"execname\" : \"%s\"," cc_bridge_settings.hdr.execname;
				Printf.fprintf oc "\n\t\t\t\"path\" : \"%s\"," cc_bridge_settings.hdr.path;
				Printf.fprintf oc "\n\t\t\t\"params\" : [ ";
				let index = ref 0 in
				while !index < ((List.length cc_bridge_settings.hdr.params)-1) do
					Printf.fprintf oc "\"%s\", " (List.nth cc_bridge_settings.hdr.params !index);
					index := !index + 1;
				done;
				if (List.length cc_bridge_settings.hdr.params) > 0 then
					Printf.fprintf oc "\"%s\" " (List.nth cc_bridge_settings.hdr.params ((List.length cc_bridge_settings.hdr.params)-1));
				Printf.fprintf oc " ],";
				Printf.fprintf oc "\n\t\t\t\"extexecname\" : \"%s\"," cc_bridge_settings.hdr.extexecname;
				Printf.fprintf oc "\n\t\t\t\"devenv\" : \"%s\"," cc_bridge_settings.hdr.devenv;
				Printf.fprintf oc "\n\t\t\t\"arch\" : \"%s\"," cc_bridge_settings.hdr.arch;
				Printf.fprintf oc "\n\t\t\t\"version\" : \"%s\"," cc_bridge_settings.hdr.version;
				Printf.fprintf oc "\n\t\t\t\"namespace\" : \"%s\"," cc_bridge_settings.hdr.namespace;
				Printf.fprintf oc "\n\t\t},";
				Printf.fprintf oc "\n\t\t\"params_prefix_to_obj\" : \"%s\"," cc_bridge_settings.params_prefix_to_obj;
				Printf.fprintf oc "\n\t\t\"params_prefix_to_asm\" : \"%s\"," cc_bridge_settings.params_prefix_to_asm;
				Printf.fprintf oc "\n\t\t\"params_prefix_to_output\" : \"%s\"," cc_bridge_settings.params_prefix_to_output;
				Printf.fprintf oc "\n\t}";
				Printf.fprintf oc "\n";
				Printf.fprintf oc "\n}";
			close_out oc;	

			(* check if bridge type is container, if so store dockerfile *)
			if cc_bridge_settings.hdr.btype = "container" then
				begin
					let input_bridge_dockerfile = cc_bridge_settings.hdr.execname in 
					let output_bridge_dockerfile = output_bridge_ns_path ^ "/uberspark-bridge.Dockerfile" in 
						Uberspark_osservices.file_copy input_bridge_dockerfile output_bridge_dockerfile;
				end
			;

		| _ -> let dummy = ref 0 in dummy := 0;
			(*Uberspark_logger.log ~lvl:Uberspark_logger.Warn "unknown bridgetype '%s', ignoring" x;*)
		;	
		
	) bridgetypes;

	()
;;