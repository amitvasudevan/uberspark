(*===========================================================================*)
(*===========================================================================*)
(* uberSpark uobj collection manifest interface implementation *)
(*	 author: amit vasudevan (amitvasudevan@acm.org) *)
(*===========================================================================*)
(*===========================================================================*)



(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(* type definitions *)
(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)

type json_node_uberspark_uobjcoll_uobjs_t =
{
	mutable f_master    : string;
	mutable f_templars  : string list;
};;

type json_node_uberspark_uobjcoll_publicmethods_t =
{
	mutable f_uobj_ns    : string;
	mutable f_pm_name	 : string;
	mutable f_sentinel_type_list : string list;
};;


type json_node_uberspark_uobjcoll_t =
{
	mutable f_namespace    : string;			
	mutable f_platform	   : string;
	mutable f_arch	       : string;
	mutable f_cpu		   : string;
	mutable f_hpl		   : string;
	mutable f_sentinels_intrauobjcoll : string list;
	mutable f_uobjs 		: json_node_uberspark_uobjcoll_uobjs_t;
	mutable f_publicmethods : (string * json_node_uberspark_uobjcoll_publicmethods_t) list;
};;



(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(* interface definitions *)
(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)


(*--------------------------------------------------------------------------*)
(* parse manifest json sub-node "uobjs" into var *)
(* return: *)
(* on success: true; var is modified with master and templar uobj lists *)
(* on failure: false; var is unmodified *)
(*--------------------------------------------------------------------------*)
let json_node_uberspark_uobjcoll_uobjs_to_var 
	(json_node_uberspark_uobjcoll : Yojson.Basic.t)
	(json_node_uberspark_uobjcoll_uobjs_var : json_node_uberspark_uobjcoll_uobjs_t)
	: bool =

	let retval = ref true in

	try
		let open Yojson.Basic.Util in
			let json_uobjcoll_uobjs = json_node_uberspark_uobjcoll |> member "uobjs" in
			if(json_uobjcoll_uobjs <> `Null) then
				begin
					json_node_uberspark_uobjcoll_uobjs_var.f_master <- json_uobjcoll_uobjs |> member "master" |> to_string;
					json_node_uberspark_uobjcoll_uobjs_var.f_templars <- (json_list_to_string_list  (json_uobjcoll_uobjs |> member "templars" |> to_list));
					retval := true;
				end
			;


	with Yojson.Basic.Util.Type_error _ -> 
			retval := false;
	;

	(!retval)
;;


(*--------------------------------------------------------------------------*)
(* parse manifest json sub-node "publicmethods" into var *)
(* return: *)
(* on success: true; var is modified with publicmethods declarations and sentinels *)
(* on failure: false; var is unmodified *)
(*--------------------------------------------------------------------------*)
let json_node_uberspark_uobjcoll_publicmethods_to_var 
	(json_node_uberspark_uobjcoll : Yojson.Basic.t)
	: bool * ((string * json_node_uberspark_uobjcoll_publicmethods_t) list) =

	let retval = ref true in
	let uobjcoll_publicmethods_assoc_list : (string * json_node_uberspark_uobjcoll_publicmethods_t) list ref = ref [] in 

	try
		let open Yojson.Basic.Util in
			let uobjcoll_publicmethods_json = json_node_uberspark_uobjcoll |> member "publicmethods" in
			if uobjcoll_publicmethods_json != `Null then	begin

				let uobj_ns_assoc_list = Yojson.Basic.Util.to_assoc uobjcoll_publicmethods_json in
					
				List.iter (fun ( (uobj_ns:string),(uobj_ns_json:Yojson.Basic.t)) ->

					let pm_name_assoc_list = Yojson.Basic.Util.to_assoc uobj_ns_json in

					List.iter (fun ( (pm_name:string),(sentinel_type_list_json:Yojson.Basic.t)) ->
						let sentinel_type_list = (json_list_to_string_list  (sentinel_type_list_json |> to_list)) in
						let entry : json_node_uberspark_uobjcoll_publicmethods_t = {
							f_uobj_ns = uobj_ns;
							f_pm_name = pm_name;
							f_sentinel_type_list = sentinel_type_list;
						} in
						let canonical_pm_name_key = (Uberspark_namespace.get_variable_name_prefix_from_ns uobj_ns) ^ "__" ^ pm_name in
						uobjcoll_publicmethods_assoc_list := !uobjcoll_publicmethods_assoc_list @ [ (canonical_pm_name_key, entry) ];

					) pm_name_assoc_list;

				) uobj_ns_assoc_list;

				retval := true;
			end;


	with Yojson.Basic.Util.Type_error _ -> 
			retval := false;
	;

	(!retval, !uobjcoll_publicmethods_assoc_list)
;;


(*--------------------------------------------------------------------------*)
(* parse manifest json sub-node "uberspark-uobjcoll" into var *)
(* return: *)
(* on success: true; var is modified with uberspark-uobjcoll json node definition *)
(* on failure: false; var is unmodified *)
(*--------------------------------------------------------------------------*)
let json_node_uberspark_uobjcoll_to_var 
	(mf_json : Yojson.Basic.t)
	(json_node_uberspark_uobjcoll_var : json_node_uberspark_uobjcoll_t)
	: bool =

	let retval = ref true in

	try
		let open Yojson.Basic.Util in
			let json_node_uberspark_uobjcoll = mf_json |> member "uberspark-uobjcoll" in
				if json_node_uberspark_uobjcoll != `Null then begin
					json_node_uberspark_uobjcoll_var.f_namespace <- json_node_uberspark_uobjcoll |> member "namespace" |> to_string;
					json_node_uberspark_uobjcoll_var.f_platform <- json_node_uberspark_uobjcoll |> member "platform" |> to_string;
					json_node_uberspark_uobjcoll_var.f_arch <- json_node_uberspark_uobjcoll |> member "arch" |> to_string;
					json_node_uberspark_uobjcoll_var.f_cpu <- json_node_uberspark_uobjcoll |> member "cpu" |> to_string;
					json_node_uberspark_uobjcoll_var.f_hpl <- json_node_uberspark_uobjcoll |> member "hpl" |> to_string;
					json_node_uberspark_uobjcoll_var.f_sentinels_intrauobjcoll <- (json_list_to_string_list (json_node_uberspark_uobjcoll |> member "sentinels-intrauobjcoll" |> to_list));

					let rval1 = (json_node_uberspark_uobjcoll_uobjs_to_var json_node_uberspark_uobjcoll json_node_uberspark_uobjcoll_var.f_uobjs) in
					let (rval2, json_node_uberspark_uobjcoll_publicmethods_var) = 
						(json_node_uberspark_uobjcoll_publicmethods_to_var json_node_uberspark_uobjcoll) in

					if (rval1 && rval2) then begin
						json_node_uberspark_uobjcoll_var.f_publicmethods <- json_node_uberspark_uobjcoll_publicmethods_var;
						retval := true;
					end;
				end;

	with Yojson.Basic.Util.Type_error _ -> 
			retval := false;
	;

	(!retval)
;;



