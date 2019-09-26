(*
  uberSpark configuration pre-processing tool
  author: amit vasudevan <amitvasudevan@acm.org>
*)

open Unix
open Sys
open Yojson


let main () = 
 
  (* sanity check usage *)
  if (Array.length Sys.argv) < 2 then
  begin
    Printf.printf "Usage: uberspark_confpp <input_json>\n\n";
  end;
   
  (* get json file and open it *)  
  let input_json_filename = Sys.argv.(1) in 
    Printf.printf "Using configuration json file: %s\n" input_json_filename;

  (* read input json file *)  
  let config_mf_json = ref `Null in
  try

    let mf_json = Yojson.Basic.from_file input_json_filename in
      config_mf_json := mf_json;
        
  with Yojson.Json_error s -> 
      Printf.printf "ERROR in reading manifest: %s" s;
      ignore(exit 1);
  ;

  Printf.printf "Successfully read json\n";

  (*parse json *)  
  try
  let open Yojson.Basic.Util in
      if !config_mf_json != `Null then
        begin

          let mf_assoc_list = Yojson.Basic.Util.to_assoc !config_mf_json in
            
            List.iter (fun (x,y) ->
             Printf.printf "%s:\n" x;

             let mf_files_json = y |> member "files" in
              if mf_files_json != `Null then
                begin
                  Printf.printf "files:\n";
                  let files_json_list = mf_files_json |> 
                      to_list in 
                    List.iter (fun x -> 
                        Printf.printf "%s\n" (x |> to_string);
                      ) files_json_list;
                end
              ;

              let mf_def_nodes_json = y |> member "def-nodes" in
              if mf_def_nodes_json != `Null then
                begin
                  Printf.printf "def-nodes:\n";
                  let def_nodes_assoc_list = Yojson.Basic.Util.to_assoc mf_def_nodes_json in
                  List.iter (fun (x,y) ->
                    Printf.printf "%s:\n" x;
                    let def_nodes_types_assoc_list = Yojson.Basic.Util.to_assoc y in
                    List.iter (fun (m,n) ->
                      Printf.printf "%s:\n" m;
                      let def_nodes_types_inner_assoc_list = Yojson.Basic.Util.to_assoc n in
                      List.iter (fun (a,b) ->
                        Printf.printf "id:%s, val:%s\n" a (b |> to_string);
                      ) def_nodes_types_inner_assoc_list;
                    ) def_nodes_types_assoc_list;
                  )def_nodes_assoc_list;
                end
              ;

              ()
            ) mf_assoc_list;
             
             Printf.printf "converted to associative list!\n";     
        end
      ;
                          
with Yojson.Basic.Util.Type_error _ -> 
  Printf.printf "ERROR in reading manifest: type error\n";
  ignore(exit 1);
;





;;


main ();;

