#load "str.cma";;
#load "unix.cma";;

let src_dir = "../../formal_ineqs";;	    
let dst_dir = "../formal_ineqs-nat";;

open List;;
open Str;;

type command = 
  (* Removes lines which match given regular expressions *)
  | Remove_lines of string list
  (* Replaces the given expression with a string in all lines *)
  | Replace of string * string
  (* Retains given lines *)
  | Retain_lines of string list
  (* Splits the file at the given point defined by a guard expression *)
  (* guard * commands1 * commands2 *)
  | Split_at of string * command list * command list
  (* Inserts lines at the given point defined by a guard expression *)
  (* guard * lines *)
  | Insert_before of string * string list
  (* Inserts lines at the end of a buffer *)
  | Insert_at_end of string list
  (* Extracts the interface if it is given explicitly in a file *)
  (* interface_cmds *)
  | Extract_interface of command list
  (* Saves all buffers with the given file names *)
  | Save of string list;;

type file_info = {
  name : string;
  commands : command list
};;

let rec unzip = function
  | (a, b) :: t ->
    let r1, r2 = unzip t in
    a :: r1, b :: r2
  | [] -> [], [];;

let search_string rexp str =
  try 
    let _ = search_forward rexp str 0 in
    true
  with Not_found -> false;;

(* Creates all missing directories *)
let rec create_dirs path =
  let dirname = Filename.dirname path in
  if Sys.file_exists dirname then
    if not (Sys.is_directory dirname) then
      failwith (Printf.sprintf "%s exists and it is not a directory" dirname)
    else
      ()
  else
    let _ = create_dirs dirname in
    let _ = Unix.mkdir dirname 0o777 in
    ();;

(* Reads all lines from a file *)
let read_file fname =
  let ic = open_in fname in
  let rec read acc =
    try
      let line = input_line ic in
      read (line :: acc)
    with End_of_file -> acc in
  let lines = read [] in
  let _ = close_in ic in
  rev lines;;

(* Writes all lines to a file *)
let write_file path buf =
  let _ = create_dirs path in
  let oc = open_out path in
  let rec write = function
    | [] -> ()
    | line :: rest ->
      let _ = output_string oc (line ^ "\n") in
      write rest in
  let _ = write buf in
  let _ = close_out oc in
  ();;

(* Removes lines from a buffer which match given regular expressions *)
(* Retains lines matching any regular expression in retain_lines *)
let remove_lines lines retain_lines =
  let reg_exps = map regexp lines in
  let save_exps = map regexp retain_lines in
  let test str = 
    let remove_flag = fold_left (fun f rexp -> search_string rexp str || f) false reg_exps in
    remove_flag && not (fold_left (fun f rexp -> search_string rexp str || f) false save_exps) in
  let rec remove acc = function
    | [] -> rev acc
    | line :: rest ->
      if test line then 
	remove acc rest
      else
	remove (line :: acc) rest in
  remove [];;

(* Replaces the given expression with a string in all buffer lines *)
let replace_lines expr str =
  let rexp = regexp expr in
  let rec replace acc = function
    | [] -> rev acc
    | line :: rest ->
      let line' = global_replace rexp str line in
      replace (line' :: acc) rest in
  replace [];;


(* Inserts lines before the line matching the given guard expression *)
let insert_before guard lines =
  let rexp = regexp guard in
  let rec insert acc = function
    | [] -> rev acc
    | line :: rest ->
      if search_string rexp line then
	rev acc @ lines @ (line :: rest)
      else
	insert (line :: acc) rest in
  insert [];;

(* Inserts lines at the end of a buffer *)
let insert_at_end lines buf = buf @ lines;;

(* Splits the buffer into two buffers at the given point defined by a guard expression *)
let split_at guard =
  let rexp = regexp guard in
  let rec split acc = function
    | [] -> rev acc, []
    | line :: rest ->
      if search_string rexp line then
	rev acc, line :: rest
      else
	split (line :: acc) rest in
  split [];;

(* Extracts interface and saves it in a file *)
let extract_interface =
  let rexp = regexp "module type" and
      rexp_end = regexp "end;;" and
      rexp_sig = regexp "^ *sig" in
  let rec extract acc = function
    | [] -> rev acc, []
    | line :: rest ->
      if search_string rexp_end line then
	rev acc, rest
      else if search_string rexp_sig line then
	extract acc rest
      else
	extract (line :: acc) rest in
  let rec find acc = function
    | [] -> [], rev acc
    | line :: rest ->
      if search_string rexp line then
	let strs, other = extract [] rest in
	strs, rev acc @ other
      else
	find (line :: acc) rest in
  find [];;

	
let process_file dst_dir buf cmds =
  let rec process retain bufs = function
    | [] -> bufs
    | cmd :: cmds ->
      begin
	match cmd with
	  | Remove_lines lines ->
	    let bufs' = map (remove_lines lines retain) bufs in
	    process retain bufs' cmds
	  | Retain_lines lines ->
	    process (lines @ retain) bufs cmds
	  | Replace (expr, str) ->
	    let bufs' = map (replace_lines expr str) bufs in
	    process retain bufs' cmds
	  | Insert_at_end lines ->
	    let bufs' = map (insert_at_end lines) bufs in
	    process retain bufs' cmds
	  | Insert_before (guard, lines) ->
	    let bufs' = map (insert_before guard lines) bufs in
	    process retain bufs' cmds
	  | Split_at (guard, cmds1, cmds2) ->
	    let bufs1, bufs2 = unzip (map (split_at guard) bufs) in
	    let bufs1' = process retain bufs1 cmds1 and
		bufs2' = process retain bufs2 cmds2 in
	    process retain (bufs1' @ bufs2') cmds
	  | Extract_interface interface_cmds ->
	    let bufs1, bufs2 = unzip (map extract_interface bufs) in
	    let _ = process retain bufs1 interface_cmds in
	    process retain bufs2 cmds
	  | Save fnames ->
	    if length fnames <> length bufs then
	      failwith "Save command: length mismatch" 
	    else
	      let _ = map2 (fun fname buf ->
		let path = Filename.concat dst_dir fname in
		write_file path buf) fnames bufs in
	      process retain bufs cmds
      end
  in
  process [] [buf] cmds;;


let process_files src_dir dst_dir files =
  let rec has_save_command cmds =
    match cmds with
      | Save _ :: _ -> true
      | Split_at (_, cmds1, cmds2) :: cmds ->
	has_save_command cmds || has_save_command cmds2 || has_save_command cmds
      | _ :: cmds -> has_save_command cmds
      | [] -> false in
  let add_save_command file =
    if has_save_command file.commands then 
      file.commands
    else
      file.commands @ [Save [file.name]] in
  let add_loaded_message fname cmds =
    let ins_cmd = Insert_at_end [Printf.sprintf "let _ = print_endline \"%s loaded\";;" fname] in
    ins_cmd :: cmds in
  let rec process = function
    | [] -> ()
    | file :: rest ->
      let buf = read_file (Filename.concat src_dir file.name) in
      let cmds = add_save_command file in
      let cmds = add_loaded_message file.name cmds in
      let _ = process_file dst_dir buf cmds in
      process rest in
  process files;;

let files =
  let std_interface = Insert_before ("", ["open Hol_core"; "open Num"]) in
  let std_remove = Remove_lines ["module.* = struct"; 
				 "^end;;"; 
				 "needs \".*\"";
				 "#load";
				 "#use";
				 "#directory";
				 "#install_printer";] in
  let std_insert = Insert_before ("", ["open Hol_core"]) in
  let std_commands = [std_remove; std_insert] in
  let ex_int name = Extract_interface [std_interface; Save [name]] in
  let mk (name, cmds) = {name = name; commands = cmds} in
  map mk [
    "arith_options.hl", std_commands;
    "verifier_options.hl", std_commands;
    "misc/misc_functions.hl", std_commands;
    "misc/misc_vars.hl", std_commands;
    "misc/report.hl", std_commands;
    "arith/arith_cache.hl", std_commands;
    "arith/arith_float.hl", [Retain_lines ["Float_ops"];
			     ex_int "arith/arith_float.mli";
			     Insert_before ("open", ["open Floor"; "open Vectors"]);
			     Replace ("Arith_float.", "")]
      @ std_commands;
    "arith/arith_nat.hl", std_commands;
    "arith/arith_num.hl", [ex_int "arith/arith_num.mli"] @ std_commands;
    "arith/eval_interval.hl", std_commands;
    "arith/float_atn.hl", [ex_int "arith/float_atn.mli";
			   Insert_before ("open", ["open Transcendentals"])] @ std_commands;
    "arith/float_theory.hl", std_commands;
    "arith/interval_arith.hl", std_commands;
    "arith/more_float.hl", std_commands;
    "arith/num_exp_theory.hl", std_commands;
    "lib/ssreflect/sections.hl", std_commands;
    "lib/ssreflect/ssreflect.hl", std_commands;
    "lib/ssrfun.hl", std_commands;
    "lib/ssrbool.hl", std_commands;
    "lib/ssrnat.hl", std_commands;
    "jordan/parse_ext_override_interface.hl", std_commands;
    "jordan/refinement.hl", std_commands;
    "jordan/real_ext.hl", [Insert_before ("open", ["open Vectors"; "open Transcendentals"])] 
      @ std_commands;
    "jordan/taylor_atn.hl", [Insert_before ("open", ["open Vectors"; 
						     "open Transcendentals"; 
						     "open Canal"; 
						     "open Complexes"; 
						     "open Convex"; 
						     "open Realanalysis"])] 
      @ std_commands;
    "list/more_list.hl", std_commands;
    "list/list_conversions.hl", [ex_int "list/list_conversions.mli"] @ std_commands;
    "list/list_float.hl", [ex_int "list/list_float.mli"] @ std_commands;
    "trig/poly.hl", std_commands;
    "trig/poly_eval.hl", std_commands;
    "trig/series.hl", [Insert_before ("", ["open Realanalysis";
					   "open Vectors";
					   "open Topology";
					   "open Canal";
					   "open Complexes";
					   "open Binomial";
					   "open Transcendentals"])] @ std_commands;
    "trig/sin_cos.hl", [Insert_before ("", ["open Transcendentals";
					    "open Realanalysis"])] @ std_commands;
    "trig/matan.hl", [Insert_before ("", ["open Misc";
					  "open Vectors";
					  "open Topology";
					  "open Transcendentals";
					  "open Realanalysis"])] @ std_commands;
    "trig/cos_bounds_eval.hl", [ex_int "trig/cos_bounds_eval.mli";
			       Insert_before ("open", ["open Transcendentals"])] @ std_commands;
    "trig/cos_eval.hl", [ex_int "trig/cos_eval.mli";
			 Insert_before ("open", ["open Transcendentals";
						 "open Floor"])] @ std_commands;
    "trig/sin_eval.hl", [ex_int "trig/sin_eval.mli";
			 Insert_before ("open", ["open Transcendentals"])] @ std_commands;
    "trig/matan_eval.hl", [ex_int "trig/matan_eval.mli"] @ std_commands;
    "taylor/theory/taylor_interval-compiled.hl",
    std_commands @ [Split_at ("LinearApproxArith", 
			      [], [Insert_before ("Section", ["include Taylor_interval1"])]);
		    Insert_before ("", ["open Binomial";
					"open Vectors";
					"open Topology";
					"open Realanalysis";
				        "open Ssreflect";
					"open Ssrfun";
					"open Ssrbool";
					"open Ssrnat";
					"open Interval_arith";
					"open Matan";
					"open Hol_core"]);
		    Save ["taylor/theory/taylor_interval1.hl"; "taylor/theory/taylor_interval.hl"]];
    "taylor/theory/multivariate_taylor-compiled.hl",
    [std_remove] @ 
      [Split_at ("Section Taylor",  [], 
		 [Insert_before ("Section", ["include Multivariate_taylor1"]);
		  Split_at ("Section Diff2Arith",
			    [], [Insert_before ("Section", ["include Multivariate_taylor2"])])]);
       Insert_before ("", ["open Hol_core";
			   "open Ssreflect";
			   "open Binomial";
			   "open Vectors";
			   "open Topology";
			   "open Derivatives";
			   "open Convex";
			   "open Dimension";
			   "open Realanalysis";
			   "open Ssrfun";
			   "open Ssrbool";
			   "open Ssrnat";
			   "open Taylor_interval";
			   "open Interval_arith"]);
       Save ["taylor/theory/multivariate_taylor1.hl"; 
	     "taylor/theory/multivariate_taylor2.hl";
	     "taylor/theory/multivariate_taylor.hl"]];
    "taylor/m_taylor.hl", 
    [Insert_before ("open", ["open Topology"; "open Realanalysis"])] @ std_commands;
    "taylor/m_taylor_arith.hl",
    [Insert_before ("open", ["open Vectors"; "open Derivatives"; "open Realanalysis"])] @ std_commands;
    "taylor/m_taylor_arith2.hl", std_commands;
    "informal/informal_nat.hl", 
    [ex_int "informal/informal_nat.mli"] @ std_commands;
    "informal/informal_float.hl",
    [ex_int "informal/informal_float.mli"] @ std_commands;
    "informal/informal_interval.hl",
    [ex_int "informal/informal_interval.mli"] @ std_commands;
    "informal/informal_poly.hl",
    [ex_int "informal/informal_poly.mli"] @ std_commands;
    "informal/informal_sin_cos.hl",
    [ex_int "informal/informal_sin_cos.mli"] @ std_commands;
    "informal/informal_atn.hl",
    [ex_int "informal/informal_atn.mli"] @ std_commands;
    "informal/informal_matan.hl",
    [ex_int "informal/informal_matan.mli"] @ std_commands;
    "informal/informal_eval_interval.hl", std_commands;
    "informal/informal_taylor.hl", std_commands;
    "informal/informal_search.hl", std_commands;
    "informal/informal_verifier.hl", std_commands;
    "verifier/certificate.hl", std_commands;
    "verifier/m_verifier_build.hl", std_commands;
    "verifier/m_verifier.hl",
    [Insert_before ("open", ["open Topology"; "open Derivatives"])] @ std_commands;
    "verifier/m_verifier_main.hl",
    [Insert_before ("open", ["open Topology"])] @ std_commands;
  ];;
    

(* Process all files *)
let _ = process_files src_dir dst_dir files;;
