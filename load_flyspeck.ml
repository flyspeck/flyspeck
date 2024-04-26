#load "unix.cma";;

(* Edit these paths *)
let flyspeck_dir = "/home/monad/work/git/forks/flyspeck/text_formalization";;
let hollight_dir = "/home/monad/work/git/forks/hol-light";;

let () = Unix.putenv "FLYSPECK_DIR" flyspeck_dir;;
let () = Unix.putenv "HOLLIGHT_DIR" hollight_dir;;

needs "Multivariate/flyspeck.ml";;

needs (Filename.concat flyspeck_dir "build/strictbuild.hl");;
needs "build/build.hl";;

let build_to_seq seq name =
  let i = index name seq in
  let seq0, _ = chop_list (i + 1) seq in
  let _ = map flyspeck_needs seq0 in
  ();;

(* Loads the given Flyspeck file and all its dependencies.
   The file path should be relative to flyspeck/text_formalization.
   The linear program bounds are not loaded and verified when this function is used.
   Examples:
   build_to "hypermap/hypermap.hl";  
   build_to "local/LFJCIXP.hl"; *)
let build_to name =
  build_to_seq Build.build_sequence_main_statement name;;

(* This function can be used to load and verify Flyspeck files including
   bounds of linear programs *)
let build_to_full name =
  build_to_seq Build.build_sequence_full name;;

(* Loading the main statement without linear program bounds *)
(*
build_to "general/the_main_statement.hl";;
*)

(* Loading the main statement with linear program bounds *)
(*
build_to_full "general/the_kepler_conjecture.hl";;
*)