(*

  Sample file for building the project.  Several lines should be
  customized depending on the local setup.

  Before following the script here, install HOL Light and download the
  Flyspeck project, as described at
  https://code.google.com/p/flyspeck/wiki/InstallationGuide

  This file sets up the directories where HOL Light and the Flyspeck
  project are found.

  It loads HOL Light.  It executes the files of the Flyspeck project,
  excluding linear programming and nonlinear inequalities.  This gives
  the formal proof of the weak version of the main statement of the
  Kepler conjecture.  Additional scripts give the strong version of
  the main statement (chk_strong_main_statement) and the nonlinear
  inequalities (chk_nonlinear_inequalities).  The nonlinear
  inequalities are obtained in a special version of HOL Light that
  allows the import of theorems from other sessions (the cloud
  computations).

  This file does not give the necessary code for the cloud computation
  of the separate nonlinear inequalities.  Cloud computation
  instructions can be found in the file azure/README.md.

  The project can be loaded in a single command line as follows:

  ocaml -init "ocamlinit_hol_light.ml"

*)


let _ = "SAMPLE load file";;
let _ = print_string "Reading ocamlinit_hol_light.ml\n";;
let homedir = "/Users/flyspeck/Desktop/googlecode/";; (*customize this*)

#load "unix.cma";;
#load "str.cma";;

(* Edit this so that HOLLIGHT_DIR is the path to the HOL Light
   files *)

Unix.putenv "HOLLIGHT_DIR" (Filename.concat homedir "hol-light");;

(* Edit this line so that FLYSPECK_DIR is the path to the
   text_formalization subdirectory in the flyspeck project.
*)

Unix.putenv "FLYSPECK_DIR" 
  (Filename.concat homedir "flyspeck/text_formalization");;

(* The following line allows import of theorems formalized in other
   sessions of HOL Light. Import is required for the thm
   `the_nonlinear_inequalities`.  Remove this line to require all
   verifications to be done in the current session of HOL Light. *)

Unix.putenv "FLYSPECK_SERIALIZATION" "1";; 

let hollight_dir = 
  (try Sys.getenv "HOLLIGHT_DIR" with Not_found -> Sys.getcwd());;

(* Add the HOL Light directory *)

Topdirs.dir_directory hollight_dir;;

(* Load HOL Light *)

#use "hol.ml";;

hol_version;;

let flyspeck_dir = 
  (try Sys.getenv "FLYSPECK_DIR" with Not_found -> Sys.getcwd());;

(* This file has instructions for building flyspeck *)

loadt (Filename.concat flyspeck_dir "build/strictbuild.hl");; 

(* The default is to load up through the weak version of the main
   statement of the Kepler conjecture:
*)

do_build(Build.build_sequence_main_statement);;

let chk_weak_main_statement = Audit_formal_proof.chk_thm
  (  The_main_statement.kepler_conjecture_with_assumptions,
     `!a:((((A)list)list)list). tame_classification a /\
       good_linear_programming_results a /\
       the_nonlinear_inequalities
     ==> the_kepler_conjecture`
  );;

(* It takes about a day to load the strong version of the main
   statement:


   do_build(Build.build_sequence_nonserial);;
   
   let chk_strong_main_statement = Audit_formal_proof.chk_thm
     (The_kepler_conjecture.tame_nonlinear_imp_kepler_conjecture,
     `import_tame_classification /\ the_nonlinear_inequalities 
     ==> the_kepler_conjecture`);;

*)

(* Finally, to get `the_nonlinear_inequalities` via imported theorems:

   let _ = Unix.putenv "FLYSPECK_SERIALIZATION" "1" in
     do_build(Build.build_sequence_the_nonlinear_inequalities);;

   let chk_nonlinear_inequalities = Audit_formal_proof.chk_thm
     (Mk_all_ineq.the_nonlinear_inequalities,
     `the_nonlinear_inequalities`);;

*)

let _ = print_string "Done reading ocamlinit_hol_light.ml\n";;
