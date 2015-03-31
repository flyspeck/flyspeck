(*

Sample file for building the project.
Several lines should be customized depending on
the local setup.

This file sets up the directories where
  HOL Light and the Flyspeck project are found.

It loads HOL Light.
It loads the files of the Flyspeck project,
  excluding linear programming and nonlinear inequalities.
Customization below shows how to include linear programs
  or the import of nonlinear inequalities.
This file does not give the necessary code for the
  cloud computation of the separate nonlinear inequalities
  that are later combined.

The project can be loaded in a single command 
line as follows:
ocaml -init "ocamlinit_hol_light.ml"

*)


let _ = "SAMPLE load file";;
let _ = print_string "Reading ocamlinit_hol_light.ml\n";;
let homedir = "/Users/flyspeck/Desktop/googlecode/";; (*customize this*)

#load "unix.cma";;
#load "str.cma";;

(* Edit this so that HOLLIGHT_DIR is the path to
   the HOL Light files *)

Unix.putenv "HOLLIGHT_DIR" (Filename.concat homedir "hol-light");;

(* Edit this line so that FLYSPECK_DIR is the path to
   the text_formalization subdirectory in the flyspeck project.
*)

Unix.putenv "FLYSPECK_DIR" 
  (Filename.concat homedir "flyspeck/text_formalization");;

Unix.putenv "FLYSPECK_SERIALIZATION" "1";; (* allow import of thms. Import is required for the thm `the_nonlinear_inequalities`.  Remove this line to disallow *)

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

(* new_build_silent()  
   loads all of the flyspeck files up through
    the (weak) main statement of the Kepler conjecture.

It can be customized to obtain somewhat different
end results, by uncommenting 
 the following options.
*)

(* build_option_main();; (* This is the default for the build, giving the weak form of the main statement. *) *)

(* build_option_main_and_lp();; (* include linear programming verifications.  This gives the main statement of the
Kepler conjecture in its strong form. *) *)

(* build_option_the_nonlinear_inequalites();; (* exclude linear program and include
   import the proof of `the_nonlinear_inequalities` *) *)
(* To use this option, serialization needs to be turned
   with Unix.putenv "FLYSPECK_SERIALIZATION" "1",
   as described above *)



new_build_silent();;
let _ = print_string "Done reading ocamlinit_hol_light.ml\n";;

