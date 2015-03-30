let _ = "SAMPLE load file";;
let _ = print_string "Reading ocamlinit_hol_light.ml\n";;
let homedir = "/Users/flyspeck/Desktop/googlecode/";; (*customize this*)

#load "unix.cma";;
#load "str.cma";;

Unix.putenv "HOLLIGHT_DIR" (Filename.concat homedir "hol-light");;
Unix.putenv "FLYSPECK_DIR" 
  (Filename.concat homedir "flyspeck/text_formalization");;
Unix.putenv "FLYSPECK_SERIALIZATION" "1";; (* allow preloaded thms. Remove this line to disallow *)
let hollight_dir = 
  (try Sys.getenv "HOLLIGHT_DIR" with Not_found -> Sys.getcwd());;
Topdirs.dir_directory hollight_dir;;
#use "hol.ml";;
hol_version;;

let flyspeck_dir = 
  (try Sys.getenv "FLYSPECK_DIR" with Not_found -> Sys.getcwd());;

loadt (Filename.concat flyspeck_dir "strictbuild.hl");; 
new_build_silent();;
let _ = print_string "Done reading ocamlinit_hol_light.ml\n";;

