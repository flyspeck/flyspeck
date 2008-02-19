
(*
 * Load HOL Light and the kepler definition and inequality files.
 * Then use [ocaml_to_sml] to generate an SML file of the
 * inequality syntax.
 *)

#use "hol.ml";;
needs "Examples/analysis.ml";;
needs "Examples/transc.ml";;
needs "Jordan/lib_ext.ml";;
needs "Jordan/parse_ext_override_interface.ml";;
unambiguous_interface();;

let kepler_home = Sys.getenv "KEPLER_HOME";;
(* 
let kepler_home = "/home/sean/save/versioned/projects/kepler/sml";;
#use "/home/sean/save/versioned/projects/kepler/sml/inequalities/holl/kep_inequalities.ml";;
*) 
needs (kepler_home ^ "/inequalities/holl/definitions_kepler.ml");;
needs (kepler_home ^ "/inequalities/holl/kep_inequalities.ml");;
needs (kepler_home ^ "/inequalities/holl/ineq_names.ml");;
needs (kepler_home ^ "/inequalities/holl/ocaml_to_sml.ml");;

let ocaml_ineqs = Ocaml_sml.translate_list ~ignore:Ineq_names.ignore ~terms:Ineq_names.ineqs;;

let _ =
  Ocaml_sml.ineqs_to_sml
    ~file:(kepler_home ^ "/inequalities/inequality-syntax.sml")
    ~ineqs:ocaml_ineqs;;
