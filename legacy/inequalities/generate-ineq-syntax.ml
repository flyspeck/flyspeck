
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
let kepler_home = "/Users/seanmcl/save/versioned/projects/kepler/src";;
*) 
loads (kepler_home ^ "/inequalities/holl/definitions_kepler.ml");;
loads (kepler_home ^ "/inequalities/holl/kep_inequalities.ml");;
loads (kepler_home ^ "/inequalities/holl/kep_ineq_bis.ml");;
loads (kepler_home ^ "/inequalities/holl/kepler_ineq_names.ml");;
loads (kepler_home ^ "/inequalities/holl/dodec_inequalities.ml");;
loads (kepler_home ^ "/inequalities/holl/dodec_ineq_names.ml");;
loads (kepler_home ^ "/inequalities/holl/ocaml_to_sml.ml");;

let kepler_ineqs = Ocaml_sml.translate_list ~ignore:Kepler_ineq_names.ignore ~terms:Kepler_ineq_names.kepler_ineqs;;
let dodec_ineqs = Ocaml_sml.translate_list ~ignore:[] ~terms:Dodec_ineq_names.dodec_ineqs;;

let _ =
  Ocaml_sml.ineqs_to_sml
    ~file:(kepler_home ^ "/inequalities/kepler-inequality-syntax-base.sml")
    ~ineqs:kepler_ineqs
    ~univ:"Kepler";;

let _ =
  Ocaml_sml.ineqs_to_sml
    ~file:(kepler_home ^ "/inequalities/dodec-inequality-syntax-base.sml")
    ~ineqs:dodec_ineqs
    ~univ:"Dodec";;
