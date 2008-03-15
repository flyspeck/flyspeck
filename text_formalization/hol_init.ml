(* Initialization for kep.ml *)

(* to load this file:  #use "../kep_init.ml";; *)

(* ocamlnum *)

(* #use "hol.ml";; *)

(* #use "/Users/thomashales/Desktop/flyspeck_google/source/text_formalization/kep_init.ml";; *)  

needs "Examples/analysis.ml";;
needs "Examples/transc.ml";;

load_path :=
     ["/Users/thomashales/Desktop/flyspeck_google/source/inequalities/";
      "/Users/thomashales/Desktop/flyspeck_google/source/text_formalization/"]
        @ (!load_path);;

(*
needs "definitions_kepler.ml";;
needs "trig.ml";;
*)
