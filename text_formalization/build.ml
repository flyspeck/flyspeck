(* The daily build.
   This file is to be edited only by T. Hales.
   Please contact him if you have changes to propose.

*)

(* Use load_path to include source/inequalities and source/text_formalization
   in the load path
*)
needs "Multivariate/flyspeck.ml";;
needs "sphere.hl";;
needs "thales_tactic.ml";;


needs "trig_spec.ml";;
needs "trig.ml";;

(* tarski *)
needs "hull.ml";;
needs "collect_geom_a.ml";;
needs "collect_geom.ml";;

(*
collect_geom_spec.ml is incompatible with collect_geom.ml,
because of incompatible new_specifications, starting with
point_eq.

needs "collect_geom_spec.ml";; 
*)

needs "volume.ml";;
needs "hypermap.ml";;
needs "fan.ml";;
needs "toplevel.ml";;
needs "geomdetail.ml";;
needs "assembly.ml";;


*)
