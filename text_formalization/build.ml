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

(* derivatives *)
  needs "deriv_spec.ml";;
  needs "deriv.ml";;

(* volume *)
  needs "prevolume_spec.ml";;
  needs "prevolume.ml";;
  needs "volume_spec.ml";;
  needs "volume.ml";;

(* hypermap *)
needs "hypermap_spec.ml";;
needs "hypermap.ml";;

(* fan *)
needs "fan_spec.ml";;
needs "fan.ml";;

(* toplevel *)
needs "toplevel_spec.ml";;
needs "toplevel.ml";;

(* geomdetail *)
needs "geomdetail_spec.ml";;
needs "geomdetail.ml";;

(* assembly_listing *)
needs "assembly_listing_spec.ml";;
needs "assembly_listing.ml";;
needs "assembly_spec.ml";;
needs "assembly.ml";;

(* tame *)
needs "tame_spec.ml";;
needs "tame.ml";;

(* computer code contributions *)
needs "graph_generator_spec.ml";;
needs "lp_bounds_spec.ml";;

(* final result *)
needs "kepler_theorem.ml";;


*)
