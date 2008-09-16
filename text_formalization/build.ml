(* The daily build.

   This file is to be edited only by T. Hales.
   Please contact him if you have changes to propose.

*)

(* Use load_path to include source/inequalities and source/text_formalization
   in the load path
*)

needs "Multivariate/vectors.ml";;    (* Eventually should load entire   *) 
needs "Examples/analysis.ml";;       (* multivariate-complex theory.    *)
needs "Examples/transc.ml";;         (* Then it won't need these three. *) 

(* 

This runs through the complete proof, except for the
   * interval arithmetic inequalities,
   * graph classification, and
   * linear programming

The order of the load is the order of the logical dependencies
in the proof.

*)

(* load all definitions *)
needs "definitions_kepler.ml";;

(* load inequalities used in text.  Skip interval arith verifications. *)
needs "inequality_spec.ml";;

(* trig *)
needs "trig_spec.ml";;
needs "trig.ml";;

(* tarski *)
needs "collect_geom_spec.ml";;
needs "collect_geom.ml";;

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


