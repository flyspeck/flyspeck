(* ========================================================================= *)
(*                          The Jordan Curve Theorem                         *)
(*                                                                           *)
(*                             Proof by Tom Hales                            *)
(*                                                                           *)
(*           A few tweaks by John Harrison for the latest HOL Light          *)
(* ========================================================================= *)

(*** Standard HOL Light library ***)

loads "Library/analysis.ml";;
loads "Library/transc.ml";;
loads "Examples/polylog.ml";;

(*** New stuff ***)

loadt "Jordan/tactics_refine.ml";; (* OK *)
loadt "Jordan/lib_ext.ml";; (* OK *)
loadt "Jordan/tactics_fix.ml";; (* OK *)
loadt "Jordan/parse_ext_override_interface.ml";; (* OK *)
loadt "Jordan/tactics_ext.ml";; (* OK *)
loadt "Jordan/num_ext_gcd.ml";;  (* OK *)
loadt "Jordan/num_ext_nabs.ml";;   (* OK *)
loadt "Jordan/real_ext_geom_series.ml";; (* OK *)
loadt "Rqe/num_calc_simp.ml";;  (* OK *)
loadt "Jordan/real_ext.ml";;  (* OK *)
loadt "Jordan/float.ml";; (* OK *)
loadt "Jordan/tactics_ext2.ml";; (* OK *)
loadt "Jordan/misc_defs_and_lemmas.ml";; (*OK *)
loadt "Jordan/compute_pi.ml";;
loadt "Jordan/metric_spaces.ml";;
loadt "Jordan/jordan_curve_theorem.ml";;
