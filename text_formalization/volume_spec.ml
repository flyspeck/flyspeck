(* volume axiom *)

let volume_axiom = new_axiom(`volume_props vol`);;


let vol_props = REWRITE_RULE[volume_props] volume_axiom;;
let VOL_TAC = REWRITE_TAC[vol_props];;

let vol_nonneg = prove(`!C. vol C >= &0`,VOL_TAC);;

(* continue... *)

