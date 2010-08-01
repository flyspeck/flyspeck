(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(* Lemma: TARJJUW                                                             *)
(* Chapter: packing                                                           *)
(* Author: Dang Tat Dat                                                       *)
(* Date: 2010-02-13                                                           *)
(* ========================================================================== *)

(* edits by thales:
    wrapped in a module.
   Moved into the project on August 2, 2010.
*)

module Tarjjuw  = struct

(*
needs "/home/nyx/flyspeck/working/flyspeck_needs.hl";;

flyspeck_needs "general/sphere.hl";;
*)

open Sphere;;

(*-----------Definition------------------------------------------------------*)
let weakly_saturated = 
    new_definition 
     `weakly_saturated (V:real^3 ->bool) (r:real) (r':real) <=>
        (!(v:real^3).(&2 <= dist(vec 0,v) ) /\ (dist(vec 0, v) <= r') ==>
            (?(u:real^3). (u IN V) /\ (~((vec 0) = u)) /\ (dist(u,v) < r)))`;;

let half_spaces =
    new_definition 
    `half_spaces (a:real^3) (b:real) =
     {x:real^3| (a dot x) <= b}`;;

(*----------------------------------------------------------------------------*)
let norm_equa = prove (`!(v:real^3) (r':real) (p:real^3).(&0 < r') /\ (~(p = vec 0)) /\ (v = (r'/(norm p))% p) ==> (r' = norm v)`,REPEAT GEN_TAC THEN STRIP_TAC THEN 
SUBGOAL_THEN `norm (v:real^3) = norm (((r':real)/(norm (p:real^3)))%p)` ASSUME_TAC THENL 
[REWRITE_TAC [] THEN
ASM_MESON_TAC [];SUBGOAL_THEN `&0 < norm (p:real^3)` ASSUME_TAC THENL
[REWRITE_TAC[] THEN 
ASM_REWRITE_TAC [NORM_POS_LT];SUBGOAL_THEN `norm (((r':real)/(norm (p:real^3)))%p) = (abs (r'/norm p))*(norm p)` ASSUME_TAC THENL [REWRITE_TAC[] THEN REWRITE_TAC [NORM_MUL];SUBGOAL_THEN `&0 < ((r':real)/(norm (p:real^3)))` ASSUME_TAC THENL [REWRITE_TAC[] THEN ASM_MESON_TAC [REAL_LT_DIV];SUBGOAL_THEN `abs ((r':real) / norm (p:real^3)) = r'/(norm p)` ASSUME_TAC THENL [REWRITE_TAC[] THEN ASM_REWRITE_TAC [REAL_ABS_REFL] THEN ASM_ARITH_TAC;SUBGOAL_THEN `abs ((r':real) / norm (p:real^3)) * norm p = ((r':real) / norm (p:real^3)) * norm p` ASSUME_TAC THENL [ASM_ARITH_TAC;SUBGOAL_THEN `~(norm (p:real^3) = &0)` ASSUME_TAC THENL [ASM_ARITH_TAC;ASM_MESON_TAC [REAL_DIV_RMUL]]]]]]]]);;

let norm_equa1 = prove (`!(v:real^3) (r':real) (p:real^3). (&0 < r') /\ (~(p = vec 0)) /\ (v = (r'/(norm p))% p) ==> norm (((r')/(norm (p)))%p) = r'`,REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `(r':real) = norm (v:real^3)` ASSUME_TAC THENL
[ASM_MESON_TAC [norm_equa];
SUBGOAL_THEN `norm (v:real^3) = norm (((r':real)/(norm (p:real^3)))%p)` ASSUME_TAC THENL
[ASM_MESON_TAC[];
SUBGOAL_THEN `(r':real) = norm (((r':real)/(norm (p:real^3)))%p)` ASSUME_TAC THENL
[ASM_ARITH_TAC;ASM_MESON_TAC [EQ_SYM_EQ]]]]);;

let norm_equa2 = prove (`!(v:real^3) (r':real) (p:real^3). (&0 < r') /\ (~(p = vec 0)) ==> norm (((r')/(norm (p)))%p) = r'`,REPEAT GEN_TAC THEN STRIP_TAC THEN
SUBGOAL_THEN `&0 < norm (p:real^3)` ASSUME_TAC THENL 
[REWRITE_TAC[] THEN
ASM_REWRITE_TAC [NORM_POS_LT];
SUBGOAL_THEN `norm (((r':real)/(norm (p:real^3)))%p) = (abs (r'/norm p))*(norm p)` ASSUME_TAC THENL 
[REWRITE_TAC[] THEN
REWRITE_TAC [NORM_MUL];
SUBGOAL_THEN `&0 < ((r':real)/(norm (p:real^3)))` ASSUME_TAC THENL
[REWRITE_TAC[] THEN
ASM_MESON_TAC [REAL_LT_DIV];
SUBGOAL_THEN `abs ((r':real) / norm (p:real^3)) = r'/(norm p)` ASSUME_TAC THENL
[REWRITE_TAC[] THEN
ASM_REWRITE_TAC [REAL_ABS_REFL] THEN ASM_ARITH_TAC;
SUBGOAL_THEN `abs ((r':real) / norm (p:real^3)) * norm p = ((r':real) / norm (p:real^3)) * norm p` ASSUME_TAC THENL
[ASM_ARITH_TAC;
SUBGOAL_THEN `~(norm (p:real^3) = &0)` ASSUME_TAC THENL 
[ASM_ARITH_TAC;
SUBGOAL_THEN `norm (((r':real)/(norm (p:real^3)))%p) =  ((r':real) / norm (p:real^3)) * norm p` ASSUME_TAC THENL 
[REWRITE_TAC[] THEN ASM_ARITH_TAC;
ASM_MESON_TAC [REAL_DIV_RMUL]]]]]]]]);;

(*-------------------------------------------------------------------*)
let th2 = prove (`!(v:real^3) (r':real) (p:real^3).(~(p = vec 0)) /\ (v = (r'/(norm p))% p) ==>
(r'% p = (norm p)%v)`,REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `(norm (p:real^3)) % (v:real^3) =(norm (p:real^3)) % ((r'/(norm p))% p) ` ASSUME_TAC THENL [REWRITE_TAC [] THEN ASM_MESON_TAC [VECTOR_MUL_LCANCEL];SUBGOAL_THEN `(norm (p:real^3)) % (((r':real)/(norm p))% p) = ((norm p) * (r'/norm p))%p` ASSUME_TAC THENL [REWRITE_TAC[] THEN MESON_TAC[VECTOR_MUL_ASSOC];SUBGOAL_THEN `~(norm (p:real^3) = &0)` ASSUME_TAC THENL [REWRITE_TAC[] THEN REWRITE_TAC[NORM_EQ_0] THEN ASM_MESON_TAC[];SUBGOAL_THEN `(norm (p:real^3)) * ((r':real)/norm p) = r'` ASSUME_TAC THENL [REWRITE_TAC[] THEN ASM_MESON_TAC [REAL_DIV_LMUL];SUBGOAL_THEN `((norm (p:real^3)) * ((r':real)/norm p))%p = r' % p` ASSUME_TAC THENL [REWRITE_TAC[] THEN ASM_MESON_TAC[];ASM_MESON_TAC[]]]]]]);;

(*-------------------------------------------------------------------*)

g `!(V:real^3 -> bool)(u:real^3).(packing V)  /\ (V SUBSET (:real^3) DIFF ball (vec 0,&2)) /\ (u IN V) ==> &2 <= norm u`;;
e (REPEAT GEN_TAC THEN REWRITE_TAC [ball; DIFF;SUBSET]);;
e (STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC));;
e (DISCH_TAC);;
e (DISCH_THEN (LABEL_TAC "F1"));;
e (REWRITE_TAC [IN] THEN REPEAT STRIP_TAC);;
e (REMOVE_THEN "F1" (MP_TAC o SPEC `u:real^3`));;
e (ASM_REWRITE_TAC [IN;IN_ELIM_THM]);;
e (STRIP_TAC);;
e (POP_ASSUM MP_TAC);;
e (REWRITE_TAC [DIST_0]);;
e (ARITH_TAC);;

let th3 = top_thm();;


g `!(V:real^3 -> bool)(u:real^3).(packing V)  /\ (V SUBSET (:real^3) DIFF ball (vec 0,&2)) /\ (u IN V) ==> ~(u = vec 0)`;;
e (REPEAT GEN_TAC);;
e (STRIP_TAC);;
e (SUBGOAL_THEN `&2 <= norm (u:real^3)` ASSUME_TAC);;
e (ASM_MESON_TAC [th3]);;
e (MP_TAC (ISPECL [`&0`;`&2`;`norm (u:real^3)`]REAL_LTE_TRANS));;
e (ASM_REWRITE_TAC [ARITH_RULE `&0 < &2`]);;
e (REWRITE_TAC[NORM_POS_LT]);;

let th31 = top_thm();;

g `!(V:real^3 -> bool)(u:real^3)(v:real^3).(packing V) /\ (vec 0 IN V) /\ (u IN V) /\ (~(vec 0 = u)) ==> &2 <= norm u`;;
e (REPEAT GEN_TAC THEN REWRITE_TAC [packing;IN] THEN STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC "F1") THEN REPEAT STRIP_TAC);;
e (ASM_CASES_TAC `&2 <= norm (u:real^3)` THENL [ASM_ARITH_TAC;POP_ASSUM MP_TAC THEN REWRITE_TAC [GSYM DIST_0]]);;
e (STRIP_TAC THEN REMOVE_THEN "F1" (MP_TAC o SPECL [`(vec 0):real^3`;`u:real^3`]));;
e (ASM_REWRITE_TAC[]);;

let th32 = top_thm();;
(*------------------------------------------------------------------------*)

let th4 =prove (`!(u:real^3) (v:real^3) (r:real).dist (u,v) < r ==> (dist (u,v)) pow 2 < r pow 2`,REPEAT GEN_TAC THEN REWRITE_TAC [dist] THEN STRIP_TAC THEN SUBGOAL_THEN `&0 <= norm ((u:real^3) - (v:real^3))` ASSUME_TAC THENL [REWRITE_TAC [NORM_POS_LE];SUBGOAL_THEN `&0 <= r` ASSUME_TAC THENL [ASM_ARITH_TAC;SUBGOAL_THEN `abs (norm ((u:real^3) - (v:real^3))) = norm (u - v)` ASSUME_TAC THENL [REWRITE_TAC [REAL_ABS_NORM];SUBGOAL_THEN `abs (r:real) = r` ASSUME_TAC THENL [ASM_ARITH_TAC;SUBGOAL_THEN `abs (norm ((u:real^3) - (v:real^3))) < abs(r:real)` ASSUME_TAC THENL [ASM_ARITH_TAC;ASM_MESON_TAC [REAL_LT_SQUARE_ABS]]]]]]);;

(*-------------------------------------------------------------------------*)

g `!(V:real^3 -> bool)(g:real^3->real) (r:real) (r':real) (u:real^3) (v:real^3) (p:real^3).(packing V) /\ V SUBSET (:real^3) DIFF ball (vec 0,&2) /\ (&2 <= r) /\ (r <= r') /\  (~(p = vec 0)) /\ ((((g u) * r')/ &2) < norm p) /\ (v = (r'/(norm p))% p) /\ ((u dot p) <= (g u)) /\ (~(vec 0 = u)) /\ (dist (u,v) < r) /\ (u IN V)  ==> (norm p < norm p)`;;
e (REPEAT GEN_TAC);;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`v:real^3`;`r':real`]norm_equa));;
e (DISCH_THEN (MP_TAC o SPEC `p:real^3`));;
e (SUBGOAL_THEN `(&2 <= r':real)` ASSUME_TAC);;
e (ASM_MESON_TAC[REAL_LE_TRANS]);;
e (SUBGOAL_THEN `&0 < (r':real)` ASSUME_TAC);;
e (POP_ASSUM MP_TAC);;
e (MP_TAC (ARITH_RULE `&0 < &2`));;
e (MESON_TAC[REAL_LTE_TRANS]);;
e (ASM_REWRITE_TAC[]);;
e (FIND_ASSUM (fun th -> REWRITE_TAC [GSYM th]) `(v:real^3) = (r':real) / norm p % (p:real^3)`);;
e (STRIP_TAC);;
e (SUBGOAL_THEN `&0 <= norm (v:real^3)` ASSUME_TAC);;
e (REWRITE_TAC [NORM_POS_LE]);;
e (SUBGOAL_THEN `((u:real^3) dot (p:real^3)) * (norm (v:real^3)) <=  ((g:real^3->real) u) * norm v` ASSUME_TAC);;
e (ASM_MESON_TAC[REAL_LE_RMUL]);;
e (SUBGOAL_THEN `(((u:real^3) dot (p:real^3)) * (norm (v:real^3)))/(&2) <=  (((g:real^3->real) u) * norm v)/(&2)` ASSUME_TAC);;
e (MP_TAC (ARITH_RULE `&0 < &2`));;
e (ASM_MESON_TAC[REAL_LE_DIV2_EQ]);;
e (MP_TAC (ISPECL [`((u:real^3) dot (p:real^3))`;`(r':real)`]REAL_MUL_SYM));;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`r':real`;`u:real^3`;`p:real^3`]DOT_RMUL));;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`v:real^3`;`r':real`;`p:real^3`]th2));;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th]) `~(p:real^3 = vec 0)`);;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th]) `v:real^3 = (r':real) / norm p % (p:real^3)`);;
e (FIND_ASSUM (fun th -> REWRITE_TAC [GSYM th]) `v:real^3 = (r':real) / norm p % (p:real^3)`);;
e (STRIP_TAC);;
e (SUBGOAL_THEN `(u:real^3) dot ((r':real)% (p:real^3)) = u dot ((norm p)%v)` ASSUME_TAC);; 
e (ASM_MESON_TAC[]);;
e (SUBGOAL_THEN ` (u:real^3) dot ((norm (p:real^3))%(v:real^3)) = (norm p) * (u dot v)` ASSUME_TAC);;
e (MESON_TAC [DOT_RMUL]);;
e (SUBGOAL_THEN `((u:real^3) dot (p:real^3)) * (r':real) = norm p * (u dot (v:real^3))` ASSUME_TAC);;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th]) `((u:real^3) dot (p:real^3)) * (r':real) = r' * (u dot p)`);;
e (FIND_ASSUM (fun th -> REWRITE_TAC [GSYM th]) `(u:real^3) dot (r':real) % (p:real^3)= r' * (u dot p)`);;
e (FIND_ASSUM (fun th -> REWRITE_TAC [GSYM th]) `(u:real^3) dot (r':real) % (p:real^3)= r' * (u dot p)`);;
e (POP_ASSUM MP_TAC);;
e (POP_ASSUM MP_TAC);;
e (MESON_TAC[EQ_TRANS]);;
e (MP_TAC (ISPECL [`(u:real^3)`;`(v:real^3)`]DOT_NORM_NEG));;
e (STRIP_TAC);;
e (SUBGOAL_THEN `((norm (p:real^3)) * ((u:real^3) dot (v:real^3))) = (((norm p) *(((norm u pow 2 + norm v pow 2) - (norm (u - v)) pow 2)) / &2))` ASSUME_TAC);; 
e (POP_ASSUM MP_TAC);;
e (MESON_TAC[]);;
e (POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM dist] THEN STRIP_TAC);;
e (MP_TAC (ISPECL [`V:real^3->bool`;`u:real^3`]th3));;
e (ASM_REWRITE_TAC[]);;

e (STRIP_TAC);;
e (MP_TAC (ISPECL [`&2`]REAL_ABS_REFL));;
e (REWRITE_TAC [ARITH_RULE `&0 <= &2`]);;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`u:real^3`]REAL_ABS_NORM) THEN STRIP_TAC);;
e (SUBGOAL_THEN `abs (&2) <= abs (norm (u:real^3))` ASSUME_TAC);;
e (ASM_ARITH_TAC);;
e (MP_TAC (ISPECL [`&2`;`norm (u:real^3)`]REAL_LE_SQUARE_ABS));;
e (POP_ASSUM (fun th -> REWRITE_TAC [th]));;
e (REWRITE_TAC [ARITH_RULE `&2 pow 2 = &4`]);;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`u:real^3`;`v:real^3`;`r:real`]th4));;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th]) `dist (u:real^3,v:real^3) < r:real`);;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`((r:real) pow 2)`;`dist (u:real^3,v:real^3) pow 2`]REAL_LT_NEG));;
e (FIRST_ASSUM (fun th -> REWRITE_TAC [th]));;
e (STRIP_TAC);;
e (SUBGOAL_THEN `(norm (v:real^3)) pow 2 = (r':real) pow 2`ASSUME_TAC);;
e (UNDISCH_TAC `r':real = norm (v:real^3)`);;
e (MESON_TAC[]);;
e (SUBGOAL_THEN `((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) =
 (norm (u:real^3)) pow 2 + (r':real) pow 2` ASSUME_TAC);;
e (ASM_ARITH_TAC);;
e (SUBGOAL_THEN `&4 + (norm (v:real^3)) pow 2 <= ((norm (u:real^3)) pow 2 + (norm v) pow 2 )` ASSUME_TAC);;
e (ASM_ARITH_TAC);;
e (SUBGOAL_THEN `(((u:real^3) dot (p:real^3)) * (r':real)) / &2 < (norm (p))` ASSUME_TAC);;
e (UNDISCH_TAC `(((u:real^3) dot (p:real^3)) * norm (v:real^3)) / &2 <= ((g:real^3->real) u * norm v) / &2`);;
e (FIND_ASSUM (fun th -> REWRITE_TAC [GSYM th]) `r':real = norm (v:real^3)`);;
e (UNDISCH_TAC `((g:real^3->real) (u:real^3) * (r':real)) / &2 < norm (p:real^3)`);;
e (ARITH_TAC);;
e (SUBGOAL_THEN `((norm (p:real^3)) * ((u:real^3) dot (v:real^3))) / &2 < (norm (p))`ASSUME_TAC);;
e (ASM_ARITH_TAC);;
e (SUBGOAL_THEN `&4 + (r':real) pow 2 <= ((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2 )` ASSUME_TAC);;
e (ASM_ARITH_TAC);;
e (SUBGOAL_THEN `&4 + (r':real) pow 2 + --(dist ((u:real^3),(v:real^3)) pow 2) <= ((norm (u)) pow 2 + (norm (v)) pow 2 + --(dist (u,v) pow 2) )` ASSUME_TAC);; e (ASM_ARITH_TAC);;
e (SUBGOAL_THEN `&4 + (r':real) pow 2 + --((r:real) pow 2)  <= &4 + (r':real) pow 2 + --(dist ((u:real^3),(v:real^3)) pow 2)` ASSUME_TAC);;
e (ASM_ARITH_TAC);;
e (SUBGOAL_THEN `&4 + (r':real) pow 2 + --((r:real) pow 2) <= ((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2 + --(dist (u,v) pow 2))` ASSUME_TAC THEN
ASM_ARITH_TAC);;
e (SUBGOAL_THEN `&0 <= r:real` ASSUME_TAC);;
e (UNDISCH_TAC `&2 <= r:real`);;
e (MP_TAC (ARITH_RULE `&0 <= &2`));;
e (MESON_TAC [REAL_LE_TRANS]);;
e (SUBGOAL_THEN `&0 <= r':real` ASSUME_TAC);;
e (UNDISCH_TAC `r <= r':real`);;
e (POP_ASSUM MP_TAC);;
e (MESON_TAC [REAL_LE_TRANS]);;
e (MP_TAC (ISPECL [`r':real`]REAL_ABS_REFL));;
e (FIND_ASSUM (fun th -> REWRITE_TAC [GSYM th]) `&0 <= r':real`);;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`r:real`]REAL_ABS_REFL));;
e (FIND_ASSUM (fun th -> REWRITE_TAC [GSYM th]) `&0 <= r:real`);;
e (STRIP_TAC);;
e (SUBGOAL_THEN `abs (r:real) <= abs(r':real)` ASSUME_TAC);;
e (POP_ASSUM (fun th -> REWRITE_TAC[th]));;
e (POP_ASSUM (fun th -> REWRITE_TAC[th]));;
e (ASM_REWRITE_TAC[]);;
e (MP_TAC (ISPECL [`r:real`;`r':real`]REAL_LE_SQUARE_ABS));;
e (POP_ASSUM (fun th -> REWRITE_TAC[th]));;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`r':real`;`r:real`]REAL_SUB_LE));;
e (UNDISCH_TAC `r:real <= r':real`);;
e (STRIP_TAC THEN POP_ASSUM (fun th -> REWRITE_TAC[th]));;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`(r':real) pow 2`;`(r:real) pow 2 `]REAL_SUB_LE));;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th]) `(r:real) pow 2 <= (r':real) pow 2`);;
e (STRIP_TAC);;
e (SUBGOAL_THEN `&4 <= &4 + (r':real) pow 2 - (r:real) pow 2` ASSUME_TAC);;
e (MP_TAC (ISPECL [`&4`;`&0`;`(r':real) pow 2 - (r:real) pow 2`]REAL_LE_LADD));;
e (POP_ASSUM (fun th -> REWRITE_TAC[th]));; 
e (REWRITE_TAC [ARITH_RULE `&4 + &0 = &4`]);;
e (MP_TAC (ISPECL [`&4 + ((r':real) pow 2)`;`((r:real) pow 2)`]real_sub));;
e (STRIP_TAC);;
e (SUBGOAL_THEN `&4 + ((r':real) pow 2) - ((r:real) pow 2) <= ((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) + --(dist (u,v) pow 2)` ASSUME_TAC);;
e  (ASM_ARITH_TAC);;
e (SUBGOAL_THEN `&4 <= ((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) + --(dist (u,v) pow 2)` ASSUME_TAC);;
e (ASM_ARITH_TAC);;
e (MP_TAC (ISPECL [`(((norm (p:real^3)) * ((u:real^3) dot (v:real^3)))/ &2)`;`(norm (p:real^3))`;`&2`]REAL_LT_RMUL));;
e (REWRITE_TAC [ARITH_RULE `&0 < &2`]);;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th]) `(norm (p:real^3) * ((u:real^3) dot (v:real^3))) / &2 < norm p`);;
e (REWRITE_TAC [ARITH_RULE `(((norm (p:real^3)) * ((u:real^3) dot (v:real^3)))/ &2) * (&2) = ((norm (p:real^3)) * ((u:real^3) dot (v:real^3)))`]);;
e (STRIP_TAC);;
e (SUBGOAL_THEN `(((norm (p:real^3)) * (((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - dist (u,v) pow 2)) / &2) < (norm p) * (&2) ` ASSUME_TAC);;
e (ASM_ARITH_TAC);;
e (MP_TAC (ISPECL [`((((norm (p:real^3)) * (((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - dist (u,v) pow 2)) / &2))`;`(norm (p:real^3)) * (&2)`;`&2`]REAL_LT_RMUL));;
e (REWRITE_TAC [ARITH_RULE `&0 < &2`]);;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th]) `(norm (p:real^3) * ((norm (u:real^3) pow 2 + norm (v:real^3) pow 2) - dist (u,v) pow 2)) / &2 < norm p * &2`);;
e (STRIP_TAC);;
e (REWRITE_TAC [ARITH_RULE `((((norm (p:real^3)) * (((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - dist (u,v) pow 2)) / &2))*(&2) = ((norm (p:real^3)) * (((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - dist (u,v) pow 2))`]);;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2)`;`(dist (u:real^3,v:real^3) pow 2)`]real_sub));;
e (STRIP_TAC);;
e (SUBGOAL_THEN `&4 <= ((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - (dist (u,v) pow 2)` ASSUME_TAC);;
e (ASM_ARITH_TAC);;
e (SUBGOAL_THEN `&0 <= (norm (p:real^3))` ASSUME_TAC);;
e (REWRITE_TAC[NORM_POS_LE]);;
e (MP_TAC (ISPECL [`(norm (p:real^3))`;`&4`;`(((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - dist (u,v) pow 2)`]REAL_LE_LMUL));;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th]) `&4 <= (norm (u:real^3) pow 2 + norm (v:real^3) pow 2) - dist (u,v) pow 2`);;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th]) `&0 <= norm (p:real^3)`);;
e (STRIP_TAC);;
e (SUBGOAL_THEN `(norm (p:real^3)) * (&4) < ((norm p) * (&2))*(&2)` ASSUME_TAC THEN ASM_ARITH_TAC);;

let th5 = top_thm();;
(*----------------------------------------------------------------*)
g `!(V:real^3 -> bool)(P:real^3->bool) (g:real^3->real) p:real^3 r r':real. (&2 <= r) /\ (r <= r') /\  (V SUBSET (:real^3) DIFF ball (vec 0,&2)) /\ (FINITE V) /\ packing V /\ (weakly_saturated V r r') /\
 P = INTERS {half_spaces u (g u)| u IN V} /\ polyhedron P /\ (p IN P)  ==>(!u:real^3. u IN V ==> p IN half_spaces u (g u))`;;
e (REPEAT GEN_TAC );;
e (STRIP_TAC);;
THEN REWRITE_TAC [INTERS;IN_ELIM_THM] THEN STRIP_TAC);;
e (POP_ASSUM MP_TAC);;
e (ASM_REWRITE_TAC[IN_ELIM_THM]);;
e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `INTERS {half_spaces u (g u) | u IN V} SUBSET half_spaces (u:real^3) ((g:real^3->real) u)` ASSUME_TAC);;
e (REWRITE_TAC [SUBSET;IN_INTERS]);;
e (GEN_TAC);;
e (DISCH_THEN (LABEL_TAC "F1"));;
e (REMOVE_THEN "F1" (MP_TAC o SPEC `half_spaces (u:real^3) ((g:real^3 -> real) u)`));;
e (STRIP_TAC);;
e (SUBGOAL_THEN `half_spaces (u:real^3) ((g:real^3 -> real) u) IN {half_spaces u (g u) | u IN (V:real^3->bool)}` ASSUME_TAC);;
e (REWRITE_TAC [half_spaces]);;
e (REWRITE_TAC [IN_ELIM_THM]);;
e (EXISTS_TAC `u:real^3`);;
e (ASM_REWRITE_TAC[]);;
e (POP_ASSUM MP_TAC);;
e (ASM_REWRITE_TAC[]);;
e (POP_ASSUM MP_TAC);;
e (REWRITE_TAC [SUBSET]);;
e (DISCH_THEN (MP_TAC o SPEC `p:real^3`));;
e (ASM_REWRITE_TAC[]);;

let th6 = top_thm();;

g `!(V:real^3 -> bool)(P:real^3->bool) (g:real^3->real) u:real^3 r r':real. (&2 <= r) /\ (r <= r') /\  (V SUBSET (:real^3) DIFF ball (vec 0,&2)) /\ (FINITE V) /\ packing V /\ (weakly_saturated V r r') /\
 P = INTERS {half_spaces u (g u)| u IN V} /\ polyhedron P /\ u IN V   ==> (!p:real^3. p IN P ==> (u dot p) <= (g u))`;;
e (REPEAT GEN_TAC THEN STRIP_TAC);;
e (GEN_TAC);;
e (STRIP_TAC);;
e (SUBGOAL_THEN `(!u:real^3. u IN (V:real^3->bool) ==> p IN half_spaces u ((g:real^3->real) u))` ASSUME_TAC);;
e (ASM_MESON_TAC[th6]);;
e (POP_ASSUM MP_TAC);;
e (REWRITE_TAC [half_spaces;IN_ELIM_THM]);;
e (DISCH_THEN (MP_TAC o SPEC `u:real^3`));;
e (ASM_REWRITE_TAC[]);;

let th7 = top_thm();;

g `!(V:real^3 -> bool)(P:real^3->bool) (g:real^3->real) r r':real. (&2 <= r) /\ (r <= r') /\  (V SUBSET (:real^3) DIFF ball (vec 0,&2)) /\ (FINITE V) /\ packing V /\ (weakly_saturated V r r') /\
 P = INTERS {half_spaces u (g u)| u IN V} /\ polyhedron P ==> (!p:real^3 u:real^3. p IN P /\ u IN V ==> (u dot p) <= ((g:real^3->real) u))`;;
e (REPEAT GEN_TAC);;
e (STRIP_TAC);;
e (REPEAT GEN_TAC);;
e (STRIP_TAC);;
e (SUBGOAL_THEN `!p:real^3. p IN (P:real^3->bool) ==> (u dot p) <= ((g:real^3->real)(u:real^3))` ASSUME_TAC);;
e (ASM_MESON_TAC [th7]);;
e (POP_ASSUM (MP_TAC o SPEC `p:real^3`));;
e (ASM_REWRITE_TAC[]);;

let th71 = top_thm();;

g `!(g:real^3->real)(r':real)(u:real^3).(&2 <= r) /\ (r <= r') /\ (&0 <= g u) ==> &0 <= ((g u) * r')/ &2`;;

e (REPEAT GEN_TAC THEN STRIP_TAC);;
e (SUBGOAL_THEN `&2 <= (r':real)` ASSUME_TAC);;
e (ASM_ARITH_TAC);;
e (SUBGOAL_THEN `&0 <= (r':real)` ASSUME_TAC);;
e (POP_ASSUM MP_TAC);;
e (MP_TAC (ARITH_RULE `&0 <= &2`));;
e (MESON_TAC[REAL_LE_TRANS]);;
e (MP_TAC (ISPECL [`(g:real^3->real) (u:real^3)`;`r':real`]REAL_LE_MUL));;
e (ASM_REWRITE_TAC[]);;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`(((g:real^3->real) (u:real^3)) * (r':real))`;`(&2)`]REAL_LE_DIV));;
e (ASM_REWRITE_TAC[ARITH_RULE `&0 <= &2`]);;

let th8 = top_thm();;

g `!(V:real^3 -> bool)(g:real^3->real) r':real.(FINITE V) /\ ~(V = {}) ==> FINITE {(g(u:real^3)*r')/(&2)|u IN V} /\ ~({(g(u:real^3)*r')/(&2)|u IN V} = {})`;;
e (REPEAT GEN_TAC);;
e (SUBGOAL_THEN `IMAGE (\u. ((g:real^3->real)(u:real^3) * (r':real)) / &2) (V:real^3->bool) = {(g u * r') / &2 | u IN V}` ASSUME_TAC);;
e (REWRITE_TAC [IMAGE;EXTENSION]);;
e (GEN_TAC);;
e (EQ_TAC);;
e (REWRITE_TAC [IN_ELIM_THM]);;
e (REWRITE_TAC [IN_ELIM_THM]);;
e (REPEAT STRIP_TAC);;
e (MP_TAC (ISPECL [`\u. (((g:real^3->real)(u:real^3)) * (r':real)) / (&2)`;`V:real^3->bool`]FINITE_IMAGE));;
e (ASM_REWRITE_TAC[]);;
e (MP_TAC (ISPECL [`\u. (((g:real^3->real)(u:real^3)) * (r':real)) / (&2)`;`V:real^3->bool`]IMAGE_EQ_EMPTY));;
e (ASM_REWRITE_TAC[]);;

let FININTE_GFUN = top_thm();;

(*----------------------------------------------------------------------------*)

g `!(V:real^3 -> bool)(P:real^3->bool) (g:real^3->real) r r':real u:real^3. (&2 <= r) /\ (r <= r') /\  (V SUBSET (:real^3) DIFF ball (vec 0,&2)) /\ (FINITE V) /\ packing V/\ ~(V = {}) /\ (weakly_saturated V r r') /\
 P = INTERS {half_spaces u (g u)| u IN V} /\ polyhedron P /\ u IN V ==>
(bounded P)`;;
e (REPEAT GEN_TAC);;
e (STRIP_TAC);;
e (SUBGOAL_THEN `!p:real^3 u:real^3. p IN P /\ u IN V ==> (u dot p) <= ((g:real^3->real) u)` ASSUME_TAC);;
e (ASM_MESON_TAC[th71]);;
e (REPEAT (POP_ASSUM MP_TAC));;
e (REWRITE_TAC [weakly_saturated;polyhedron;half_spaces] THEN STRIP_TAC);;
e (DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC);;
e (STRIP_TAC);;
e (DISCH_THEN (LABEL_TAC "F1"));;
e (DISCH_TAC);;
e (DISCH_THEN (LABEL_TAC "F2"));;
e (DISCH_TAC);;
e (DISCH_THEN (LABEL_TAC "F3"));; 
(*
e (ASM_CASES_TAC `(V:real^3->bool) = {}`);;
e (SUBGOAL_THEN `IMAGE (\(u:real^3). {x:real^3 | u dot x <= g u}) (V:real^3->bool) = {{x | u dot x <= g u} | u IN V}` ASSUME_TAC);;
e (REWRITE_TAC[IMAGE;EXTENSION]);;
e (GEN_TAC);;
e (EQ_TAC);;
e (REWRITE_TAC [IN_ELIM_THM]);;
e (STRIP_TAC);;
e (EXISTS_TAC `x':real^3`);;
e (ASM_REWRITE_TAC[]);;
e (POP_ASSUM (LABEL_TAC "B1"));;
e (REWRITE_TAC [EXTENSION]);;
e (STRIP_TAC);;
e (REWRITE_TAC[IN_ELIM_THM]);;
e (REMOVE_THEN "B1" (MP_TAC o SPEC `x'':real^3`));;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC [IN_ELIM_THM]);;
e (STRIP_TAC);;
e (EXISTS_TAC `u':real^3`);;
e (ASM_REWRITE_TAC[]);;
e (STRIP_TAC);;
e (REWRITE_TAC [IN_ELIM_THM]);;
e (MP_TAC (ISPECL [`(\(u:real^3). {x:real^3 | u dot x <= g u})`;`V:real^3->bool`]IMAGE_EQ_EMPTY));;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th]) `(V:real^3->bool) = {}`);;
e (POP_ASSUM MP_TAC);;
e (ASM_REWRITE_TAC[]);;
e (DISCH_TAC);;
e (POP_ASSUM (fun th -> REWRITE_TAC [GSYM th]));;
e (DISCH_TAC);;
e ( POP_ASSUM (fun th -> REWRITE_TAC [th]));;
e (REWRITE_TAC [INTERS_0]);;
*)

e (MP_TAC (ISPECL [`V:real^3->bool`;`(g:real^3->real)`;`r':real`]FININTE_GFUN));;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th]) `~ ((V:real^3->bool) = {})`);;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th]) `FINITE (V:real^3->bool) `);;
e (STRIP_TAC);;
e (ASM_CASES_TAC `bounded (P:real^3->bool)`);;
e (ASM_REWRITE_TAC[]);;
e (POP_ASSUM MP_TAC);;
e (REWRITE_TAC [bounded]);;
e (REWRITE_TAC [NOT_EXISTS_THM;NOT_FORALL_THM]);;
e (REWRITE_TAC [NOT_IMP;REAL_NOT_LE]);;
e (DISCH_THEN (LABEL_TAC "F4"));;
e (REWRITE_TAC [GSYM bounded]);;
e (SUBGOAL_THEN `!u:real^3 . u IN (V:real^3->bool) ==> (?p:real^3. p IN (P:real^3->bool) /\ (((g:real^3->real)(u:real^3)) * (r':real)) / (&2) < norm p)` ASSUME_TAC);;
e (REPEAT STRIP_TAC);;
e (REMOVE_THEN "F4" (MP_TAC o SPEC `sup {((g:real^3->real)(u:real^3) * (r':real)) / &2 | u IN (V:real^3->bool)}`));;
e (DISCH_THEN (X_CHOOSE_TAC `p:real^3`));;
e (POP_ASSUM MP_TAC THEN STRIP_TAC);;
e (EXISTS_TAC `p:real^3`);;
e (ASM_REWRITE_TAC[]);;
e (MP_TAC (ISPECL [`{((g:real^3->real)(u:real^3) * (r':real)) / &2 | u IN (V:real^3->bool)}`]SUP_FINITE));;
e (ASM_REWRITE_TAC[]);;
e (STRIP_TAC);;
e (POP_ASSUM (MP_TAC o SPEC `((g:real^3->real)(u':real^3) * (r':real)) / &2 `));;
e (REWRITE_TAC [IN_ELIM_THM]);;
e (SUBGOAL_THEN `(?u:real^3. u IN (V:real^3->bool) /\ ((g:real^3->real)(u':real^3) * (r':real)) / &2 = (g u * r') / &2)` ASSUME_TAC);;
e (EXISTS_TAC `u':real^3`);;
e (ASM_REWRITE_TAC[]);;
e (POP_ASSUM (fun th ->REWRITE_TAC [th]));;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`((g:real^3->real)(u':real^3) * (r':real)) / &2`;`sup {((g:real^3->real)(u:real^3) * (r':real)) / &2 | u IN (V:real^3->bool)}`;`norm (p:real^3)`]REAL_LET_TRANS));;
e (POP_ASSUM (fun th ->REWRITE_TAC [th]));;
e (POP_ASSUM MP_TAC);;
e (POP_ASSUM (fun th ->REWRITE_TAC [th]));;
e (POP_ASSUM (LABEL_TAC "F5"));;
e (REMOVE_THEN "F4" (MP_TAC o SPEC `sup {((g:real^3->real)(u:real^3) * (r':real)) / &2 | u IN (V:real^3->bool)}`));;
e (DISCH_THEN (X_CHOOSE_TAC `p:real^3`));;
e (POP_ASSUM MP_TAC THEN STRIP_TAC);;
e (REMOVE_THEN "F5" (MP_TAC o SPEC `u:real^3`));;
e (FIND_ASSUM (fun th ->REWRITE_TAC [th]) `(u:real^3) IN (V:real^3 -> bool)`);;
e (STRIP_TAC);;
e (USE_THEN "F3" (MP_TAC o SPECL [`p:real^3`;`u:real^3`]));;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th])`(p:real^3) IN (P:real^3->bool)`);;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th])`(u:real^3) IN (V:real^3->bool)`);;
e (DISCH_TAC);;
e (MP_TAC (ISPECL [`{((g:real^3->real)(u:real^3) * (r':real)) / &2 | u IN (V:real^3->bool)}`]SUP_FINITE));;
e (ASM_REWRITE_TAC[]);;
e (STRIP_TAC);;
e (POP_ASSUM (MP_TAC o SPEC `((g:real^3->real)(u:real^3) * (r':real)) / &2`));;
e (REWRITE_TAC [IN_ELIM_THM]);;
e (SUBGOAL_THEN `(?(u':real^3). u' IN (V:real^3->bool) /\ ((g:real^3->real)(u:real^3) * (r':real)) / &2 = (g u' * r') / &2)` ASSUME_TAC);;
e (EXISTS_TAC `u:real^3`);;
e (ASM_REWRITE_TAC[]);;
e (POP_ASSUM (fun th -> REWRITE_TAC[th]));;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`((g:real^3->real)(u:real^3) * (r':real)) / &2`;`sup {((g:real^3->real)(u:real^3) * (r':real)) / &2 | u IN (V:real^3->bool)}`;`norm (p:real^3)`]REAL_LET_TRANS));;
e (ASM_REWRITE_TAC[]);;
e (STRIP_TAC);;
e (ASM_CASES_TAC `(p:real^3) = vec 0`);;
e (SUBGOAL_THEN `((r':real)/(norm (p:real^3)))% p = vec 0` ASSUME_TAC);;
e (POP_ASSUM (fun th -> REWRITE_TAC [th]));;
e (MESON_TAC [VECTOR_MUL_RZERO]);;
e (SUBGOAL_THEN `norm (((r':real)/(norm (p:real^3)))% p) = &0` ASSUME_TAC );;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC [NORM_EQ_0]);;
e (MP_TAC (ISPECL [`p:real^3`]NORM_EQ_0));;
e (ASM_REWRITE_TAC[]);;
e (STRIP_TAC);;
e (UNDISCH_TAC `((g:real^3->real)(u:real^3) * (r':real)) / (&2) < norm (p:real^3)`);;
e (ASM_REWRITE_TAC[]);;
e (STRIP_TAC);;
e (USE_THEN "F3" (MP_TAC o SPECL [`(vec 0):real^3`;`u:real^3`]));;
e (UNDISCH_TAC `(p:real^3) IN (P:real^3->bool)`);;
e (UNDISCH_TAC `p:real^3 = vec 0`);;
e (DISCH_TAC THEN POP_ASSUM (fun th ->REWRITE_TAC [th]));;
e (DISCH_TAC THEN POP_ASSUM (fun th ->REWRITE_TAC [th]));;
e (FIND_ASSUM (fun th -> REWRITE_TAC [th]) `(u:real^3) IN (V:real^3->bool)`);;
e (UNDISCH_TAC `(P:real^3->bool) = INTERS {{x:real^3 | u dot x <= (g:real^3->real)(u)} | (u:real^3) IN (V:real^3->bool)}`);;
e (DISCH_TAC);;
e (POP_ASSUM (fun th -> REWRITE_TAC [GSYM th]));;
e (REWRITE_TAC [DOT_RZERO]);;
e (SUBGOAL_THEN `&2 <= r':real` ASSUME_TAC);;
e (ASM_ARITH_TAC);;
e (MP_TAC (ISPECL [`&0`;`&2`;`r':real`]REAL_LTE_TRANS));;
e (ASM_REWRITE_TAC [ARITH_RULE `&0 < &2`]);;
e (STRIP_TAC);;
e (MP_TAC (ARITH_RULE `(((g:real^3->real))(u:real^3) * (r':real)) / &2 < &0 <=> g u * r' < &0`));;
e (POP_ASSUM MP_TAC);;
e (POP_ASSUM MP_TAC);;
e (POP_ASSUM (fun th ->REWRITE_TAC [th]));;
e (REPEAT STRIP_TAC);;
e (MP_TAC (ISPECL [`((g:real^3->real))(u:real^3)`;`&0`;`r':real`]REAL_LT_RDIV_EQ));;
e (POP_ASSUM MP_TAC);;
e (POP_ASSUM (fun th ->REWRITE_TAC [th]));;
e (POP_ASSUM (fun th ->REWRITE_TAC [th]));;
e (REWRITE_TAC [ARITH_RULE `&0 / (r':real) = &0`]);;
e (ARITH_TAC);;
e (SUBGOAL_THEN `~(u:real^3 = vec 0)` ASSUME_TAC);;
e (ASM_MESON_TAC[th31]);;

e (SUBGOAL_THEN `!v:real^3.(v = ((r':real)/(norm p))% (p:real^3)) ==> (r' = norm v)` ASSUME_TAC);;
e (GEN_TAC);;
e (STRIP_TAC);;
e (SUBGOAL_THEN `&2 <= r':real` ASSUME_TAC);;
e (ASM_ARITH_TAC);;
e (MP_TAC (ISPECL [`&0`;`&2`;`r':real`]REAL_LTE_TRANS));;
e (ASM_REWRITE_TAC [ARITH_RULE `&0 < &2`]);;
e (STRIP_TAC);;
e (FIND_ASSUM (fun th -> REWRITE_TAC [GSYM th]) `(v:real^3) = (r':real) / norm p % (p:real^3)`);;
e (ASM_MESON_TAC [norm_equa]);;
e (POP_ASSUM (LABEL_TAC "F7"));;
e (USE_THEN "F1" (MP_TAC o SPEC `((r':real)/(norm (p:real^3)))% p`));;
e (REWRITE_TAC [dist;NORM_SUB;VECTOR_SUB_RZERO]);;
e (ABBREV_TAC `v = (r':real) / norm p % (p:real^3)`);;
e (ASM_REWRITE_TAC[]);;
e (REMOVE_THEN "F7" (MP_TAC o SPEC `v:real^3`));;
e (REWRITE_TAC[]);;
e (STRIP_TAC);;
e (SUBGOAL_THEN `&2 <= r':real` ASSUME_TAC);;
e (ASM_ARITH_TAC);;
e (POP_ASSUM MP_TAC);;
e (ASM_REWRITE_TAC[]);;
e (STRIP_TAC);;
e (ASM_REWRITE_TAC[ARITH_RULE `norm (v:real^3) <= norm v`]);;
e (STRIP_TAC);;
e (POP_ASSUM MP_TAC);;
e (REWRITE_TAC [GSYM dist]);;
e (STRIP_TAC);;
e (REMOVE_THEN "F3" (MP_TAC o SPECL [`p:real^3`;`u':real^3`]));;
e (ASM_REWRITE_TAC[]);;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`{((g:real^3->real)(u:real^3) * (r':real)) / &2 | u IN (V:real^3->bool)}`]SUP_FINITE));;
e (ASM_REWRITE_TAC[]);;
e (UNDISCH_TAC `(r':real) = norm (v:real^3)`);;
e (STRIP_TAC);;
e (POP_ASSUM (fun th -> REWRITE_TAC[GSYM th]));;
e (STRIP_TAC);;
e (POP_ASSUM (MP_TAC o SPEC `((g:real^3->real)(u':real^3) * (r':real)) / &2`));;
e (REWRITE_TAC [IN_ELIM_THM]);;
e (SUBGOAL_THEN `(?(u:real^3). u IN (V:real^3->bool) /\ ((g:real^3->real)(u':real^3) * (r':real)) / &2 = (g u * r') / &2)` ASSUME_TAC);;
e (EXISTS_TAC `u':real^3`);;
e (ASM_REWRITE_TAC[]);;
e (POP_ASSUM (fun th -> REWRITE_TAC[th]));;
e (STRIP_TAC);;
e (MP_TAC (ISPECL [`((g:real^3->real)(u':real^3) * (r':real)) / &2`;`sup {((g:real^3->real)(u:real^3) * (r':real)) / &2 | u IN (V:real^3->bool)}`;`norm (p:real^3)`]REAL_LET_TRANS));;
e (ASM_REWRITE_TAC[]);;
e (STRIP_TAC);;
e (UNDISCH_TAC `(r':real) / norm (p:real^3) % p = v:real^3`);;
e (REWRITE_TAC [EQ_SYM_EQ]);;
e (STRIP_TAC);;
e (SUBGOAL_THEN `norm (p:real^3) < norm p` ASSUME_TAC);;
e (ASM_MESON_TAC[th5]);;
e (UNDISCH_TAC `(P:real^3->bool) = INTERS {{x:real^3 | u dot x <= (g:real^3->real)(u:real^3)} | u IN (V:real^3->bool)}`);;
e (STRIP_TAC);;
e (POP_ASSUM (fun th -> REWRITE_TAC [GSYM th]));;
e (ASM_ARITH_TAC);;

let TARJJUW = top_thm();;

 end;;
