(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(*                                                                            *)
(* A bound for the number pi *)
(* Chapter: Tame                                                           *)
(* Author:  Vu Quang Thanh                                                  *)
(* Date: 2010-02-13                                                          *)
(* ========================================================================== *)



(* ========================================================================= *)
(* Quick derivation of a pi approximation (could do this more nicely).       *)
(* ========================================================================= *)


module Pishort  = struct


let TAYLOR_SIN = prove
 (`!n x. abs(sin x - 
             sum(0..n) (\i. (if i MOD 4 = 0 then &0
                             else if i MOD 4 = 1 then &1 
                             else if i MOD 4 = 2 then &0 
                             else -- &1) * x pow i / &(FACT i)))
         <= abs x pow (n + 1) / &(FACT (n + 1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. if n MOD 4 = 0 then sin
                      else if n MOD 4 = 1 then cos
                      else if n MOD 4 = 2 then \x. --(sin x)
                      else \x. --(cos x)`;
                 `n:num`;
                 `real_interval[--(abs x),abs x]`; `&1`]
        REAL_TAYLOR) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL 
     [REWRITE_TAC[is_realinterval; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      ALL_TAC; 
      MESON_TAC[REAL_ABS_NEG; SIN_BOUND; COS_BOUND]] THEN
    ONCE_REWRITE_TAC[GSYM(MATCH_MP MOD_ADD_MOD (ARITH_RULE `~(4 = 0)`))] THEN
    REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC (ARITH_RULE
     `i MOD 4 = 0 \/ i MOD 4 = 1 \/ i MOD 4 = 2 \/ i MOD 4 = 3`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
    REWRITE_TAC[] THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[COND_RATOR] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0:real`; `x:real`]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO; COS_0; SIN_0; REAL_NEG_0; REAL_MUL_LID]]);;

let PI_LOWERBOUND_WEAK = prove
 (`&627 / &256 <= pi`,
  SUBGOAL_THEN
   `!x. &0 < x /\ x < &627 / &256 ==> &0 < sin x` (MP_TAC o SPEC `pi`)
  THENL [ALL_TAC; SIMP_TAC[SIN_PI; REAL_LT_REFL; PI_POS; REAL_NOT_LT]] THEN
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`2`; `x:real`] TAYLOR_SIN) THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; SUM_CLAUSES_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN MATCH_MP_TAC(REAL_ARITH
   `e + d < a ==> abs(s - a) <= d ==> e < s`) THEN
  REWRITE_TAC[REAL_ARITH
   `&0 + x pow 3 / &6 < x pow 1 / &1 <=> x * x pow 2 < x * &6`] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `(&627 / &256) pow 2` THEN
  ASM_SIMP_TAC[REAL_POW_LT2; ARITH_EQ; REAL_LT_IMP_LE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let COS_TREBLE_COS = prove
 (`!x. cos(&3 * x) = &4 * cos(x) pow 3 - &3 * cos x`,
  GEN_TAC THEN REWRITE_TAC[COS_ADD; REAL_ARITH `&3 * x = &2 * x + x`] THEN
  REWRITE_TAC[SIN_DOUBLE; COS_DOUBLE_COS] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

let COS_PI6 = prove
 (`cos(pi / &6) = sqrt(&3) / &2`,
  MP_TAC(ISPEC `pi / &6` COS_TREBLE_COS) THEN
  REWRITE_TAC[REAL_ARITH `&3 * x / &6 = x / &2`; COS_PI2] THEN
  REWRITE_TAC[REAL_RING `&0 = &4 * c pow 3 - &3 * c <=>
                         c = &0 \/ (&2 * c) pow 2 = &3`] THEN
  SUBGOAL_THEN `&0 < cos(pi / &6)` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_POS_PI THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `sqrt`) THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LE_MUL; REAL_LT_IMP_LE; REAL_POS] THEN
    REAL_ARITH_TAC]);;

let SIN_PI6 = prove
 (`sin(pi / &6) = &1 / &2`,
  MP_TAC(SPEC `pi / &6` SIN_CIRCLE) THEN REWRITE_TAC[COS_PI6] THEN
  SIMP_TAC[REAL_POW_DIV; SQRT_POW_2; REAL_POS] THEN MATCH_MP_TAC(REAL_FIELD
   `~(s + &1 / &2 = &0) ==> s pow 2 + &3 / &2 pow 2 = &1 ==> s = &1 / &2`) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x + &1 / &2 = &0)`) THEN
  MATCH_MP_TAC SIN_POS_PI THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let SIN_PI6_STRADDLE = prove
 (`!a b. &0 <= a /\ a <= b /\ b <= &7 /\
         sin(a / &6) <= &1 / &2 /\ &1 / &2 <= sin(b / &6)
         ==> a <= pi /\ pi <= b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`pi / &6`; `b / &6`] SIN_MONO_LE_EQ) THEN
  MP_TAC(SPECL [`a / &6`; `pi / &6`] SIN_MONO_LE_EQ) THEN
  ASM_REWRITE_TAC[SIN_PI6] THEN
  MP_TAC PI_LOWERBOUND_WEAK THEN ASM_REAL_ARITH_TAC);;

let PI_APPROX = prove
 (`abs(pi - &13493037705 / &4294967296) <= inv(&2 pow 32)`,
  REWRITE_TAC[REAL_ARITH `abs(x - a) <= e <=> a - e <= x /\ x <= a + e`] THEN
  MATCH_MP_TAC SIN_PI6_STRADDLE THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand o lhand) (SPEC `12` TAYLOR_SIN) o
        lhand o snd);
    W(MP_TAC o PART_MATCH (lhand o rand o lhand) (SPEC `12` TAYLOR_SIN) o
        rand o snd)] THEN
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `12`] THEN
  REPLICATE_TAC 13
   (ONCE_REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN REWRITE_TAC[LE_0]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let bound_for_pi = prove (`!n. &n * (&852 / &1000) <= &2 * pi ==> n <= 7`, REPEAT STRIP_TAC THEN ASSUME_TAC (PI_APPROX) THEN SUBGOAL_THEN `abs (pi - &13493037705 / &4294967296) < &1 / &128` ASSUME_TAC THENL[ASM_REAL_ARITH_TAC; MP_TAC (SPECL [`pi`; `&13493037705 / &4294967296`; `&1 / &128`] REAL_ABS_BOUND) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN SUBGOAL_THEN `&n < &8` ASSUME_TAC THENL[ASM_REAL_ARITH_TAC ; MP_TAC (SPECL [`n:num`; `8`] REAL_OF_NUM_LT) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]]);;



end;;
