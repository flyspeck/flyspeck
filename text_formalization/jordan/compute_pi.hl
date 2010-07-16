

(* split off from misc_defs_and_lemmas.ml *)


(* ------------------------------------------------------------------ *)
(* COMPUTING PI *)
(* ------------------------------------------------------------------ *)

unambiguous_interface();;
prioritize_real();;

(* ------------------------------------------------------------------ *)
(* general series approximations *)
(* ------------------------------------------------------------------ *)

let SER_APPROX1 = prove_by_refinement(
  `!s f g.  (f sums s) /\ (summable g) ==>
    (!k. ((!n. (||. (f (n+k)) <=. (g (n+k)))) ==>
    ( (s - (sum(0,k) f)) <=. (suminf (\n. (g (n +| k)))))))`,
  (* {{{ proof *)
  [
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  GEN_TAC;
  DISCH_TAC;
  IMP_RES_THEN ASSUME_TAC SUM_SUMMABLE;
  IMP_RES_THEN (fun th -> (ASSUME_TAC (SPEC `k:num` th))) SER_OFFSET;
  IMP_RES_THEN ASSUME_TAC SUM_UNIQ;
  SUBGOAL_THEN `(\n. (f (n+ k))) sums (s - (sum(0,k) f))` ASSUME_TAC;
  ASM_MESON_TAC[];
  SUBGOAL_THEN `summable (\n. (f (n+k))) /\ (suminf (\n. (f (n+k))) <=. (suminf (\n. (g (n+k)))))` ASSUME_TAC;
  MATCH_MP_TAC SER_LE2;
  BETA_TAC;
  ASM_REWRITE_TAC[];
  IMP_RES_THEN ASSUME_TAC SER_OFFSET;
  FIRST_X_ASSUM (fun th -> ACCEPT_TAC (MATCH_MP SUM_SUMMABLE (((SPEC `k:num`) th))));
  ASM_MESON_TAC[SUM_UNIQ]
  ]);;
  (* }}} *)

let SER_APPROX = prove_by_refinement(
  `!s f g.  (f sums s) /\ (!n. (||. (f n) <=. (g n))) /\
       (summable g) ==>
    (!k. (abs (s - (sum(0,k) f)) <=. (suminf (\n. (g (n +| k))))))`,
  (* {{{ proof *)
  [
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  GEN_TAC;
  REWRITE_TAC[REAL_ABS_BOUNDS];
  CONJ_TAC;
  SUBGOAL_THEN `(!k. ((!n. (||. ((\p. (--. (f p))) (n+k))) <=. (g (n+k)))) ==> ((--.s) - (sum(0,k) (\p. (--. (f p)))) <=. (suminf (\n. (g (n +k))))))` ASSUME_TAC;
  MATCH_MP_TAC SER_APPROX1;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC SER_NEG ;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC (REAL_ARITH (`(--. s -. (--. u) <=. x) ==> (--. x <=. (s -. u))`));
  ONCE_REWRITE_TAC[GSYM SUM_NEG];
  FIRST_X_ASSUM (fun th -> (MATCH_MP_TAC th));
  BETA_TAC;
  ASM_REWRITE_TAC[REAL_ABS_NEG];
  H_VAL2 CONJ (HYP "0") (HYP "2");
  IMP_RES_THEN MATCH_MP_TAC SER_APPROX1 ;
  GEN_TAC;
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

(* ------------------------------------------------------------------ *)
(* now for pi calculation stuff *)
(* ------------------------------------------------------------------ *)


let local_def = local_definition "trig";;


let PI_EST = prove_by_refinement(
               `!n. (1 <=| n) ==> (abs(&4 / &(8 * n + 1) -
            &2 / &(8 * n + 4) -
            &1 / &(8 * n + 5) -
            &1 / &(8 * n + 6)) <= &.622/(&.819))`,
  (* {{{ proof *)
   [
   GEN_TAC THEN DISCH_ALL_TAC;
   REWRITE_TAC[real_div];
   MATCH_MP_TAC (REWRITE_RULE[real_div] (REWRITE_RULE[REAL_RAT_REDUCE_CONV `(&.4/(&.9) +(&.2/(&.12)) + (&.1/(&.13))+ (&.1/(&.14)))`] (REAL_ARITH `(abs((&.4)*.u)<=. (&.4)/(&.9)) /\ (abs((&.2)*.v)<=. (&.2)/(&.12)) /\ (abs((&.1)*w) <=. (&.1)/(&.13)) /\ (abs((&.1)*x) <=. (&.1)/(&.14)) ==> (abs((&.4)*u -(&.2)*v - (&.1)*w - (&.1)*x) <= (&.4/(&.9) +(&.2/(&.12)) + (&.1/(&.13))+ (&.1/(&.14))))`)));
   IMP_RES_THEN ASSUME_TAC (ARITH_RULE `1 <=| n ==> (0 < n)`);
   FIRST_X_ASSUM (fun th -> ASSUME_TAC (REWRITE_RULE[GSYM REAL_OF_NUM_LT] th));
   ASSUME_TAC (prove(`(a<=.b) ==> (&.n*a <=. (&.n)*b)`,MESON_TAC[REAL_PROP_LE_LMUL;REAL_POS]));
   REWRITE_TAC[REAL_ABS_MUL;REAL_ABS_INV;prove(`||.(&.n) = (&.n)`,MESON_TAC[REAL_POS;REAL_ABS_REFL])];
   REPEAT CONJ_TAC THEN (POP_ASSUM (fun th -> MATCH_MP_TAC th)) THEN (MATCH_MP_TAC (prove(`((&.0 <. (&.n)) /\ (&.n <=. a)) ==> (inv(a)<=. (inv(&.n)))`,MESON_TAC[REAL_ABS_REFL;REAL_ABS_INV;REAL_LE_INV2]))) THEN
   REWRITE_TAC[REAL_LT;REAL_LE] THEN (H_UNDISCH_TAC (HYP"0")) THEN
   ARITH_TAC]);;
  (* }}} *)

let pi_fun = local_def `pi_fun n = inv (&.16 **. n) *.
          (&.4 / &.(8 *| n +| 1) -.
           &.2 / &.(8 *| n +| 4) -.
           &.1 / &.(8 *| n +| 5) -.
           &.1 / &.(8 *| n +| 6))`;;

let pi_bound_fun = local_def `pi_bound_fun n = if (n=0) then (&.8) else
    (((&.15)/(&.16))*(inv(&.16 **. n))) `;;

let PI_EST2 = prove_by_refinement(
    `!k. abs(pi_fun k) <=. (pi_bound_fun k)`,
  (* {{{ proof *)
   [
   GEN_TAC;
   REWRITE_TAC[pi_fun;pi_bound_fun];
   COND_CASES_TAC;
   ASM_REWRITE_TAC[];
   CONV_TAC (NUM_REDUCE_CONV);
   (CONV_TAC (REAL_RAT_REDUCE_CONV));
   CONV_TAC (RAND_CONV (REWR_CONV (REAL_ARITH `a*b = b*.a`)));
   REWRITE_TAC[REAL_ABS_MUL;REAL_ABS_INV;REAL_ABS_POW;prove(`||.(&.n) = (&.n)`,MESON_TAC[REAL_POS;REAL_ABS_REFL])];
   MATCH_MP_TAC (prove(`!x y z. (&.0 <. z /\ (y <=. x) ==> (z*y <=. (z*x)))`,MESON_TAC[REAL_LE_LMUL_EQ]));
   ASSUME_TAC (REWRITE_RULE[] (REAL_RAT_REDUCE_CONV `(&.622)/(&.819) <=. (&.15)/(&.16)`));
   IMP_RES_THEN ASSUME_TAC (ARITH_RULE `~(k=0) ==> (1<=| k)`);
   IMP_RES_THEN ASSUME_TAC (PI_EST);
   CONJ_TAC;
   SIMP_TAC[REAL_POW_LT;REAL_LT_INV;ARITH_RULE `&.0 < (&.16)`];
   ASM_MESON_TAC[REAL_LE_TRANS];
   ]);;
  (* }}} *)

let GP16 = prove_by_refinement(
  `!k. (\n. inv (&16 pow k) * inv (&16 pow n)) sums
         inv (&16 pow k) * &16 / &15`,
  (* {{{ proof *)
  [
  GEN_TAC;
  ASSUME_TAC (REWRITE_RULE[] (REAL_RAT_REDUCE_CONV `abs (&.1 / (&. 16)) <. (&.1)`));
  IMP_RES_THEN (fun th -> ASSUME_TAC (CONV_RULE REAL_RAT_REDUCE_CONV th)) GP;
  MATCH_MP_TAC SER_CMUL;
  ASM_REWRITE_TAC[GSYM REAL_POW_INV;REAL_INV_1OVER];
  ]);;
  (* }}} *)

let GP16a = prove_by_refinement(
   `!k. (0<|k) ==> (\n. (pi_bound_fun (n+k))) sums (inv(&.16 **. k))`,
  (* {{{ proof *)
   [
   GEN_TAC;
   DISCH_TAC;
   SUBGOAL_THEN `(\n. pi_bound_fun (n+k)) = (\n. ((&.15/(&.16))* (inv(&.16)**. k) *. inv(&.16 **. n)))` (fun th-> REWRITE_TAC[th]);
   MATCH_MP_TAC EQ_EXT;
   X_GEN_TAC `n:num` THEN BETA_TAC;
   REWRITE_TAC[pi_bound_fun];
   COND_CASES_TAC;
   ASM_MESON_TAC[ARITH_RULE `0<| k ==> (~(n+k = 0))`];
   REWRITE_TAC[GSYM REAL_MUL_ASSOC];
   AP_TERM_TAC;
   REWRITE_TAC[REAL_INV_MUL;REAL_POW_ADD;REAL_POW_INV;REAL_MUL_AC];
   SUBGOAL_THEN `(\n. (&.15/(&.16)) *. ((inv(&.16)**. k)*. inv(&.16 **. n))) sums ((&.15/(&.16)) *.(inv(&.16**. k)*. ((&.16)/(&.15))))` ASSUME_TAC;
   MATCH_MP_TAC SER_CMUL;
   REWRITE_TAC[REAL_POW_INV];
   ACCEPT_TAC (SPEC `k:num` GP16);
   FIRST_X_ASSUM MP_TAC;
   REWRITE_TAC[REAL_MUL_ASSOC];
   MATCH_MP_TAC (prove (`(x=y) ==> ((a sums x) ==> (a sums y))`,MESON_TAC[]));
   MATCH_MP_TAC (REAL_ARITH `(b*(a*c) = (b*(&.1))) ==> ((a*b)*c = b)`);
   AP_TERM_TAC;
   CONV_TAC (REAL_RAT_REDUCE_CONV);
   ]);;
  (* }}} *)

let PI_SER = prove_by_refinement(
  `!k. (0<|k) ==> (abs(pi - (sum(0,k) pi_fun)) <=. (inv(&.16 **. (k))))`,
  (* {{{ proof *)
   [
   GEN_TAC THEN DISCH_TAC;
   ASSUME_TAC (ONCE_REWRITE_RULE[ETA_AX] (REWRITE_RULE[GSYM pi_fun] POLYLOG_THM));
   ASSUME_TAC PI_EST2;
   IMP_RES_THEN (ASSUME_TAC) GP16a;
   IMP_RES_THEN (ASSUME_TAC) SUM_SUMMABLE;
   IMP_RES_THEN (ASSUME_TAC) SER_OFFSET_REV;
   IMP_RES_THEN (ASSUME_TAC) SUM_SUMMABLE;
   MP_TAC (SPECL [`pi`;`pi_fun`;`pi_bound_fun` ] SER_APPROX);
   ASM_REWRITE_TAC[];
   DISCH_THEN (fun th -> MP_TAC (SPEC `k:num` th));
   SUBGOAL_THEN `suminf (\n. pi_bound_fun (n + k)) = inv (&.16 **. k)` (fun th -> (MESON_TAC[th]));
   ASM_MESON_TAC[SUM_UNIQ];
   ]);;
  (* }}} *)

(* replace 3 by SUC (SUC (SUC 0)) *)
let SUC_EXPAND_CONV tm =
   let count = dest_numeral tm in
   let rec add_suc i r =
     if (i <=/ (Int 0)) then r
     else add_suc (i -/ (Int 1)) (mk_comb (`SUC`,r)) in
   let tm' = add_suc count `0` in
   REWRITE_RULE[] (ARITH_REWRITE_CONV[] (mk_eq (tm,tm')));;

let inv_twopow = prove(
  `!n. inv (&.16 **. n) = (twopow (--: (&:(4*n)))) `,
    REWRITE_TAC[TWOPOW_NEG;GSYM (NUM_RED_CONV `2 EXP 4`);
    REAL_OF_NUM_POW;EXP_MULT]);;

let PI_SERn n =
   let SUM_EXPAND_CONV =
           (ARITH_REWRITE_CONV[]) THENC
           (TOP_DEPTH_CONV SUC_EXPAND_CONV) THENC
           (REWRITE_CONV[sum]) THENC
           (ARITH_REWRITE_CONV[REAL_ADD_LID;GSYM REAL_ADD_ASSOC]) in
   let sum_thm = SUM_EXPAND_CONV (vsubst [n,`i:num`] `sum(0,i) f`) in
   let gt_thm = ARITH_RULE (vsubst [n,`i:num`] `0 <| i`) in
   ((* CONV_RULE REAL_RAT_REDUCE_CONV *)(CONV_RULE (ARITH_REWRITE_CONV[]) (BETA_RULE (REWRITE_RULE[sum_thm;pi_fun;inv_twopow] (MATCH_MP PI_SER gt_thm)))));;

(* abs(pi - u ) < e *)
let recompute_pi bprec =
   let n = (bprec /4) in
   let pi_ser = PI_SERn (mk_numeral (Int n)) in
   let _ = remove_real_constant `pi` in
   (add_real_constant pi_ser; INTERVAL_OF_TERM bprec `pi`);;

(* ------------------------------------------------------------------ *)
(* restore defaults *)
(* ------------------------------------------------------------------ *)

reduce_local_interface("trig");; 
