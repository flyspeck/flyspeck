(*DANG TAT DAT*)
(*TARJJUW*)

(*-----------Definition------------------------------------------------------*)
let packing = 
   new_definition 
     `packing (V:real^3 -> bool) = 
      (!u:real^3 v:real^3. (u IN V) /\ (v IN V) /\ (dist( u, v) < &2) ==>
      (u = v))`;;

let saturated_packing = 
   new_definition 
    `saturated_packing (V:real^3 -> bool) <=>
      (packing V) /\ (!(p:real^3).(?(u:real^3).(u IN V) /\ (dist(u,p) < &2)))`;;

let weakly_saturated = 
    new_definition 
     `weakly_saturated (V:real^3 ->bool) (r:real) (r':real) <=>
        (!(v:real^3).(dist(vec 0,v) > r') \/ (?(u:real^3). (u IN V) /\
        (~((vec 0) = u)) /\ (dist(u,v) < r)))`;;

let weakly_saturated_finite_packing = 
    new_definition 
    `weakly_saturated_finite_packing (V:real^3->bool) (r:real) (r':real) <=> 
    (FINITE V) /\ (saturated_packing V) /\
    (weakly_saturated V r r') /\ ((vec 0) IN V)`;;

let half_spaces =
    new_definition 
    `half_spaces (g:(real^3 ->real)) (u:real^3) =
     {p:real^3| (u dot p) <= (g u)}`;;

let polyhedron =
    new_definition
    `polyhedron (V:real^3 -> bool) (g:(real^3 ->real)) =
     INTERS {half_spaces g u| (u IN V) /\ (~(vec 0 = u))}`;;

(*--------proff---------------------------------------------------------------*)

(*-----------------------------------------------------------------------*)
let th1 = prove (`!(V:real^3 -> bool)(g:real^3->real) (r:real) (r':real) (u:real^3)(a:real). (&2 <= r) /\ (r <= r') /\ (~(bounded (polyhedron V g))) /\ (u IN V) /\ (~(vec 0 = u )) /\ (a = ((g u) * r')/ &2) ==> (?p:real^3. (p IN (polyhedron V g)) /\ (a < norm p))`,REPEAT GEN_TAC THEN REWRITE_TAC [bounded;NOT_EXISTS_THM;NOT_FORALL_THM;NOT_IMP;REAL_NOT_LE;polyhedron] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "F1") THEN REPEAT STRIP_TAC THEN USE_THEN "F1" (MP_TAC o SPEC `a:real`) THEN DISCH_THEN (X_CHOOSE_TAC `p:real^3`) THEN EXISTS_TAC `p:real^3` THEN ASM_ARITH_TAC);;

let th11 = prove (`!(V:real^3 -> bool)(g:real^3->real) (r:real) (r':real) (u:real^3). (&2 <= r) /\ (r <= r') /\ (~(bounded (polyhedron V g))) /\ (u IN V) /\ (~(vec 0 = u )) ==> (?p:real^3. (p IN (polyhedron V g)) /\ ((((g u) * r')/ &2) < norm p))`,
REPEAT GEN_TAC THEN REWRITE_TAC [bounded;NOT_EXISTS_THM;NOT_FORALL_THM;NOT_IMP;REAL_NOT_LE;polyhedron] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
POP_ASSUM MP_TAC THEN
POP_ASSUM MP_TAC THEN
DISCH_THEN (LABEL_TAC "F1") THEN
REPEAT STRIP_TAC THEN
USE_THEN "F1" (MP_TAC o SPEC `((((g:real^3->real) (u:real^3)) * (r':real))/ (&2)) `) THEN
DISCH_THEN (X_CHOOSE_TAC `p:real^3`) THEN
EXISTS_TAC `p:real^3` THEN
ASM_ARITH_TAC);;
(*-------------------------------------------------------------------------*)
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
let th3 = prove (`!(V:real^3 -> bool)(u:real^3)(v:real^3).(packing V) /\ (vec 0 IN V) /\ (u IN V) /\ (~(vec 0 = u)) ==> norm u >= &2`,REPEAT GEN_TAC THEN REWRITE_TAC [packing] THEN STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC "F1") THEN REPEAT STRIP_TAC THEN ASM_CASES_TAC `&2 <= norm (u:real^3)` THENL [ASM_ARITH_TAC;POP_ASSUM MP_TAC THEN REWRITE_TAC [GSYM DIST_0] THEN STRIP_TAC THEN USE_THEN "F1" (MP_TAC o SPECL [`v:real^3`;`u:real^3`]) THEN DISCH_TAC THEN SUBGOAL_THEN `dist (vec 0,(u:real^3)) < &2 ==> vec 0 = u` ASSUME_TAC THENL [REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];SUBGOAL_THEN `dist (vec 0,(u:real^3)) < &2` ASSUME_TAC THENL [ASM_MESON_TAC [REAL_NOT_LE];SUBGOAL_THEN `vec 0 = u:real^3` ASSUME_TAC THENL [ASM_MESON_TAC[];ASM_MESON_TAC[]]]]]);;

(*------------------------------------------------------------------------*)
let th4 =prove (`!(u:real^3) (v:real^3) (r:real).dist (u,v) < r ==> (dist (u,v)) pow 2 < r pow 2`,REPEAT GEN_TAC THEN REWRITE_TAC [dist] THEN STRIP_TAC THEN SUBGOAL_THEN `&0 <= norm ((u:real^3) - (v:real^3))` ASSUME_TAC THENL [REWRITE_TAC [NORM_POS_LE];SUBGOAL_THEN `&0 <= r` ASSUME_TAC THENL [ASM_ARITH_TAC;SUBGOAL_THEN `abs (norm ((u:real^3) - (v:real^3))) = norm (u - v)` ASSUME_TAC THENL [REWRITE_TAC [REAL_ABS_NORM];SUBGOAL_THEN `abs (r:real) = r` ASSUME_TAC THENL [ASM_ARITH_TAC;SUBGOAL_THEN `abs (norm ((u:real^3) - (v:real^3))) < abs(r:real)` ASSUME_TAC THENL [ASM_ARITH_TAC;ASM_MESON_TAC [REAL_LT_SQUARE_ABS]]]]]]);;

(*-------------------------------------------------------------------------*)
let th5 = prove (`!(V:real^3 -> bool)(g:real^3->real) (r:real) (r':real) (u:real^3)(a:real)
(v:real^3) (p:real^3).(packing V) /\ (&2 <= r) /\ (r <= r') /\  (~(p = vec 0)) /\ (a = ((g u) * r')/ &2) /\ (a < norm p) /\ (v = (r'/(norm p))% p) /\ ((u dot p) <= (g u)) /\ (~(vec 0 = u)) /\ (dist (u,v) < r) /\ (vec 0 IN V) /\ (u IN V)  ==> (norm p < norm p)`,REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `(&0 < r':real)` ASSUME_TAC THENL 
[ASM_ARITH_TAC;SUBGOAL_THEN ` (norm (v:real^3)= (r':real))` ASSUME_TAC THENL 

[ASM_MESON_TAC [norm_equa];
(*---Sub2*)
SUBGOAL_THEN `(((g:real^3-> real) (u:real^3)) * (r':real)) / &2 < norm (p:real^3)` ASSUME_TAC THENL 

[ASM_ARITH_TAC;POP_ASSUM MP_TAC THEN STRIP_TAC THEN 
SUBGOAL_THEN `&0 <= norm (v:real^3)` ASSUME_TAC(*]]]);;*) THENL

[ASM_ARITH_TAC;
SUBGOAL_THEN `((u:real^3) dot (p:real^3)) * (norm (v:real^3)) <=  ((g:real^3->real) u) * norm v` ASSUME_TAC THENL

[ASM_MESON_TAC[REAL_LE_RMUL];

SUBGOAL_THEN `(((u:real^3) dot (p:real^3)) * (norm (v:real^3)))/(&2) <=  (((g:real^3->real) u) * norm v)/(&2)` ASSUME_TAC THENL

[ASM_ARITH_TAC;POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN 
SUBGOAL_THEN `((u:real^3) dot (p:real^3)) * (r':real) = (r') * ((u) dot (p))` ASSUME_TAC THENL   

[ARITH_TAC;

SUBGOAL_THEN `(r':real) * ((u:real^3) dot (p:real^3)) = u dot (r'% p)` ASSUME_TAC THENL
[MESON_TAC [DOT_RMUL];

SUBGOAL_THEN `(r':real)% (p:real^3) = (norm p)%(v:real^3)` ASSUME_TAC THENL
[ASM_MESON_TAC [th2];

SUBGOAL_THEN `(u:real^3) dot ((r':real)% (p:real^3)) = u dot ((norm p)%v)` ASSUME_TAC THENL
[ASM_MESON_TAC[];

SUBGOAL_THEN ` (u:real^3) dot ((norm (p:real^3))%(v:real^3)) = (norm p) * (u dot v)` ASSUME_TAC(*]]]]]]]]]);;*) THENL
[MESON_TAC [DOT_RMUL];

SUBGOAL_THEN `((u:real^3) dot (p:real^3)) * (r':real) = norm p * (u dot (v:real^3))` ASSUME_TAC THENL
[ASM_MESON_TAC[];

SUBGOAL_THEN `((norm (p:real^3)) * ((u:real^3) dot (v:real^3))) = (((norm p) *
(((norm u pow 2 + norm v pow 2) - (norm (u - v)) pow 2)) / &2))` ASSUME_TAC THENL

[MESON_TAC[DOT_NORM_NEG];POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM dist] THEN STRIP_TAC THEN 

SUBGOAL_THEN `norm (u:real^3) >= &2` ASSUME_TAC THENL
[ASM_MESON_TAC [th3];

SUBGOAL_THEN `&0 <= &2` ASSUME_TAC THENL
[ARITH_TAC;

SUBGOAL_THEN `abs (&2) = &2` ASSUME_TAC THENL
[ASM_MESON_TAC [REAL_ABS_REFL];

SUBGOAL_THEN `abs (norm (u:real^3)) >= abs (&2)` ASSUME_TAC THENL
[ASM_REWRITE_TAC [REAL_ABS_NORM];

SUBGOAL_THEN `abs (&2) <= abs (norm (u:real^3))` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `(&2) pow 2 <= (norm (u:real^3)) pow 2` ASSUME_TAC THENL 
[ASM_MESON_TAC[REAL_LE_SQUARE_ABS];POP_ASSUM MP_TAC THEN REWRITE_TAC [ARITH_RULE `&2 pow 2 = &4`] THEN STRIP_TAC THEN

SUBGOAL_THEN `(dist (u:real^3,v:real^3)) pow 2 < (r:real) pow 2` ASSUME_TAC THENL
[ASM_MESON_TAC [th4];

SUBGOAL_THEN `--((r:real) pow 2) < --((dist (u:real^3,v:real^3)) pow 2) ` ASSUME_TAC THENL
[ASM_MESON_TAC [REAL_LT_NEG];

SUBGOAL_THEN `(norm (v:real^3)) pow 2 = (r':real) pow 2` ASSUME_TAC(*]]]]]]]]]]]]]]]]]]]]);;*) THENL
[ASM_MESON_TAC[];

SUBGOAL_THEN `((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) =
 (norm (u:real^3)) pow 2 + (r':real) pow 2` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `&4 + (norm (v:real^3)) pow 2 <= ((norm (u:real^3)) pow 2 + (norm v) pow 2 )` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `(((u:real^3) dot (p:real^3)) * (r':real)) / &2 < (norm (p))`
ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `((norm (p:real^3)) * ((u:real^3) dot (v:real^3))) / &2 < (norm (p))`
ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `&4 + (r':real) pow 2 <= ((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2 )` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `&4 + (r':real) pow 2 + --(dist ((u:real^3),(v:real^3)) pow 2) <= ((norm (u)) pow 2 + (norm (v)) pow 2 + --(dist (u,v) pow 2) )` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `&4 + (r':real) pow 2 + --((r:real) pow 2)  <= &4 + (r':real) pow 2 + --(dist ((u:real^3),(v:real^3)) pow 2)` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `&4 + (r':real) pow 2 + --((r:real) pow 2) <= ((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2 + --(dist (u,v) pow 2))` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `&0 <= r:real` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `&0 <= r':real` ASSUME_TAC(*]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]);;*) THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `abs (r':real) = r'` ASSUME_TAC THENL
[ASM_MESON_TAC[REAL_ABS_REFL];

SUBGOAL_THEN `abs (r:real) = r` ASSUME_TAC THENL
[ASM_MESON_TAC[REAL_ABS_REFL];

SUBGOAL_THEN `abs (r:real) <= abs(r':real)` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `(r:real) pow 2 <= (r':real) pow 2` ASSUME_TAC THENL
[ASM_MESON_TAC[REAL_LE_SQUARE_ABS];

SUBGOAL_THEN `&0 <= (r':real) pow 2 - (r:real) pow 2 ` ASSUME_TAC THENL
[ASM_MESON_TAC [REAL_SUB_LE];

SUBGOAL_THEN `&4 <= &4 + (r':real) pow 2 - (r:real) pow 2` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `&4 + ((r':real) pow 2) - ((r:real) pow 2) = &4 + ((r':real) pow 2) + --((r:real) pow 2)` ASSUME_TAC THENL
[MESON_TAC[real_sub];

SUBGOAL_THEN `&4 + ((r':real) pow 2) - ((r:real) pow 2) <= ((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) + --(dist (u,v) pow 2)` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `&4 <= ((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) + --(dist (u,v) pow 2)` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `&0 < &2` ASSUME_TAC(*]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]);;*) THENL
[ARITH_TAC;

SUBGOAL_THEN `~(&2 = &0)` ASSUME_TAC THENL
[ARITH_TAC;

SUBGOAL_THEN `(((norm (p:real^3)) * ((u:real^3) dot (v:real^3)))/ &2) * (&2) < (norm p) * (&2)` ASSUME_TAC THENL
[ASM_MESON_TAC [REAL_LT_RMUL];

SUBGOAL_THEN `(((norm (p:real^3)) * ((u:real^3) dot (v:real^3)))/ &2) * (&2) = ((norm (p:real^3)) * ((u:real^3) dot (v:real^3)))` ASSUME_TAC THENL
[ASM_MESON_TAC [REAL_DIV_RMUL];

SUBGOAL_THEN `((norm (p:real^3)) * ((u:real^3) dot (v:real^3))) < (norm p) * (&2) ` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `(((norm (p:real^3)) * (((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - dist (u,v) pow 2)) / &2) < (norm p) * (&2) ` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `((((norm (p:real^3)) * (((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - dist (u,v) pow 2)) / &2))*(&2) < ((norm p) * (&2))*(&2) ` ASSUME_TAC THENL
[ASM_MESON_TAC[REAL_LT_RMUL];

SUBGOAL_THEN `((((norm (p:real^3)) * (((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - dist (u,v) pow 2)) / &2))*(&2) = ((norm (p:real^3)) * (((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - dist (u,v) pow 2))` ASSUME_TAC THENL
[ASM_MESON_TAC [REAL_DIV_RMUL];

SUBGOAL_THEN `((norm (p:real^3)) * (((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - dist (u,v) pow 2)) < (norm p * &2) * &2` ASSUME_TAC THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - (dist (u,v) pow 2) = ((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) +  --(dist (u,v) pow 2)` ASSUME_TAC THENL
[MESON_TAC[real_sub];

SUBGOAL_THEN `&4 <= ((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - (dist (u,v) pow 2)` ASSUME_TAC(*]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]);;*) THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `&0 <= (norm (p:real^3))` ASSUME_TAC THENL
[MESON_TAC[NORM_POS_LE];

SUBGOAL_THEN `(norm (p:real^3)) * (&4) <= (norm (p:real^3)) * (((norm (u:real^3)) pow 2 + (norm (v:real^3)) pow 2) - dist (u,v) pow 2)` ASSUME_TAC(*]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]);;*) THENL
[ASM_MESON_TAC [REAL_LE_LMUL];

SUBGOAL_THEN `(norm (p:real^3)) * (&4) < ((norm p) * (&2))*(&2)` ASSUME_TAC(*]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]);;*) THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `((norm (p:real^3)) * (&2))*(&2) = (norm p) * (&2) * (&2)` ASSUME_TAC(*]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]);;*) THENL 
[ARITH_TAC;POP_ASSUM MP_TAC THEN REWRITE_TAC [ARITH_RULE `&2 * &2 = &4`] THEN STRIP_TAC THEN

SUBGOAL_THEN `(norm (p:real^3)) * (&4) < (norm (p:real^3)) * (&4)` ASSUME_TAC(*]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]);;*) THENL
[ASM_ARITH_TAC;

SUBGOAL_THEN `&0 < &4` ASSUME_TAC (*]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]);;*)
THENL
[ARITH_TAC;ASM_ARITH_TAC]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]);;

(*----------------------------------------------------------------*)
let th6 = prove (`!(V:real^3 -> bool) (g:real^3->real) (p:real^3) (u:real^3). (u IN V) /\ (~(vec 0 = u)) /\ (p IN (polyhedron V g)) ==> p IN half_spaces g u`,REPEAT GEN_TAC THEN REWRITE_TAC [polyhedron;INTERS;IN_ELIM_THM] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "F1") THEN USE_THEN "F1" (MP_TAC o SPEC `half_spaces (g:real^3 -> real) (u:real^3)`) THEN STRIP_TAC THEN ASM_MESON_TAC[]);;

let th7 = prove (`!(V:real^3 -> bool) (g:real^3->real) (p:real^3) (u:real^3). (u IN V) /\ (~(vec 0 = u)) /\ (p IN (polyhedron V g)) ==>  (u dot p) <= (g u)`,REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `(p:real^3) IN half_spaces (g:real^3 -> real) (u:real^3)` ASSUME_TAC THENL [ASM_MESON_TAC [th6];POP_ASSUM MP_TAC THEN REWRITE_TAC [half_spaces]] THEN REWRITE_TAC [IN_ELIM_THM]);;

let th8 = prove(`!(g:real^3->real)(r':real)(a:real)(u:real^3).(&2 <= r) /\ (r <= r') /\
 (a = ((g u) * r')/ &2) /\ (&0 <= g u) ==> &0 <= a`,REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `&2 <= (r':real)` ASSUME_TAC THENL
[ASM_ARITH_TAC;SUBGOAL_THEN `&0 <= (r':real)` ASSUME_TAC THENL
[ASM_ARITH_TAC;
SUBGOAL_THEN `&0 <= (((g:real^3->real) (u:real^3)) * (r':real))` ASSUME_TAC THENL
[ASM_MESON_TAC[REAL_LE_MUL];
SUBGOAL_THEN `&0 <= &2` ASSUME_TAC THENL
[ARITH_TAC;
SUBGOAL_THEN `&0 <= (((g:real^3->real) (u:real^3)) * (r':real))/(&2)` ASSUME_TAC THENL
[ASM_MESON_TAC [REAL_LE_DIV];ASM_ARITH_TAC]]]]]);;

(*-------------------------------------------------------------------------*)

(*---------------------------------------------------------------*)
let TARJJUW = prove (`!(V:real^3 -> bool)(g:real^3->real) (r:real) (r':real)(a:real).(&2 <= r) /\ (r <= r') /\ (!(u:real^3).(u IN V) /\ (~(vec 0 = u )) ==> (a = ((g u) * r')/ &2)) /\ (!(v:real^3) (p:real^3). (~(p = vec 0)) ==> (v = (r'/(norm p))% p)) /\ (weakly_saturated_finite_packing V r r') ==>
(bounded (polyhedron V g))`,
REPEAT GEN_TAC THEN REWRITE_TAC [weakly_saturated_finite_packing;saturated_packing;weakly_saturated] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "A1") THEN DISCH_THEN (LABEL_TAC "A2") THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN (LABEL_TAC "F1") THEN DISCH_THEN (LABEL_TAC "F2") THEN STRIP_TAC THEN SUBGOAL_THEN `&2 <= (r':real)` ASSUME_TAC THENL
[ASM_ARITH_TAC;
SUBGOAL_THEN `&0 < &2` ASSUME_TAC THENL

[ARITH_TAC;
SUBGOAL_THEN `&0 < (r':real)` ASSUME_TAC THENL
[ASM_ARITH_TAC;

ASM_CASES_TAC `bounded (polyhedron (V:real^3 -> bool) (g:real^3 -> real))` THENL
[ASM_ARITH_TAC;
ASM_REWRITE_TAC[]]]]] THEN POP_ASSUM MP_TAC THEN
DISCH_THEN (LABEL_TAC "A3") THEN

USE_THEN "F2" (MP_TAC o SPEC `(((r':real)/(norm (p:real^3)))% p) `) THEN
DISCH_TAC THEN
POP_ASSUM MP_TAC THEN
REWRITE_TAC [dist;NORM_SUB;VECTOR_SUB_RZERO] THEN

STRIP_TAC THENL
(*sub in sub*)
[REWRITE_TAC[] THEN
ASM_CASES_TAC `(p:real^3) = vec 0` THENL
[REWRITE_TAC[] THEN
SUBGOAL_THEN `((r':real)/(norm (p:real^3)))% p = vec 0` ASSUME_TAC THENL
[ASM_MESON_TAC [VECTOR_MUL_RZERO];
SUBGOAL_THEN `norm (((r':real)/(norm (p:real^3)))% p) = &0` ASSUME_TAC THENL
[ASM_MESON_TAC [NORM_EQ_0];
SUBGOAL_THEN `&0 > r':real` ASSUME_TAC THENL
[ASM_ARITH_TAC;ASM_ARITH_TAC]]];

SUBGOAL_THEN `norm (((r':real)/(norm (p:real^3)))%p) = r'` ASSUME_TAC THENL
[ASM_MESON_TAC [norm_equa2];
SUBGOAL_THEN `r':real > r'` ASSUME_TAC THENL
[ASM_ARITH_TAC;ASM_ARITH_TAC]]];

SUBGOAL_THEN `?(p:real^3). (p IN (polyhedron (V:real^3->bool) (g:real^3->real))) /\ ((a:real) < (norm p))` ASSUME_TAC THENL
[ASM_MESON_TAC[th1];
POP_ASSUM MP_TAC THEN
REWRITE_TAC[] THEN STRIP_TAC]] THEN
SUBGOAL_THEN `(u:real^3) dot (p:real^3) <= (g:real^3->real) (u)` ASSUME_TAC THENL
[ASM_MESON_TAC [th7];

USE_THEN "A1" (MP_TAC o SPEC `u:real^3`) THEN
STRIP_TAC] THEN
SUBGOAL_THEN `(a:real) = (((g:real^3->real) (u:real^3)) * (r':real))/(&2)` ASSUME_TAC THENL
[ASM_MESON_TAC[];

(**)

ASM_CASES_TAC `(p:real^3) = vec 0` THENL
[SUBGOAL_THEN `norm (p:real^3) = &0` ASSUME_TAC THENL
[ASM_MESON_TAC [NORM_EQ_0];
SUBGOAL_THEN `(u:real^3) dot (p:real^3) = &0` ASSUME_TAC THENL
[ASM_MESON_TAC [FORALL_DOT_EQ_0];
SUBGOAL_THEN `&0 <= ((g:real^3->real) (u:real^3))` ASSUME_TAC THENL
[ASM_ARITH_TAC;
SUBGOAL_THEN `&0 <= (a:real)` ASSUME_TAC THENL
[ASM_MESON_TAC [th8];
SUBGOAL_THEN `(a:real) < &0` ASSUME_TAC THENL
[ASM_MESON_TAC[];ASM_ARITH_TAC]]]]];
SUBGOAL_THEN `norm (p:real^3) < norm p` ASSUME_TAC THENL
[ASM_MESON_TAC [th5];ASM_ARITH_TAC]]]);;
(**)
