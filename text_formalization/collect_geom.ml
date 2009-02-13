needs "Multivariate/vectors.ml";; (* Eventually should load entire *) 	   
needs "Examples/analysis.ml";; (* multivariate-complex theory. *)	   
needs "Examples/transc.ml";; (* Then it won't need these three. *)
needs "convex_header.ml";; 
needs "definitions_kepler.ml";;
needs "geomdetail.ml";;

prioritize_real();;

let ups_x = new_definition ` ups_x x1 x2 x6 =
         --x1 * x1 - x2 * x2 - x6 * x6 +
         &2 * x1 * x6 +
         &2 * x1 * x2 +
         &2 * x2 * x6 `;;
let rho = new_definition ` rho (x12 :real) x13 x14 x23 x24 x34 =
         --(x14 * x14 * x23 * x23) -
         x13 * x13 * x24 * x24 -
         x12 * x12 * x34 * x34 +
         &2 *
         (x12 * x14 * x23 * x34 +
          x12 * x13 * x24 * x34 +
          x13 * x14 * x23 * x24) `;;
let chi = new_definition ` chi x12 x13 x14 x23 x24 x34 =
         x13 * x23 * x24 +
         x14 * x23 * x24 +
         x12 * x23 * x34 +
         x14 * x23 * x34 +
         x12 * x24 * x34 +
         x13 * x24 * x34 -
         &2 * x23 * x24 * x34 -
         x12 * x34 * x34 -
         x14 * x23 * x23 -
         x13 * x24 * x24 `;;
let delta = new_definition ` delta x12 x13 x14 x23 x24 x34 =
   --(x12 * x13 * x23) -
         x12 * x14 * x24 -
         x13 * x14 * x34 -
         x23 * x24 * x34 +
         x12 * x34 * (--x12 + x13 + x14 + x23 + x24 - x34) + 
         x13 * x24 * (x12 - x13 + x14 + x23 - x24 + x34 ) +
         x14 * x23 * ( x12 + x13 - x14 - x23 + x24 + x34 ) `;;
(* How can I write the definition of R(xij)? Do I have to compute the determinant *)
let eta_v = new_definition ` eta_v v1 v2 (v3: real^N) =
        let e1 = dist (v2, v3) in
  	  let e2 = dist (v1, v3) in
  	  let e3 = dist (v2, v1) in
  	  e1 * e2 * e3 / sqrt ( ups_x (e1 pow 2 ) ( e2 pow 2) ( e3 pow 2 ) ) `;;


let max_real3 = new_definition ` max_real3 x y z = max_real (max_real x y ) z `;;
let ups_x_pow2 = new_definition` ups_x_pow2 x y z = ups_x ( x*x ) ( y * y) ( z * z)`;;


(* NGUYEN DUC PHUONG *)
(* Definition of Cayley – Menger square cm3 *)
let cm3_ups_x = new_definition `!(v1:real^3) (v2:real^3) (v3:real^3).
   cm3_ups_x v1 v2 v3 = 
  (((v2 - v1)$2 * (v3 - v1)$3 ) - ((v2 - v1)$3 * (v3 - v1)$2)) pow 2 +
  (((v2 - v1)$3 * (v3 - v1)$1 ) - ((v2 - v1)$1 * (v3 - v1)$3)) pow 2 +
  (((v2 - v1)$1 * (v3 - v1)$2 ) - ((v2 - v1)$2 * (v3 - v1)$1)) pow 2 `;;

(* Nguyen Tuyen Hoang, Nguyen Duc Phuong *)

(* The polynomial ups can be expressed as a Cayley- Menger square *)  

let lemma_cm3 = prove (`!(x:real^3) y. 
(x-y)$1 = x$1 - y$1 /\ (x-y)$2 = x$2 - y$2 /\ (x-y)$3 = x$3 - y$3`, 

(REPEAT GEN_TAC) THEN (REPEAT CONJ_TAC) THENL 
[(MESON_TAC[VECTOR_SUB_COMPONENT;DIMINDEX_3;ARITH_RULE `1 <= 1 /\ 1 <= 3`]);
(MESON_TAC[VECTOR_SUB_COMPONENT;DIMINDEX_3;ARITH_RULE `1 <= 2 /\ 2 <= 3`]);
(MESON_TAC[VECTOR_SUB_COMPONENT;DIMINDEX_3;ARITH_RULE `1 <= 3 /\ 3 <= 3`])]);;

let lemma7 = prove ( `! (v1 : real ^3)(v2: real^3)(v3:real^3).
  cm3_ups_x v1 v2 v3 = 
  ups_x (norm (v1 -v2) pow 2) (norm (v2 -v3) pow 2) (norm (v3 -v1) pow 2) / &4`,

 (REPEAT GEN_TAC) THEN
 (REWRITE_TAC[cm3_ups_x; ups_x]) THEN
 (REWRITE_TAC[GSYM DOT_SQUARE_NORM;DOT_3;REAL_POW_2]) THEN
 (REWRITE_TAC[lemma_cm3]) THEN
  REAL_ARITH_TAC );;

let pow_g = prove ( `! (x:real). &0 <= x pow 2`,
  GEN_TAC THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]);;

let lemma8 = prove ( `! (v1:real^3)(v2:real^3)(v3:real^3). 
&0 <= ups_x (norm (v1 - v2) pow 2)(norm (v2 - v3) pow 2)(norm (v3 - v1) pow 2)`,
 (REPEAT GEN_TAC)
THEN (MATCH_MP_TAC (REAL_ARITH `&0 <= a/ &4 ==> &0 <= a `))
THEN (REWRITE_TAC[GSYM lemma7])
THEN (REWRITE_TAC[cm3_ups_x])

THEN (ABBREV_TAC `(a:real) = (((v2:real^3) - v1)$2 * (v3 - v1)$3 - (v2 - v1)$3 * (v3 - v1)$2) pow 2`)
THEN (FIRST_X_ASSUM ((LABEL_TAC "1") o GSYM))
THEN (ABBREV_TAC `(b:real) = (((v2:real^3) - v1)$3 * (v3 - v1)$1 - (v2 - v1)$1 * (v3 - v1)$3) pow 2`)
THEN (FIRST_X_ASSUM((LABEL_TAC "2") o GSYM))
THEN (ABBREV_TAC `(c:real) = (((v2:real^3) - v1)$1 * (v3 - v1)$2 - (v2 - v1)$2 * (v3 - v1)$1) pow 2`)
THEN (FIRST_X_ASSUM((LABEL_TAC "3") o GSYM))

THEN (MATCH_MP_TAC (SPEC_ALL REAL_LE_ADD))
THEN CONJ_TAC
THEN (ASM_REWRITE_TAC[pow_g])
THEN (MATCH_MP_TAC (SPEC_ALL REAL_LE_ADD))
THEN CONJ_TAC
THEN (ASM_REWRITE_TAC[pow_g]));;

(* ========== *)
(* QUANG TRUONG *)
(* ============ *)
let GONTONG = REAL_RING ` ((a + b) + c = a + b + c ) `;;
let SUB_SUM_SUB = REAL_RING ` (a - ( b + c ) = a - b - c )/\( a - (b- c) = a - b + c )` ;;

(* lemma 4, p 7 *)
let JVUNDLC = prove(`!a b c s.
     s = (a + b + c) / &2
     ==> &16 * s * (s - a) * (s - b) * (s - c) =
         ups_x (a pow 2) (b pow 2) (c pow 2)`, SIMP_TAC [ ups_x] THEN 
REWRITE_TAC[REAL_FIELD` a / &2 - b = ( a - &2 * b ) / &2 `] THEN 
REWRITE_TAC[REAL_FIELD ` &16 * ( a / &2 ) * ( b / &2 ) * (c / &2 ) *
( d / &2 ) = a * b * c * d `] THEN REAL_ARITH_TAC);;

let SET_TAC =
   let basicthms =
    [NOT_IN_EMPTY; IN_UNIV; IN_UNION; IN_INTER; IN_DIFF; IN_INSERT;
     IN_DELETE; IN_REST; IN_INTERS; IN_UNIONS; IN_IMAGE] in
   let allthms = basicthms @ map (REWRITE_RULE[IN]) basicthms @
                 [IN_ELIM_THM; IN] in
   let PRESET_TAC =
     TRY(POP_ASSUM_LIST(MP_TAC o end_itlist CONJ)) THEN
     REPEAT COND_CASES_TAC THEN
     REWRITE_TAC[EXTENSION; SUBSET; PSUBSET; DISJOINT; SING] THEN
     REWRITE_TAC allthms in
   fun ths ->
     PRESET_TAC THEN
     (if ths = [] then ALL_TAC else MP_TAC(end_itlist CONJ ths)) THEN
     MESON_TAC[];;

 let SET_RULE tm = prove(tm,SET_TAC[]);;

(* some TRUONG TACTICS *)

let PHA = REWRITE_TAC[ MESON[] ` (a/\b)/\c <=> a/\ b /\ c `];;

let NGOAC = REWRITE_TAC[ MESON[] ` a/\b/\c <=> (a/\b)/\c `];;

let DAO = NGOAC THEN REWRITE_TAC[ MESON[]` a /\ b <=> b /\ a`];;

let PHAT = REWRITE_TAC[ MESON[] ` (a\/b)\/c <=> a\/b\/c `];;

let NGOACT =  REWRITE_TAC[ GSYM (MESON[] ` (a\/b)\/c <=> a\/b\/c `)];;

let KHANANG = PHA THEN REWRITE_TAC[ MESON[]` ( a\/ b ) /\ c <=> a /\ c \/ b /\ c `] THEN 
 REWRITE_TAC[ MESON[]` a /\ ( b \/ c ) <=> a /\ b \/ a /\ c `];;

let ATTACH thm = MATCH_MP (MESON[]` ! a b. ( a ==> b ) ==> ( a <=> a /\ b )`) thm;;

let NHANH tm = ONCE_REWRITE_TAC[ ATTACH (tm)];;
let STRIP_TR = REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM MP_TAC)
      THEN REWRITE_TAC[IMP_IMP] THEN PHA;;


let elimin = REWRITE_RULE[IN];;

let CONV_EM = prove(`conv {} = {}:real^A->bool`,
  REWRITE_TAC[conv;sgn_ge;affsign;UNION_EMPTY;FUN_EQ_THM;elimin
NOT_IN_EMPTY;lin_combo;SUM_CLAUSES]
  THEN REAL_ARITH_TAC);;

let CONV_SING = prove(`!u. conv {u:real^A} = {u}`,
 REWRITE_TAC[conv;sgn_ge;affsign;FUN_EQ_THM;UNION_EMPTY;lin_combo;SUM_SING;VSUM_SING;
 elimin IN_SING] THEN REPEAT GEN_TAC THEN
 REWRITE_TAC[TAUT `(p <=> q) = ((p ==> q) /\ (q ==> p))`] THEN
 REPEAT STRIP_TAC THENL [ASM_MESON_TAC[VECTOR_MUL_LID];
 ASM_REWRITE_TAC[]] THEN EXISTS_TAC `\ (v:real^A). &1` THEN
 MESON_TAC[VECTOR_MUL_LID;REAL_ARITH `&0 <= &1`] );;

let IN_ACT_SING = SET_RULE `! a x. ({a} x <=> a = x ) /\ ( x IN {a} <=> x = a) /\ {a} a`;;

let IN_SET2 = SET_RULE `!a b x.
         (x IN {a, b} <=> x = a \/ x = b) /\ ({a, b} x <=> x = a \/ x = b)`;;

let SUM_DIS2 = prove(`! x y f. ~(x=y) ==> sum {x,y} f = f x + f y `,REWRITE_TAC[
   SET_RULE ` ~( x = y)
 <=> ~(x IN {y})`] THEN MESON_TAC[ FINITE_RULES; SUM_CLAUSES; SUM_SING]);;


let VSUM_DIS2 = prove(` ! x y f. ~(x=y) ==>  vsum {x,y} f = f x + f y`, REWRITE_TAC[
   SET_RULE ` ~( x = y)
 <=> ~(x IN {y})`] THEN MESON_TAC[ FINITE_RULES; VSUM_CLAUSES; VSUM_SING]);;

let NOV10 = prove(` ! x y. (x = y
      ==> (!x. y = x <=>
               (?a b. &0 <= a /\ &0 <= b /\ a + b = &1 /\ x = a % y + b % y))) `,
REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB] THEN 
REWRITE_TAC[ MESON[VECTOR_MUL_LID]` a + b = &1 /\ x = (a + b) % y <=> a + b = &1 /\ 
x = y`]THEN REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN NGOAC THEN 
REWRITE_TAC[LEFT_EXISTS_AND_THM] THEN MATCH_MP_TAC (MESON[]` a ==> ( x = y <=> a /\
 y = x )`)THEN EXISTS_TAC `&0` THEN EXISTS_TAC ` &1` THEN REAL_ARITH_TAC);;


let TRUONG_LEMMA = prove
  (  `!x y x':real^N.
       (?f. x' = f x % x + f y % y /\ (&0 <= f x /\ &0 <= f y) /\
            f x + f y = &1) <=>
       (?a b. &0 <= a /\ &0 <= b /\ a + b = &1 /\ x' = a % x + b % y)`   ,
   REPEAT GEN_TAC THEN EQ_TAC 
THENL [MESON_TAC[]; STRIP_TAC] THEN
   ASM_CASES_TAC `y:real^N = x` THENL
    [EXISTS_TAC `\x:real^N. &1 / &2`;
     EXISTS_TAC `\u:real^N. if u = x then (a:real) else b`] THEN
   ASM_REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB] THEN
   CONV_TAC REAL_RAT_REDUCE_CONV);;

let CONV_SET2 = prove(` ! x y:real^A. conv {x,y} = {w | ? a b. &0 <= a /\ &0 <= b /\ a + b = &1 /\
  w = a%x + b%y}`,
ONCE_REWRITE_TAC[ MESON[] ` (! a b. P a b ) <=> ( ! a b. a = b \/ ~( a= b)
  ==> P a b )`] THEN 
REWRITE_TAC[ MESON[]` a \/ b ==> c <=> ( a==> c) /\ ( b==> c)`] THEN 
SIMP_TAC[] THEN REWRITE_TAC[ SET_RULE ` {a,a} = {a}`; CONV_SING; FUN_EQ_THM;
 IN_ELIM_THM] THEN REWRITE_TAC[ IN_ACT_SING] THEN REWRITE_TAC[NOV10] THEN 
REWRITE_TAC[conv; sgn_ge; affsign; lin_combo] THEN 
REWRITE_TAC[UNION_EMPTY; IN_SET2] THEN 
ONCE_REWRITE_TAC[ MESON[]`  ~(x = y) ==> (!x'. (?f. P f x') <=> l x') <=>
  ~(x = y) ==> (!x'. (?f. ~(x=y) /\ P f x') <=> l x')`] THEN 
REWRITE_TAC[ MESON[VSUM_DIS2; SUM_DIS2]` ~(x = y) /\x' = vsum {x, y} ff /\ l /\ 
sum {x, y} f = &1 <=> ~(x = y) /\ x' = ff x + ff y /\ l /\ f x + f y = &1 `] THEN 
REWRITE_TAC[ MESON[]` (!w. w = x \/ w = y ==> &0 <= f w) <=> &0 <= f x /\ &0 <= f y`] 
THEN ONCE_REWRITE_TAC[ GSYM (MESON[]`  ~(x = y) ==> (!x'. (?f. P f x') <=> l x') <=>
  ~(x = y) ==> (!x'. (?f. ~(x=y) /\ P f x') <=> l x')`)] THEN 
REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[ TRUONG_LEMMA]);;

let LE_OF_ZPGPXNN = prove(` ! a b v v1 v2 . &0 <= a /\ &0 <= b /\ a + b = &1 /\
 v = a % v1 + b % v2  ==> dist ( v,v1) + dist (v,v2) = dist(v1,v2)`, 
SIMP_TAC[dist; REAL_ARITH ` a + b = &1 <=> b = &1 - a `] THEN 
REWRITE_TAC[VECTOR_ARITH ` (a % v1 + (&1 - a) % v2) - v1 = ( a - &1 )%( v1 - v2)`] THEN 
REWRITE_TAC[VECTOR_ARITH` (a % v1 + (&1 - a) % v2) - v2 = a % ( v1 - v2) `] THEN 
SIMP_TAC[NORM_MUL; GSYM REAL_ABS_REFL] THEN REWRITE_TAC[ REAL_ARITH ` abs ( a - &1 )
 = abs ( &1 - a ) `] THEN REAL_ARITH_TAC);;

let LENGTH_EQUA = prove(` ! v v1 v2. v IN conv {v1,v2} ==> dist (v,v1) + 
 dist (v,v2) = dist (v1,v2) `,REWRITE_TAC[CONV_SET2; IN_ELIM_THM] THEN 
MESON_TAC[LE_OF_ZPGPXNN]);;

let simp_def2 = new_axiom`(!a b v0.
          aff_gt {a, b} {v0} =
          {x | ?ta tb t.
                   ta + tb + t = &1 /\ &0 < t /\ x = ta % a + tb % b + t % v0} /\
          aff_ge {a, b} {v0} =
          {x | ?ta tb t.
                   ta + tb + t = &1 /\
                   &0 <= t /\
                   x = ta % a + tb % b + t % v0}) /\
     (!x y z.
          conv0 {x, y, z} =
          {t | ?a b c.
                   a + b + c = &1 /\
                   &0 < a /\
                   &0 < b /\
                   &0 < c /\
                   t = a % x + b % y + c % z}) /\
     (!x y z.
          affine hull {x, y, z} =
          {t | ?a b c. a + b + c = &1 /\ t = a % x + b % y + c % z})/\
 (!v1 v2 v3.
          aff_lt {v2, v3} {v1} =
          {x | ?t2 t3 t1.
                   t2 + t3 + t1 = &1 /\
                   t1 < &0 /\
                   x = t2 % v2 + t3 % v3 + t1 % v1}) `;;

(* lemma 10. p 14 *)
let ZPGPXNN = prove(`!v1 v2 v. dist (v1,v2) < dist (v,v1) + dist (v,v2) ==> 
 ~(v IN conv {v1, v2})`,
REWRITE_TAC[MESON[] `a ==> ~ b <=> ~(a /\ b )`] THEN REWRITE_TAC[CONV_SET2; IN_ELIM_THM]
THEN MESON_TAC[LE_OF_ZPGPXNN; REAL_ARITH ` a < b ==> ~ ( a = b ) `]);;

let REDUCE_T2 = MESON[]` !P Q.
     (!v1 v2 v3 t1 t2 t3. P v1 t1 v2 t2 v3 t3 <=> P v2 t2 v1 t1 v3 t3) /\
     (!v1 v2 v3. Q v1 v2 v3 <=> Q v2 v1 v3) /\
     (!v1 v2 v3 t1 t2 t3.
          ~(t1 = &0 /\ t3 = &0) /\ P v1 t1 v2 t2 v3 t3 ==> Q v1 v2 v3)
     ==> (!v1 v2 v3 t1 t2 t3.
              ~(t1 = &0 /\ t2 = &0 /\ t3 = &0) /\ P v1 t1 v2 t2 v3 t3
              ==> Q v1 v2 v3)`;;

let VEC_PER2_3 = VECTOR_ARITH `((a:real^N ) + b + c = b + a + c)/\
   ( (a:real^N ) + b + c = c + b + a )`;;
let PER2_IN3 = SET_RULE `  {a,b,c} = {b,a,c} /\ {a,b,c} = {c,b,a}`;;

let REDUCE_T3 = MESON[]`!P Q.
     (!v1 v2 v3 t1 t2 t3. P v1 t1 v2 t2 v3 t3 <=> P v3 t3 v2 t2 v1 t1) /\
     (!v1 v2 v3. Q v1 v2 v3 <=> Q v3 v2 v1) /\
     (!v1 v2 v3 t1 t2 t3. ~(t1 = &0) /\ P v1 t1 v2 t2 v3 t3 ==> Q v1 v2 v3)
     ==> (!v1 v2 v3 t1 t2 t3.
              ~(t1 = &0 /\ t3 = &0) /\ P v1 t1 v2 t2 v3 t3 ==> Q v1 v2 v3)`;;


let SUB_PACKING = prove(`!sub s.
     packing s /\ sub SUBSET s
     ==> (!x y. x IN sub /\ y IN sub /\ ~(x = y) ==> &2 <= d3 x y)`,
REWRITE_TAC[ packing; GSYM d3] THEN SET_TAC[]);;


let PAIR_EQ_EXPAND =
 SET_RULE `{a,b} = {c,d} <=> a = c /\ b = d \/ a = d /\ b = c`;;

let IN_SET3 = SET_RULE ` x IN {a,b,c} <=> x = a \/ x = b \/ x = c `;;
let IN_SET4 = SET_RULE ` x IN {a,b,c,d} <=> x = a \/ x = b \/ x = c \/ x = d `;;

(* le 8. p 13 *)
let SGFCDZO = prove(`! (v1:real^3) v2 v3 t1 t2 t3.
     t1 % v1 + t2 % v2 + t3 % v3 = vec 0 /\
     t1 + t2 + t3 = &0 /\
     ~(t1 = &0 /\ t2 = &0 /\ t3 = &0)
     ==> collinear {v1, v2, v3}`, 
ONCE_REWRITE_TAC[MESON[]` a /\ b/\c <=> c /\ a /\ b `] THEN 
MATCH_MP_TAC REDUCE_T2 THEN 
CONJ_TAC THENL [SIMP_TAC[VEC_PER2_3; REAL_ADD_AC]; CONJ_TAC THENL 
  [SIMP_TAC[PER2_IN3]; MATCH_MP_TAC REDUCE_T3]] THEN 
CONJ_TAC THENL [SIMP_TAC[REAL_ADD_AC; VEC_PER2_3]; 
CONJ_TAC THENL [SIMP_TAC[PER2_IN3];  REWRITE_TAC[]]] THEN 
REPEAT GEN_TAC THEN REWRITE_TAC[collinear] THEN 
STRIP_TAC THEN EXISTS_TAC `v2 - (v3:real^3)` THEN 
ONCE_REWRITE_TAC[MESON[]` x IN s /\ y IN s <=> 
  ( x = y \/ ~ ( x = y))/\ x IN s /\ y IN s `] THEN 
REWRITE_TAC[IN_SET3] THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[MESON[]` (a \/ b) /\ c ==> d <=> (a /\ c ==> d) /\ (b /\ c ==> d)`] 
THEN CONJ_TAC THENL [DISCH_TAC THEN EXISTS_TAC `&0` THEN 
FIRST_X_ASSUM MP_TAC THEN MATCH_MP_TAC (MESON[]` (a ==> c) ==> a /\ b ==> c `) THEN 
MESON_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_EQ]; STRIP_TAC] THENL [

ASM_MESON_TAC[] ;

EXISTS_TAC ` t3  / t1 ` THEN ASM_SIMP_TAC[] THEN STRIP_TR THEN 
ONCE_REWRITE_TAC[MESON[VECTOR_MUL_LCANCEL]`
  ~(t1 = &0) /\ a ==> x = y <=> ~(t1 = &0) /\ a ==> t1 % x = t1 % y`] THEN 
REWRITE_TAC[VECTOR_MUL_ASSOC] THEN SIMP_TAC[REAL_DIV_LMUL] THEN 
ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN 
REWRITE_TAC[ VECTOR_ARITH ` ( a + b + (c:real^N) ) - vec 0 = vec 0 <=>
  a = -- ( b + c ) `; REAL_ARITH` a + b + c = &0 <=> a = -- ( b + c ) `] THEN 
SIMP_TAC[VECTOR_SUB_LDISTRIB] THEN 
MESON_TAC[VECTOR_ARITH ` --(t2 % v2 + t3 % v3) - --(t2 + t3) % v2 - 
  (t3 % v2 - t3 % v3) = vec 0`]; 

EXISTS_TAC ` ( -- t2 ) / t1 ` THEN ASM_SIMP_TAC[] THEN STRIP_TR THEN 
ONCE_REWRITE_TAC[MESON[VECTOR_MUL_LCANCEL]`
  ~(t1 = &0) /\ a ==> x = y <=> ~(t1 = &0) /\ a ==> t1 % x = t1 % y`] THEN 
REWRITE_TAC[VECTOR_MUL_ASSOC] THEN SIMP_TAC[REAL_DIV_LMUL] THEN 
ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN 
REWRITE_TAC[ VECTOR_ARITH ` ( a + b + (c:real^N) ) - vec 0 = vec 0 <=>
  a = -- ( b + c ) `; REAL_ARITH` a + b + c = &0 <=> a = -- ( b + c ) `] THEN 
SIMP_TAC[VECTOR_SUB_LDISTRIB] THEN 
MESON_TAC[VECTOR_ARITH ` --(t2 % v2 + t3 % v3) - --(t2 + t3) % v3 - 
 (--t2 % v2 - --t2 % v3) =  vec 0`];


EXISTS_TAC ` ( -- t3) / t1 ` THEN ASM_SIMP_TAC[] THEN STRIP_TR THEN 
ONCE_REWRITE_TAC[MESON[VECTOR_MUL_LCANCEL]`
  ~(t1 = &0) /\ a ==> x = y <=> ~(t1 = &0) /\ a ==> t1 % x = t1 % y`] THEN 
REWRITE_TAC[VECTOR_MUL_ASSOC] THEN SIMP_TAC[REAL_DIV_LMUL] THEN 
ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN 
REWRITE_TAC[ VECTOR_ARITH ` ( a + b + (c:real^N) ) - vec 0 = vec 0 <=>
  a = -- ( b + c ) `; REAL_ARITH` a + b + c = &0 <=> a = -- ( b + c ) `] THEN 
SIMP_TAC[VECTOR_SUB_LDISTRIB] THEN MESON_TAC[VECTOR_ARITH ` --(t2 + t3) % v2 
- --(t2 % v2 + t3 % v3) - (--t3 % v2 - --t3 % v3) = vec 0`];


ASM_MESON_TAC[];


EXISTS_TAC ` &1 ` THEN ASM_SIMP_TAC[VECTOR_MUL_LID];


EXISTS_TAC ` t2 / t1 ` THEN ASM_SIMP_TAC[] THEN STRIP_TR THEN 
ONCE_REWRITE_TAC[MESON[VECTOR_MUL_LCANCEL]`
  ~(t1 = &0) /\ a ==> x = y <=> ~(t1 = &0) /\ a ==> t1 % x = t1 % y`] THEN 
REWRITE_TAC[VECTOR_MUL_ASSOC] THEN SIMP_TAC[REAL_DIV_LMUL] THEN 
ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN 
REWRITE_TAC[ VECTOR_ARITH ` ( a + b + (c:real^N) ) - vec 0 = vec 0 <=>
  a = -- ( b + c ) `; REAL_ARITH` a + b + c = &0 <=> a = -- ( b + c ) `] THEN 
SIMP_TAC[VECTOR_SUB_LDISTRIB] THEN 
MESON_TAC[VECTOR_ARITH ` --(t2 + t3) % v3 - --(t2 % v2 + t3 % v3) -
   (t2 % v2 - t2 % v3) = vec 0`];

EXISTS_TAC ` -- &1 ` THEN ASM_MESON_TAC[VECTOR_ARITH ` v3 - v2 = -- &1 % (v2 - v3)`];


ASM_MESON_TAC[]]);;


(* le 2. p 6 *)
let RHUFIIB = prove( ` !x12 x13 x14 x23 x24 x34.
         rho x12 x13 x14 x23 x24 x34 * ups_x x34 x24 x23 =
         chi x12 x13 x14 x23 x24 x34 pow 2 +
         &4 * delta x12 x13 x14 x23 x24 x34 * x34 * x24 * x23 `,
REWRITE_TAC[rho; chi; delta; ups_x] THEN REAL_ARITH_TAC);;


let RIGHT_END_POINT = prove( `!x aa bb.
     (?a b. &0 < a /\ b = &0 /\ a + b = &1 /\ x = a % aa + b % bb) <=> x = aa`,
REPEAT GEN_TAC THEN EQ_TAC THENL [STRIP_TR THEN 
REWRITE_TAC[ MESON[REAL_ARITH `b = &0 /\ a + b = &1 <=> b= &0 /\ a = &1 `]`
   b = &0 /\ a + b = &1 /\ P a b  <=>  b = &0 /\ a = &1 /\ P (&1 ) ( &0 ) `] THEN 
MESON_TAC[VECTOR_ARITH ` &1 % aa + &0 % bb = aa `];
DISCH_TAC  THEN EXISTS_TAC ` &1 ` THEN EXISTS_TAC ` &0 ` THEN 
REWRITE_TAC[REAL_ARITH ` &0 < &1 /\ &1 + &0 = &1 `] THEN 
ASM_MESON_TAC[VECTOR_ARITH ` &1 % aa + &0 % bb = aa `]]);;

let LEFT_END_POINT = prove(` !x aa bb.
     (?a b. a = &0 /\ &0 < b /\ a + b = &1 /\ x = &0 % aa + &1 % bb)
  <=> x = bb `,
REWRITE_TAC[VECTOR_ARITH ` &0 % aa + &1 % bb = bb `] THEN 
MESON_TAC[REAL_ARITH ` &0 = &0 /\ &0 < &1 /\ &0 + &1 = &1 `]);;


let CONV_CONV0 = prove(`! x a b. x IN conv {a,b} <=> x = a \/ x = b \/ x IN conv0 {a,b} `,
REWRITE_TAC[CONV_SET2; CONV0_SET2; IN_ELIM_THM] THEN 
REWRITE_TAC[REAL_ARITH ` &0 <= a <=> a = &0 \/ &0 < a `] THEN 
KHANANG THEN REWRITE_TAC[EXISTS_OR_THM] THEN 
SIMP_TAC[MESON[REAL_ARITH ` ~(a = &0 /\ b = &0 /\ a + b = &1)`]`
  ~(a = &0 /\ b = &0 /\ a + b = &1 /\ las )` ] THEN 
REWRITE_TAC[MESON[REAL_ARITH ` a = &0 /\ a + b = &1 <=> a = &0 /\ b = &1 `]`
  a = &0 /\ &0 < b /\ a + b = &1 /\ x = a % aa + b % ba <=>
     a = &0 /\ &0 < b /\ a + b = &1 /\ x = &0 % aa + &1 % ba`] THEN 
MESON_TAC[ RIGHT_END_POINT; LEFT_END_POINT]);;




let CON3_SUB_CONE3 = prove(` ! w1 v1 v2 v3. conv {v1, v2, v3} SUBSET cone w1 {v1,v2,v3}`,
REWRITE_TAC[CONV_SET3; cone; GSYM aff_ge_def; simp_def] THEN 
REWRITE_TAC[ SET_RULE ` {x | p x} SUBSET {x | q x} <=> ( ! x. p x ==> q x)`] THEN 
MESON_TAC[ REAL_ARITH ` &0 + a = a `; VECTOR_ARITH ` &0 % x + y = y `]);;



let QHSEWMI = prove (` !v1 v2 v3 w1 w2.
         ~(conv {w1, w2} INTER conv {v1, v2, v3} = {}) /\
         ~(w1 IN conv {v1, v2, v3})
         ==> w2 IN cone w1 {v1, v2, v3}`,
REWRITE_TAC[INTER_DIF_EM_EX] THEN REPEAT GEN_TAC THEN REWRITE_TAC[CONV_CONV0] THEN 
STRIP_TAC THENL [ASM_MESON_TAC[]; 
ASM_MESON_TAC[CON3_SUB_CONE3;SET_RULE`a SUBSET b <=> (! x. x IN a ==> x IN b )`];
ASM_MESON_TAC[REWRITE_RULE[INTER_DIF_EM_EX] AFF_LE_CONE ]]);;


let GONTONG = REWRITE_TAC[REAL_ARITH ` ( a + b ) + c = a + b + c `];;

(* le 27. p 20 *)
let MAEWNPU = prove(` ?b c.
         !x12 x13 x14 x23 x24 x34.
             delta x12 x13 x14 x23 x24 x34 =
             --x12 * x34 pow 2 +
             b x12 x13 x14 x23 x24 * x34 +
             c x12 x13 x14 x23 x24 `,
REWRITE_TAC[delta; REAL_ARITH ` a - b = a + -- b `; 
  REAL_ARITH ` a * (b + c )= a * b + a * c ` ] THEN 
REWRITE_TAC[REAL_ARITH ` a * b * -- c = -- a * b * c /\ -- ( a * b ) = -- a * b `] THEN 
REWRITE_TAC[REAL_ARITH` x12 * x34 * x23 + x12 * x34 * x24 +
   --x12 * x34 * x34 = x12 * x34 * x23 + x12 * x34 * x24 +
   -- x12 * ( x34 pow 2 )  `] THEN 
REWRITE_TAC[REAL_ARITH ` ( a + b ) + c = a + b + c `] THEN 
REWRITE_TAC[REAL_ARITH ` a + b * c pow 2 + d = b * c pow 2 + a + d `] THEN 
ONCE_REWRITE_TAC[REAL_ARITH `a + b + c + d + e = a + d + b + c + e `] THEN 
REWRITE_TAC[REAL_ARITH ` a * b * c = ( a * b ) * c `] THEN 
REPLICATE_TAC 30 ( ONCE_REWRITE_TAC[REAL_ARITH ` a * x pow 2 + b * x + d + e
  = a * x pow 2 + b * x + e + d `] THEN GONTONG THEN REWRITE_TAC[ REAL_ARITH 
 ` a * x pow 2 + b * x + d * x  + e = a * x pow 2 + ( b  +  d)  * x  + e`]) THEN 
REPLICATE_TAC 50 ( ONCE_REWRITE_TAC[REAL_ARITH ` a * x pow 2 + b * x + d + e
  = a * x pow 2 + b * x + e + d `] THEN GONTONG THEN ONCE_REWRITE_TAC[ REAL_ARITH ` a * x pow 2 + b * x + (d * x) * h  + e
 = a * x pow 2 + ( b  +  d * h )  * x  + e`]) THEN 
EXISTS_TAC ` (\ x12 x13 x14 x23 x24. --x13 * x14 +
          --x23 * x24 +
          x13 * x24 +
          x14 * x23 +
          --x12 * x12 +
          x12 * x14 +
          x12 * x24 +
          x12 * x13 +
          x12 * x23 ) ` THEN 
EXISTS_TAC ` (\ x12 x13 x14 x23 x24. (x14 * x23) * x12 +
         (x14 * x23) * x13 +
         (--x14 * x23) * x14 +
         (--x14 * x23) * x23 +
         (x14 * x23) * x24 +
         (--x12 * x13) * x23 +
         (--x12 * x14) * x24 +
         (x13 * x24) * x12 +
         (--x13 * x24) * x13 +
         (x13 * x24) * x14 +
         (x13 * x24) * x23 +
         (--x13 * x24) * x24 ) ` THEN 
SIMP_TAC[]);;

(* ----new ------- *)

let DELTA_COEFS = new_specification ["b_coef"; "c_coef"] MAEWNPU;;


let DELTA_X34 = prove(` !x12 x13 x14 x23 x24 x34.
     delta x12 x13 x14 x23 x24 x34 =
     --x12 * x34 pow 2 +
     (--x13 * x14 +
      --x23 * x24 +
      x13 * x24 +
      x14 * x23 +
      --x12 * x12 +
      x12 * x14 +
      x12 * x24 +
      x12 * x13 +
      x12 * x23) *
     x34 +
     (x14 * x23) * x12 +
     (x14 * x23) * x13 +
     (--x14 * x23) * x14 +
     (--x14 * x23) * x23 +
     (x14 * x23) * x24 +
     (--x12 * x13) * x23 +
     (--x12 * x14) * x24 +
     (x13 * x24) * x12 +
     (--x13 * x24) * x13 +
     (x13 * x24) * x14 +
     (x13 * x24) * x23 +
     (--x13 * x24) * x24`, REWRITE_TAC[delta] THEN REAL_ARITH_TAC);;


let C_COEF_FORMULA = prove(`! x12 x13 x14 x23 x24. c_coef x12 x13 x14 x23 x24
  = (x14 * x23) * x12 +
         (x14 * x23) * x13 +
         (--x14 * x23) * x14 +
         (--x14 * x23) * x23 +
         (x14 * x23) * x24 +
         (--x12 * x13) * x23 +
         (--x12 * x14) * x24 +
         (x13 * x24) * x12 +
         (--x13 * x24) * x13 +
         (x13 * x24) * x14 +
         (x13 * x24) * x23 +
         (--x13 * x24) * x24`, MP_TAC DELTA_COEFS THEN 
NHANH (MESON[]` (!x12 x13 x14 x23 x24 x34. p x12 x13 x14 x23 x24 x34)
  ==> (! x12 x13 x14 x23 x24. p x12 x13 x14 x23 x24 (&0) ) `) THEN 
REWRITE_TAC[DELTA_X34] THEN 
REWRITE_TAC[REAL_ARITH ` &0 pow 2 = &0 `; REAL_MUL_RZERO; REAL_ADD_LID] THEN 
SIMP_TAC[]);;

let BC_DEL_FOR = prove(` ! x12 x13 x14 x23 x24. b_coef x12 x13 x14 x23 x24 =
  --x13 * x14 +
          --x23 * x24 +
          x13 * x24 +
          x14 * x23 +
          --x12 * x12 +
          x12 * x14 +
          x12 * x24 +
          x12 * x13 +
          x12 * x23 /\ 
  c_coef x12 x13 x14 x23 x24 =
         (x14 * x23) * x12 +
         (x14 * x23) * x13 +
         (--x14 * x23) * x14 +
         (--x14 * x23) * x23 +
         (x14 * x23) * x24 +
         (--x12 * x13) * x23 +
         (--x12 * x14) * x24 +
         (x13 * x24) * x12 +
         (--x13 * x24) * x13 +
         (x13 * x24) * x14 +
         (x13 * x24) * x23 +
         (--x13 * x24) * x24 `, REWRITE_TAC[C_COEF_FORMULA] THEN 
MP_TAC DELTA_COEFS THEN NHANH (MESON[]` (!x12 x13 x14 x23 x24 x34. 
p x12 x13 x14 x23 x24 x34)
  ==> (! x12 x13 x14 x23 x24. p x12 x13 x14 x23 x24 (&1) ) `) THEN 
REWRITE_TAC[DELTA_X34; C_COEF_FORMULA] THEN 
REWRITE_TAC[REAL_ARITH ` a + b + c = a + b' + c <=> b = b' `] THEN 
SIMP_TAC[REAL_RING` a * &1 = a `]);;

let AGBWHRD = prove(` !x12 x13 x14 x23 x24 x12 x13 x14 x23 x24.
         b_coef x12 x13 x14 x23 x24 pow 2 +
         &4 * x12 * c_coef x12 x13 x14 x23 x24 =
         ups_x x12 x23 x13 * ups_x x12 x24 x14`, REWRITE_TAC[BC_DEL_FOR; ups_x] THEN 
REAL_ARITH_TAC);;


let COLLINEAR_EX = prove(` ! x y (z:real^3) . collinear {x,y,z} <=> ( ? a b c. a + b + c = &0 /\ ~ ( a = &0 /\
b = &0 /\ c = &0 ) /\ a % x + b % y + c % z = vec 0 ) `,
REWRITE_TAC[collinear] THEN 
REPEAT GEN_TAC THEN 
STRIP_TR THEN 
EQ_TAC THENL [
NHANH (SET_RULE` (!x' y'. x' IN {x, y, z} /\ y' IN {x, y, z} ==> P x' y' )
    ==> P x y /\ P x z `) THEN 
STRIP_TR THEN 
DISJ_CASES_TAC (MESON[]` c = &0 /\ c' = &0 \/ ~( c = &0 /\ c' = &0  ) `) THENL [
ASM_SIMP_TAC[VECTOR_ARITH ` x - y = &0 % t <=> y = x`] THEN 
DISCH_TAC THEN 
EXISTS_TAC ` &1 ` THEN EXISTS_TAC ` &1 ` THEN 
EXISTS_TAC ` -- &2 ` THEN 
REWRITE_TAC[REAL_ARITH ` &1 + &1 + -- &2 = &0 /\
 ~(&1 = &0 /\ &1 = &0 /\ -- &2 = &0)`; VECTOR_ARITH` &1 % x + &1 % x + 
  -- &2 % x = vec 0`];



NHANH (MESON[VECTOR_MUL_LCANCEL]` x = c % u /\
  y  = c' % u ==> c' % x = c' % (c % u) /\ c % y = c % c' % u `) THEN 
REWRITE_TAC[VECTOR_ARITH ` x = c' % c % u /\ y = c % c' % u <=>
   x = y /\ y = c % c' % u`] THEN 
REWRITE_TAC[VECTOR_ARITH ` c' % (x - y) = c % (x - z) <=> (c - c' ) % x + c' % y +
  -- c % z = vec 0 `] THEN 
ASM_MESON_TAC[REAL_ARITH ` (( c - b ) + b + -- c = &0 ) /\ (~( c = &0 ) 
   <=> ~( -- c = &0 ))`]];REWRITE_TAC[GSYM collinear] THEN MESON_TAC[SGFCDZO]]);;


let MAX_REAL_LESS_EX = prove(`!x y a. max_real x y <= a <=> x <= a /\ y <= a`,
REWRITE_TAC[max_real; COND_EXPAND; COND_ELIM_THM;COND_RAND; COND_RATOR] THEN 
REPEAT GEN_TAC THEN 
MESON_TAC[REAL_ARITH ` (~ ( b < a ) /\ b <= c ==> a <= c)`;  REAL_ARITH ` a < b /\ b <= c ==> a <= c `]);;


let MAX_REAL3_LESS_EX = prove(`! x y z a. max_real3 x y z <= a <=> x <= a /\ 
y <= a /\ z <= a `, REWRITE_TAC[max_real3; MAX_REAL_LESS_EX] THEN MESON_TAC[]);;


MESON[]` (!x y z.
          (P x y z <=> P y x z) /\
          (P x y z <=> P x z y) /\
          (Q x y z <=> Q y x z) /\
          (Q x y z <=> Q x z y)) /\
     (!x y z. P x y z ==> Q x y z)
     ==> (!x y z. P x y z ==> Q x y z /\ Q y x z /\ Q z x y)`;;
(* ========== *)

let UPS_X_SYM = prove(` ! x y z. ups_x x y z = ups_x y x z /\
  ups_x x y z = ups_x x z y `, REWRITE_TAC[ups_x] THEN REAL_ARITH_TAC);;

let PER_MUL3 = REAL_ARITH ` a*b*c = b * a * c /\ a *b *c = a * c * b `;;

let ETA_X_SYM = prove(` ! x y z. &0 <= x /\ &0 <= y /\ &0 <= z /\ &0 <= ups_x x y z ==>
  eta_x x y z = eta_x y x z /\ eta_x x y z = eta_x x z y `,
REWRITE_TAC[eta_x] THEN 
NHANH (MESON[UPS_X_SYM]` &0 <= ups_x x y z ==> &0 <= ups_x y x z 
  /\ &0 <= ups_x x z y `) THEN 
NHANH (MESON[REAL_LE_MUL]`&0 <= x /\ &0 <= y /\ &0 <= z /\ las ==> 
  &0 <= x * y * z`) THEN 
PHA THEN NHANH (MESON[REAL_LE_DIV; REAL_ARITH ` a * b * c = b * a * c 
  /\ a * b * c = a * c * b `]`
  &0 <= ups_x x y z /\ &0 <= aa /\ &0 <= bb /\ &0 <= x * y * z
     ==> &0 <= (x * y * z) / ups_x x y z /\
         &0 <= (y * x * z) / aa /\
         &0 <= (x * z * y) / bb`) THEN 
SIMP_TAC[SQRT_INJ] THEN 
MESON_TAC[UPS_X_SYM; PER_MUL3]);;

let ETA_Y_SYM = prove(` ! x y z. &0 <= ups_x (x * x) (y * y) (z * z) ==>
  eta_y x y z = eta_y y x z /\ eta_y x y z = eta_y x z y `,
REWRITE_TAC[eta_y] THEN REPEAT LET_TAC THEN MESON_TAC[ETA_X_SYM; REAL_LE_SQUARE]);;



let ETA_Y_SYMM = MESON[UPS_X_SYM; ETA_Y_SYM]` ! x y z. &0 <= ups_x (x * x) (y * y) (z * z)
   ==> eta_y x y z = eta_y x z y /\
         eta_y x y z = eta_y y x z /\
         eta_y x y z = eta_y z x y /\
         eta_y x y z = eta_y y z x /\
         eta_y x y z = eta_y z y x`;;


let IMPLY_POS = prove(`! x y z . &0 <= ups_x (x * x) (y * y) (z * z) ==>
  &0 <= ((z * z) * (x * x) * y * y) / ups_x (z * z) (x * x) (y * y) /\ 
  &0 <= ((x * x) * (y * y) * z * z) / ups_x (x * x) (y * y) (z * z) /\
  &0 <= ((y * y) * (z * z) * x * x) / ups_x (y * y) (z * z) (x * x) `, MP_TAC
 REAL_LE_SQUARE THEN MP_TAC REAL_LE_MUL THEN MESON_TAC[UPS_X_SYM; REAL_LE_DIV]);;

let POW2_COND = MESON[REAL_ABS_REFL; REAL_LE_SQUARE_ABS]` ! a b. &0 <= a /\ &0 <= b ==> 
( a <= b <=> a pow 2 <= b pow 2 ) `;;


let TRUONGG = prove(`! x y z. &0 < ups_x_pow2 z x y ==> 
 ((z * z) * (x * x) * y * y) / ups_x (z * z) (x * x) (y * y) -
    z pow 2 / &4 = ( z pow 2 * (( z pow 2 - x pow 2 - y pow 2 ) pow 2 )) 
   / (&4 * ups_x_pow2 z x y )`,
REWRITE_TAC[ups_x; ups_x_pow2] THEN CONV_TAC REAL_FIELD);;

let RE_TRUONGG = REWRITE_RULE[GSYM ups_x_pow2] TRUONGG;;

let HVXIKHW = prove(` !x y z.
         &0 <= x /\ &0 <= y /\ &0 <= z /\ &0 < ups_x_pow2 x y z
         ==> max_real3 x y z / &2 <= eta_y x y z`,
REWRITE_TAC[REAL_ARITH` a / &2 <= b <=> a <= &2 * b `; MAX_REAL3_LESS_EX] THEN 
REWRITE_TAC[eta_x; ups_x_pow2] THEN 
NHANH (REAL_ARITH` &0 < a ==> &0 <= a `) THEN 
DAO THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[MESON[ETA_Y_SYMM]` &0 <= ups_x (x * x) (y * y) (z * z) /\ las
 ==> z <= &2 * eta_y x y z /\ x <= &2 * eta_y x y z /\ y <= &2 * eta_y x y z 
  <=> &0 <= ups_x (x * x) (y * y) (z * z) /\ las
 ==> z <= &2 * eta_y z x y /\ x <= &2 * eta_y x y z /\ y <= &2 * eta_y y z x`] THEN 
REWRITE_TAC[eta_y] THEN CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[eta_x] 
THEN NHANH (SPEC_ALL IMPLY_POS) THEN 
NHANH (SPEC_ALL (prove(` ! a b x y. &0 <= a / b /\ &0 <= x /\ &0 <= y ==>
   &0 <=  &2 * sqrt ( a/b) /\ &0 <= &2 * sqrt x /\ &0 <= &2 * sqrt y `,
REWRITE_TAC[REAL_ARITH ` &0 <= &2 * a <=> &0 <= a `] THEN 
SIMP_TAC[SQRT_WORKS]))) THEN SIMP_TAC[POW2_COND] THEN 
REWRITE_TAC[REAL_ARITH ` x <= ( &2 * y ) pow 2 <=> x / &4 <= y pow 2 `] THEN 
SIMP_TAC[ SQRT_POW_2] THEN REWRITE_TAC[ GSYM ups_x_pow2] THEN 
REWRITE_TAC[REAL_FIELD` a / b <= c <=> &0 <= c - a / b `] THEN 
SIMP_TAC[ups_x_pow2; UPS_X_SYM; RE_TRUONGG] THEN DAO THEN 
MATCH_MP_TAC (MESON[]` (a4 ==> l) ==> (a1/\a2/\a3/\a4/\a5) ==> l `) THEN 
MP_TAC REAL_LE_SQUARE THEN MP_TAC REAL_LE_MUL THEN MP_TAC REAL_LE_DIV THEN 
REWRITE_TAC[GSYM REAL_POW_2] THEN MESON_TAC[REAL_ARITH ` &0 < a ==> &0 <= &4 * a `]);;


let EXISTS_INV = REAL_FIELD` ~( a = &0 ) <=> a * &1 / a = &1 /\ &1 / a * a = &1 `;;


let MIDDLE_POINT = prove(` ! x y (z:real^3) . collinear {x,y,z} ==> x IN conv {y,z} \/ 
y IN conv {x,z} \/  z IN conv {x,y} `, REWRITE_TAC[COLLINEAR_EX] THEN REPEAT 
GEN_TAC THEN 
MATCH_MP_TAC (prove(`(!(a:real) (b:real) (c:real). P a b c <=> P (--a) (--b) (--c)) /\
   ((?a b c. &0 <= a /\ P a b c) ==> l) ==>  ( ? a b c. P a b c ) ==> l `,
 DISCH_TAC THEN ASM_MESON_TAC[REAL_ARITH ` ! a. a <= &0 \/ &0 <= a`;
   REAL_ARITH ` a <= &0 <=> &0 <= -- a `])) THEN 
CONJ_TAC THENL [MESON_TAC[REAL_ARITH` a = &0 <=> -- a = &0 `; REAL_ARITH ` a + b + c = &0
  <=> --a + --b + --c = &0`; VECTOR_ARITH ` a % x + b % y + c % z = vec 0
  <=> --a % x + --b % y + --c % z = vec 0 `]; STRIP_TAC] THEN 
DISJ_CASES_TAC (REAL_ARITH ` &0 < b \/ b <= &0`) THENL
[STRIP_TR THEN REWRITE_TAC[VECTOR_ARITH ` a + b + c % z = vec 0 <=>
  --c % z = a + b `] THEN 
NHANH (MESON[VECTOR_MUL_LCANCEL]` a % x = y ==> (&1 / a) % a % x = &1 / a % y `) THEN 
REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN 
REWRITE_TAC[MESON[]` a1/\a2/\a3/\a4/\a5 ==> l <=> a1 /\ a5 /\ a2 ==>
  a3/\a4 ==> l `] THEN 
NHANH (REAL_FIELD ` &0 <= a /\ &0 < b /\ a + b + c = &0 ==> 
  a / ( -- c ) + b /( -- c ) = &1 /\ ~ ( -- c = &0 )/\ &0 < -- c `) THEN 
SIMP_TAC[EXISTS_INV] THEN 
ONCE_REWRITE_TAC[MESON[POS_EQ_INV_POS]` a /\ &0 < c <=> a /\ &0 < &1 / c `] THEN 
REWRITE_TAC[VECTOR_MUL_LID; CONV_SET2; IN_ELIM_THM; GSYM (REAL_ARITH` a / b =
   &1 / b * a `)] THEN 
ONCE_REWRITE_TAC[REAL_ARITH` a / b = &1 / b * a `] THEN 
MP_TAC (GEN_ALL (MESON[REAL_ARITH`( a * &1 = a ) /\ ( &0 < a ==> &0 <= a )`; 
 REAL_LE_MUL]` &0 < &1 / c * &1 /\ ( &0 <= a \/ &0 < a ) ==> &0 <= &1 / c * a `)) THEN 
MESON_TAC[]; STRIP_TR THEN 
NHANH (MESON[REAL_ARITH` &0 <= c \/ c <= &0`]` a + b + v = &0 ==>
  &0 <= v \/ v <= &0 `) THEN 
REWRITE_TAC[MESON[]` a1/\(a2 /\ (aa\/ bb))/\ dd <=>
  (aa\/bb) /\ a1/\a2/\dd`] THEN SPEC_TAC (`a:real`, `a:real`) THEN 
SPEC_TAC (`b:real`, `b:real`) THEN SPEC_TAC (`c:real`, `c:real`) THEN 
KHANANG THEN REWRITE_TAC[(prove( `&0 <= c /\ &0 <= a /\ a + b + c = &0 /\
 ~(a = &0 /\ b = &0 /\ c = &0) /\ a % x + b % y + c % z = vec 0 /\
 b <= &0 <=> --a <= &0 /\ &0 <= --b /\ --b + --c + --a = &0 /\
 ~(--b = &0 /\ --c = &0 /\ --a = &0) /\ --b % y + --c % z + -- a % x = vec 0 /\
 --c <= &0`, MESON_TAC[
REAL_ARITH ` (a = &0 <=> --a = &0) /\ ( b <= &0 <=> &0 <= -- b ) /\
     (&0 <= a <=> --a <= &0) /\
     (a + b + c = &0 <=> --b + --c + -- a = &0)`;
VECTOR_ARITH` a % x + b % y + c % z = vec 0 <=> 
 --b % y + --c % z + --a % x = vec 0 `]))] THEN 
REWRITE_TAC[MESON[]` a \/ b ==> c <=> (a ==> c) /\(b==>c)`] THEN 
REWRITE_TAC[MESON[REAL_ARITH `&0 <= a <=> a = &0 \/ &0 < a `]`
  c <= &0 /\ &0 <= a /\ l <=> ( a = &0 \/ &0 < a ) /\ c <= &0 /\ l`] THEN 
KHANANG THEN 
REWRITE_TAC[MESON[REAL_ARITH `a = &0 /\ c <= &0 /\ a + b + c = &0 /\ b <= &0
     ==> a = &0 /\ b = &0 /\ c = &0`]`a = &0 /\      c <= &0 /\
      a + b + c = &0 /\ ~(a = &0 /\ b = &0 /\ c = &0) /\a2/\ b <= &0 <=> F `] THEN 
NHANH (MESON[REAL_FIELD ` &0 < a /\
         a + b + c = &0 ==> -- b / a + -- c / a = &1 `]`&0 < a /\      c <= &0 /\
      a + b + c = &0 /\ l ==> --b / a + --c / a = &1 `) THEN 
REWRITE_TAC[VECTOR_ARITH `  a % x + b % y + c % z = vec 0 <=>
  a % x = -- b % y + -- c % z `] THEN 
NHANH (MESON[VECTOR_MUL_LCANCEL]` a % x = y ==> &1 / a % a % x = &1 / a % y `) THEN 
REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; REAL_ARITH ` &1 / a * b 
  = b / a `;VECTOR_MUL_LID ] THEN PHA THEN 
PURE_ONCE_REWRITE_TAC[MESON[REAL_FIELD ` &0 < a ==> a / a = &1`]`
   &0 < a /\ P ( a / a) <=> &0 < a /\ P ( &1 ) `] THEN 
REWRITE_TAC[VECTOR_MUL_LID ] THEN 
REWRITE_TAC[MESON[SET_RULE ` {a,b} = {b,a}`]` y IN conv {x, z} \/ z IN conv {x, y}
  <=> y IN conv {z,x} \/ z IN conv {x,y} `] THEN 
REWRITE_TAC[CONV_SET2; IN_ELIM_THM] THEN 
REWRITE_TAC[ REAL_ARITH ` a <= &0 <=> &0 <= -- a `] THEN 
MESON_TAC[REAL_LE_DIV; REAL_ARITH ` &0 < a ==> &0 <= a `]]);;


let IN_CONV_COLLINEAR = prove(` ! (v:real^3) v1 v2. v IN conv {v1,v2} ==> 
collinear {v,v1,v2} `, REWRITE_TAC[COLLINEAR_EX] THEN 
REWRITE_TAC[COLLINEAR_EX; CONV_SET2; IN_ELIM_THM] THEN 
REWRITE_TAC[VECTOR_ARITH ` v = a % v1 + b % v2 <=> 
   &1 % v + -- a % v1 + -- b % v2 = vec 0 `] THEN 
MESON_TAC[REAL_ARITH `~ ( &1 = &0 ) /\ (a + b = &1 <=> &1 + --a + --b = &0 )`]);;

let COLLINERA_AS_IN_CONV2 = prove(` ! x y (z:real^3) . collinear {x,y,z} <=> 
x IN conv {y,z} \/ 
y IN conv {x,z} \/  z IN conv {x,y}`, 
MESON_TAC[PER_SET3; IN_CONV_COLLINEAR; MIDDLE_POINT]);;


let LENGTH_EQ_EX = prove(`!v v1 v2.
     dist (v1,v) + dist (v,v2) = dist (v1,v2) <=>
     ~(dist (v1,v2) < dist (v1,v) + dist (v,v2))`,
REPEAT GEN_TAC THEN 
REWRITE_TAC[REAL_ARITH ` ~( a < b) <=> b <= a `] THEN 
EQ_TAC THENL [REAL_ARITH_TAC; 
NHANH (MESON[DIST_TRIANGLE]` dist (v1,v) + dist (v,v2) <= dist (v1,v2)
  ==> dist(v1,v2) <= dist (v1,v) + dist (v,v2)`) THEN 
REAL_ARITH_TAC]);;


let BETWEEN_IMP_IN_CONVEX_HULL = new_axiom` !v v1 v2. dist(v1,v) + dist(v,v2) = 
dist(v1,v2)
 ==> (?a b. &0 <= a /\ &0 <= b /\ a + b = &1 /\  v = a % v1 + b % v2)`;;
(* HARRISON have proved this lemma as following, but it must be loaded after convec.ml *)
(*   let BETWEEN_IFF_IN_CONVEX_HULL = prove
  (`!v v1 v2:real^N.
         dist(v1,v) + dist(v,v2) = dist(v1,v2) <=> v IN convex hull {v1,v2}`,
   REPEAT GEN_TAC THEN ASM_CASES_TAC  `v1:real^N = v2` THENL
    [ASM_REWRITE_TAC[INSERT_AC; CONVEX_HULL_SING; IN_SING] THEN NORM_ARITH_TAC;
     REWRITE_TAC[CONVEX_HULL_2_ALT; IN_ELIM_THM] THEN EQ_TAC THENL
      [DISCH_TAC THEN EXISTS_TAC `dist(v1:real^N,v) / dist(v1,v2)` THEN
       ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; DIST_POS_LT] THEN CONJ_TAC
       THENL [FIRST_ASSUM(SUBST1_TAC o SYM) THEN NORM_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN
       EXISTS_TAC `dist(v1:real^N,v2)` THEN
       ASM_SIMP_TAC[VECTOR_MUL_ASSOC; VECTOR_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
                    REAL_DIV_LMUL; DIST_EQ_0] THEN
       FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DIST_TRIANGLE_EQ] o SYM) THEN
       FIRST_ASSUM(SUBST1_TAC o SYM) THEN
       REWRITE_TAC[dist; REAL_ARITH `(a + b) * &1 - a = b`] THEN
       VECTOR_ARITH_TAC;
       STRIP_TAC THEN ASM_REWRITE_TAC[dist] THEN
       REWRITE_TAC[VECTOR_ARITH `a - (a + b:real^N) = --b`;
                   VECTOR_ARITH `(a + u % (b - a)) - b = (&1 - u) % (a - b)`;
                   NORM_NEG; NORM_MUL; GSYM REAL_ADD_LDISTRIB] THEN
       REWRITE_TAC[NORM_SUB] THEN REPEAT(POP_ASSUM MP_TAC) THEN
       CONV_TAC REAL_FIELD]]);;

From this, your version follows easily:

 let BETWEEN_IMP_IN_CONVEX_HULL = prove
  (`!v v1 v2. dist(v1,v) + dist(v,v2) = dist(v1,v2)
              ==> (?a b. &0 <= a /\ &0 <= b /\ a + b = &1 /\
                         v = a % v1 + b % v2)`,
   REWRITE_TAC[BETWEEN_IFF_IN_CONVEX_HULL; CONVEX_HULL_2; IN_ELIM_THM] THEN
   REWRITE_TAC[CONJ_ASSOC]);;
*)



let PRE_HE = prove(` ! x y z. let p = ( x + y + z ) / &2 in
  ups_x_pow2 x y z = &16 * p * ( p - x ) * ( p - y ) * ( p - z ) `,
CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN 
REWRITE_TAC[ups_x_pow2; ups_x] THEN REAL_ARITH_TAC);;

let PRE_HER = prove(`!x y z.
     ups_x_pow2 x y z =
     &16 *
     (x + y + z) / &2 *
     ((x + y + z) / &2 - x) *
     ((x + y + z) / &2 - y) *
     ((x + y + z) / &2 - z)`, 
REWRITE_TAC[ups_x_pow2; ups_x] THEN REAL_ARITH_TAC);;


let TRIVIVAL_LE = prove(`!v1 v2 v3.
     ~(v2 = v3 /\ v1 = v2)
     ==> ~(dist (v1,v2) + dist (v1,v3) + dist (v2,v3) = &0)`,
SIMP_TAC[DE_MORGAN_THM; DIST_NZ] THEN 
NHANH (MESON[DIST_POS_LE]`&0 < dist (v2,v3) \/ &0 < dist (v1,v2) ==>
  &0 <= dist(v1,v3) `) THEN MP_TAC DIST_POS_LE THEN KHANANG THEN 
REWRITE_TAC[OR_IMP_EX] THEN 
NHANH (MESON[DIST_POS_LE]`&0 < dist (v2,v3) /\ &0 <= dist (v1,v3)
  ==> &0 <= dist(v1,v2) `) THEN 
SIMP_TAC[REAL_ARITH`( &0 < a /\ &0 <= b ) /\ &0 <= c ==> ~(c + b + a = &0 ) `] THEN 
NHANH (MESON[DIST_POS_LE]`&0 < dist (v1,v2) /\ &0 <= dist (v1,v3) ==>
  &0 <= dist(v2,v3) `) THEN 
MESON_TAC[REAL_ARITH ` &0 < a /\ &0 <= b /\ &0 <= c ==> ~( a + b + c = &0 ) `]);;



let MID_COND = prove(` ! v v1 v2. v IN conv {v1,v2} <=> dist(v1,v) + dist(v,v2)
 = dist(v1,v2) `, REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[LENGTH_EQUA; DIST_SYM];
REWRITE_TAC[CONV_SET2; IN_ELIM_THM] THEN 
MESON_TAC[DIST_SYM; BETWEEN_IMP_IN_CONVEX_HULL]]);;


(* lemma 9. p 13 *)
let FHFMKIY = prove(`!(v1:real^3) v2 v3 x12 x13 x23.
         x12 = dist (v1,v2) pow 2 /\
         x13 = dist (v1,v3) pow 2 /\
         x23 = dist (v2,v3) pow 2
         ==> (collinear {v1, v2, v3} <=> ups_x x12 x13 x23 = &0)`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[COLLINERA_AS_IN_CONV2]
 THEN REWRITE_TAC[REAL_ARITH ` x pow 2 = x * x `; GSYM ups_x_pow2] THEN 
REWRITE_TAC[PRE_HER] THEN REWRITE_TAC[REAL_ENTIRE] THEN 
ONCE_REWRITE_TAC[MESON[]`( v1 IN conv {v2, v3} \/ a \/ b <=> l ) <=> 
(v1 = v2 /\ v1 = v3 ) \/  ~(v1 = v2 /\ v1 = v3) ==> ( v1 IN conv {v2, v3} 
\/ a \/ b <=> l )`] THEN REWRITE_TAC[OR_IMP_EX] THEN 
SIMP_TAC[DIST_SYM; DIST_REFL; MESON[]` a= b/\ a= c <=> b = c /\ a= b`] THEN 
SIMP_TAC[SET_RULE ` {a,a} = {a} /\ a IN {a} `; CONV_SING;
   REAL_ARITH ` (&0 + &0 + &0)/ &2 = &0 `] THEN SIMP_TAC[ TRIVIVAL_LE; 
REAL_ARITH `~( &16 = &0) /\(~( a = &0) ==> ~( a / &2 = &0))`] THEN 
REWRITE_TAC[REAL_ARITH ` (a+ b + c ) / &2 - a = &0 <=> b + c = a `] THEN 
REWRITE_TAC[REAL_ARITH ` (a+ b + c ) / &2 - b = &0 <=> c + a = b  `] THEN 
REWRITE_TAC[REAL_ARITH ` (a+ b + c ) / &2 - c = &0 <=> a + b = c `] THEN 
REWRITE_TAC[MESON[SET_RULE `{a,b} = {b,a} `]`v2 IN conv {v1, v3} \/ v3 IN 
conv {v1, v2}  <=> v2 IN conv {v3,v1} \/ v3 IN conv {v1, v2}`] THEN 
REWRITE_TAC[MID_COND] THEN MESON_TAC[DIST_SYM]);;

(* le 11. p 14 *)
let FAFKVLR = new_axiom ` ? t1 t2 t3. ! v1 v2 v3 (v:real^3).
   v IN ( affine hull {v1,v2,v3} ) /\
   ~collinear {v1, v2, v3} 
             ==> v = t1 v1 v2 v3 v % v1 + t2 v1 v2 v3 v % v2 + t3 v1 v2 v3 v % v3 /\
                 t1 v1 v2 v3 v + t2 v1 v2 v3 v + t3 v1 v2 v3 v = &1 /\
                 (!ta tb tc. v = ta % v1 + tb % v2 + tc % v3
                    ==> ta = t1 v1 v2 v3 v /\
                        tb = t2 v1 v2 v3 v /\
                        tc = t3 v1 v2 v3 v )`;;

let equivalent_lemma = prove(` (?t1 t2 t3.
         !v1 v2 v3 (v:real^N).
             v IN affine hull {v1, v2, v3} /\ ~collinear {v1, v2, v3}
             ==> v =
                 t1 v1 v2 v3 v % v1 + t2 v1 v2 v3 v % v2 + t3 v1 v2 v3 v % v3 /\
                 t1 v1 v2 v3 v + t2 v1 v2 v3 v + t3 v1 v2 v3 v = &1 /\
                 (!ta tb tc.
                      v = ta % v1 + tb % v2 + tc % v3
                      ==> ta = t1 v1 v2 v3 v /\
                          tb = t2 v1 v2 v3 v /\
                          tc = t3 v1 v2 v3 v))  <=>
     
          ( !v1 v2 v3 (v:real^N).
             v IN affine hull {v1, v2, v3} /\ ~collinear {v1, v2, v3}
          ==> (?t1 t2 t3.
                   v = t1 % v1 + t2 % v2 + t3 % v3 /\
                   t1 + t2 + t3 = &1 /\
                   (!ta tb tc.
                        v = ta % v1 + tb % v2 + tc % v3
                        ==> ta = t1 /\ tb = t2 /\ tc = t3))) `,
REWRITE_TAC[GSYM SKOLEM_THM; LEFT_FORALL_IMP_THM; RIGHT_EXISTS_IMP_THM]);;

let lemma11 = REWRITE_RULE[equivalent_lemma] FAFKVLR;;
let COEFS = new_specification ["coef1"; "coef2"; "coef3"] FAFKVLR;;
let plane_3p = new_definition `plane_3p (a:real^3) b c =
         {x | ~collinear {a, b, c} /\
              (?ta tb tc. ta + tb + tc = &1 /\ x = ta % a + tb % b + tc % c)}`;;

let lem11 = REWRITE_RULE[simp_def2; IN_ELIM_THM] lemma11;;

let IN_CONV3_EQ = prove(`! (v:real^3) v1 v2 v3. ~collinear {v1,v2,v3} ==> (v IN conv {v1, v2, v3} <=> 
  v IN aff_ge {v1,v2} {v3} /\
  v IN aff_ge {v2,v3} {v1} /\ v IN aff_ge {v3,v1} {v2} )`, 
REWRITE_TAC[CONV_SET3; simp_def2; IN_ELIM_THM] THEN 
REPEAT GEN_TAC THEN DISCH_TAC THEN  EQ_TAC THENL [
MESON_TAC[REAL_ARITH` a + b + c = b + a + c /\ a + b + c = c + b + a `;
  VECTOR_ARITH `(a:real^N) + b + c = b + a + c /\ a + b + c = c + b + a `; lem11]; 
NHANH (MESON[]` (? a b c. P a b c /\ Q c /\ R a b c) /\ aa /\ bb ==>
   (? a b c. P a b c /\ R a b c) `) THEN 
FIRST_X_ASSUM MP_TAC THEN 
REWRITE_TAC[IMP_IMP] THEN 
REWRITE_TAC[MESON[]` ~a/\ b <=> b /\ ~ a `] THEN 
PHA THEN 
NHANH (SPEC_ALL lem11) THEN 
STRIP_TR THEN REWRITE_TAC[MESON[]` (v = w:real^N) /\ a <=> a /\ v = w `] THEN PHA THEN 
NHANH (MESON[VEC_PER2_3]` (!ta tb tc.
      v = ta % v1 + tb % v2 + tc % v3 ==> ta = t1 /\ tb = t2 /\ tc = t3) /\bbb/\
 v = ta''' % v1 + tb''' % v2 + t''' % v3 /\
 v = ta'' % v3 + tb'' % v1 + t'' % v2 /\
 v = ta' % v2 + tb' % v3 + t' % v1 /\
aa  ==> t' = t1 /\ t'' = t2 /\ t''' = t3 `) THEN 
MESON_TAC[]]);;


let IN_CONV03_EQ = prove(`! (v:real^3) v1 v2 v3. ~collinear {v1,v2,v3} ==> 
(v IN conv0 {v1, v2, v3} <=>   v IN aff_gt {v1,v2} {v3} /\
  v IN aff_gt {v2,v3} {v1} /\ v IN aff_gt {v3,v1} {v2} )`,
REWRITE_TAC[CONV_SET3; simp_def2; IN_ELIM_THM] THEN 
REPEAT GEN_TAC THEN DISCH_TAC THEN  EQ_TAC THENL [
MESON_TAC[REAL_ARITH` a + b + c = b + a + c /\ a + b + c = c + b + a `;
  VECTOR_ARITH `(a:real^N) + b + c = b + a + c /\ a + b + c = c + b + a `; lem11]; 
NHANH (MESON[]` (? a b c. P a b c /\ Q c /\ R a b c) /\ aa /\ bb ==>
   (? a b c. P a b c /\ R a b c) `) THEN 
FIRST_X_ASSUM MP_TAC THEN 
REWRITE_TAC[IMP_IMP] THEN 
REWRITE_TAC[MESON[]` ~a/\ b <=> b /\ ~ a `] THEN 
PHA THEN 
NHANH (SPEC_ALL lem11) THEN 
STRIP_TR THEN REWRITE_TAC[MESON[]` (v = w:real^N) /\ a <=> a /\ v = w `] THEN PHA THEN 
NHANH (MESON[VEC_PER2_3]` (!ta tb tc.
      v = ta % v1 + tb % v2 + tc % v3 ==> ta = t1 /\ tb = t2 /\ tc = t3) /\bbb/\
 v = ta''' % v1 + tb''' % v2 + t''' % v3 /\
 v = ta'' % v3 + tb'' % v1 + t'' % v2 /\
 v = ta' % v2 + tb' % v3 + t' % v1 /\
aa  ==> t' = t1 /\ t'' = t2 /\ t''' = t3 `) THEN 
MESON_TAC[]]);;


let AFFINE_SET_GEN_BY_TWO_POINTS = prove(`! a b. affine {x | ?ta tb. ta + tb = &1 /\ x = ta % a + tb % b}`,
REWRITE_TAC[affine; IN_ELIM_THM] THEN 
REPEAT GEN_TAC THEN 
STRIP_TAC THEN 
EXISTS_TAC ` u * ta + v * ta' ` THEN 
EXISTS_TAC ` u * tb + v * tb' ` THEN 
REWRITE_TAC[REAL_ARITH ` (u * ta + v * ta') + u * tb + v * tb' =
  u * (ta + tb) + v * (ta' + tb' ) `] THEN 
ASM_SIMP_TAC[REAL_ARITH ` a * &1 = a `] THEN 
CONV_TAC VECTOR_ARITH);;

let GENERATING_POINT_IN_SET_AFF = prove(` ! a b. {a,b} SUBSET {x | ?ta tb. 
ta + tb = &1 /\ x = ta % a + tb % b}`,REWRITE_TAC[SET2_SU_EX; IN_ELIM_THM]
THEN REPEAT GEN_TAC THEN 
MESON_TAC[REAL_ARITH` &0 + &1 = &1 /\ a + b = b + a`; VECTOR_ARITH `
  a = &0 % b + &1 % a /\ a = &1 % a + &0 % b `]);;


let AFF_2POINTS_INTERPRET = prove(`!a b. aff {a, b} = {x | ?ta tb. ta + tb = &1 /\ x = ta % a + tb % b}`,
REWRITE_TAC[aff; hull] THEN 
REPEAT GEN_TAC THEN 
REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN 
SIMP_TAC[INTERS_SUBSET; AFFINE_SET_GEN_BY_TWO_POINTS;
  GENERATING_POINT_IN_SET_AFF] THEN 
REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN 
REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERS; affine] THEN 
SET_TAC[]);;


let IN_AFF_GE_INTERPRET_TO_AFF_GT_AND_AFF = prove(` ! v v1 v2 v3 . 
v IN aff_ge {v1,v2} {v3} <=> v IN aff_gt {v1,v2} {v3} \/
  v IN aff {v1,v2} `,
REWRITE_TAC[simp_def2; AFF_2POINTS_INTERPRET; IN_ELIM_THM ] THEN 
REWRITE_TAC [REAL_ARITH ` &0 <= a <=> &0 < a \/ a = &0 `] THEN 
MESON_TAC[REAL_ARITH ` (&0 <= a <=> &0 < a \/ a = &0 )/\( a + &0 = a ) `;
  VECTOR_ARITH ` a + &0 % c = a `]);;

let DOWN_TAC = REPEAT (FIRST_X_ASSUM MP_TAC) THEN REWRITE_TAC[IMP_IMP] THEN PHA;;
let IMP_IMP_TAC = REWRITE_TAC[IMP_IMP] THEN PHA;;


let AFFINE_AFF_HULL = prove(` ! s. affine ( aff s ) `, 
REWRITE_TAC[aff; AFFINE_AFFINE_HULL]);;


let AFFINE_CONTAIN_LINE = prove(`! a b s. affine s /\ {a,b} SUBSET s ==>
 aff {a,b} SUBSET s `,
REWRITE_TAC[affine ; AFF_2POINTS_INTERPRET; IN_ELIM_THM] THEN SET_TAC[]);;

let VECTOR_SUB_DISTRIBUTE = VECTOR_ARITH ` ! a x y. a % x - a % y = a % ( x - y ) `;;


let CHANGE_SIDE = prove(` ~( a = &0 ) ==> ( x = a % y <=> ( &1 / a) % x = y )`,
MESON_TAC[ VECTOR_ARITH `  ( a * b ) % x = a % b % x `; VECTOR_MUL_LID;
  REAL_FIELD `~( a = &0 ) ==>  a * &1 / a = &1 `; VECTOR_MUL_LCANCEL]);;


let PRE_INVERSE_SUB = prove(` ! a b v w. {a, b} SUBSET aff {v, w} /\ ~(a = b)
 ==> {v, w} SUBSET aff {a, b}`, 
REWRITE_TAC[AFF_2POINTS_INTERPRET; SET2_SU_EX; IN_ELIM_THM] THEN 
REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (FIRST_X_ASSUM MP_TAC) THEN 
REWRITE_TAC[IMP_IMP] THEN PHA THEN 
NHANH (MESON[]` (a:real^N) = b /\ gg /\ a' = b' /\ ll ==> a - a' = b - b' `) THEN 
REWRITE_TAC[VECTOR_ARITH` (ta % v + tb % w) - (ta' % v + tb' % w) =
  ( ta - ta') % v + ( tb - tb' ) % w `] THEN 
PHA THEN REWRITE_TAC[MESON[]` a = &1 /\ b <=> b /\ a = &1 `] THEN PHA THEN 
NHANH (REAL_ARITH ` ta + tb = &1 /\ ta' + tb' = &1 ==> ta' - ta = tb - tb' `) THEN 
REWRITE_TAC[VECTOR_ARITH ` a + ( x - y ) % b = a - ( y - x) % b `] THEN 
REWRITE_TAC[MESON[]` a - b = ta % v - tb % w /\aa/\
   ta = tb <=> a - b = ta % v - ta % w /\ aa /\ ta = tb `] THEN 
ASM_CASES_TAC `(ta:real) = ta' ` THENL [ASM_SIMP_TAC[REAL_SUB_REFL; 
VECTOR_MUL_LZERO; VECTOR_SUB_RZERO; VECTOR_SUB_EQ] THEN MESON_TAC[]; ALL_TAC] THEN 
REWRITE_TAC[VECTOR_SUB_DISTRIBUTE] THEN FIRST_X_ASSUM MP_TAC THEN 
ONCE_REWRITE_TAC[REAL_ARITH` ~( a = b) <=> ~( a - b = &0 )`] THEN IMP_IMP_TAC THEN 
REWRITE_TAC[MESON[]` ~( a = b:real) /\ l <=> l /\ ~(a = b) `; MESON[]` 
a = d % b /\ l  <=> l /\  a = d % b `] THEN PHA THEN 
REWRITE_TAC[MESON[CHANGE_SIDE]` x = a % y /\ ~( a = &0 ) <=>  &1 / a % x = y /\
 ~( a = &0 )`] THEN NHANH (MESON[VECTOR_MUL_LCANCEL]` ta - ta' = tb' - tb /\
 a = b  /\ l ==> tb % a = tb % b /\ ta % a = ta % b `) THEN 
ONCE_REWRITE_TAC[MESON[]` a = (b:real^n) /\ l <=> l /\ a = b `] THEN PHA 
THEN REWRITE_TAC[GSYM VECTOR_SUB_DISTRIBUTE] THEN 
ONCE_REWRITE_TAC[VECTOR_ARITH` a = (b:real^N) /\ a1 = (b1:real^N) /\ a2 = 
  (b2:real^N) <=> a2 = b2 /\ a + a2 = b + b2 /\ a2 - a1 = b2 - b1 `] THEN 
REWRITE_TAC[VECTOR_ARITH` (ta % v + tb % w) - (ta % v - ta % w) = ( ta + tb ) % w `;
  VECTOR_ARITH` tb % v - tb % w + ta % v + tb % w = ( ta + tb ) % v `] THEN 
REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH` a - ( x % a - y % b ) = 
(&1 - x ) % a + y % b `] THEN REWRITE_TAC[VECTOR_ARITH` a % x - b % y + x = 
(a + &1 ) % x + --b % y `] THEN 
REWRITE_TAC[MESON[]` a = &1 /\ b = &1 /\ l <=> a = &1 /\ l /\b = &1 `] THEN 
DAO THEN MATCH_MP_TAC (MESON[]`( a1 /\a2/\a3/\a5 ==> l) ==> 
(a1/\a2/\a3/\a4/\a5/\a6   ==> l ) `) THEN PURE_ONCE_REWRITE_TAC[ MESON[]`
 a + b = &1 /\ P ( a + b ) <=> a + b = &1 /\  P (&1) `] THEN 
REWRITE_TAC[VECTOR_MUL_LID] THEN MESON_TAC[REAL_FIELD ` ~(ta - ta' = &0)
     ==> (tb * &1 / (ta - ta') + &1) + --(tb * &1 / (ta - ta')) = &1 /\ 
  &1 - ta * &1 / (ta - ta') + ta * &1 / (ta - ta') = &1 `]);;



let LEMMA5 = prove(
`!(a:real^N) b x. line x /\ {a, b} SUBSET x /\ ~(a = b) ==> x = aff {a, b}`,
REWRITE_TAC[line; GSYM aff] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN 
REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN ASM_SIMP_TAC[AFFINE_AFF_HULL; 
AFFINE_CONTAIN_LINE] THEN STRIP_TR THEN 
ABBREV_TAC ` (ki : bool ) = aff {(v:real^N), (w:real^N)} 
  SUBSET aff {(a:real^N), (b:real^N)}` THEN 
REWRITE_TAC[MESON[]` a/\b/\c ==> d <=> b ==> a/\c ==> d `] THEN SIMP_TAC[]
THEN DISCH_TAC THEN IMP_IMP_TAC THEN 
NHANH (MESON[PRE_INVERSE_SUB]`{a, b} SUBSET aff {v, w} /\ aa /\ ~(a = b) 
  ==> {v, w} SUBSET aff {a, b} `) THEN 
NHANH (MESON[AFFINE_AFF_HULL]` aa /\ v SUBSET aff {a, b} ==> affine (aff {a,b})`)
THEN DOWN_TAC THEN MESON_TAC[AFFINE_CONTAIN_LINE]);;

let RCEABUJ = LEMMA5;;



(* lemma 17 *)

let CDEUSDF = new_axiom `!va vb vc a b c.
     a = d3 vb vc /\ b = d3 va vc /\ c = d3 va vb /\ ~collinear {va, vb, vc}
     ==> (?p. p IN affine hull {va, vb, vc} /\
              (?c. !w. w IN {va, vb, vc} ==> c = dist (p,w)) /\
              (!p'. p' IN affine hull {va, vb, vc} /\
                    (?c. !w. w IN {va, vb, vc} ==> c = dist (p',w))
                    ==> p = p')) /\
         (let al_a =
              (a pow 2 * (b pow 2 + c pow 2 - a pow 2)) /
              (&2 * ups_x (a pow 2) (b pow 2) (c pow 2)) in
          let al_b =
              (b pow 2 * (a pow 2 + c pow 2 - b pow 2)) /
              (&2 * ups_x (a pow 2) (b pow 2) (c pow 2)) in
          let al_c =
              (c pow 2 * (a pow 2 + b pow 2 - c pow 2)) /
              (&2 * ups_x (a pow 2) (b pow 2) (c pow 2)) in
          al_a % va + al_b % vb + al_c % vc = circumcenter {va, vb, vc}) /\
         radV {va, vb, vc} = eta_y a b c`;;



prove(`!va vb vc a b c.
     a = d3 vb vc /\ b = d3 va vc /\ c = d3 va vb /\ ~collinear {va, vb, vc}
     ==> (?p. p IN affine hull {va, vb, vc} /\
              (?c. !w. w IN {va, vb, vc} ==> c = dist (p,w)) /\
              (!p'. p' IN affine hull {va, vb, vc} /\
                    (?c. !w. w IN {va, vb, vc} ==> c = dist (p',w))
                    ==> p = p'))`, NHANH (SPEC_ALL CDEUSDF) THEN SIMP_TAC[]);;

let TRUONG_WELL = prove(`! (va:real^3) vb vc. ~collinear {va, vb, vc}
     ==> (?p. p IN affine hull {va, vb, vc} /\
              (?c. !w. w IN {va, vb, vc} ==> c = dist (p,w)) /\
              (!p'. p' IN affine hull {va, vb, vc} /\
                    (?c. !w. w IN {va, vb, vc} ==> c = dist (p',w))
                    ==> p = p'))`,
MP_TAC (prove(`!va vb vc a b c.
     a = d3 vb vc /\ b = d3 va vc /\ c = d3 va vb /\ ~collinear {va, vb, vc}
     ==> (?p. p IN affine hull {va, vb, vc} /\
              (?c. !w. w IN {va, vb, vc} ==> c = dist (p,w)) /\
              (!p'. p' IN affine hull {va, vb, vc} /\
                    (?c. !w. w IN {va, vb, vc} ==> c = dist (p',w))
                    ==> p = p'))`, NHANH (SPEC_ALL CDEUSDF) THEN SIMP_TAC[])) THEN 
REWRITE_TAC[MESON[]`( !(va:real^3) vb vc a b c.
         a = d3 vb vc /\
         b = d3 va vc /\
         c = d3 va vb /\
         ~collinear {va, vb, vc} ==> P va vb vc ) ==> (! va vb vc.
  ~collinear {va, vb, vc} ==> P va vb vc )`]);;

let NGAY_MONG6 = MESON[TRUONG_WELL] `! va vb (vc:real^3). 
         ~collinear {va, vb, vc} ==> (?p. p IN affine hull {va, vb, vc} /\
                  (?c. !w. w IN {va, vb, vc} ==> c = dist (p,w))  ) `;;


let CIRCUMCENTER_PROPTIES = prove(`!va vb (vc:real^3).
     ~collinear {va, vb, vc}
     ==> circumcenter {va, vb, vc} IN affine hull {va, vb, vc} /\
(?c. !w. w IN {va, vb, vc}
                  ==> c = dist (circumcenter {va, vb, vc},w))`,
NHANH (SPEC_ALL NGAY_MONG6) THEN REWRITE_TAC[IN; 
circumcenter; EXISTS_THM] THEN SIMP_TAC[]);;






let SIMP_DOT_ALEM = prove(  `&0 < (b - a) dot x <=> x dot (a - b) < &0`,
SIMP_TAC[DOT_SYM] THEN 
REWRITE_TAC[ REAL_ARITH ` a < &0 <=> &0 < -- a `; GSYM DOT_RNEG] THEN 
REWRITE_TAC[VECTOR_ARITH ` -- ((a:real^N) - b) = b - a `]);;




let MONG7_ROI = prove(` ! p a (b:real^A). dist (p,a) = dist (p,b) <=> 
  (p - &1 / &2 % ( a + b )) dot ( a - b)  = &0 `,
REWRITE_TAC[ REAL_ARITH ` a = b <=> ~ ( a < b) /\ ~( b < a ) `; 
DIST_LT_HALF_PLANE] THEN 
REWRITE_TAC[VECTOR_ARITH` (p - &1 / &2 % (a + b)) dot (a - b)
  = &1 / &2 * ( (&2 % p - (a + b ) ) dot ( a- b ) )  `] THEN 
REWRITE_TAC[REAL_ARITH `( &1 / &2 * a < &0 <=> a < &0) /\ 
(&0 < &1 / &2 * a <=> &0 < a )`] THEN 
REWRITE_TAC[SIMP_DOT_ALEM] THEN 
SIMP_TAC[VECTOR_ARITH` (a - b) dot (c - d) = (b - a) dot (d - c)`; DOT_SYM; 
VECTOR_ADD_SYM] THEN MESON_TAC[]);;

let LEMMA26 = prove(`!v1 v2 (v3:real^3) p.
     ~collinear {v1, v2, v3} /\ p = circumcenter {v1, v2, v3}
     ==> (p - &1 / &2 % (v1 + v2)) dot (v1 - v2) = &0 /\
         (p - &1 / &2 % (v2 + v3)) dot (v2 - v3) = &0 /\
         (p - &1 / &2 % (v3 + v1)) dot (v3 - v1) = &0`,
NHANH (SPEC_ALL CIRCUMCENTER_PROPTIES) THEN 
NHANH (SET_RULE` (?c. !w. w IN {v1, v2, v3} ==> c = P w) ==> P v1 = P v2
  /\ P v2 = P v3 /\ P v3 = P v1 `) THEN 
SIMP_TAC[MONG7_ROI]);;

let POXDVXO = LEMMA26;;



let NOT_COLL_IMP_RADV_EQ_ETA_Y = MESON[prove(`!va vb vc a b c.
     a = d3 vb vc /\ b = d3 va vc /\ c = d3 va vb /\ ~collinear {va, vb, vc}
     ==> radV {va, vb, vc} = eta_y (d3 vb vc) (d3 va vc) (d3 va vb)`,
SIMP_TAC[CDEUSDF])]` 
  !va vb vc . ~collinear {va, vb, vc}
     ==> radV {va, vb, vc} = eta_y (d3 vb vc) (d3 va vc) (d3 va vb)`;;


 g ` ! x (y:real^N). collinear {x,y} `;;
e (REPEAT GEN_TAC THEN REWRITE_TAC[collinear]);;
e (EXISTS_TAC ` x -(y: real^N)`);;
e (ASM_SIMP_TAC[SET_RULE` a = b ==> {a,b,c} = {a,c} `]);;
e (REWRITE_TAC[IN_SET2]);;
e (REPEAT GEN_TAC);;
e (STRIP_TAC);;

e (ASM_SIMP_TAC[] THEN EXISTS_TAC ` &0 ` THEN CONV_TAC VECTOR_ARITH);;

e (ASM_SIMP_TAC[] THEN EXISTS_TAC ` &1 ` THEN CONV_TAC VECTOR_ARITH);;

e (ASM_SIMP_TAC[] THEN EXISTS_TAC ` -- &1 ` THEN CONV_TAC VECTOR_ARITH);;

e (ASM_SIMP_TAC[] THEN EXISTS_TAC ` &0 ` THEN CONV_TAC VECTOR_ARITH);;
let COLLINEAR2 = top_thm();;


let TWO_EQ_IMP_COL3 = prove(` ! (x:real^N) y z .  x = y ==> collinear {x, y, z} `,
STRIP_TR THEN SIMP_TAC[SET_RULE` a = b ==> {a,b,c} = {a,c} `; COLLINEAR2]);;


let NOT_CO_IMP_DIST_POS = prove(`! x y z. ~ collinear {x,y,z} ==> &0 < dist (x,y) `,
NHANH (MESON[TWO_EQ_IMP_COL3]` ~collinear {x, y, z} ==> ~( x= y) `) THEN 
SIMP_TAC[DIST_POS_LT]);;


let NOT_COLL_IMP_POS_SUM = prove( ` !x y z.
     ~collinear {x, y, z} ==> &0 < ( d3 x y + d3 y z + d3 z x) / &2 `,
NHANH (SPEC_ALL NOT_CO_IMP_DIST_POS) THEN 
NHANH (MESON[DIST_POS_LE]` ~collinear {x, y, z} ==>
  &0 <= dist (y,z) /\ &0 <= dist (z,x) `) THEN 
SIMP_TAC[d3] THEN REAL_ARITH_TAC);;

let PER_SET2 = SET_RULE ` {a,b} = {b,a} `;;


let COLLINEAR_AS_IN_CONV2 = MESON[PER_SET2; COLLINERA_AS_IN_CONV2]`! x y (z:real^3). collinear {x, y, z} <=>
 x IN conv {y, z} \/ y IN conv {z, x} \/ z IN conv {x, y}`;;

let COLLINEAR_IMP_POS_UPS2 = prove(` ! x y (z:real^3). ~ collinear {x,y,z} ==>
  &0 < ups_x_pow2 ( d3 x y ) ( d3 y z ) ( d3 z x ) `,
REWRITE_TAC[PRE_HER] THEN NHANH (SPEC_ALL NOT_COLL_IMP_POS_SUM ) THEN 
REWRITE_TAC[COLLINEAR_AS_IN_CONV2] THEN REWRITE_TAC[MID_COND] THEN 
REWRITE_TAC[LENGTH_EQ_EX] THEN REWRITE_TAC[DE_MORGAN_THM] THEN 
SIMP_TAC[d3] THEN REPEAT GEN_TAC THEN SIMP_TAC[
prove(` &0 < a ==> ( &0 < &16 * a * b <=> &0 < b ) `,
REWRITE_TAC[REAL_ARITH ` &0 < &16 * a <=> &0 < a `] THEN 
REWRITE_TAC[REAL_LT_MUL_EQ])] THEN 
REWRITE_TAC[REAL_ARITH ` (a + b + c ) / &2 - a = ( b + c - a ) / &2 `] THEN 
REWRITE_TAC[REAL_ARITH ` (a + b + c ) / &2 - b = ( c + a - b ) / &2 `] THEN 
REWRITE_TAC[REAL_ARITH ` (a + b + c ) / &2 - c = ( a + b - c ) / &2 `] THEN 
REWRITE_TAC[REAL_ARITH ` a < b + c <=> &0 < ( b + c - a ) / &2 `] THEN 
SIMP_TAC[DIST_SYM] THEN SIMP_TAC[REAL_ARITH ` a + b - c = b + a - c `] THEN 
SIMP_TAC[REAL_LT_MUL]);;



let RADV_FORMULAR = MESON[CDEUSDF]` !(va:real^3) vb vc.
     ~collinear {va, vb, vc}
     ==> radV {va, vb, vc} = eta_y (d3 vb vc) (d3 va vc) (d3 va vb)`;;



let MUL3_SYM = REAL_ARITH ` ! a b c. a * b * c = b * a * c /\
  a * b * c = c * b * a `;;

let ETA_X_SYMM = prove(` ! a b c. eta_x a b c = eta_x b a c /\
 eta_x a b c = eta_x c b a `,SIMP_TAC[eta_x; MUL3_SYM; UPS_X_SYM]);;

let ETA_Y_SYYM = prove(` ! x y z. eta_y x y z = eta_y y x z /\ 
eta_y x y z = eta_y z y x `, REWRITE_TAC[eta_y] THEN 
CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN MESON_TAC[ETA_X_SYMM]);;



let NOT_COL3_IMP_DIFF = MESON[PER_SET3; TWO_EQ_IMP_COL3]`!a b c. 
~collinear {a, b, c} ==> ~(a = b \/ a = c \/ b = c)`;;

let LET_TR = CONV_TAC (TOP_DEPTH_CONV let_CONV);;


let POW2_COND_LT = MESON[POW2_COND; REAL_ARITH ` &0 < a ==> &0 <= a `]` 
  !a b. &0 < a /\ &0 < b ==> (a <= b <=> a pow 2 <= b pow 2)`;;


let ETA_Y_2 = prove(` eta_y (&2) (&2) (&2)  = &2 / sqrt (&3) `,
REWRITE_TAC[eta_y; eta_x; ups_x] THEN 
LET_TR THEN 
REWRITE_TAC[REAL_ARITH ` ((&2 * &2) * (&2 * &2) * &2 * &2) /
  (--(&2 * &2) * &2 * &2 - (&2 * &2) * &2 * &2 - (&2 * &2) * &2 * &2 +
   &2 * (&2 * &2) * &2 * &2 +
   &2 * (&2 * &2) * &2 * &2 +
   &2 * (&2 * &2) * &2 * &2) = &4 / &3 `] THEN 
MP_TAC (MESON[REAL_LT_DIV; MESON[SQRT_POS_LT; REAL_ARITH` &0 < &3 `] ` 
&0 < sqrt (&3) `; REAL_ARITH ` &0 < &2 /\ &0 < &4 /\ &0 < &3 `] ` &0 < &4 / &3 
/\ &0 < &2 / sqrt (&3) `) THEN 
REWRITE_TAC[REAL_ARITH` a = b <=> a <= b /\ b <= a `] THEN 
SIMP_TAC[SQRT_POS_LT; POW2_COND_LT] THEN 
REWRITE_TAC[GSYM (REAL_ARITH` a = b <=> a <= b /\ b <= a `)] THEN 
SIMP_TAC[REAL_LT_IMP_LE; SQRT_POW_2] THEN 
REWRITE_TAC[REAL_FIELD` (a/ b) pow 2 = a pow 2 / ( b pow 2 ) `] THEN 
SIMP_TAC[REAL_ARITH ` &0 <= &3 `; SQRT_POW_2] THEN 
REAL_ARITH_TAC);;

let D3_POS_LE = MESON[d3; DIST_POS_LE]` ! x y. &0 <= d3 x y `;;


(* le 19. p 17 *)
let BYOWBDF = new_axiom`! a b c a' b' ( c':real). &0 < a /\
         a <= a' /\
         &0 < b /\
         b <= b' /\
         &0 < c /\
         c <= c' /\
         a' pow 2 <= b pow 2 + c pow 2 /\
         b' pow 2 <= a pow 2 + c pow 2 /\
         c' pow 2 <= a pow 2 + b pow 2
         ==> eta_y a b c <= eta_y a' b' c' `;;


let LEMMA25 = prove(` !(a:real^3) b c.
 packing {a, b, c} /\ ~ collinear {a,b,c}
         ==> &2 / sqrt (&3) <= radV {a, b, c} `, 
SIMP_TAC[RADV_FORMULAR] THEN REPEAT GEN_TAC THEN 
ASM_CASES_TAC ` (? x. x IN  { d3 b c, d3 c a, d3 a b } /\ &4 / sqrt (&3)
    <= x ) ` THENL [DOWN_TAC THEN STRIP_TAC THEN DOWN_TAC THEN 
NHANH (SPEC_ALL COLLINEAR_IMP_POS_UPS2) THEN 
REWRITE_TAC[d3] THEN NHANH (MESON[DIST_POS_LE; HVXIKHW]` 
&0 < ups_x_pow2 (dist (a,b)) (dist (b,c)) (dist (c,a))
  ==> max_real3 (dist (a,b)) (dist (b,c)) (dist (c,a)) / &2 <=
 eta_y (dist (a,b)) (dist (b,c)) (dist (c,a)) `) THEN 
REWRITE_TAC[REAL_ARITH` a / &2 <= b <=> a <= &2 * b `; MAX_REAL3_LESS_EX] THEN 
NHANH (SET_RULE ` x IN { a , b, c } /\ a1/\a2/\a3/\a4 /\ c <= aa /\ a <= aa
  /\ b <= aa ==> x <= aa `) THEN REWRITE_TAC[MESON[]` a/ b <= aa /\ l <=> l 
/\ a/b <= aa `] THEN PHA THEN DAO THEN 
NHANH (MESON[REAL_LE_TRANS]` a <= b /\ c <= a /\ l ==> c <= b `) THEN 
MATCH_MP_TAC (MESON[]` ( b ==> c ) ==> a/\b ==> c `) THEN 
REWRITE_TAC[REAL_ARITH ` &4 / a <= &2 * b <=> &2 / a <= b `] THEN 
MESON_TAC[DIST_SYM; ETA_Y_SYYM]; REWRITE_TAC[packing] THEN 
NHANH (SPEC_ALL NOT_COL3_IMP_DIFF) THEN 
NHANH (SET_RULE` (!u v. {a, b, c} u /\ {a, b, c} v /\ ~(u = v) ==> P u v )
  /\ l /\ ~(a = b \/ a = c \/ b = c) ==> P a b /\ P b c /\ P c a `) THEN 
DOWN_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN 
NHANH (SET_RULE` (! x. ~( x IN {a,b,c} /\ P x )) ==> ~ P a /\ ~P b /\ ~P c`) THEN 
SIMP_TAC[MESON[REAL_LE_DIV; SQRT_POS_LE; REAL_ARITH ` &0 <= &3 /\ &0 <= &4 `]`
     &0 <=  &4 / sqrt (&3)  `; D3_POS_LE; POW2_COND] THEN 
REWRITE_TAC[REAL_ARITH` ~( a <= b ) <=> b < a `] THEN 
REWRITE_TAC[REAL_FIELD` ( &4 / a ) pow 2 = &16 / ( a pow 2 ) `] THEN 
SIMP_TAC[REAL_ARITH` &0 <= &3 `; SQRT_POW_2] THEN 
NHANH (REAL_ARITH ` a < &16 / &3 ==> a <= &2 pow 2 + &2 pow 2 `) THEN 
PHA THEN REWRITE_TAC[MESON[]` a <= b + c /\ d <=> d /\ a <= b + c `] THEN 
REWRITE_TAC[GSYM d3] THEN PHA THEN 
NHANH (MESON[REAL_ARITH `&0 < &2 `; BYOWBDF]`&2 <= d3 a b /\
 &2 <= d3 b c /\ &2 <= d3 c a /\ d3 a b pow 2 <= &2 pow 2 + &2 pow 2 /\
 d3 c a pow 2 <= &2 pow 2 + &2 pow 2 /\ d3 b c pow 2 <= &2 pow 2 + &2 pow 2 
==>  eta_y (&2) (&2) (&2) <= eta_y (d3 a b) (d3 b c) (d3 c a) `) THEN 
DAO THEN MATCH_MP_TAC (TAUT` (a ==> b) ==> a /\ c ==> b `) THEN 
SIMP_TAC[ETA_Y_2;D3_SYM; ETA_Y_SYYM] THEN MESON_TAC[ETA_Y_SYYM]]);;



let COEF1_POS_EQ_V1_IN = prove(`!v1 v2 v3 (v:real^3). ~collinear {v1, v2, v3} /\ 
v IN affine hull {v1, v2, v3} ==> 
  ( &0 < coef1 v1 v2 v3 v <=> v IN aff_gt {v2, v3} {v1} ) `, DAO THEN 
NHANH (SPEC_ALL COEFS) THEN REWRITE_TAC[simp_def2; IN_ELIM_THM] THEN 
MESON_TAC[REAL_ADD_AC; VEC_PER2_3]);;


let COEFS1_EQ_0_IFF_V_IN_AFF = prove(` !v1 v2 v3 v.
         ~collinear {v1, v2, v3} /\ v IN affine hull {v1, v2, v3} ==>
  (&0 = coef1 v1 v2 v3 v <=> v IN aff {v2, v3}) `,
DAO THEN NHANH (SPEC_ALL COEFS) THEN 
REWRITE_TAC[AFF_2POINTS_INTERPRET; IN_ELIM_THM] THEN 
REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL [
DOWN_TAC THEN DAO THEN PURE_ONCE_REWRITE_TAC[MESON[]` &0 = a /\
 P a <=> &0 = a /\ P ( &0 ) `] THEN REWRITE_TAC[VECTOR_MUL_LZERO;
 VECTOR_ADD_LID; REAL_ADD_LID] THEN MESON_TAC[]; 
STRIP_TAC THEN DOWN_TAC THEN DAO THEN 
MESON_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; REAL_ADD_LID]]);;


let cayleytr = new_definition ` 
  cayleytr x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 = 
  &2 * x23 * x25 * x34 +
      &2 * x23 * x24 * x35 +
      -- &1 * x23 pow 2 * x45 +
      -- &2 * x15 * x23 * x34 +
      -- &2 * x15 * x23 * x24 +
      &2 * x15 * x23 pow 2 +
      -- &2 * x14 * x23 * x35 +
      -- &2 * x14 * x23 * x25 +
      &2 * x14 * x23 pow 2 +
      &4 * x14 * x15 * x23 +
      -- &2 * x13 * x25 * x34 +
      -- &2 * x13 * x24 * x35 +
      &4 * x13 * x24 * x25 +
      &2 * x13 * x23 * x45 +
      -- &2 * x13 * x23 * x25 +
      -- &2 * x13 * x23 * x24 +
      &2 * x13 * x15 * x34 +
      -- &2 * x13 * x15 * x24 +
      -- &2 * x13 * x15 * x23 +
      &2 * x13 * x14 * x35 +
      -- &2 * x13 * x14 * x25 +
      -- &2 * x13 * x14 * x23 +
      -- &1 * x13 pow 2 * x45 +
      &2 * x13 pow 2 * x25 +
      &2 * x13 pow 2 * x24 +
      &4 * x12 * x34 * x35 +
      -- &2 * x12 * x25 * x34 +
      -- &2 * x12 * x24 * x35 +
      &2 * x12 * x23 * x45 +
      -- &2 * x12 * x23 * x35 +
      -- &2 * x12 * x23 * x34 +
   -- &2 * x12 * x15 * x34 +
      &2 * x12 * x15 * x24 +
      -- &2 * x12 * x15 * x23 +
      -- &2 * x12 * x14 * x35 +
      &2 * x12 * x14 * x25 +
      -- &2 * x12 * x14 * x23 +
      &2 * x12 * x13 * x45 +
      -- &2 * x12 * x13 * x35 +
      -- &2 * x12 * x13 * x34 +
      -- &2 * x12 * x13 * x25 +
      -- &2 * x12 * x13 * x24 +
      &4 * x12 * x13 * x23 +
      -- &1 * x12 pow 2 * x45 +
      &2 * x12 pow 2 * x35 +
      &2 * x12 pow 2 * x34 `;;

(* NGUYEN QUANG TRUONG *)
let LTCTBAN = prove(` cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 = 
ups_x x12 x13 x23 * x45 pow 2 + cayleytr x12 x13 x14 x15 x23 x24 x25 x34 x35 ( &0 )
* x45 + cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 ( &0 ) `,
REWRITE_TAC[ups_x; cayleyR;cayleytr] THEN REAL_ARITH_TAC);;


let COEF1_NEG_IFF_V1_IN_AFF_LT = prove(` ! v1 v2 v3 v. ~collinear {v1, v2, v3} /\
 v IN affine hull {v1, v2, v3}
  ==> (coef1 v1 v2 v3 v < &0 <=> v IN aff_lt {v2, v3} {v1}) `,
DAO THEN NHANH (SPEC_ALL COEFS) THEN REWRITE_TAC[simp_def2; IN_ELIM_THM] THEN 
MESON_TAC[REAL_ADD_AC; VEC_PER2_3]);;

let condA = new_definition `condA (v1:real^3) v2 v3 v4 x12 x13 x14 x23 x24 x34 = 
  ( ~ ( v1 = v2 ) /\ coplanar {v1,v2,v3,v4} /\
  ( dist ( v1, v2) pow 2 ) = x12 /\
  dist (v1,v3) pow 2 = x13 /\
  dist (v1,v4) pow 2 = x14 /\
  dist (v2,v3) pow 2 = x23 /\ dist (v2,v4) pow 2 = x24 )`;;


(* le 15 *)
let POLFLZY = new_axiom ` ! x1 x2 x3 (x4: real^3).  
         let x12 = dist (x1,x2) pow 2 in
         let x13 = dist (x1,x3) pow 2 in
         let x14 = dist (x1,x4) pow 2 in
         let x23 = dist (x2,x3) pow 2 in
         let x24 = dist (x2,x4) pow 2 in
         let x34 = dist (x3,x4) pow 2 in
         coplanar {x1, x2, x3, x4} <=> delta x12 x13 x14 x23 x24 x34 = &0 `;;
let LEMMA15 = POLFLZY;;

let muy_delta = new_definition ` muy_delta = delta `;;

let VCRLIHC = prove(`!(v1:real^3) v2 v3 v4 x34 x12 x13 x14 x23 x24.
         condA v1 v2 v3 v4 x12 x13 x14 x23 x24 x34
         ==> muy_delta x12 x13 x14 x23 x24 (dist (v3,v4) pow 2) = &0`,
REWRITE_TAC[condA; muy_delta] THEN MP_TAC POLFLZY THEN LET_TR THEN MESON_TAC[]);;


let ZERO_NEUTRAL = REAL_ARITH ` ! x. &0 * x = &0 /\ x * &0 = &0 /\ &0 + x = x /\ x + &0 = x /\ x - &0 = x /\
  -- &0 = &0 `;;

let EQUATE_CONEFS_POLINOMIAL_POW2 = prove( `!a b c aa bb cc. ( ! x. 
     a * x pow 2 + b * x + c = aa * x pow 2 + bb * x + cc ) <=>
     a = aa /\ b = bb /\ c = cc`, REPEAT GEN_TAC THEN EQ_TAC THENL [
NHANH (MESON[]` (! (x:real). P x ) ==> P ( &0 ) /\ P ( &1 ) /\ P ( &2 )`) THEN 
REAL_ARITH_TAC THEN REAL_ARITH_TAC; SIMP_TAC[]]);;

let GJWYYPS = prove(`!x12 x13 x14 x15 x23 x24 x25 x34 x35 a b c.
    (! x45.  cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 =
     a  * x45 pow 2 + b * x45 + c )
     ==> b pow 2 - &4 * a * c =
         &16 * delta x12 x13 x14 x23 x24 x34 * delta x12 x13 x15 x23 x25 x35`,
ONCE_REWRITE_TAC[LTCTBAN] THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[EQUATE_CONEFS_POLINOMIAL_POW2] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ]
THEN SIMP_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[ups_x; cayleytr; cayleyR;
 delta; ZERO_NEUTRAL] THEN REAL_ARITH_TAC);;

let LEMMA51 = GJWYYPS ;;

g `!v1 v2 (v:real^3). ~(v1 = v2) ==> (collinear {v, v1, v2} <=> v IN aff {v1, v2})`;;
e (REWRITE_TAC[COLLINEAR_EX]);;
e (NHANH (MESON[]` a % b + c = vec 0 ==> ( a = &0 \/ ~(a = &0 ))`));;
e (KHANANG);;
e (NGOAC THEN PURE_ONCE_REWRITE_TAC[MESON[]` P a /\ a = &0 <=> P ( &0 ) 
  /\ a = &0 `]);;
e (REWRITE_TAC[REAL_ADD_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID]);;
e (REWRITE_TAC[REAL_ARITH ` a + b= &0 <=> a = -- b `; VECTOR_ARITH` a % x + b % y = vec 0 
 <=> a % x = ( -- b) % y`]);;
e (NHANH (MESON[REAL_ARITH ` a = &0 <=> -- a = &0 `; VECTOR_MUL_LCANCEL]` (b = --c /\ ~(b = &0 /\ c = &0)) /\ b % v1 = --c % v2
  ==> v1 = v2 `));;
e (SIMP_TAC[]);;
e (REWRITE_TAC[AFF_2POINTS_INTERPRET; IN_ELIM_THM]);;
e (REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC);;
e (REWRITE_TAC[VECTOR_ARITH ` a % v + b % v1 + c % v2 = vec 0 <=>
  a % v = ( -- b) % v1 + ( --c ) % v2 `]);;
e (PHA THEN REWRITE_TAC[MESON[CHANGE_SIDE]` a % v = v1  /\
               ~(a = &0) <=> v = &1 / a % v1 /\ ~( a = &0 ) `]);;
e (REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; REAL_ARITH `&1 / a * b = b / a`]);;
e (REWRITE_TAC[AFF_2POINTS_INTERPRET; IN_ELIM_THM]);;
e (MESON_TAC[REAL_FIELD ` ~ ( a = &0 ) /\ a = -- (b + c) ==>
   ( -- b) / a + ( -- c) / a = &1 `]);;
e (STRIP_TAC);;
e (EXISTS_TAC ` &1 `);;
e (EXISTS_TAC ` -- ta`);;
e (EXISTS_TAC ` -- tb`);;
e (PHA);;
e (ASM_SIMP_TAC[REAL_ARITH` ~(&1 = &0 ) /\ -- ( -- a + -- b ) = a + b `]);;
e (CONV_TAC VECTOR_ARITH);;

let NOT_TOW_EQ_IMP_COL_EQUAVALENT = top_thm();;


let LEMMA30 = prove(`!v1 v2 v3 v4 x12 x13 x14 x23 x24 x34 a b c.
         condA v1 v2 v3 v4 x12 x13 x14 x23 x24 x34 /\
         (!x12 x13 x14 x23 x24 x34.
              muy_delta x12 x13 x14 x23 x24 x34 =
              a x12 x13 x14 x23 x24 * x34 pow 2 +
              b x12 x13 x14 x23 x24 * x34 +
              c x12 x13 x14 x23 x24 )
         ==> (v3 IN aff {v1, v2} \/ v4 IN aff {v1, v2} <=>
              b x12 x13 x14 x23 x24 pow 2 -
              &4 * a x12 x13 x14 x23 x24 * c x12 x13 x14 x23 x24 =
              &0)`,
REWRITE_TAC[muy_delta; DELTA_COEFS; EQUATE_CONEFS_POLINOMIAL_POW2 ] THEN 
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN SIMP_TAC[] THEN REPEAT GEN_TAC THEN 
DISCH_TAC THEN REWRITE_TAC[REAL_ARITH` a - b * -- c * d = a + b * c * d `; 
AGBWHRD] THEN DOWN_TAC THEN SIMP_TAC[condA; REAL_ENTIRE; 
GSYM NOT_TOW_EQ_IMP_COL_EQUAVALENT] THEN ONCE_REWRITE_TAC[MESON[PER_SET3]`
 p {v3, v1, v2} \/ p {v4, v1, v2}  <=> p {v1,v2,v3} \/ p {v1,v2,v4} `] THEN 
ONCE_REWRITE_TAC[MESON[UPS_X_SYM]` ups_x x12 x23 x13 = &0 \/ 
ups_x x12 x24 x14 = &0 <=>     ups_x x12 x13 x23 = &0 \/ 
ups_x x12 x14 x24 = &0 `] THEN MESON_TAC[UPS_X_SYM; PER_SET3; FHFMKIY]);;

let EWVIFXW = LEMMA30;;



let WITH_COEF1 = prove(` ! (v1:real^3) (v2:real^3) (v3:real^3) (v:real^3).
 ~ collinear {v1,v2,v3} /\ v IN affine hull {v1, v2, v3} 
  ==> ( &0 < coef1 v1 v2 v3 v <=> v IN aff_gt {v2,v3} {v1} ) /\
  ( &0 = coef1 v1 v2 v3 v <=> v IN aff {v2,v3} ) /\
  ( coef1 v1 v2 v3 v < &0 <=> v IN aff_lt {v2,v3} {v1} ) `,
SIMP_TAC[COEF1_POS_EQ_V1_IN; COEFS1_EQ_0_IFF_V_IN_AFF; COEF1_NEG_IFF_V1_IN_AFF_LT]);;

let PER_COEF1_COEF2 = prove(` ! (v1:real^3) (v2:real^3) (v3:real^3) (v:real^3).
           v IN affine hull {v1, v2, v3} /\ ~collinear {v1, v2, v3}
==> coef1 v2 v3 v1 v = coef2 v1 v2 v3 v `,
NHANH (SPEC_ALL COEFS) THEN 
ONCE_REWRITE_TAC[MESON[PER_SET3]` p {a,b,c} = p {b,c,a} `] THEN 
NHANH (SPEC_ALL COEFS) THEN MESON_TAC[VEC_PER2_3]);;


let PER_COEF1_COEF3 = prove(` ! (v1:real^3) (v2:real^3) (v3:real^3) (v:real^3).
           v IN affine hull {v1, v2, v3} /\ ~collinear {v1, v2, v3}
==> coef1 v3 v1 v2 v = coef3 v1 v2 v3 v `, NHANH (SPEC_ALL COEFS) THEN 
ONCE_REWRITE_TAC[MESON[PER_SET3]` p {a,b,c} = p {c,a,b} `] THEN 
NHANH (SPEC_ALL COEFS) THEN MESON_TAC[VEC_PER2_3]);;

let PER_COEF1 = prove(  ` ! (v1:real^3) (v2:real^3) (v3:real^3) (v:real^3).
           v IN affine hull {v1, v2, v3} /\ ~collinear {v1, v2, v3}
==> coef1 v3 v1 v2 v = coef3 v1 v2 v3 v /\ coef1 v2 v3 v1 v = coef2 v1 v2 v3 v `,
SIMP_TAC[PER_COEF1_COEF2; PER_COEF1_COEF3]);;



let LEMMA12 = prove(`! (v1:real^3) (v2:real^3) (v3:real^3) (v:real^3). 
~ collinear {v1,v2,v3} /\ v IN affine hull {v1, v2, v3} 
  ==> ( &0 < coef1 v1 v2 v3 v <=> v IN aff_gt {v2,v3} {v1} ) /\
  ( &0 = coef1 v1 v2 v3 v <=> v IN aff {v2,v3} ) /\
  ( coef1 v1 v2 v3 v < &0 <=> v IN aff_lt {v2,v3} {v1} ) /\
   ( &0 < coef2 v1 v2 v3 v <=> v IN aff_gt {v3,v1} {v2} ) /\
  ( &0 = coef2 v1 v2 v3 v <=> v IN aff {v3,v1} ) /\
  ( coef2 v1 v2 v3 v < &0 <=> v IN aff_lt {v3,v1} {v2} )/\
   ( &0 < coef3 v1 v2 v3 v <=> v IN aff_gt {v1,v2} {v3} ) /\
  ( &0 = coef3 v1 v2 v3 v <=> v IN aff {v1,v2} ) /\
  ( coef3 v1 v2 v3 v < &0 <=> v IN aff_lt {v1,v2} {v3})`,
MP_TAC WITH_COEF1 THEN SIMP_TAC[PER_SET3; GSYM PER_COEF1_COEF3; PER_COEF1]);;

let CNXIFFC = LEMMA12;;
 

let NGAY_23_THANG1 = prove(`! (v1:real^3) (v2:real^3) (v3:real^3) (v:real^3). ~collinear {v1, v2, v3} /\ v IN affine hull {v1, v2, v3} ==>
  ( v IN aff_ge {v2, v3} {v1} <=> &0 <= coef1 v1 v2 v3 v ) /\
  ( v IN aff_ge {v3,v1} {v2} <=> &0 <= coef2 v1 v2 v3 v ) /\
  ( v IN aff_ge {v1,v2} {v3} <=> &0 <= coef3 v1 
v2 v3 v ) `,
REWRITE_TAC[IN_AFF_GE_INTERPRET_TO_AFF_GT_AND_AFF; REAL_ARITH ` &0 <= a
  <=> &0 < a \/ &0 = a `] THEN SIMP_TAC[CNXIFFC]);;


let MYOQCBS = prove(` !(v1:real^3) v2 v3 v.
         ~collinear {v1, v2, v3} /\ v IN affine hull {v1, v2, v3}
         ==> (v IN conv {v1, v2, v3} <=>
              &0 <= coef1 v1 v2 v3 v /\
              &0 <= coef2 v1 v2 v3 v /\
              &0 <= coef3 v1 v2 v3 v) /\
             (v IN conv0 {v1, v2, v3} <=>
              &0 < coef1 v1 v2 v3 v /\
              &0 < coef2 v1 v2 v3 v /\
              &0 < coef3 v1 v2 v3 v) `,
SIMP_TAC[IN_CONV3_EQ; IN_CONV03_EQ; NGAY_23_THANG1; CNXIFFC ] THEN MESON_TAC[]);;

let LEMMA51 = GJWYYPS;;
let LEMMA50 = LTCTBAN;;
let muy_v = new_definition ` muy_v (x1: real^N ) (x2:real^N) (x3:real^N) (x4:real^N)
(x5:real^N) x45 = 
          (let x12 = dist (x1,x2) pow 2 in
          let x13 = dist (x1,x3) pow 2 in
          let x14 = dist (x1,x4) pow 2 in
          let x15 = dist (x1,x5) pow 2 in
          let x23 = dist (x2,x3) pow 2 in
          let x24 = dist (x2,x4) pow 2 in
          let x25 = dist (x2,x5) pow 2 in
          let x34 = dist (x3,x4) pow 2 in
          let x35 = dist (x3,x5) pow 2 in
          cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45) `;;

let REMOVE_TAC = MATCH_MP_TAC (MESON[]` a ==> b ==> a `);;

let ALE = MESON[LTCTBAN]`!x12 x13 x14 x15 x23 x24 x25 x34 x35.
     (!a b c. (! x.
          cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x =
          a * x pow 2 + b * x + c )
          ==> b pow 2 - &4 * a * c = &0)
     ==> cayleytr x12 x13 x14 x15 x23 x24 x25 x34 x35 (&0) pow 2 -
         &4 *
         ups_x x12 x13 x23 *
         cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 (&0) =
         &0`;;

let DISCRIMINANT_OF_CAY = MESON[LTCTBAN; GJWYYPS]`cayleytr x12 x13 x14 x15 x23 x24 x25 x34 x35 (&0) pow 2 -
 &4 * ups_x x12 x13 x23 * cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 (&0) =
 &16 * delta x12 x13 x14 x23 x24 x34 * delta x12 x13 x15 x23 x25 x35`;;

let NOT_TWO_EQ_IMP_COL_EQUAVALENT = NOT_TOW_EQ_IMP_COL_EQUAVALENT;;

let GDLRUZB = prove(` ! (v1:real^3) (v2:real^3) (v3:real^3) (v4:real^3) (v5:real^3) a b c.
  coplanar {v1, v2, v3, v4} \/ coplanar {v1, v2, v3, v5} <=>
         (! a b c. (! x. muy_v v1 v2 v3 v4 v5 x = a * x pow 2 + b * x + c )
 ==> b pow 2 - &4 * a * c = &0) `,REWRITE_TAC[muy_v] THEN LET_TR THEN 
REPEAT GEN_TAC THEN EQ_TAC THENL [DISCH_TAC THEN 
NHANH (MESON[GJWYYPS]` (!x45. cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 =
                a * x45 pow 2 + b * x45 + c)
         ==> b pow 2 - &4 * a * c =
             &16 *
             delta x12 x13 x14 x23 x24 x34 *
             delta x12 x13 x15 x23 x25 x35`) THEN SIMP_TAC[] THEN 
UNDISCH_TAC ` coplanar {(v1:real^3), v2, v3, v4}\/ coplanar {v1, v2, v3, v5}` THEN 
MP_TAC LEMMA15 THEN LET_TR THEN REWRITE_TAC[REAL_FIELD` &16 * a * b = &0 
<=> a = &0 \/ b = &0 `] THEN SIMP_TAC[]; NHANH (SPEC_ALL ALE) THEN 
REWRITE_TAC[DISCRIMINANT_OF_CAY ] THEN MP_TAC POLFLZY THEN LET_TR THEN 
REWRITE_TAC[REAL_FIELD` &16 * a * b = &0 <=> a = &0 \/ b = &0 `] THEN 
MESON_TAC[]]);;


let det_vec3 = new_definition ` det_vec3 (a:real^3) (b:real^3) (c:real^3) = 
  a$1 * b$2 * c$3 + b$1 * c$2 * a$3 + c$1 * a$2 * b$3 - 
  ( a$1 * c$2 * b$3 + b$1 * a$2 * c$3 + c$1 * b$2 * a$3 ) `;;

let DET_VEC3_AND_DELTA = prove(`!(a:real^3) b c d.
     &4 * ( det_vec3 (a - d) (b - d) (c - d) ) pow 2 =
     delta  ( d3 a d pow 2)
     (d3 b d pow 2)
     (d3 c d pow 2) (d3 a b pow 2) (d3 a c pow 2) (d3 b c pow 2)   `,
SIMP_TAC[d3; dist] THEN 
REWRITE_TAC[GSYM (MESON[VECTOR_ARITH ` (a :real^N) - b = ( a - x ) - ( b - x ) `]`
  delta      (norm (a - d) pow 2)     (norm (b - d) pow 2)
     (norm (c - d) pow 2) (norm ((a - d)  - (b - d )) pow 2) 
(norm ((a - d)  - ( c - d )) pow 2) (norm ((b - d ) - ( c - d )) pow 2)    =
   delta   (norm (a - d) pow 2)     (norm (b - d) pow 2)   (norm (c - d) pow 2)
(norm (a - b) pow 2) (norm (a - c) pow 2) (norm (b - c) pow 2)    `)] THEN 
SIMP_TAC[ vector_norm; DOT_POS_LE; SQRT_WORKS] THEN 
REWRITE_TAC[DOT_3] THEN 
REWRITE_TAC[MESON[lemma_cm3]`((a:real^3) - d - (b - d))$1 = (a - d)$1 - (b - d)$1 /\
  (a - d - (b - d))$2 = (a - d)$2 - (b - d)$2 /\
  (a - d - (b - d))$3 = (a - d)$3 - (b - d)$3 `] THEN 
REWRITE_TAC[delta; det_vec3] THEN 
REAL_ARITH_TAC);;


let DET_VECC3_AND_DELTA = prove(` (! d a b c .
      delta (d3 d a pow 2) (d3 d b pow 2) (d3 d c pow 2) (d3 a b pow 2)
      (d3 a c pow 2)
      (d3 b c pow 2) =
      &4 * det_vec3 (a - d) (b - d) (c - d) pow 2) `, MESON_TAC[D3_SYM; 
DET_VEC3_AND_DELTA]);;


let DELTA_POS_4POINTS = prove(`!x1 x2 x3 (x4:real^3).
     &0 <=
     delta (dist (x1,x2) pow 2) (dist (x1,x3) pow 2) (dist (x1,x4) pow 2)
     (dist (x2,x3) pow 2)
     (dist (x2,x4) pow 2)
     (dist (x3,x4) pow 2)`, REWRITE_TAC[GSYM d3] THEN SIMP_TAC[D3_SYM] THEN 
MP_TAC (DET_VECC3_AND_DELTA) THEN SIMP_TAC[] THEN DISCH_TAC THEN MP_TAC
 REAL_LE_SQUARE_POW THEN MESON_TAC[REAL_ARITH` &0 <= x <=> &0 <= &4 * x `]);;



let DIST_POW2_DOT = 
prove(` ! a (b:real^N) . dist (a,b) pow 2 = ( a - b ) dot ( a- b) `,
SIMP_TAC[dist; vector_norm; DOT_POS_LE; SQRT_WORKS]);;

(* this lemma is proved as below, but it take time to run it *)
let CAYLEYR_5POINTS = new_axiom` !x1 x2 x3 x4 (x5 :real^3). 
         let x12 = dist (x1,x2) pow 2 in
         let x13 = dist (x1,x3) pow 2 in
         let x14 = dist (x1,x4) pow 2 in
         let x15 = dist (x1,x5) pow 2 in
         let x23 = dist (x2,x3) pow 2 in
         let x24 = dist (x2,x4) pow 2 in
         let x25 = dist (x2,x5) pow 2 in
         let x34 = dist (x3,x4) pow 2 in
         let x35 = dist (x3,x5) pow 2 in
         let x45 = dist (x4,x5) pow 2 in
         cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 = &0 `;;

(* let CAYLEYR_5POINTS = prove(`  !x1 x2 x3 x4 (x5 :real^3). 
         let x12 = dist (x1,x2) pow 2 in
         let x13 = dist (x1,x3) pow 2 in
         let x14 = dist (x1,x4) pow 2 in
         let x15 = dist (x1,x5) pow 2 in
         let x23 = dist (x2,x3) pow 2 in
         let x24 = dist (x2,x4) pow 2 in
         let x25 = dist (x2,x5) pow 2 in
         let x34 = dist (x3,x4) pow 2 in
         let x35 = dist (x3,x5) pow 2 in
         let x45 = dist (x4,x5) pow 2 in
         cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 = &0 `,
LET_TR THEN REWRITE_TAC[ DIST_POW2_DOT] THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[ MESON[VECTOR_ARITH` (a:real^n) - b = a - x - ( b - x ) `]`
  AA ( (x1 - x5 ) dot ( x1 - x5)) ((x2 - x3) dot (x2 - x3))
 ((x2 - x4) dot (x2 - x4))
 ((x2 - x5) dot (x2 - x5))
 ((x3 - x4) dot (x3 - x4))
 ((x3 - x5) dot (x3 - x5))
 ((x4 - x5) dot (x4 - x5)) =
  AA ( (x1 - x5 ) dot ( x1 - x5)) ((x2 - x1 - ( x3 - x1 )) dot (x2 - x1 - ( x3 - x1 )))
  ((x2 - x1 - ( x4 - x1 )) dot (x2 - x1 - ( x4 - x1 )))
  ((x2 - x1 - ( x5 - x1 )) dot (x2 - x1 - ( x5 - x1 )))
  ((x3 - x1 - ( x4 - x1 )) dot (x3 - x1 - ( x4 - x1 )))
  ((x3 - x1 - ( x5 - x1 )) dot (x3 - x1 - ( x5 - x1 )))
    ((x4 - x1 - ( x5 - x1 )) dot (x4 - x1 - ( x5 - x1 ))) ` ] THEN 
SIMP_TAC[VECTOR_ARITH ` ((x4: real^N) - x1 - (x5 - x1)) = x1 - x5 - ( x1 - x4 ) `] THEN 
ABBREV_TAC ` x12 = (x1 - ( x2:real^3)) ` THEN 
ABBREV_TAC ` x13 = (x1 - ( x3:real^3)) ` THEN 
ABBREV_TAC ` x14 = (x1 - ( x4:real^3)) ` THEN 
ABBREV_TAC ` x15 = (x1 - ( x5:real^3)) ` THEN 
REWRITE_TAC[DOT_3] THEN REWRITE_TAC[lemma_cm3; cayleyR] THEN REAL_AROTH_TAC);; *)


let UPS_X_POS = MESON[lemma8; UPS_X_SYM; NORM_SUB]` &0 <=
          ups_x (norm ((x1 : real^3) - x2) pow 2) (norm (x1 - x3) pow 2)
          (norm (x2 - x3) pow 2) `;;

let UPS_X_SYM = MESON[UPS_X_SYM]` !x y z. ups_x x y z = ups_x y x z /\ ups_x x y z = ups_x x z y
  /\ ups_x x y z = ups_x x z y `;;

let LEMMA3 = prove(` !x1 x2 x3 x4 (x5 :real^3). 
                 let x12 = dist (x1,x2) pow 2 in
         let x13 = dist (x1,x3) pow 2 in
         let x14 = dist (x1,x4) pow 2 in
         let x15 = dist (x1,x5) pow 2 in
         let x23 = dist (x2,x3) pow 2 in
         let x24 = dist (x2,x4) pow 2 in
         let x25 = dist (x2,x5) pow 2 in
         let x34 = dist (x3,x4) pow 2 in
         let x35 = dist (x3,x5) pow 2 in
         let x45 = dist (x4,x5) pow 2 in
         &0 <= ups_x x12 x13 x23 /\
         &0 <= delta x12 x13 x14 x23 x24 x34 /\
         cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 = &0 `, MP_TAC 
CAYLEYR_5POINTS THEN LET_TR THEN 
SIMP_TAC[ dist; UPS_X_POS; DELTA_POS_4POINTS]);;
