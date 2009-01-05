(* Formal Spec of Blueprint Chapter  on Collection of Problems in Geometry *)

needs "Examples/transc.ml";;
needs "definitions_kepler.ml";;

prioritize_real();;

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


let GONTONG = REAL_RING ` ((a + b) + c = a + b + c ) `;;
let SUB_SUM_SUB = REAL_RING ` (a - ( b + c ) = a - b - c )/\( a - (b- c) = a - b + c );;

let JVUNDLC = prove(`!a b c s.
     s = (a + b + c) / &2
     ==> &16 * s * (s - a) * (s - b) * (s - c) =
         ups_x (a pow 2) (b pow 2) (c pow 2)`, SIMP_TAC [ ups_x] THEN 
REWRITE_TAC[REAL_FIELD` a / &2 - b = ( a - &2 * b ) / &2 `] THEN 
REWRITE_TAC[REAL_FIELD ` &16 * ( a / &2 ) * ( b / &2 ) * (c / &2 ) *
( d / &2 ) = a * b * c * d `] THEN REAL_ARITH_TAC);;

