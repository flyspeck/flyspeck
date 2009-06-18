(* Tran Nam Trung *)

needs "Examples/permutations.ml";;

prioritize_num();;


(* Iterate of a function f with n times *)

let iterate_function = new_recursive_definition num_RECURSION
`(iterate_function (f:A->A) 0 (x:A) = x) /\ (iterate_function (f:A->A)
(SUC n) (x:A) = iterate_function f n (f x))`;;

let iterate_map = new_recursive_definition num_RECURSION `(iterate_map
(f:A->A) 0  = I) /\ (iterate_map (f:A->A) (SUC n) = (iterate_map f n)o
f)`;;

let iterate_map0 = prove(`!f:A->A. iterate_map f 0 = I`,
REWRITE_TAC[iterate_map]);;

let iterate_map1 = prove(`!f:A->A. iterate_map f 1 = f`,
REWRITE_TAC[iterate_map; ARITH_RULE `1 = SUC 0`; I_O_ID]);;

let iterate_map2 = prove(`!f:A->A. iterate_map f 2 = f o f`,
REWRITE_TAC[iterate_map; ARITH_RULE `2 = SUC 1`; iterate_map1]);;

let calculate_value = prove(`!f:A->A n:num x:A. (iterate_map f n) x =
iterate_function f n x`, GEN_TAC THEN INDUCT_TAC
THENL[REWRITE_TAC[iterate_map; iterate_function; I_THM]; GEN_TAC THEN
ASM_REWRITE_TAC[iterate_map; iterate_function; o_DEF]]);;

let orbit_map = new_definition `orbit_map (f:A->A)  (x:A) = {(iterate_map
f n) x | n >= 0}`;;

(* the definition of hypermap *)

let pppp1 = new_definition `pppp1 ((D,e,n,f):(A->bool)#(A->A)#(A->A)#(A->A)) = D`;;

let pppp2 = new_definition `pppp2 ((D,e,n,f):(A->bool)#(A->A)#(A->A)#(A->A)) = e`;;

let pppp3 = new_definition `pppp3 ((D,e,n,f):(A->bool)#(A->A)#(A->A)#(A->A)) = n`;;

let pppp4 = new_definition `pppp4 ((D,e,n,f):(A->bool)#(A->A)#(A->A)#(A->A)) = f`;;

let exist_hypermap = prove(`?H:((A->bool)#(A->A)#(A->A)#(A->A)). FINITE
(pppp1 H) /\ pppp2 H permutes pppp1 H /\ pppp3 H permutes pppp1 H /\ pppp4
H permutes pppp1 H /\ pppp2 H o pppp3 H o pppp4 H = I`,EXISTS_TAC
`({},I,I,I):(A->bool)#(A->A)#(A->A)#(A->A)` THEN REWRITE_TAC[pppp1; pppp2;
pppp3; pppp4; FINITE_RULES; PERMUTES_I; I_O_ID]);;

let hypermap_tybij = REWRITE_RULE[] (new_type_definition "hypermap" ("hypermap", "tuple_hypermap")exist_hypermap);;

let dart = new_definition `dart (H:(A)hypermap) = pppp1 (tuple_hypermap H)`;;

let edge_map = new_definition `edge_map (H:(A)hypermap) = pppp2(tuple_hypermap H)`;;

let node_map = new_definition `node_map (H:(A)hypermap) = pppp3(tuple_hypermap H)`;;

let face_map = new_definition `face_map (H:(A)hypermap) = pppp4(tuple_hypermap H)`;;

let hypermap_lemma = prove(`!H:(A)hypermap. FINITE (dart H) /\ edge_map H
permutes dart H /\ node_map H permutes dart H /\ face_map H permutes dart
H /\ edge_map H o node_map H o face_map H = I`,
ASM_REWRITE_TAC[hypermap_tybij; pppp1; pppp2; pppp3; pppp4; dart;
edge_map; node_map; face_map]);;

(* edges, nodes, faces, group orbits of a hypermap*)

let edge = new_definition `edge (H:(A)hypermap) (x:A) = orbit_map
(edge_map H) x`;;

let node = new_definition `node (H:(A)hypermap) (x:A) = orbit_map
(node_map H) x`;;

let face = new_definition `face (H:(A)hypermap) (x:A) = orbit_map
(face_map H) x`;;


let connect_by_path  = new_recursive_definition num_RECURSION
  `(connected_by_path (H:(A)hypermap) (x:A) (y:A) 0 <=> (x IN dart H) /\ (x = y)) /\
   (connected_by_path (H:(A)hypermap) (x:A) (y:A) (SUC (n:num)) <=> ?z:A. (connected_by_path H x z n) /\
   (y = (edge_map H) z \/ y = (node_map H) z \/ y = (face_map H) z ))`;;


let in_combinatorial_component = new_definition `in_combinatorial_component (H:(A)hypermap) (x:A) (y:A) <=> (?m:num. connected_by_path H x y m)`;; 

let combinatorial_component = new_definition `combinatorial_component (H:(A)hypermap) (x:A) = {y:A| in_combinatorial_component H x y}`;;

(* some definitions on orbits *)

let set_of_orbits = new_definition `set_of_orbits (D:A->bool) (f:A->A) = {orbit_map f x | x IN D}`;;

let number_of_orbits = new_definition `number_of_orbits (D:A->bool) (f:A->A) = CARD(set_of_orbits D f)`;;


(* the orbits on hypermaps*)

let edge_set = new_definition `edge_set (H:(A)hypermap) = set_of_orbits (dart H) (edge_map H)`;;

let node_set = new_definition `node_set  (H:(A)hypermap) = set_of_orbits (dart H) (node_map H)`;;

let face_set = new_definition `face_set (H:(A)hypermap) = set_of_orbits (dart H) (face_map H)`;;

let component_set = new_definition `component_set (H:(A)hypermap) = {combinatorial_component H (x:A) | x IN dart H}`;;


(* counting the numbers of edges, nodes, faces and group orbits *)

let number_of_edges = new_definition `number_of_edges (H:(A)hypermap) =
CARD (edge_set H)`;;

let number_of_nodes = new_definition `number_of_nodes (H:(A)hypermap) =
CARD (node_set H)`;;

let number_of_faces = new_definition `number_of_faces (H:(A)hypermap) =
CARD (face_set H)`;;

let number_of_components = new_definition `number_of_components
(H:(A)hypermap) = CARD (component_set H)`;;


(* some special hypergraphs *)

let plain_hypermap = new_definition `plain_hypermap (H:(A)hypermap) <=>
edge_map H o edge_map H = I`;;

let planar_hypermap = new_definition `planar_hypermap (H:(A)hypermap) <=>
number_of_nodes H + number_of_edges H + number_of_faces H = (CARD (dart
H)) + 2 * number_of_components H`;;

let simple_hypermap = new_definition `simple_hypermap (H:(A)hypermap) <=>
(!x:A. dart H x ==> (node H x) INTER (face H x) = {x})`;;


(* a dart x is degenerate or nondegenerate *)

let dart_degenerate = new_definition `dart_degenerate (H:(A)hypermap)
(x:A)  <=> (edge_map H x = x \/ node_map H x = x \/ face_map H x = x)`;;

let dart_nondegenerate = new_definition `dart_nondegenerate
(H:(A)hypermap) (x:A) <=> ~(edge_map H x = x) /\ ~(node_map H x = x) /\ ~(
face_map H x = x)`;;


(* some properties of symmetric groups *)

let LEFT_MULT_MAP = prove(`!u:A->A v:A->A w:A->A. v = w ==> u o v = u o
w`, MESON_TAC[]);;

let RIGHT_MULT_MAP = prove(`!u:A->A v:A->A w:A->A. u = v ==> u o w = v o
w`, MESON_TAC[]);;

let LEFT_INVERSE_EQUATION = prove(`!s:A->bool u:A->A v:A->A w:A->A. u
permutes s /\ u o v = w ==> v = inverse u o w`,
REPEAT STRIP_TAC THEN SUBGOAL_THEN `inverse (u:A->A) o u o (v:A->A) =
inverse u o (w:A->A)` MP_TAC
THENL[ ASM_MESON_TAC[]; REWRITE_TAC[o_ASSOC] THEN
ASM_MESON_TAC[PERMUTES_INVERSES_o; I_O_ID]]);;

let RIGHT_INVERSE_EQUATION = prove(`!s:A->bool u:A->A v:A->A w:A->A. v
permutes s /\ u o v = w ==> u = w o inverse v`,
REPEAT STRIP_TAC THEN SUBGOAL_THEN `(u:A->A) o (v:A->A) o inverse v =
(w:A->A) o inverse v` MP_TAC
THENL [ASM_MESON_TAC[o_ASSOC]; ASM_MESON_TAC[PERMUTES_INVERSES_o;I_O_ID] ]);;


let iterate_orbit = prove(`!(s:A->bool) (u:A->A). u permutes s ==>
!(n:num) (x:A). x IN s ==> (iterate_map u n) x IN s`,
REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP PERMUTES_IN_IMAGE)
THEN INDUCT_TAC
THENL[GEN_TAC THEN REWRITE_TAC[iterate_map; I_THM]; REPEAT GEN_TAC
THEN REWRITE_TAC[iterate_map; o_DEF] THEN ASM_MESON_TAC[]]);;

let orbit_subset = prove(`!(s:A->bool) (u:A->A). u permutes s ==> !(x:A).
x IN s ==> (orbit_map u x) SUBSET s`,
REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; orbit_map; IN_ELIM_THM] THEN
ASM_MESON_TAC[iterate_orbit]);;

let comm_iterate_map = prove(`!(n:num) (f:A->A). iterate_map f (SUC n) = f
o (iterate_map f n)`,
INDUCT_TAC THENL[ REWRITE_TAC [ARITH_RULE `(SUC 0) = 1`; iterate_map;
I_O_ID];
REPEAT STRIP_TAC THEN POP_ASSUM(ASSUME_TAC o GSYM o (ISPEC `f:A->A`))
THEN ASM_REWRITE_TAC[iterate_map; o_ASSOC]]);;

let addition_exponents = prove(`!m n (f:A->A). iterate_map f (m + n) =
(iterate_map f m) o (iterate_map f n)`,
INDUCT_TAC THENL [STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `(0 + n) = n`;
iterate_map; I_O_ID];
POP_ASSUM(ASSUME_TAC o GSYM o (ISPECL[`n:num`;`f:A->A`]))
THEN REWRITE_TAC[comm_iterate_map; GSYM o_ASSOC]
THEN ASM_REWRITE_TAC[comm_iterate_map; GSYM o_ASSOC;
ARITH_RULE `(SUC m + n) = SUC (m + n)`] ]);;

let multiplication_exponents = prove(`!m n (f:A->A). iterate_map f (m * n)
= iterate_map (iterate_map f n) m`, INDUCT_TAC THENL [STRIP_TAC THEN
REWRITE_TAC[ARITH_RULE `(0 * n) = 0`; iterate_map; I_O_ID]; ALL_TAC] THEN
REPEAT GEN_TAC THEN POP_ASSUM(ASSUME_TAC o (SPECL[`n:num`; `f:A->A`]))
THEN ASM_REWRITE_TAC[ARITH_RULE `SUC m * n = m * n + n`;
addition_exponents;iterate_map]);;


let power_unit_map = prove(`!n f:A->A. iterate_map f n = I ==> !m.
iterate_map f (m * n) = I`,
REPLICATE_TAC 3 STRIP_TAC THEN INDUCT_TAC THENL[REWRITE_TAC[ARITH_RULE `(0
* n) = 0`;
iterate_map]; REWRITE_TAC[ARITH_RULE `(SUC m * n) = (m * n) + n`;
addition_exponents]
THEN ASM_REWRITE_TAC[I_O_ID]]);;

let power_map_fix_point = prove(`!n f:A->A x:A. (iterate_map f n) x = x
==> !m. (iterate_map f (m * n)) x = x`,
REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
[REWRITE_TAC[ARITH_RULE `(0 * n) = 0`;
iterate_map; I_THM]; REWRITE_TAC[ARITH_RULE `(SUC m * n) = (m * n) + n`;
addition_exponents; o_DEF]
THEN ASM_REWRITE_TAC[]]);;

let orbit_cyclic = prove(`!(f:A->A) m:num (x:A). ~(m = 0) /\ (iterate_map
f m) x = x ==> orbit_map f x = {(iterate_map f k) x | k < m}`, REPEAT
STRIP_TAC THEN REWRITE_TAC[orbit_map; EXTENSION; IN_ELIM_THM] THEN GEN_TAC
THEN EQ_TAC THENL [ STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIND_ASSUM
(MP_TAC o (SPEC `n:num`) o MATCH_MP DIVMOD_EXIST) `~(m:num = 0)` THEN
REPEAT STRIP_TAC THEN UNDISCH_THEN `iterate_map (f:A->A) (m:num) (x:A) =
x` (ASSUME_TAC o (SPEC `q:num`) o MATCH_MP power_map_fix_point) THEN
ASM_REWRITE_TAC[ADD_SYM; addition_exponents; o_DEF] THEN EXISTS_TAC
`r:num` THEN ASM_SIMP_TAC[]; REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
EXISTS_TAC `k:num`THEN SIMP_TAC[ARITH_RULE `k >= 0`]]);;


(* Some lemmas on the cardinality of finite series *)

let LT_RIGHT_SUC = prove(`!i n. i < n ==> i < SUC n`,
REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `i < n ==>
SUC i < SUC n`))
THEN MP_TAC (ARITH_RULE `i < SUC i`) THEN ARITH_TAC);;

let INSERT_IN_SET = prove(`!x s. x IN s ==> x INSERT s = s`, REPEAT
GEN_TAC THEN SET_TAC[]);;


let NULL_SERIES = prove(`!f. {f(i) | i < 0} = {}`,
GEN_TAC THEN REWRITE_TAC[EXTENSION; EMPTY; IN_ELIM_THM] THEN REPEAT STRIP_TAC
THEN FIRST_ASSUM (MP_TAC o MATCH_MP ( ARITH_RULE `i < 0 ==> F`)) THEN
SIMP_TAC[]);;

let INSERT_SERIES = prove(`!n f. {f(i) | i < SUC n} = f(n) INSERT {f(i) |
i < n}`,
REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; INSERT; IN_ELIM_THM] THEN
GEN_TAC THEN EQ_TAC
THENL[STRIP_TAC
THEN FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE `i < SUC n ==> i
< n \/ i = n`))
THENL[DISJ1_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; DISJ2_TAC
THEN ASM_REWRITE_TAC[]]; DISCH_THEN DISJ_CASES_TAC
THENL[POP_ASSUM(X_CHOOSE_THEN `i:num` ASSUME_TAC)
THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN  FIRST_ASSUM (MP_TAC o
CONJUNCT1)
THEN DISCH_THEN(MP_TAC o MATCH_MP LT_RIGHT_SUC) THEN SIMP_TAC[];
EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]]);;

let FINITE_SERIES = prove(`!(n:num) (f:num->A). FINITE {f(i) | i < n}`,
INDUCT_TAC THENL[GEN_TAC THEN ASSUME_TAC(ISPEC `f:num->A` NULL_SERIES)
THEN ASM_REWRITE_TAC[FINITE_RULES]; GEN_TAC THEN POP_ASSUM(ASSUME_TAC o
(ISPEC `f:num->A`))
THEN SUBST1_TAC (ISPECL [`n:num`; `f:num->A`] INSERT_SERIES)
THEN MP_TAC (ISPECL[` f(n):A`; `{f i | i < n}:A->bool`] (CONJUNCT2
FINITE_RULES))
THEN ASM_MESON_TAC[FINITE_RULES; INSERT_SERIES] ]);;

let IMAGE_SEG = prove(`!(n:num) (f:num->A). ~(n = 0) ==> IMAGE f (0..n-1)
= {f(i) | i < n}`,
REPEAT STRIP_TAC THEN REWRITE_TAC[IMAGE; numseg; EXTENSION; IN_ELIM_THM]
THEN GEN_TAC
THEN SPEC_TAC(`x:A`, `t:A`) THEN GEN_TAC THEN EQ_TAC
THENL [DISCH_THEN(X_CHOOSE_THEN `x:num` MP_TAC)
THEN REPEAT STRIP_TAC THEN EXISTS_TAC `x:num`
THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `~(n = 0) ==> (x <= n-1
==> x < n)`))
THEN ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `i:num` MP_TAC)
THEN REPEAT STRIP_TAC THEN EXISTS_TAC `i:num`
THEN FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `~(n = 0) ==> (i < n ==> i
<= n-1)`))
THEN ASSUME_TAC (ARITH_RULE `0 <= i`) THEN ASM_REWRITE_TAC[]]);;

let CARD_FINITE_SERIES_LE  = prove(`!(n:num) (f:num->A). CARD {f(i) | i <
n} <= n`,
REPEAT GEN_TAC THEN DISJ_CASES_TAC (ARITH_RULE `(n = 0) \/ ~(n = 0)`)
THENL [ASM_SIMP_TAC[] THEN SUBST1_TAC (ISPEC `f:num->A` NULL_SERIES)
THEN MP_TAC(CONJUNCT1 CARD_CLAUSES) THEN ARITH_TAC;
FIRST_ASSUM(SUBST1_TAC o GSYM o (ISPEC `f:num->A`) o MATCH_MP IMAGE_SEG)
THEN ASSUME_TAC (SPECL[`0`; `(n-1):num`] FINITE_NUMSEG)
THEN MP_TAC (ISPECL[`f:num->A`; `(0..n-1):num->bool`] CARD_IMAGE_LE) THEN
ASM_REWRITE_TAC[]
THEN ASSUME_TAC(SPECL[`0`; `(n-1):num`] CARD_NUMSEG)
THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP(ARITH_RULE `~(n = 0) ==> (n - 1 +
1) - 0 = n`))
THEN ASM_REWRITE_TAC[] ]);;

let LEMMA_INJ = prove(`(!(n:num) (f:num->A). ~(n = 0) ==> (!i:num j:num. i
< n /\ j < i ==> ~(f(i) = f(j))) ==> (!x:num y:num. x IN 0..n - 1 /\ y IN
0..n - 1 /\ f x = f y ==> x = y))`,
REWRITE_TAC[numseg; IN_ELIM_THM; ARITH_RULE `0 <= x /\ 0 <= y`] THEN
REPEAT STRIP_TAC
THEN SIMP_TAC[ARITH_RULE `(x = y) <=> ~(x < y \/ y < x)`] THEN STRIP_TAC
THENL[FIRST_X_ASSUM(MP_TAC o (SPECL[`y:num`;`x:num`])) THEN SIMP_TAC[NOT_IMP]
THEN ASM_REWRITE_TAC[] THEN MP_TAC (ARITH_RULE `~(n = 0) /\ (y <= n-1) ==>
y < n`)
THEN ASM_REWRITE_TAC[]; FIRST_X_ASSUM(MP_TAC o (SPECL[`x:num`;`y:num`]))
THEN SIMP_TAC[NOT_IMP] THEN ASM_REWRITE_TAC[]
THEN MP_TAC (ARITH_RULE `~(n = 0) /\ (x <= n-1) ==> x < n`) THEN
ASM_REWRITE_TAC[] ]);;

let CARD_FINITE_SERIES_EQ  = prove(
`!(n:num) (f:num->A). (!i:num j:num. i < n /\  j < i ==> ~(f(i) = f(j)))
==> CARD {f(i) | i < n} = n`,
REPEAT GEN_TAC THEN DISJ_CASES_TAC (ARITH_RULE `(n = 0) \/ ~(n = 0)`)
THENL [ASM_SIMP_TAC[] THEN SUBST1_TAC (ISPEC `f:num->A` NULL_SERIES) THEN
MP_TAC(CONJUNCT1 CARD_CLAUSES) THEN ARITH_TAC; ALL_TAC]
THEN FIRST_ASSUM(SUBST1_TAC o GSYM o (ISPEC `f:num->A`) o MATCH_MP IMAGE_SEG)
THEN ASSUME_TAC (SPECL[`0`; `(n-1):num`] FINITE_NUMSEG) THEN DISCH_TAC
THEN MP_TAC(ISPECL[`n:num`; `f:num->A`] LEMMA_INJ) THEN ASM_REWRITE_TAC[]
THEN STRIP_TAC THEN MP_TAC (ISPECL[`f:num->A`; `(0..n-1):num->bool`]
CARD_IMAGE_INJ)
THEN ASM_REWRITE_TAC[] THEN ASSUME_TAC(SPECL[`0`; `(n-1):num`] CARD_NUMSEG)
THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP(ARITH_RULE `~(n = 0) ==> (n - 1 +
1) - 0 = n`))
THEN ASM_REWRITE_TAC[]);;


(* In arbitrary finite group, every element has finite order *)


let power_permutation = prove(`!(s:A->bool) (p:A->A). p permutes s ==>
!(n:num). (iterate_map p n) permutes s`, REPLICATE_TAC 3 STRIP_TAC THEN
INDUCT_TAC THENL[REWRITE_TAC[iterate_map; PERMUTES_I];
REWRITE_TAC[iterate_map] THEN ASM_MESON_TAC[PERMUTES_COMPOSE]]);;

let LM_AUX = prove(`!m n. m < n ==> ?k. ~(k = 0) /\ n = m + k`,
REPEAT GEN_TAC THEN REWRITE_TAC[LT_EXISTS] THEN DISCH_THEN(X_CHOOSE_THEN
`d:num` ASSUME_TAC)
THEN EXISTS_TAC `SUC d` THEN ASM_REWRITE_TAC[ARITH_RULE `~(SUC d = 0)`]);;


let LM1 = prove(`!s:A->bool p:A->A n:num m:num. p permutes s /\
iterate_map p (m+n) = iterate_map p m ==> iterate_map p n = I`,
REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (MP_TAC))
THEN REWRITE_TAC[addition_exponents] THEN DISCH_TAC THEN
REMOVE_THEN "c1" (ASSUME_TAC o (SPEC `m:num`) o MATCH_MP power_permutation)
THEN MP_TAC (SPECL[`s:A->bool`; `(iterate_map (p:A->A) m):A->A`;
`(iterate_map (p:A->A) n):A->A`; `(iterate_map (p:A->A) m):A->A`]
LEFT_INVERSE_EQUATION)
THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o CONJUNCT2 o (MATCH_MP
PERMUTES_INVERSES_o))
THEN SIMP_TAC[]);;

let inj_iterate_segment = prove(`!s:A->bool p:A->A (n:num). p permutes s
/\ ~(n=0) ==> (!m. ~(m = 0) /\ (m < n) ==> ~(iterate_map p m = I)) ==> (!i
j. (i < n) /\ (j < i) ==> ~(iterate_map p i = iterate_map p j))`,
REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c2") (ASSUME_TAC))
THEN DISCH_THEN (LABEL_TAC "c3") THEN REPLICATE_TAC 3 STRIP_TAC
THEN DISCH_THEN (LABEL_TAC "c4") THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP LM_AUX)
THEN REPEAT STRIP_TAC THEN REMOVE_THEN "c3" MP_TAC THEN
REWRITE_TAC[NOT_FORALL_THM; NOT_IMP]
THEN EXISTS_TAC `k:num` THEN MP_TAC (ARITH_RULE `(i< n) /\ (i = j + k) ==>
k < n`)
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
THEN REMOVE_THEN "c4" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THEN MP_TAC (ISPECL[`s:A->bool`; `p:A->A`; `k:num`; `j:num`] LM1) THEN
ASM_REWRITE_TAC[]);;

let inj_iterate_lemma = prove(`!s:A->bool p:A->A. p permutes s /\
(!(n:num). ~(n = 0) ==> ~(iterate_map p n = I)) ==> (!m. CARD
({iterate_map p k | k < m}) = m)`,
REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "c1")
(LABEL_TAC "c2"))
THEN GEN_TAC THEN  SUBGOAL_THEN `!i:num j:num. i < (m:num) /\  j < i ==>
~(iterate_map (p:A->A) i = iterate_map p j)` ASSUME_TAC
THENL [ REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM (MP_TAC o MATCH_MP
LM_AUX)
THEN STRIP_TAC THEN ASM_REWRITE_TAC[]  THEN STRIP_TAC
THEN MP_TAC (ISPECL[`s:A->bool`; `p:A->A`; `k:num`; `j:num`] LM1) THEN
ASM_REWRITE_TAC[]
THEN STRIP_TAC THEN REMOVE_THEN "c2" (MP_TAC o SPEC(`k:num`)) THEN
REWRITE_TAC[NOT_IMP]
THEN ASM_REWRITE_TAC[]; POP_ASSUM(MP_TAC o MATCH_MP CARD_FINITE_SERIES_EQ)
THEN SIMP_TAC[]]);;


(* Two following therems in files: sets.ml *)

let NEW_FINITE_SUBSET = prove(`!(s:(A->A)->bool) t. FINITE t /\ s SUBSET t
==> FINITE s`,
ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN REWRITE_TAC[IMP_CONJ]
THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC FINITE_INDUCT
THEN CONJ_TAC THENL [MESON_TAC[SUBSET_EMPTY; FINITE_RULES]; ALL_TAC]
THEN X_GEN_TAC `x:(A->A)` THEN X_GEN_TAC `u:(A->A)->bool` THEN DISCH_TAC
THEN X_GEN_TAC `t:(A->A)->bool` THEN DISCH_TAC
THEN SUBGOAL_THEN `FINITE((x:A->A) INSERT (t DELETE x))` ASSUME_TAC
THENL [MATCH_MP_TAC(CONJUNCT2 FINITE_RULES) THEN FIRST_ASSUM MATCH_MP_TAC
THEN UNDISCH_TAC `t SUBSET (x:A->A INSERT u)` THEN SET_TAC[];
ASM_CASES_TAC `x:A->A IN t`
THENL [SUBGOAL_THEN `x:A->A INSERT (t DELETE x) = t` SUBST_ALL_TAC
THENL [UNDISCH_TAC `x:A->A IN t` THEN SET_TAC[]; ASM_REWRITE_TAC[]];
FIRST_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `t SUBSET x:A->A INSERT u`
THEN UNDISCH_TAC `~(x:A->A IN t)` THEN SET_TAC[]]]);;

let NEW_CARD_SUBSET = prove (`!(a:(A->A)->bool) b. a SUBSET b /\ FINITE(b)
==> CARD(a) <= CARD(b)`,
REPEAT STRIP_TAC THEN SUBGOAL_THEN `b:(A->A)->bool = a UNION (b DIFF a)`
SUBST1_TAC
THENL [UNDISCH_TAC `a:(A->A)->bool SUBSET b` THEN SET_TAC[]; ALL_TAC]
THEN SUBGOAL_THEN `CARD (a UNION b DIFF a) = CARD(a:(A->A)->bool) + CARD(b
DIFF a)` SUBST1_TAC
THENL [MATCH_MP_TAC CARD_UNION THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC
NEW_FINITE_SUBSET
THEN EXISTS_TAC `b:(A->A)->bool` THEN ASM_REWRITE_TAC[]; MATCH_MP_TAC
NEW_FINITE_SUBSET
THEN EXISTS_TAC `b:(A->A)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
SET_TAC[]]; ARITH_TAC]);;

(* finite order theorem on every element in arbitrary finite group *)

let finite_order = prove(
`!s:A->bool p:A->A. FINITE s /\ p permutes s ==> ?(n:num). ~(n = 0) /\
iterate_map p n = I`,
REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1")
(ASSUME_TAC)) THEN
ASM_CASES_TAC `?(n:num). ~(n = 0) /\ iterate_map (p:A->A) n = I` THENL [
ASM_SIMP_TAC[]; ALL_TAC]
THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM; TAUT
`!a b. ~(a /\ b) = (a ==> ~b)`]
THEN DISCH_TAC THEN MP_TAC (ISPECL[`s:A->bool`; `p:A->A`] inj_iterate_lemma)
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN USE_THEN "c1" (ASSUME_TAC o MATCH_MP FINITE_PERMUTATIONS)
THEN ABBREV_TAC `md = SUC(CARD({p | p permutes (s:A->bool)}))`
THEN SUBGOAL_THEN `{iterate_map (p:A->A) k | k < (md:num)} SUBSET {p | p
permutes (s:A->bool)}` ASSUME_TAC
THENL [ REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
ASM_MESON_TAC[power_permutation]; ALL_TAC]
THEN MP_TAC (ISPECL[`{iterate_map (p:A->A) k | k < (md:num)}`;`{p | p
permutes (s:A->bool)}`] NEW_CARD_SUBSET)
THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "md" THEN ARITH_TAC);;

let inverse_element_lemma = prove(`!s:A->bool p:A->A. FINITE s /\ p
permutes s ==> ?j:num. inverse p = iterate_map p j`,
REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC (MATCH_MP finite_order th)
THEN ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT2 th))
THEN STRIP_TAC THEN MP_TAC (ARITH_RULE `~(n = 0) ==> n = 1 + (PRE n)`)
THEN ASM_REWRITE_TAC[]
THEN DISCH_TAC THEN UNDISCH_TAC `iterate_map (p:A->A) (n:num) = I` THEN 
ONCE_ASM_REWRITE_TAC[]
THEN ASM_REWRITE_TAC[addition_exponents; iterate_map1]
THEN UNDISCH_TAC `p:A->A permutes s:A->bool` THEN REWRITE_TAC[IMP_IMP]
THEN DISCH_THEN (MP_TAC o MATCH_MP LEFT_INVERSE_EQUATION) THEN
REWRITE_TAC[I_O_ID]
THEN DISCH_THEN (ASSUME_TAC o SYM) THEN EXISTS_TAC `PRE n` THEN
ASM_SIMP_TAC[]);;


(* some properties of orbits *)

let orbit_reflect = prove(`!f:A->A x:A. x IN (orbit_map f x)`, REPEAT
GEN_TAC THEN REWRITE_TAC[orbit_map; IN_ELIM_THM] THEN EXISTS_TAC `0` THEN
REWRITE_TAC[iterate_map; ARITH_RULE `0>=0`;I_THM]);;

let orbit_sym = prove(`!s:A->bool p:A->A x:A y:A. FINITE s /\ p permutes s
==> (x IN (orbit_map p y) ==> y IN (orbit_map p x))`, REPLICATE_TAC 5
STRIP_TAC THEN REWRITE_TAC[orbit_map; IN_ELIM_THM] THEN  STRIP_TAC THEN
FIND_ASSUM (ASSUME_TAC o (SPEC `n:num`) o MATCH_MP power_permutation)
`p:A->A permutes s` THEN POP_ASSUM (MP_TAC o (SPECL[`y:A`; `x:A`]) o
MATCH_MP PERMUTES_INVERSE_EQ) THEN POP_ASSUM(ASSUME_TAC o SYM) THEN
ASM_REWRITE_TAC[] THEN UNDISCH_THEN `p:A->A permutes s` (ASSUME_TAC o
(SPEC `n:num`) o MATCH_MP power_permutation) THEN
MP_TAC(SPECL[`s:A->bool`; `iterate_map (p:A->A) (n:num)`]
inverse_element_lemma) THEN ASM_REWRITE_TAC[GSYM multiplication_exponents]
THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC
`(j:num) * n` THEN ASM_REWRITE_TAC[ARITH_RULE `j * n >= 0`]);;

let orbit_trans = prove(`!f:A->A x:A y:A z:A. x IN orbit_map f y /\ y IN
orbit_map f z ==> x IN orbit_map f z`,  REPEAT GEN_TAC THEN
REWRITE_TAC[orbit_map; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN 
UNDISCH_THEN `x:A = iterate_map f n y` MP_TAC THEN  ASM_REWRITE_TAC[] THEN
 DISCH_THEN (ASSUME_TAC o SYM) THEN MP_TAC (SPECL[`n:num`; `n':num`;
`f:A->A`] addition_exponents) THEN  DISCH_THEN(fun th -> MP_TAC (AP_THM th
`z:A`)) THEN ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN (ASSUME_TAC o SYM)
THEN EXISTS_TAC `(n:num) + n'` THEN ASM_REWRITE_TAC[ARITH_RULE `n+n'
>=0`]);;

let in_orbit_lemma = prove(`!f:A->A n:num x:A y:A. y = (iterate_map f n) x
 ==> y IN orbit_map f x`, REPEAT STRIP_TAC THEN REWRITE_TAC[orbit_map;
IN_ELIM_THM] THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[ARITH_RULE
`n>=0`]);;


let partition_orbit = prove(`!s:A->bool p:A->A. FINITE s /\ p permutes s
==>(!x:A y:A. (orbit_map p x INTER orbit_map p y = {}) \/ (orbit_map p x =
orbit_map p y))`, REPEAT STRIP_TAC THEN ASM_CASES_TAC `orbit_map (p:A->A)
(x:A) INTER orbit_map (p:A->A) (y:A) = {}` THENL[ASM_REWRITE_TAC[];
ALL_TAC] THEN DISJ2_TAC THEN  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM
MEMBER_NOT_EMPTY] THEN REWRITE_TAC[INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
MP_TAC (SPECL[`s:A->bool`; `p:A->A`; `x':A`; `x:A`] orbit_sym) THEN
ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MP_TAC (SPECL[`s:A->bool`; `p:A->A`;
`x':A`; `y:A`] orbit_sym) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN EQ_TAC THENL [STRIP_TAC THEN
MP_TAC (SPECL[`p:A->A`; `x'':A`; `x:A`;`x':A`] orbit_trans) THEN
ASM_MESON_TAC[orbit_trans]; STRIP_TAC THEN MP_TAC (SPECL[`p:A->A`;
`x'':A`; `y:A`;`x':A`] orbit_trans) THEN ASM_MESON_TAC[orbit_trans]]);;

let card_orbit_le = prove(`!f:A->A n:num x:A. ~(n = 0) /\ (iterate_map f
n) x = x ==> CARD(orbit_map f x) <= n`, REPEAT GEN_TAC THEN DISCH_THEN
(fun th -> SUBST1_TAC (MATCH_MP orbit_cyclic th) THEN ASSUME_TAC
(CONJUNCT1 th)) THEN MP_TAC (SPECL[`n:num`; `(\k. (iterate_map (f:A->A) k)
(x:A))`] CARD_FINITE_SERIES_LE) THEN MESON_TAC[]);;




(* some properties of hypermap *)


let cyclic_maps = prove(`!D:A->bool e:A->A n:A->A f:A->A. (FINITE D) /\ e
permutes D /\ n permutes D /\ f permutes D /\ e o n o f = I ==> (n o f o e
= I) /\ (f o e o n = I)`, REPEAT STRIP_TAC THENL[ MP_TAC
(ISPECL[`D:A->bool`;`e:A->A`; `(n:A->A) o (f:A->A)`; `I:A->A`]
LEFT_INVERSE_EQUATION) THEN ASM_REWRITE_TAC[I_O_ID] THEN FIND_ASSUM
(ASSUME_TAC o CONJUNCT2 o MATCH_MP PERMUTES_INVERSES_o) `e:A->A permutes
D:A->bool` THEN DISCH_TAC THEN MP_TAC (ISPECL[`(n:A->A)o(f:A->A)`;
`inverse(e:A->A)`;`e:A->A` ] RIGHT_MULT_MAP) THEN
ASM_REWRITE_TAC[o_ASSOC]; MP_TAC (ISPECL[`D:A->bool`;`(e:A->A)o(n:A->A)`;
`(f:A->A)`; `I:A->A`] RIGHT_INVERSE_EQUATION) THEN ASM_REWRITE_TAC[I_O_ID;
GSYM o_ASSOC] THEN DISCH_TAC  THEN MP_TAC (ISPECL[`D:A->bool`;`(e:A->A) o
(n:A->A)`; `(f:A->A)`; `I:A->A`] RIGHT_INVERSE_EQUATION) THEN
ASM_REWRITE_TAC[GSYM o_ASSOC; I_O_ID] THEN FIND_ASSUM (ASSUME_TAC o
CONJUNCT1 o MATCH_MP PERMUTES_INVERSES_o) `f:A->A permutes D:A->bool` THEN
ASM_SIMP_TAC[]]);;


let cyclic_inverses_maps = prove(`!D:A->bool e:A->A n:A->A f:A->A. (FINITE
D) /\ e permutes D /\ n permutes D /\ f permutes D /\ e o n o f = I ==>
inverse n o inverse e o inverse f = I`, REPEAT STRIP_TAC THEN MP_TAC
(ISPECL[`D:A->bool`; `e:A->A`; `n:A->A`; `f:A->A`] cyclic_maps) THEN
ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN  MP_TAC
(ISPECL[`D:A->bool`;`f:A->A`; `(e:A->A) o (n:A->A)`; `I:A->A`]
LEFT_INVERSE_EQUATION) THEN ASM_REWRITE_TAC[I_O_ID] THEN STRIP_TAC THEN
MP_TAC (ISPECL[`D:A->bool`;`e:A->A`; `(n:A->A)`; `inverse(f:A->A)`]
LEFT_INVERSE_EQUATION) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN  MP_TAC
(ISPECL[`inverse(n:A->A)`; `n:A->A`; `inverse(e:A->A) o inverse(f:A->A)`]
LEFT_MULT_MAP) THEN FIND_ASSUM (ASSUME_TAC o CONJUNCT2 o MATCH_MP
PERMUTES_INVERSES_o) `n:A->A permutes D:A->bool` THEN ASM_REWRITE_TAC[]
THEN DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[]);;


let lemma5dot1 = prove(`!H:(A)hypermap. (simple_hypermap H /\
plain_hypermap H /\ (!x:A. x IN dart H ==> CARD (face H x) >= 3)) ==>
(!x:A. x IN dart H ==> ~(node_map H x = x))`,
GEN_TAC THEN REWRITE_TAC[simple_hypermap; plain_hypermap;face; node] THEN
MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma)
THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2
(LABEL_TAC "c2") (CONJUNCTS_THEN2 (LABEL_TAC "c3") (CONJUNCTS_THEN2
(LABEL_TAC "c4") (LABEL_TAC "c5")))))
THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c6") (CONJUNCTS_THEN2
(LABEL_TAC "c7") (LABEL_TAC "c8")))
THEN GEN_TAC THEN DISCH_THEN (LABEL_TAC "c9") THEN DISCH_THEN (LABEL_TAC
"c10")
THEN ABBREV_TAC `D = dart (H:(A)hypermap)` THEN ABBREV_TAC `e = edge_map
(H:(A)hypermap)`  THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` THEN
ABBREV_TAC `f = face_map (H:(A)hypermap)`
THEN USE_THEN "c2" (MP_TAC o (SPEC `x:A`) o MATCH_MP PERMUTES_IN_IMAGE)
THEN USE_THEN "c4" (MP_TAC o (SPEC `x:A`) o MATCH_MP PERMUTES_IN_IMAGE)
THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ABBREV_TAC `y:A =
(f:A->A) (x:A)` THEN ABBREV_TAC `z:A = (e:A->A) (x:A)`
THEN USE_THEN "c7" MP_TAC THEN USE_THEN "c2" MP_TAC THEN REWRITE_TAC[IMP_IMP]
THEN DISCH_THEN (MP_TAC o MATCH_MP LEFT_INVERSE_EQUATION) THEN
REWRITE_TAC[I_O_ID]
THEN DISCH_THEN(fun th -> (ASSUME_TAC (SYM th)) THEN (ASSUME_TAC (AP_THM
(SYM th) `x:A`)))
THEN USE_THEN "c3" (MP_TAC o (SPECL[`x:A`;`x:A`]) o MATCH_MP
PERMUTES_INVERSE_EQ)
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN USE_THEN "c5" MP_TAC
THEN USE_THEN "c2" MP_TAC THEN REWRITE_TAC[IMP_IMP]
THEN DISCH_THEN (MP_TAC o MATCH_MP LEFT_INVERSE_EQUATION) THEN
REWRITE_TAC[I_O_ID]
THEN DISCH_THEN(fun th -> (ASSUME_TAC (SYM th)) THEN (MP_TAC (AP_THM (SYM
th) `x:A`)))
THEN ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN (MP_TAC o SYM)
THEN MP_TAC (SPECL[`D:A->bool`; `e:A->A`; `n:A->A`; `f:A->A`] cyclic_maps)
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (fun th -> MP_TAC (AP_THM
(CONJUNCT2 th) `x:A`))
THEN ASM_REWRITE_TAC[o_THM; I_THM] THEN DISCH_THEN (MP_TAC o AP_TERM
`f:A->A`) THEN ASM_REWRITE_TAC[]
THEN DISCH_THEN (LABEL_TAC "c11") THEN DISCH_THEN (LABEL_TAC "c12")
THEN MP_TAC (SPECL[`f:A->A`; `2`; `z:A`; `y:A`] in_orbit_lemma) THEN
ASM_REWRITE_TAC[iterate_map2; o_THM]
THEN DISCH_TAC THEN MP_TAC (SPECL[`D:A->bool`; `f:A->A`; `y:A`; `z:A`]
orbit_sym)
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "d1") THEN MP_TAC
(SPECL[`n:A->A`; `1`; `y:A`; `z:A`] in_orbit_lemma)
THEN ASM_REWRITE_TAC[iterate_map1] THEN DISCH_THEN (LABEL_TAC "d2")
THEN REMOVE_THEN "c6" (MP_TAC o (SPEC `y:A`))
THEN UNDISCH_TAC `(y:A) IN D` THEN ASM_REWRITE_TAC[IN] THEN STRIP_TAC
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THEN MP_TAC (SPECL[`orbit_map (n:A->A) (y:A)`;`orbit_map (f:A->A) (y:A)`;
`z:A`] IN_INTER)
THEN ASM_REWRITE_TAC[IN_SING] THEN STRIP_TAC
THEN REMOVE_THEN "c11" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC (SPECL[`f:A->A`; `2`; `y:A`] card_orbit_le)
THEN ASM_REWRITE_TAC[ARITH; iterate_map2; o_DEF] THEN DISCH_TAC
THEN REMOVE_THEN "c8" (MP_TAC o (SPEC `y:A`)) THEN ASM_REWRITE_TAC[IN]
THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;


(* Definition of connected *)

let connected_hypermap = new_definition `connected_hypermap (H:(A)hypermap) <=> number_of_components H = 1`;;

(* Some lemmas about counting the orbits of a permutation *)



let finite_orbits_lemma = prove(`!D:A->bool p:A->A. (FINITE D /\ p permutes D) ==> FINITE (set_of_orbits D p)`, REPEAT STRIP_TAC THEN SUBGOAL_THEN `IMAGE (\x:A. orbit_map (p:A->A) x) (D:A->bool) = set_of_orbits D p` ASSUME_TAC THENL[REWRITE_TAC[EXTENSION] THEN STRIP_TAC THEN EQ_TAC THENL[REWRITE_TAC[set_of_orbits;IMAGE;IN;IN_ELIM_THM];ALL_TAC] THEN REWRITE_TAC[set_of_orbits;IMAGE;IN;IN_ELIM_THM];ALL_TAC] THEN POP_ASSUM (fun th -> REWRITE_TAC[SYM th]) THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[]);;


let lemma_disjoints = prove(`!(s:(A->bool)->bool) (t:A->bool). (!(v:A->bool). v IN s ==> DISJOINT t v) ==> DISJOINT t (UNIONS s)`, SET_TAC[]);;


let SET_SIZE_CLAUSES = prove (`(!s. s HAS_SIZE 0 <=> (s = {})) /\(!s (n:num). s HAS_SIZE (SUC n) <=> ?a t. t HAS_SIZE n /\ ~(a IN t) /\ (s = a INSERT t))`,let lemma = SET_RULE `a IN s ==> (s = a INSERT (s DELETE a))` in REWRITE_TAC[HAS_SIZE_0] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL [REWRITE_TAC[HAS_SIZE_SUC; GSYM MEMBER_NOT_EMPTY] THEN MESON_TAC[lemma; IN_DELETE]; SIMP_TAC[LEFT_IMP_EXISTS_THM; HAS_SIZE; CARD_CLAUSES; FINITE_INSERT]]);;


let TYPED_FINITE_UNIONS = prove
 (`!s:(A->bool)->bool. FINITE(s) ==> (FINITE(UNIONS s) <=> (!g:A->bool. g IN s ==> FINITE(g)))`,
  MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; UNIONS_0; UNIONS_INSERT] THEN
  REWRITE_TAC[FINITE_UNION; FINITE_RULES] THEN MESON_TAC[]);;


let lemma_card_ge = prove
(`!(n:num) (s:(A->bool)->bool) (m:num). ((FINITE s /\ CARD(s) = n) /\ (!u:A->bool v:A->bool. (u IN s /\ v IN s) ==> (u = v \/ DISJOINT u v)) /\ (!g:A->bool.(g IN s) ==> (FINITE g /\ CARD(g) >= m))) ==> (CARD(UNIONS s) >= m * CARD(s))`, 
INDUCT_TAC 
THENL[REPEAT STRIP_TAC THEN MP_TAC(ISPECL[`s:(A->bool)->bool`]  CARD_EQ_0) 
THEN ASM_REWRITE_TAC[ARITH_RULE `m * 0=0`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[UNIONS_0] 
THEN SIMP_TAC[CONJUNCT1 CARD_CLAUSES;ARITH];ALL_TAC]

THEN POP_ASSUM (LABEL_TAC "f0") THEN REPEAT GEN_TAC 
THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f1") (CONJUNCTS_THEN2 (LABEL_TAC "f2") (LABEL_TAC "f3"))) 
THEN MP_TAC(ISPECL[`s:(A->bool)->bool`;`SUC(n:num)`] HAS_SIZE) THEN ASM_SIMP_TAC[] THEN DISCH_THEN(LABEL_TAC "F4") 
THEN MP_TAC (ISPECL[`s:(A->bool)->bool`; `n:num`] (CONJUNCT2 SET_SIZE_CLAUSES)) THEN ASM_SIMP_TAC[] 
THEN DISCH_THEN (X_CHOOSE_THEN `a:(A->bool)` MP_TAC) THEN DISCH_THEN (X_CHOOSE_THEN `t:(A->bool)->bool` MP_TAC) 
THEN REWRITE_TAC[HAS_SIZE] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f5") (CONJUNCTS_THEN2 (LABEL_TAC "f6") (LABEL_TAC "f7")))
THEN MP_TAC (SET_RULE `UNIONS(a:A->bool INSERT t:(A->bool)->bool) = a UNION (UNIONS  t)`) THEN ASM_REWRITE_TAC[]
THEN SUBGOAL_THEN `DISJOINT (a:A->bool) (UNIONS (t:(A->bool)->bool))` (LABEL_TAC "F8") 

THENL[POP_ASSUM SUBST_ALL_TAC 
THEN MATCH_MP_TAC lemma_disjoints THEN GEN_TAC THEN DISCH_THEN(LABEL_TAC "f9") THEN USE_THEN "f2"(MP_TAC o SPEC `a:A->bool`) 
THEN DISCH_THEN(MP_TAC o SPEC `v:A->bool`) THEN REWRITE_TAC[SET_RULE `a IN a INSERT t`] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INSERT] 
THEN DISJ_CASES_TAC (SET_RULE `(a:A->bool = v:A->bool) \/ ~(a = v)`) 
THENL[MP_TAC (MESON[] ` (a:A->bool = v:A->bool) /\ (v IN t:(A->bool)->bool) ==> a IN t`) 
THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]]; ALL_TAC] 

THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN MP_TAC(ISPECL[`a:A->bool`;`(UNIONS (t:(A->bool)->bool))`] CARD_UNION) 
THEN POP_ASSUM MP_TAC THEN SIMP_TAC[DISJOINT] THEN STRIP_TAC THEN REMOVE_THEN "f7"(SUBST_ALL_TAC)
THEN USE_THEN "f3"(MP_TAC o SPEC `a:A->bool`) THEN REWRITE_TAC[SET_RULE `a IN a INSERT t`] 
THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MP_TAC (ISPECL[`t:(A->bool)->bool`] TYPED_FINITE_UNIONS) 
THEN MP_TAC(SET_RULE  `(!g:A->bool. g IN ((a:A->bool) INSERT (t:(A->bool)->bool)) ==> (FINITE g) /\ (CARD g >= (m:num))) ==> (!g:A->bool. g IN (t:(A->bool)->bool) ==> FINITE g /\ CARD g >= m)`) 
THEN MP_TAC(SET_RULE `(s:(A->bool)->bool = (a:A->bool) INSERT (t:(A->bool)->bool)) /\ (!g:A->bool. g IN s ==> FINITE g) ==> FINITE a`) 
THEN USE_THEN "f3" (MP_TAC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] 
 THEN REWRITE_TAC[MULT_SUC] 
THEN MP_TAC(SET_RULE  `(!g:A->bool. g IN ((a:A->bool) INSERT (t:(A->bool)->bool)) ==> (FINITE g) /\ (CARD g >= (m:num))) ==> (!g:A->bool. g IN (t:(A->bool)->bool) ==> FINITE g /\ CARD g >= m)`) 
THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN REMOVE_THEN "f0"(fun th-> MP_TAC(ISPECL[`t:(A->bool)->bool`; `m:num`] th)) 
THEN ASM_REWRITE_TAC[] 
THEN MP_TAC(SET_RULE  `(!u:A->bool v:A->bool. u IN ((a:A->bool) INSERT (t:(A->bool)->bool)) /\ v IN (a INSERT t)  ==>(u = v \/ DISJOINT u v)) ==>(!u:A->bool v:A->bool. u IN t /\ (v IN t)  ==> (u = v \/ DISJOINT u v))`) 
THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN STRIP_TAC 
THEN ASM_MESON_TAC[ARITH_RULE `a >= b /\ c >= d ==> a + c >= b+d`]);;


let lemma_card_le = prove
(`!(n:num) (s:(A->bool)->bool) (m:num). ((FINITE s /\ CARD(s) = n) /\ (!u:A->bool v:A->bool. (u IN s /\ v IN s) ==> (u = v \/ DISJOINT u v)) /\ (!g:A->bool.(g IN s) ==> (FINITE g /\ CARD(g) <= m))) ==> (CARD(UNIONS s) <= m * CARD(s))`, 
INDUCT_TAC 
THENL[REPEAT STRIP_TAC THEN MP_TAC(ISPECL[`s:(A->bool)->bool`]  CARD_EQ_0) 
THEN ASM_REWRITE_TAC[ARITH_RULE `m * 0=0`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[UNIONS_0] 
THEN SIMP_TAC[CONJUNCT1 CARD_CLAUSES;ARITH];ALL_TAC]

THEN POP_ASSUM (LABEL_TAC "f0") THEN REPEAT GEN_TAC 
THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f1") (CONJUNCTS_THEN2 (LABEL_TAC "f2") (LABEL_TAC "f3"))) 
THEN MP_TAC(ISPECL[`s:(A->bool)->bool`;`SUC(n:num)`] HAS_SIZE) THEN ASM_SIMP_TAC[] THEN DISCH_THEN(LABEL_TAC "F4") 
THEN MP_TAC (ISPECL[`s:(A->bool)->bool`; `n:num`] (CONJUNCT2 SET_SIZE_CLAUSES)) THEN ASM_SIMP_TAC[] 
THEN DISCH_THEN (X_CHOOSE_THEN `a:(A->bool)` MP_TAC) THEN DISCH_THEN (X_CHOOSE_THEN `t:(A->bool)->bool` MP_TAC) 
THEN REWRITE_TAC[HAS_SIZE] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f5") (CONJUNCTS_THEN2 (LABEL_TAC "f6") (LABEL_TAC "f7")))
THEN MP_TAC (SET_RULE `UNIONS(a:A->bool INSERT t:(A->bool)->bool) = a UNION (UNIONS  t)`) THEN ASM_REWRITE_TAC[]
THEN SUBGOAL_THEN `DISJOINT (a:A->bool) (UNIONS (t:(A->bool)->bool))` (LABEL_TAC "F8") 

THENL[POP_ASSUM SUBST_ALL_TAC 
THEN MATCH_MP_TAC lemma_disjoints THEN GEN_TAC THEN DISCH_THEN(LABEL_TAC "f9") THEN USE_THEN "f2"(MP_TAC o SPEC `a:A->bool`) 
THEN DISCH_THEN(MP_TAC o SPEC `v:A->bool`) THEN REWRITE_TAC[SET_RULE `a IN a INSERT t`] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INSERT] 
THEN DISJ_CASES_TAC (SET_RULE `(a:A->bool = v:A->bool) \/ ~(a = v)`) 
THENL[MP_TAC (MESON[] ` (a:A->bool = v:A->bool) /\ (v IN t:(A->bool)->bool) ==> a IN t`) 
THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]]; ALL_TAC] 

THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN MP_TAC(ISPECL[`a:A->bool`;`(UNIONS (t:(A->bool)->bool))`] CARD_UNION) 
THEN POP_ASSUM MP_TAC THEN SIMP_TAC[DISJOINT] THEN STRIP_TAC THEN REMOVE_THEN "f7"(SUBST_ALL_TAC)
THEN USE_THEN "f3"(MP_TAC o SPEC `a:A->bool`) THEN REWRITE_TAC[SET_RULE `a IN a INSERT t`] 
THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MP_TAC (ISPECL[`t:(A->bool)->bool`] TYPED_FINITE_UNIONS) 
THEN MP_TAC(SET_RULE  `(!g:A->bool. g IN ((a:A->bool) INSERT (t:(A->bool)->bool)) ==> (FINITE g) /\ (CARD g <= (m:num))) ==> (!g:A->bool. g IN (t:(A->bool)->bool) ==> FINITE g /\ CARD g <= m)`) 
THEN MP_TAC(SET_RULE `(s:(A->bool)->bool = (a:A->bool) INSERT (t:(A->bool)->bool)) /\ (!g:A->bool. g IN s ==> FINITE g) ==> FINITE a`) 
THEN USE_THEN "f3" (MP_TAC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] 
 THEN REWRITE_TAC[MULT_SUC] 
THEN MP_TAC(SET_RULE  `(!g:A->bool. g IN ((a:A->bool) INSERT (t:(A->bool)->bool)) ==> (FINITE g) /\ (CARD g <= (m:num))) ==> (!g:A->bool. g IN (t:(A->bool)->bool) ==> FINITE g /\ CARD g <= m)`) 
THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN REMOVE_THEN "f0"(fun th-> MP_TAC(ISPECL[`t:(A->bool)->bool`; `m:num`] th)) 
THEN ASM_REWRITE_TAC[] 
THEN MP_TAC(SET_RULE  `(!u:A->bool v:A->bool. u IN ((a:A->bool) INSERT (t:(A->bool)->bool)) /\ v IN (a INSERT t)  ==>(u = v \/ DISJOINT u v)) ==>(!u:A->bool v:A->bool. u IN t /\ (v IN t)  ==> (u = v \/ DISJOINT u v))`) 
THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN STRIP_TAC 
THEN ASM_MESON_TAC[ARITH_RULE `a <= b /\ c <= d ==> a + c <= b+d`]);;


let lemma_card_eq = prove
(`!(n:num) (s:(A->bool)->bool) (m:num). ((FINITE s /\ CARD(s) = n) /\ (!u:A->bool v:A->bool. (u IN s /\ v IN s) ==> (u = v \/ DISJOINT u v)) /\ (!g:A->bool.(g IN s) ==> (FINITE g /\ CARD(g) = m))) ==> (CARD(UNIONS s) = m * CARD(s))`, 
INDUCT_TAC 
THENL[REPEAT STRIP_TAC THEN MP_TAC(ISPECL[`s:(A->bool)->bool`]  CARD_EQ_0) 
THEN ASM_REWRITE_TAC[ARITH_RULE `m * 0=0`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[UNIONS_0] 
THEN SIMP_TAC[CONJUNCT1 CARD_CLAUSES;ARITH];ALL_TAC]

THEN POP_ASSUM (LABEL_TAC "f0") THEN REPEAT GEN_TAC 
THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f1") (CONJUNCTS_THEN2 (LABEL_TAC "f2") (LABEL_TAC "f3"))) 
THEN MP_TAC(ISPECL[`s:(A->bool)->bool`;`SUC(n:num)`] HAS_SIZE) THEN ASM_SIMP_TAC[] THEN DISCH_THEN(LABEL_TAC "F4") 
THEN MP_TAC (ISPECL[`s:(A->bool)->bool`; `n:num`] (CONJUNCT2 SET_SIZE_CLAUSES)) THEN ASM_SIMP_TAC[] 
THEN DISCH_THEN (X_CHOOSE_THEN `a:(A->bool)` MP_TAC) THEN DISCH_THEN (X_CHOOSE_THEN `t:(A->bool)->bool` MP_TAC) 
THEN REWRITE_TAC[HAS_SIZE] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f5") (CONJUNCTS_THEN2 (LABEL_TAC "f6") (LABEL_TAC "f7")))
THEN MP_TAC (SET_RULE `UNIONS(a:A->bool INSERT t:(A->bool)->bool) = a UNION (UNIONS  t)`) THEN ASM_REWRITE_TAC[]
THEN SUBGOAL_THEN `DISJOINT (a:A->bool) (UNIONS (t:(A->bool)->bool))` (LABEL_TAC "F8") 

THENL[POP_ASSUM SUBST_ALL_TAC 
THEN MATCH_MP_TAC lemma_disjoints THEN GEN_TAC THEN DISCH_THEN(LABEL_TAC "f9") THEN USE_THEN "f2"(MP_TAC o SPEC `a:A->bool`) 
THEN DISCH_THEN(MP_TAC o SPEC `v:A->bool`) THEN REWRITE_TAC[SET_RULE `a IN a INSERT t`] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INSERT] 
THEN DISJ_CASES_TAC (SET_RULE `(a:A->bool = v:A->bool) \/ ~(a = v)`) 
THENL[MP_TAC (MESON[] ` (a:A->bool = v:A->bool) /\ (v IN t:(A->bool)->bool) ==> a IN t`) 
THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]]; ALL_TAC] 

THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN MP_TAC(ISPECL[`a:A->bool`;`(UNIONS (t:(A->bool)->bool))`] CARD_UNION) 
THEN POP_ASSUM MP_TAC THEN SIMP_TAC[DISJOINT] THEN STRIP_TAC THEN REMOVE_THEN "f7"(SUBST_ALL_TAC)
THEN USE_THEN "f3"(MP_TAC o SPEC `a:A->bool`) THEN REWRITE_TAC[SET_RULE `a IN a INSERT t`] 
THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MP_TAC (ISPECL[`t:(A->bool)->bool`] TYPED_FINITE_UNIONS) 
THEN MP_TAC(SET_RULE  `(!g:A->bool. g IN ((a:A->bool) INSERT (t:(A->bool)->bool)) ==> (FINITE g) /\ (CARD g = (m:num))) ==> (!g:A->bool. g IN (t:(A->bool)->bool) ==> FINITE g /\ CARD g = m)`) 
THEN MP_TAC(SET_RULE `(s:(A->bool)->bool = (a:A->bool) INSERT (t:(A->bool)->bool)) /\ (!g:A->bool. g IN s ==> FINITE g) ==> FINITE a`) 
THEN USE_THEN "f3" (MP_TAC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] 
 THEN REWRITE_TAC[MULT_SUC] 
THEN MP_TAC(SET_RULE  `(!g:A->bool. g IN ((a:A->bool) INSERT (t:(A->bool)->bool)) ==> (FINITE g) /\ (CARD g = (m:num))) ==> (!g:A->bool. g IN (t:(A->bool)->bool) ==> FINITE g /\ CARD g = m)`) 
THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN REMOVE_THEN "f0"(fun th-> MP_TAC(ISPECL[`t:(A->bool)->bool`; `m:num`] th)) 
THEN ASM_REWRITE_TAC[] 
THEN MP_TAC(SET_RULE  `(!u:A->bool v:A->bool. u IN ((a:A->bool) INSERT (t:(A->bool)->bool)) /\ v IN (a INSERT t)  ==>(u = v \/ DISJOINT u v)) ==>(!u:A->bool v:A->bool. u IN t /\ (v IN t)  ==> (u = v \/ DISJOINT u v))`) 
THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN STRIP_TAC 
THEN ASM_MESON_TAC[ARITH_RULE `a = b /\ c = d ==> a + c = b+d`]);;


let lemma_partion = prove( `!s:A->bool p:A->A. FINITE s /\ p permutes s ==> s = UNIONS (set_of_orbits s p)`,REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION;IN_UNIONS] THEN  GEN_TAC THEN EQ_TAC THENL[MP_TAC (ISPECL[`p:A->A`;`x:A`] orbit_reflect) THEN REWRITE_TAC[set_of_orbits] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `(orbit_map p x):A->bool` THEN (SET_TAC[]); DISCH_THEN(X_CHOOSE_THEN `t:A->bool` MP_TAC) THEN REWRITE_TAC[IN_ELIM_THM;set_of_orbits] THEN STRIP_TAC THEN FIRST_ASSUM SUBST_ALL_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP  orbit_subset) THEN SET_TAC[]]);;


let lemma_card_eq = prove
(`!(n:num) (s:(A->bool)->bool) (m:num). ((FINITE s /\ CARD(s) = n) /\ (!u:A->bool v:A->bool. (u IN s /\ v IN s) ==> (u = v \/ DISJOINT u v)) /\ (!g:A->bool.(g IN s) ==> (FINITE g /\ CARD(g) = m))) ==> (CARD(UNIONS s) = m * CARD(s))`, 
INDUCT_TAC 
THENL[REPEAT STRIP_TAC THEN MP_TAC(ISPECL[`s:(A->bool)->bool`]  CARD_EQ_0) 
THEN ASM_REWRITE_TAC[ARITH_RULE `m * 0=0`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[UNIONS_0] 
THEN SIMP_TAC[CONJUNCT1 CARD_CLAUSES;ARITH];ALL_TAC]

THEN POP_ASSUM (LABEL_TAC "f0") THEN REPEAT GEN_TAC 
THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f1") (CONJUNCTS_THEN2 (LABEL_TAC "f2") (LABEL_TAC "f3"))) 
THEN MP_TAC(ISPECL[`s:(A->bool)->bool`;`SUC(n:num)`] HAS_SIZE) THEN ASM_SIMP_TAC[] THEN DISCH_THEN(LABEL_TAC "F4") 
THEN MP_TAC (ISPECL[`s:(A->bool)->bool`; `n:num`] (CONJUNCT2 SET_SIZE_CLAUSES)) THEN ASM_SIMP_TAC[] 
THEN DISCH_THEN (X_CHOOSE_THEN `a:(A->bool)` MP_TAC) THEN DISCH_THEN (X_CHOOSE_THEN `t:(A->bool)->bool` MP_TAC) 
THEN REWRITE_TAC[HAS_SIZE] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f5") (CONJUNCTS_THEN2 (LABEL_TAC "f6") (LABEL_TAC "f7")))
THEN MP_TAC (SET_RULE `UNIONS(a:A->bool INSERT t:(A->bool)->bool) = a UNION (UNIONS  t)`) THEN ASM_REWRITE_TAC[]
THEN SUBGOAL_THEN `DISJOINT (a:A->bool) (UNIONS (t:(A->bool)->bool))` (LABEL_TAC "F8") 

THENL[POP_ASSUM SUBST_ALL_TAC 
THEN MATCH_MP_TAC lemma_disjoints THEN GEN_TAC THEN DISCH_THEN(LABEL_TAC "f9") THEN USE_THEN "f2"(MP_TAC o SPEC `a:A->bool`) 
THEN DISCH_THEN(MP_TAC o SPEC `v:A->bool`) THEN REWRITE_TAC[SET_RULE `a IN a INSERT t`] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INSERT] 
THEN DISJ_CASES_TAC (SET_RULE `(a:A->bool = v:A->bool) \/ ~(a = v)`) 
THENL[MP_TAC (MESON[] ` (a:A->bool = v:A->bool) /\ (v IN t:(A->bool)->bool) ==> a IN t`) 
THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]]; ALL_TAC] 

THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN MP_TAC(ISPECL[`a:A->bool`;`(UNIONS (t:(A->bool)->bool))`] CARD_UNION) 
THEN POP_ASSUM MP_TAC THEN SIMP_TAC[DISJOINT] THEN STRIP_TAC THEN REMOVE_THEN "f7"(SUBST_ALL_TAC)
THEN USE_THEN "f3"(MP_TAC o SPEC `a:A->bool`) THEN REWRITE_TAC[SET_RULE `a IN a INSERT t`] 
THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MP_TAC (ISPECL[`t:(A->bool)->bool`] TYPED_FINITE_UNIONS) 
THEN MP_TAC(SET_RULE  `(!g:A->bool. g IN ((a:A->bool) INSERT (t:(A->bool)->bool)) ==> (FINITE g) /\ (CARD g = (m:num))) ==> (!g:A->bool. g IN (t:(A->bool)->bool) ==> FINITE g /\ CARD g = m)`) 
THEN MP_TAC(SET_RULE `(s:(A->bool)->bool = (a:A->bool) INSERT (t:(A->bool)->bool)) /\ (!g:A->bool. g IN s ==> FINITE g) ==> FINITE a`) 
THEN USE_THEN "f3" (MP_TAC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] 
 THEN REWRITE_TAC[MULT_SUC] 
THEN MP_TAC(SET_RULE  `(!g:A->bool. g IN ((a:A->bool) INSERT (t:(A->bool)->bool)) ==> (FINITE g) /\ (CARD g = (m:num))) ==> (!g:A->bool. g IN (t:(A->bool)->bool) ==> FINITE g /\ CARD g = m)`) 
THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN REMOVE_THEN "f0"(fun th-> MP_TAC(ISPECL[`t:(A->bool)->bool`; `m:num`] th)) 
THEN ASM_REWRITE_TAC[] 
THEN MP_TAC(SET_RULE  `(!u:A->bool v:A->bool. u IN ((a:A->bool) INSERT (t:(A->bool)->bool)) /\ v IN (a INSERT t)  ==>(u = v \/ DISJOINT u v)) ==>(!u:A->bool v:A->bool. u IN t /\ (v IN t)  ==> (u = v \/ DISJOINT u v))`) 
THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN STRIP_TAC 
THEN ASM_MESON_TAC[ARITH_RULE `a = b /\ c = d ==> a + c = b+d`]);;


let lemma_partition = prove( `!s:A->bool p:A->A. FINITE s /\ p permutes s ==> s = UNIONS (set_of_orbits s p)`,REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION;IN_UNIONS] THEN  GEN_TAC THEN EQ_TAC THENL[MP_TAC (ISPECL[`p:A->A`;`x:A`] orbit_reflect) THEN REWRITE_TAC[set_of_orbits] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `(orbit_map p x):A->bool` THEN (SET_TAC[]); DISCH_THEN(X_CHOOSE_THEN `t:A->bool` MP_TAC) THEN REWRITE_TAC[IN_ELIM_THM;set_of_orbits] THEN STRIP_TAC THEN FIRST_ASSUM SUBST_ALL_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP  orbit_subset) THEN SET_TAC[]]);;



let lemma_partition = prove( `!s:A->bool p:A->A. FINITE s /\ p permutes s ==> s = UNIONS (set_of_orbits s p)`,REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION;IN_UNIONS] THEN  GEN_TAC THEN EQ_TAC THENL[MP_TAC (ISPECL[`p:A->A`;`x:A`] orbit_reflect) THEN REWRITE_TAC[set_of_orbits] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `(orbit_map p x):A->bool` THEN (SET_TAC[]); DISCH_THEN(X_CHOOSE_THEN `t:A->bool` MP_TAC) THEN REWRITE_TAC[IN_ELIM_THM;set_of_orbits] THEN STRIP_TAC THEN FIRST_ASSUM SUBST_ALL_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP  orbit_subset) THEN SET_TAC[]]);;



let lemma_orbits_ge = prove(`!D:A->bool p:A->A m:num. FINITE D /\ p permutes D /\ (!x:A. x IN D ==> CARD(orbit_map p x) >= m) ==> (CARD D >= m * (number_of_orbits D p))`, 
REPEAT STRIP_TAC 
THEN MP_TAC(ISPECL[`D:A->bool`; `p:A->A`] lemma_partition) 
THEN ASM_REWRITE_TAC[number_of_orbits] 
THEN SUBGOAL_THEN `!u:A->bool v:A->bool. u IN (set_of_orbits (D:A->bool) (p:A->A)) /\ v IN (set_of_orbits D p) ==> u = v \/ DISJOINT u v` ASSUME_TAC
THENL[REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM; set_of_orbits] 
 THEN DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:A` MP_TAC) (X_CHOOSE_THEN `b:A` MP_TAC)) 
 THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F1")) 
 THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F2")) 
 THEN ASM_REWRITE_TAC[DISJOINT] THEN ASM_MESON_TAC[partition_orbit]; 
ALL_TAC] 
THEN SUBGOAL_THEN `!g. g IN  set_of_orbits (D:A->bool) (p:A->A) ==> FINITE g /\ CARD g >= m:num` ASSUME_TAC
THENL[STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM;set_of_orbits] THEN STRIP_TAC THEN ASM_SIMP_TAC[] 
 THEN MP_TAC(ISPECL[`D:A->bool`; `p:A->A`] orbit_subset)
 THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC
]
THEN MP_TAC(ISPECL[`D:A->bool`; `p:A->A`] finite_orbits_lemma) THEN ASM_REWRITE_TAC[] 
THEN REPEAT STRIP_TAC THEN ABBREV_TAC `s = set_of_orbits (D:A->bool) (p:A->A)` THEN ABBREV_TAC `n = CARD(s:(A->bool)->bool)` 
THEN MP_TAC(ISPECL[`n:num`;`s:(A->bool)->bool`;`m:num`] lemma_card_ge) THEN ASM_REWRITE_TAC[]);;


let lemma_orbits_eq = prove(`!D:A->bool p:A->A m:num. FINITE D /\ p permutes D /\ (!x:A. x IN D ==> CARD(orbit_map p x) = m) ==> (CARD D = m * (number_of_orbits D p))`, 
REPEAT STRIP_TAC 
THEN MP_TAC(ISPECL[`D:A->bool`; `p:A->A`] lemma_partition) 
THEN ASM_REWRITE_TAC[number_of_orbits] 
THEN SUBGOAL_THEN `!u:A->bool v:A->bool. u IN (set_of_orbits (D:A->bool) (p:A->A)) /\ v IN (set_of_orbits D p) ==> u = v \/ DISJOINT u v` ASSUME_TAC
THENL[REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM; set_of_orbits] 
 THEN DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:A` MP_TAC) (X_CHOOSE_THEN `b:A` MP_TAC)) 
 THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F1")) 
 THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F2")) 
 THEN ASM_REWRITE_TAC[DISJOINT] THEN ASM_MESON_TAC[partition_orbit]; 
ALL_TAC] 
THEN SUBGOAL_THEN `!g. g IN  set_of_orbits (D:A->bool) (p:A->A) ==> FINITE g /\ CARD g = m:num` ASSUME_TAC
THENL[STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM;set_of_orbits] THEN STRIP_TAC THEN ASM_SIMP_TAC[] 
 THEN MP_TAC(ISPECL[`D:A->bool`; `p:A->A`] orbit_subset)
 THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC
]
THEN MP_TAC(ISPECL[`D:A->bool`; `p:A->A`] finite_orbits_lemma) THEN ASM_REWRITE_TAC[] 
THEN REPEAT STRIP_TAC THEN ABBREV_TAC `s = set_of_orbits (D:A->bool) (p:A->A)` THEN ABBREV_TAC `n = CARD(s:(A->bool)->bool)` 
THEN MP_TAC(ISPECL[`n:num`;`s:(A->bool)->bool`;`m:num`] lemma_card_eq) THEN ASM_REWRITE_TAC[]);;


let lemma_card_atleast_1 = prove(`!s:A->bool. FINITE s /\ (?x. x IN s) ==> CARD s >= 1`, REPEAT STRIP_TAC
THEN DISJ_CASES_TAC (SET_RULE`(CARD(s:A->bool) = 0) \/ ~(CARD(s) = 0)`)
THENL[MP_TAC (ISPECL[`s:A->bool`] (CONJUNCT1 SET_SIZE_CLAUSES)) THEN ASM_REWRITE_TAC[HAS_SIZE] THEN SET_TAC[];ALL_TAC]
THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;


let lemma_card_atleast_2 = prove(`!s:A->bool. FINITE s /\ (?x:A y:A. (x IN s) /\ (y IN s) /\ ~( x = y)) ==> CARD s >= 2`,
REPEAT STRIP_TAC THEN ASSUME_TAC(SPEC `x:A`INSERT_DELETE) THEN POP_ASSUM(MP_TAC o SPEC `s:A->bool`)
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MP_TAC(ISPECL[`s:A->bool`;`x:A`] FINITE_DELETE_IMP) THEN ASM_REWRITE_TAC[]
THEN STRIP_TAC THEN MP_TAC(ISPECL[`x:A`;`s:A->bool DELETE x:A`] (CONJUNCT2 CARD_CLAUSES )) THEN ASM_REWRITE_TAC[]
THEN COND_CASES_TAC THENL[SET_TAC[];ALL_TAC]
THEN REWRITE_TAC[ARITH_RULE `SUC(CARD(s:A->bool DELETE x:A)) = CARD(s DELETE x) +1`] THEN STRIP_TAC THEN MP_TAC(ISPECL[`s:A->bool`;`y:A`;`x:A`] IN_DELETE)
THEN ASM_REWRITE_TAC[] THEN ABBREV_TAC `t = s:A->bool DELETE x:A` THEN STRIP_TAC
THEN ASSUME_TAC(SPEC `y:A` INSERT_DELETE) THEN POP_ASSUM(MP_TAC o SPEC `t:A->bool`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THEN MP_TAC(ISPECL[`t:A->bool`;`y:A`] FINITE_DELETE_IMP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THEN MP_TAC(ISPECL[`y:A`;`t:A->bool DELETE y:A`] (CONJUNCT2 CARD_CLAUSES )) THEN ASM_REWRITE_TAC[]
THEN COND_CASES_TAC THENL[SET_TAC[];ALL_TAC]
THEN REWRITE_TAC[ARITH_RULE `SUC(CARD(t:A->bool DELETE y:A)) = CARD(t DELETE y) +1`]
THEN STRIP_TAC THEN ASM_REWRITE_TAC[ARITH] THEN ARITH_TAC);;


let lemma_nondegenerate_convolution = prove(`!s:A->bool p:A->A. FINITE s /\ p permutes s /\ p o p = I /\ (!x:A. x IN s ==> ~(p x = x)) ==> (!x:A. x IN s ==> FINITE (orbit_map p x) /\ CARD(orbit_map p x) = 2)`,
REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "F1") (CONJUNCTS_THEN2 (LABEL_TAC "F2")(CONJUNCTS_THEN2 (LABEL_TAC "F3")(LABEL_TAC "F4"))))
  THEN GEN_TAC THEN (DISCH_THEN(LABEL_TAC "F5")) THEN USE_THEN "F2"(MP_TAC o SPEC `x:A` o MATCH_MP orbit_subset) THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (LABEL_TAC "F6") THEN 
  USE_THEN "F1"(fun th1 -> (USE_THEN "F6"(fun th2 -> (MP_TAC(MATCH_MP FINITE_SUBSET (CONJ th1 th2))))))
  THEN DISCH_THEN(LABEL_TAC "F7") THEN ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL[`p:A->A`;`2`;`x:A`] card_orbit_le)
  THEN ASM_REWRITE_TAC[ARITH; SPEC `(p:A->A)` iterate_map2;I_THM] THEN DISCH_THEN(LABEL_TAC "F8")
  THEN MP_TAC(ISPECL[`p:A->A`;`1`; `x:A`; `(p:A->A) (x:A)`] in_orbit_lemma) THEN REWRITE_TAC[iterate_map1]
  THEN DISCH_THEN(LABEL_TAC "F9") THEN LABEL_TAC "F10" (ISPECL[`p:A->A`;`x:A`] orbit_reflect)
  THEN USE_THEN "F1"(fun th1 -> (USE_THEN "F6" (fun th2 -> LABEL_TAC "F11" (MATCH_MP FINITE_SUBSET (CONJ th1 th2) ))))
  THEN SUBGOAL_THEN `?u:A v:A. u IN orbit_map (p:A->A) (x:A) /\ v IN orbit_map p x /\ ~(u = v)` (LABEL_TAC "F12")
  THENL[EXISTS_TAC `(p:A->A) (x:A)` THEN EXISTS_TAC `x:A` THEN ASM_SIMP_TAC[];ALL_TAC]
  THEN USE_THEN "F11"(fun th1 -> USE_THEN "F12"(fun th2 -> MP_TAC(MATCH_MP lemma_card_atleast_2 (CONJ th1 th2))))
  THEN USE_THEN "F8"(MP_TAC) THEN ARITH_TAC);;


let lemmaTGJISOK = prove(`!H:(A)hypermap. connected_hypermap H /\ plain_hypermap H /\ planar_hypermap H /\(!x:A. x IN (dart H) ==> ~(edge_map H x = x)/\ (CARD(node H x) >= 3)) ==> (CARD (dart H) <= (6*(number_of_faces H)-12))`,
GEN_TAC THEN REWRITE_TAC[connected_hypermap; plain_hypermap; planar_hypermap;number_of_edges;number_of_nodes; number_of_faces;number_of_components]
  THEN DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC) (MP_TAC )) THEN POP_ASSUM SUBST1_TAC THEN SIMP_TAC[ARITH]
  THEN MP_TAC(SPEC `H:(A)hypermap` hypermap_lemma)
  THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
  THEN ABBREV_TAC `e = edge_map(H:(A)hypermap)`
  THEN ABBREV_TAC `n = node_map (H:(A)hypermap)`
  THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
  THEN REWRITE_TAC[SPEC `H:(A)hypermap` node_set]
  THEN  REWRITE_TAC[SPEC `H:(A)hypermap` edge_set]
  THEN REWRITE_TAC[SPEC `H:(A)hypermap` face_set]
  THEN ASM_REWRITE_TAC[(SPEC `H:(A)hypermap` node)]
  THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "F1") (CONJUNCTS_THEN2 (LABEL_TAC "F2")(CONJUNCTS_THEN2 (LABEL_TAC "F3")(LABEL_TAC "F4"))))
  THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "F5") (CONJUNCTS_THEN2 (LABEL_TAC "F6") (LABEL_TAC "F7")))
  THEN SUBGOAL_THEN `!x:A. x IN (D:A->bool) ==> CARD (orbit_map e x) = 2` (LABEL_TAC "F8")
  THENL[MP_TAC(ISPECL[`D:A->bool`; `e:A->A`] lemma_nondegenerate_convolution) THEN ASM_SIMP_TAC[];ALL_TAC]
  THEN SUBGOAL_THEN `!x:A. x IN (D:A->bool) ==> CARD (orbit_map n x) >= 3` (LABEL_TAC "F9")
  THENL[ASM_SIMP_TAC[];ALL_TAC]
  THEN MP_TAC(ISPECL[`D:A->bool`; `e:A->A`] lemma_orbits_eq)
  THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `2`)
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN(LABEL_TAC "F16")
  THEN MP_TAC(ISPECL[`D:A->bool`; `n:A->A`] lemma_orbits_ge)
  THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `3`) THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN(LABEL_TAC "F16") THEN REMOVE_THEN "F6" (MP_TAC)
  THEN REMOVE_THEN "F16" (MP_TAC)
  THEN ASM_REWRITE_TAC[]
  THEN REWRITE_TAC[ISPECL[`D:A->bool`;`e:A->A`] number_of_orbits]
  THEN REWRITE_TAC[ISPECL[`D:A->bool`;`n:A->A`] number_of_orbits]
  THEN REWRITE_TAC[ISPECL[`D:A->bool`;`f:A->A`] number_of_orbits]
  THEN ARITH_TAC);;

prioritize_real();;


