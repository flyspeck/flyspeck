 (* Tran Nam Trung *)

needs "Examples/permutations.ml";;

prioritize_num();;

(* The definition of the nth exponent of a map *)

parse_as_infix("POWER",(24,"right"));;

let POWER = new_recursive_definition num_RECURSION 
 `(!(f:A->A). f POWER 0  = I) /\  
  (!(f:A->A) (n:num). f POWER (SUC n) = (f POWER n) o f)`;;

let POWER_0 = prove(`!f:A->A. f POWER 0 = I`,
 REWRITE_TAC[POWER]);;

let POWER_1 = prove(`!f:A->A. f POWER 1 = f`,
 REWRITE_TAC[POWER; ONE; I_O_ID]);;

let POWER_2 = prove(`!f:A->A. f POWER 2 = f o f`,
 REWRITE_TAC[POWER; TWO; POWER_1]);;

let orbit_map = new_definition `orbit_map (f:A->A)  (x:A) = {(f POWER n) x | n >= 0}`;;

(* the definition of hypermap *)


let exist_hypermap = prove(`?H:((A->bool)#(A->A)#(A->A)#(A->A)). FINITE
(FST H) /\ (FST(SND H)) permutes (FST H) /\ (FST(SND(SND H))) permutes (FST H) /\ (SND(SND(SND H))) permutes (FST H) /\ (FST(SND H)) o (FST(SND(SND  H))) o (SND(SND(SND H))) = I`,EXISTS_TAC
`({},I,I,I):(A->bool)#(A->A)#(A->A)#(A->A)` THEN REWRITE_TAC[FINITE_RULES; PERMUTES_I; I_O_ID]);;



let hypermap_tybij = (new_type_definition "hypermap" ("hypermap", "tuple_hypermap")exist_hypermap);;

let dart = new_definition `dart (H:(A)hypermap) = FST (tuple_hypermap H)`;;

let edge_map = new_definition `edge_map (H:(A)hypermap) = FST(SND(tuple_hypermap H))`;;

let node_map = new_definition `node_map (H:(A)hypermap) = FST(SND(SND(tuple_hypermap H)))`;;

let face_map = new_definition `face_map (H:(A)hypermap) = SND(SND(SND(tuple_hypermap H)))`;;

let hypermap_lemma = prove(`!H:(A)hypermap. FINITE (dart H) /\ edge_map H
permutes dart H /\ node_map H permutes dart H /\ face_map H permutes dart
H /\ edge_map H o node_map H o face_map H = I`,
ASM_REWRITE_TAC[hypermap_tybij;dart;edge_map; node_map; face_map]);;

(* edges, nodes, faces, group orbits of a hypermap*)

let edge = new_definition `edge (H:(A)hypermap) (x:A) = orbit_map
 (edge_map H) x`;;

let node = new_definition `node (H:(A)hypermap) (x:A) = orbit_map
 (node_map H) x`;;

let face = new_definition `face (H:(A)hypermap) (x:A) = orbit_map
 (face_map H) x`;;


(* We define the component *)

let go_one_step = new_definition `go_one_step (H:(A)hypermap) (x:A) (y:A) <=> (y = (edge_map H) x) \/ (y = (node_map H) x) \/ (y = (face_map H) x)`;;

let is_path = new_recursive_definition num_RECURSION  `(is_path (H:(A)hypermap) (p:num->A) 0 <=> T)/\
(is_path (H:(A)hypermap) (p:num->A) (SUC n) <=> ((is_path H p n) /\ go_one_step H (p n) (p (SUC n))))`;; 


let is_in_component = new_definition `is_in_component (H:(A)hypermap) (x:A) (y:A) <=> ?p:num->A n:num. p 0 = x /\ p n = y /\ is_path H p n`;;

let combinatorial_component = new_definition `combinatorial_component (H:(A)hypermap) (x:A) = {y:A| is_in_component H x y}`;;


(* some definitions on orbits *)

let set_of_orbits = new_definition `set_of_orbits (D:A->bool) (f:A->A) = {orbit_map f x | x IN D}`;;

let number_of_orbits = new_definition `number_of_orbits (D:A->bool) (f:A->A) = CARD(set_of_orbits D f)`;;



(* the orbits on hypermaps*)

let edge_set = new_definition `edge_set (H:(A)hypermap) = set_of_orbits (dart H) (edge_map H)`;;

let node_set = new_definition `node_set  (H:(A)hypermap) = set_of_orbits (dart H) (node_map H)`;;

let face_set = new_definition `face_set (H:(A)hypermap) = set_of_orbits (dart H) (face_map H)`;;

let component_set = new_definition `component_set (H:(A)hypermap) = {combinatorial_component H (x:A) | x IN dart H}`;;


(* counting the numbers of edges, nodes, faces and group orbits *)

let number_of_edges = new_definition 
 `number_of_edges (H:(A)hypermap) = CARD (edge_set H)`;;

let number_of_nodes = new_definition 
 `number_of_nodes (H:(A)hypermap) = CARD (node_set H)`;;

let number_of_faces = new_definition 
 `number_of_faces (H:(A)hypermap) = CARD (face_set H)`;;

let number_of_components = new_definition 
 `number_of_components (H:(A)hypermap) = CARD (component_set H)`;;


(* some special hypergraphs *)

let plain_hypermap = new_definition `plain_hypermap (H:(A)hypermap) <=>
 edge_map H o edge_map H = I`;;

let planar_hypermap = new_definition `planar_hypermap (H:(A)hypermap) <=>
 number_of_nodes H + number_of_edges H + number_of_faces H = (CARD (dart H)) 
 + 2 * number_of_components H`;;

let simple_hypermap = new_definition `simple_hypermap (H:(A)hypermap) <=>
 (!x:A. x IN dart H ==> (node H x) INTER (face H x) = {x})`;;


(* a dart x is degenerate or nondegenerate *)

let dart_degenerate = new_definition `dart_degenerate (H:(A)hypermap)
(x:A)  <=> (edge_map H x = x \/ node_map H x = x \/ face_map H x = x)`;;

let dart_nondegenerate = new_definition `dart_nondegenerate (H:(A)hypermap) (x:A) <=> ~(edge_map H x = x) /\ ~(node_map H x = x) /\ ~(face_map H x = x)`;;


(* some properties of symmetric groups *)

let LEFT_MULT_MAP = prove(`!u:A->A v:A->A w:A->A. v = w  ==> u o v = u o w`, MESON_TAC[]);;

let RIGHT_MULT_MAP = prove(`!u:A->A v:A->A w:A->A. u = v 
 ==> u o w = v o w`, MESON_TAC[]);;

let LEFT_INVERSE_EQUATION = prove(`!s:A->bool u:A->A v:A->A w:A->A. u permutes s /\ u o v = w ==> v = inverse u o w`,
REPEAT STRIP_TAC THEN 
SUBGOAL_THEN `inverse (u:A->A) o u o (v:A->A) = inverse u o (w:A->A)` MP_TAC
THENL[ ASM_MESON_TAC[]; REWRITE_TAC[o_ASSOC] 
	 THEN ASM_MESON_TAC[PERMUTES_INVERSES_o; I_O_ID]]);;

let RIGHT_INVERSE_EQUATION = prove(`!s:A->bool u:A->A v:A->A w:A->A. v permutes s /\ u o v = w ==> u = w o inverse v`,
REPEAT STRIP_TAC 
THEN SUBGOAL_THEN `(u:A->A) o (v:A->A) o inverse v = (w:A->A) o inverse v` MP_TAC
THENL [ASM_MESON_TAC[o_ASSOC]; ASM_MESON_TAC[PERMUTES_INVERSES_o;I_O_ID]]);;


let iterate_orbit = prove(`!(s:A->bool) (u:A->A). u permutes s ==> !(n:num) (x:A). x IN s ==> (u POWER n) x IN s`,
REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP PERMUTES_IN_IMAGE)
THEN INDUCT_TAC
THENL[GEN_TAC THEN REWRITE_TAC[POWER; I_THM]; REPEAT GEN_TAC
 THEN REWRITE_TAC[POWER; o_DEF] THEN ASM_MESON_TAC[]]);;

let orbit_subset = prove(`!(s:A->bool) (u:A->A). u permutes s ==> !(x:A). x IN s ==> (orbit_map u x) SUBSET s`,
REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; orbit_map; IN_ELIM_THM] THEN
ASM_MESON_TAC[iterate_orbit]);;

let COM_POWER = prove(`!(n:num) (f:A->A). f POWER (SUC n) = f o (f POWER n)`,
INDUCT_TAC THENL[ REWRITE_TAC [ONE; POWER;I_O_ID];
REPEAT STRIP_TAC THEN POP_ASSUM(ASSUME_TAC o GSYM o (ISPEC `f:A->A`))
THEN ASM_REWRITE_TAC[POWER; o_ASSOC]]);;

let addition_exponents = prove(`!m n (f:A->A). f POWER (m + n) = (f POWER m) o (f POWER n)`,
INDUCT_TAC 
THENL [STRIP_TAC THEN REWRITE_TAC[ADD; POWER; I_O_ID];
 POP_ASSUM(ASSUME_TAC o GSYM o (ISPECL[`n:num`;`f:A->A`]))
 THEN REWRITE_TAC[COM_POWER; GSYM o_ASSOC]
 THEN ASM_REWRITE_TAC[COM_POWER; GSYM o_ASSOC; ADD]]);;

let multiplication_exponents = prove(`!m n (f:A->A). f POWER (m * n) = (f POWER n) POWER m`, 
INDUCT_TAC 
THENL [STRIP_TAC THEN REWRITE_TAC[MULT; POWER; I_O_ID]; ALL_TAC] 
THEN REPEAT GEN_TAC THEN POP_ASSUM(ASSUME_TAC o (SPECL[`n:num`; `f:A->A`]))
THEN ASM_REWRITE_TAC[MULT; addition_exponents; POWER]);;


let power_unit_map = prove(`!n f:A->A. f POWER n = I ==> !m. f POWER (m * n) = I`,
REPLICATE_TAC 3 STRIP_TAC THEN INDUCT_TAC THENL[REWRITE_TAC[MULT; POWER]; 
 REWRITE_TAC[MULT; addition_exponents] THEN ASM_REWRITE_TAC[I_O_ID]]);;

let power_map_fix_point = prove(`!n f:A->A x:A. (f POWER n) x = x ==> !m. (f POWER (m * n)) x = x`,
REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC 
THENL [REWRITE_TAC[MULT; POWER; I_THM]; 
 REWRITE_TAC[MULT; addition_exponents; o_DEF] THEN ASM_REWRITE_TAC[]]);;

let orbit_cyclic = prove(`!(f:A->A) m:num (x:A). ~(m = 0) /\ (f POWER m) x = x ==> orbit_map f x = {(f POWER k) x | k < m}`, 
REPEAT STRIP_TAC THEN REWRITE_TAC[orbit_map; EXTENSION; IN_ELIM_THM] 
THEN GEN_TAC THEN EQ_TAC 
THENL [STRIP_TAC THEN ASM_REWRITE_TAC[] 
 THEN FIND_ASSUM (MP_TAC o (SPEC `n:num`) o MATCH_MP DIVMOD_EXIST) `~(m:num = 0)` 
 THEN REPEAT STRIP_TAC 
 THEN UNDISCH_THEN `((f:A->A) POWER (m:num)) (x:A) = x` (ASSUME_TAC o (SPEC `q:num`) o MATCH_MP power_map_fix_point) 
 THEN ASM_REWRITE_TAC[ADD_SYM; addition_exponents; o_DEF] 
 THEN EXISTS_TAC `r:num` THEN ASM_SIMP_TAC[]; 
 REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] 
 THEN EXISTS_TAC `k:num` THEN SIMP_TAC[ARITH_RULE `k:num >= 0`]]);;


(* Some lemmas on the cardinality of finite series *)

let LT_RIGHT_SUC = prove(`!i:num n:num. i < n ==> i < SUC n`,
 REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `i < n ==> SUC i < SUC n`))
 THEN MP_TAC (ARITH_RULE `i < SUC i`) THEN ARITH_TAC);;

let INSERT_IN_SET = prove(`!x s. x IN s ==> x INSERT s = s`, 
 REPEAT GEN_TAC THEN SET_TAC[]);;


let NULL_SERIES = prove(`!f. {f(i) | i < 0} = {}`,
GEN_TAC THEN REWRITE_TAC[EXTENSION; EMPTY; IN_ELIM_THM] THEN REPEAT STRIP_TAC
THEN FIRST_ASSUM (MP_TAC o MATCH_MP (ARITH_RULE `i < 0 ==> F`)) 
THEN SIMP_TAC[]);;

let INSERT_SERIES = prove(`!n f. {f(i) | i < SUC n} = f(n) INSERT {f(i) | i < n}`,
REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; INSERT; IN_ELIM_THM] 
THEN GEN_TAC THEN EQ_TAC
THENL[STRIP_TAC 
 THEN FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE `i < SUC n ==> i < n \/ i = n`))
 THENL[DISJ1_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; DISJ2_TAC
  THEN ASM_REWRITE_TAC[]]; DISCH_THEN DISJ_CASES_TAC
  THENL[POP_ASSUM(X_CHOOSE_THEN `i:num` ASSUME_TAC)
    THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN  FIRST_ASSUM (MP_TAC o CONJUNCT1)
    THEN DISCH_THEN(MP_TAC o MATCH_MP LT_RIGHT_SUC) THEN SIMP_TAC[];
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]]);;

let FINITE_SERIES = prove(`!(n:num) (f:num->A). FINITE {f(i) | i < n}`,
 INDUCT_TAC 
 THENL[GEN_TAC THEN ASSUME_TAC(ISPEC `f:num->A` NULL_SERIES)
   THEN ASM_REWRITE_TAC[FINITE_RULES]; 
   GEN_TAC THEN POP_ASSUM(ASSUME_TAC o (ISPEC `f:num->A`))
   THEN SUBST1_TAC (ISPECL [`n:num`; `f:num->A`] INSERT_SERIES)
   THEN MP_TAC (ISPECL[` f(n):A`; `{f i | i < n}:A->bool`] (CONJUNCT2 FINITE_RULES))
   THEN ASM_MESON_TAC[FINITE_RULES; INSERT_SERIES] ]);;

let IMAGE_SEG = prove(`!(n:num) (f:num->A). ~(n = 0) ==> IMAGE f (0..n-1) = {f(i) | i < n}`,
REPEAT STRIP_TAC THEN REWRITE_TAC[IMAGE; numseg; EXTENSION; IN_ELIM_THM]
THEN GEN_TAC THEN SPEC_TAC(`x:A`, `t:A`) THEN GEN_TAC THEN EQ_TAC
THENL [DISCH_THEN(X_CHOOSE_THEN `x:num` MP_TAC)
 THEN REPEAT STRIP_TAC THEN EXISTS_TAC `x:num`
 THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `~(n = 0) ==> (x <= n-1 ==> x < n)`))
 THEN ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `i:num` MP_TAC)
 THEN REPEAT STRIP_TAC THEN EXISTS_TAC `i:num`
 THEN FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `~(n = 0) ==> (i < n ==> i <= n-1)`))
 THEN ASSUME_TAC (ARITH_RULE `0 <= i`) THEN ASM_REWRITE_TAC[]]);;

let CARD_FINITE_SERIES_LE  = prove(`!(n:num) (f:num->A). CARD {f(i) | i < n} <= n`,
REPEAT GEN_TAC THEN DISJ_CASES_TAC (ARITH_RULE `(n = 0) \/ ~(n = 0)`)
THENL [ASM_SIMP_TAC[] THEN SUBST1_TAC (ISPEC `f:num->A` NULL_SERIES)
  THEN MP_TAC(CONJUNCT1 CARD_CLAUSES) THEN ARITH_TAC;
  FIRST_ASSUM(SUBST1_TAC o GSYM o (ISPEC `f:num->A`) o MATCH_MP IMAGE_SEG)
  THEN ASSUME_TAC (SPECL[`0`; `(n-1):num`] FINITE_NUMSEG)
  THEN MP_TAC (ISPECL[`f:num->A`; `(0..n-1):num->bool`] CARD_IMAGE_LE) THEN
  ASM_REWRITE_TAC[]
  THEN ASSUME_TAC(SPECL[`0`; `(n-1):num`] CARD_NUMSEG)
  THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP(ARITH_RULE `~(n = 0) ==> (n - 1 + 1) - 0 = n`))
  THEN ASM_REWRITE_TAC[] ]);;

let LEMMA_INJ = prove(`(!(n:num) (f:num->A). ~(n = 0) ==> (!i:num j:num. i < n /\ j < i ==> ~(f(i) = f(j))) ==> (!x:num y:num. x IN 0..n - 1 /\ y IN 0..n - 1 /\ f x = f y ==> x = y))`,
REWRITE_TAC[numseg; IN_ELIM_THM; ARITH_RULE `0 <= x /\ 0 <= y`] 
THEN REPEAT STRIP_TAC
THEN SIMP_TAC[ARITH_RULE `(x = y) <=> ~(x < y \/ y < x)`] THEN STRIP_TAC
THENL[FIRST_X_ASSUM(MP_TAC o (SPECL[`y:num`;`x:num`])) 
 THEN SIMP_TAC[NOT_IMP] THEN ASM_REWRITE_TAC[] 
 THEN MP_TAC (ARITH_RULE `~(n = 0) /\ (y <= n-1) ==> y < n`)
 THEN ASM_REWRITE_TAC[]; 
 FIRST_X_ASSUM(MP_TAC o (SPECL[`x:num`;`y:num`]))
 THEN SIMP_TAC[NOT_IMP] THEN ASM_REWRITE_TAC[]
 THEN MP_TAC (ARITH_RULE `~(n = 0) /\ (x <= n-1) ==> x < n`) 
 THEN ASM_REWRITE_TAC[]]);;

let CARD_FINITE_SERIES_EQ  = prove(`!(n:num) (f:num->A). (!i:num j:num. i < n /\  j < i ==> ~(f(i) = f(j)))
==> CARD {f(i) | i < n} = n`,
REPEAT GEN_TAC THEN DISJ_CASES_TAC (ARITH_RULE `(n = 0) \/ ~(n = 0)`)
THENL [ASM_SIMP_TAC[] THEN SUBST1_TAC (ISPEC `f:num->A` NULL_SERIES) 
THEN MP_TAC(CONJUNCT1 CARD_CLAUSES) THEN ARITH_TAC; ALL_TAC]
THEN FIRST_ASSUM(SUBST1_TAC o GSYM o (ISPEC `f:num->A`) o MATCH_MP IMAGE_SEG)
THEN ASSUME_TAC (SPECL[`0`; `(n-1):num`] FINITE_NUMSEG) THEN DISCH_TAC
THEN MP_TAC(ISPECL[`n:num`; `f:num->A`] LEMMA_INJ) THEN ASM_REWRITE_TAC[]
THEN STRIP_TAC THEN MP_TAC (ISPECL[`f:num->A`; `(0..n-1):num->bool`] CARD_IMAGE_INJ)
THEN ASM_REWRITE_TAC[] THEN ASSUME_TAC(SPECL[`0`; `(n-1):num`] CARD_NUMSEG)
THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP(ARITH_RULE `~(n = 0) ==> (n - 1 + 1) - 0 = n`))
THEN ASM_REWRITE_TAC[]);;


(* In arbitrary finite group, every element has finite order *)

let power_permutation = prove(`!(s:A->bool) (p:A->A). p permutes s 
 ==> !(n:num). (p POWER n) permutes s`, 
REPLICATE_TAC 3 STRIP_TAC THEN INDUCT_TAC 
THENL[REWRITE_TAC[POWER; PERMUTES_I];
   REWRITE_TAC[POWER] THEN ASM_MESON_TAC[PERMUTES_COMPOSE]]);;

let LM_AUX = prove(`!m n. m < n ==> ?k. ~(k = 0) /\ n = m + k`,
REPEAT GEN_TAC THEN REWRITE_TAC[LT_EXISTS] 
THEN DISCH_THEN(X_CHOOSE_THEN `d:num` ASSUME_TAC)
THEN EXISTS_TAC `SUC d` 
THEN ASM_REWRITE_TAC[ARITH_RULE `~(SUC d = 0)`]);;


let LM1 = prove(`!s:A->bool p:A->A n:num m:num. p permutes s /\ p POWER (m+n) = p POWER m ==> p POWER n = I`,
REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (MP_TAC))
THEN REWRITE_TAC[addition_exponents] THEN DISCH_TAC THEN
REMOVE_THEN "c1" (ASSUME_TAC o (SPEC `m:num`) o MATCH_MP power_permutation)
THEN MP_TAC (SPECL[`s:A->bool`; `(p:A->A) POWER (m:num)`;`(p:A->A) POWER (n:num)`; `(p:A->A) POWER (m:num)`] LEFT_INVERSE_EQUATION)
THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(MP_TAC o CONJUNCT2 o (MATCH_MP PERMUTES_INVERSES_o))
THEN SIMP_TAC[]);;


let inj_iterate_segment = prove(`!s:A->bool p:A->A (n:num). p permutes s /\ 
   ~(n = 0) ==> (!m:num. ~(m = 0) /\ (m < n) ==> ~(p POWER m = I)) 
   ==> (!i:num j:num. (i < n) /\ (j < i) ==> ~(p POWER i = p POWER j))`,
REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c2") (ASSUME_TAC))
THEN DISCH_THEN (LABEL_TAC "c3") THEN REPLICATE_TAC 3 STRIP_TAC
THEN DISCH_THEN (LABEL_TAC "c4") THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP LM_AUX)
THEN REPEAT STRIP_TAC THEN REMOVE_THEN "c3" MP_TAC THEN
REWRITE_TAC[NOT_FORALL_THM; NOT_IMP]
THEN EXISTS_TAC `k:num` THEN MP_TAC (ARITH_RULE `(i:num < n:num) /\ (i = (j:num) + (k:num)) ==> k < n`)
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
THEN REMOVE_THEN "c4" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THEN MP_TAC (ISPECL[`s:A->bool`; `p:A->A`; `k:num`; `j:num`] LM1) 
THEN ASM_REWRITE_TAC[]);;

let inj_iterate_lemma = prove(`!s:A->bool p:A->A. p permutes s /\
(!(n:num). ~(n = 0) ==> ~(p POWER n = I)) ==> (!m. CARD({p POWER k | k < m}) = m)`,
REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "c2"))
THEN GEN_TAC 
THEN  SUBGOAL_THEN `!i:num j:num. i < (m:num) /\  j < i ==> ~((p:A->A) POWER i = p POWER j)` ASSUME_TAC
THENL [ REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM (MP_TAC o MATCH_MP LM_AUX)
   THEN STRIP_TAC THEN ASM_REWRITE_TAC[]  THEN STRIP_TAC
   THEN MP_TAC (ISPECL[`s:A->bool`; `p:A->A`; `k:num`; `j:num`] LM1) 
   THEN ASM_REWRITE_TAC[]
   THEN STRIP_TAC THEN REMOVE_THEN "c2" (MP_TAC o SPEC(`k:num`)) 
   THEN REWRITE_TAC[NOT_IMP]
   THEN ASM_REWRITE_TAC[]; 
   POP_ASSUM(MP_TAC o MATCH_MP CARD_FINITE_SERIES_EQ)
   THEN SIMP_TAC[]]);;


(* Two following therems in files: sets.ml *)

let NEW_FINITE_SUBSET = prove(`!(s:(A->A)->bool) t. FINITE t /\ s SUBSET t ==> FINITE s`,
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

let NEW_CARD_SUBSET = prove (`!(a:(A->A)->bool) b. a SUBSET b /\ FINITE(b) ==> CARD(a) <= CARD(b)`,
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

let finite_order = prove( `!s:A->bool p:A->A. FINITE s /\ p permutes s 
   ==> ?(n:num). ~(n = 0) /\ p POWER n = I`,
REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (ASSUME_TAC)) 
THEN ASM_CASES_TAC `?(n:num). ~(n = 0) /\ (p:A->A) POWER n = I` 
THENL [ASM_SIMP_TAC[]; ALL_TAC]
THEN POP_ASSUM MP_TAC 
THEN REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM; TAUT `!a b. ~(a /\ b) = (a ==> ~b)`]
THEN DISCH_TAC THEN MP_TAC (ISPECL[`s:A->bool`; `p:A->A`] inj_iterate_lemma)
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN USE_THEN "c1" (ASSUME_TAC o MATCH_MP FINITE_PERMUTATIONS)
THEN ABBREV_TAC `md = SUC(CARD({p | p permutes (s:A->bool)}))`
THEN SUBGOAL_THEN `{(p:A->A) POWER (k:num) | k < (md:num)} SUBSET {p | p permutes (s:A->bool)}` ASSUME_TAC
THENL [ REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC 
THEN ASM_MESON_TAC[power_permutation]; ALL_TAC]
THEN MP_TAC (ISPECL[`{(p:A->A) POWER (k:num) | k < (md:num)}`;`{p | p permutes (s:A->bool)}`] NEW_CARD_SUBSET)
THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "md" THEN ARITH_TAC);;


let inverse_element_lemma = prove(`!s:A->bool p:A->A. FINITE s /\ p permutes s ==> ?j:num. inverse p = p POWER j`,
REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC (MATCH_MP finite_order th)
THEN ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT2 th))
THEN STRIP_TAC THEN MP_TAC (ARITH_RULE `~(n = 0) ==> n = 1 + (PRE n)`)
THEN ASM_REWRITE_TAC[]
THEN DISCH_TAC THEN UNDISCH_TAC `(p:A->A) POWER (n:num) = I` THEN 
ONCE_ASM_REWRITE_TAC[]
THEN ASM_REWRITE_TAC[addition_exponents; POWER_1]
THEN UNDISCH_TAC `p:A->A permutes s:A->bool` THEN REWRITE_TAC[IMP_IMP]
THEN DISCH_THEN (MP_TAC o MATCH_MP LEFT_INVERSE_EQUATION) THEN
REWRITE_TAC[I_O_ID]
THEN DISCH_THEN (ASSUME_TAC o SYM) THEN EXISTS_TAC `PRE n` THEN
ASM_SIMP_TAC[]);;

let inverse_relation = prove(`!(s:A->bool) p:A->A x:A y:A. FINITE s /\ p permutes s /\ y = p x ==>(?k:num. x = (p POWER k) y)`, 
REPEAT STRIP_TAC THEN MP_TAC(SPECL[`s:A->bool`; `p:A->A`] inverse_element_lemma) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `j:num` 
THEN POP_ASSUM(fun th -> REWRITE_TAC[SYM th]) 
THEN REWRITE_TAC[GSYM(ISPECL[`(inverse (p:A->A)):(A->A)`; `p:A->A`; `(x:A)`] o_THM)] 
THEN UNDISCH_THEN `p:A->A permutes s`(fun th-> REWRITE_TAC[CONJUNCT2 (MATCH_MP PERMUTES_INVERSES_o th);I_THM]));;

(* some properties of orbits *)

let orbit_reflect = prove(`!f:A->A x:A. x IN (orbit_map f x)`, 
REPEAT GEN_TAC THEN REWRITE_TAC[orbit_map; IN_ELIM_THM] 
THEN EXISTS_TAC `0` THEN REWRITE_TAC[POWER; ARITH_RULE `0>=0`;I_THM]);;

let orbit_sym = prove(`!s:A->bool p:A->A x:A y:A. FINITE s /\ p permutes s
   ==> (x IN (orbit_map p y) ==> y IN (orbit_map p x))`, 
REPLICATE_TAC 5 STRIP_TAC THEN REWRITE_TAC[orbit_map; IN_ELIM_THM] 
THEN  STRIP_TAC 
THEN FIND_ASSUM (ASSUME_TAC o (SPEC `n:num`) o MATCH_MP power_permutation) `p:A->A permutes (s:A->bool)` 
THEN POP_ASSUM (MP_TAC o (SPECL[`y:A`; `x:A`]) o MATCH_MP PERMUTES_INVERSE_EQ) 
THEN POP_ASSUM(ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC[] 
THEN UNDISCH_THEN `p:A->A permutes s` (ASSUME_TAC o (SPEC `n:num`) o MATCH_MP power_permutation) 
THEN MP_TAC(SPECL[`s:A->bool`; `(p:A->A) POWER (n:num)`] inverse_element_lemma) 
THEN ASM_REWRITE_TAC[GSYM multiplication_exponents]
THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
THEN EXISTS_TAC `(j:num) * (n:num)` 
THEN ASM_REWRITE_TAC[ARITH_RULE `(j:num) * (n:num) >= 0`]);;

let orbit_trans = prove(`!f:A->A x:A y:A z:A. x IN orbit_map f y /\ y IN orbit_map f z 
   ==> x IN orbit_map f z`,
REPEAT GEN_TAC THEN REWRITE_TAC[orbit_map; IN_ELIM_THM] 
THEN REPEAT STRIP_TAC THEN 
UNDISCH_THEN `x:A = ((f:A->A) POWER (n:num)) (y:A)` MP_TAC 
THEN  ASM_REWRITE_TAC[] 
THEN DISCH_THEN (ASSUME_TAC o SYM) THEN MP_TAC (SPECL[`n:num`; `n':num`; `f:A->A`] addition_exponents) 
THEN  DISCH_THEN(fun th -> MP_TAC (AP_THM th `z:A`)) 
THEN ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN (ASSUME_TAC o SYM)
THEN EXISTS_TAC `(n:num) + n'` 
THEN ASM_REWRITE_TAC[ARITH_RULE `(n:num) + (n':num) >= 0`]);;

let in_orbit_lemma = prove(`!f:A->A n:num x:A y:A. y = (f POWER n) x ==> y IN orbit_map f x`,
REPEAT STRIP_TAC THEN REWRITE_TAC[orbit_map;IN_ELIM_THM] 
THEN EXISTS_TAC `n:num` 
THEN ASM_REWRITE_TAC[ARITH_RULE `n:num >= 0`]);;


let partition_orbit = prove(`!s:A->bool p:A->A. FINITE s /\ p permutes s
   ==>(!x:A y:A. (orbit_map p x INTER orbit_map p y = {}) \/ (orbit_map p x = orbit_map p y))`, 
REPEAT STRIP_TAC THEN ASM_CASES_TAC `orbit_map (p:A->A)(x:A) INTER orbit_map (p:A->A) (y:A) = {}` 
THENL[ASM_REWRITE_TAC[]; ALL_TAC] 
THEN DISJ2_TAC THEN  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] 
THEN REWRITE_TAC[INTER; IN_ELIM_THM] THEN STRIP_TAC 
THEN MP_TAC (SPECL[`s:A->bool`; `p:A->A`; `x':A`; `x:A`] orbit_sym) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MP_TAC (SPECL[`s:A->bool`; `p:A->A`; `x':A`; `y:A`] orbit_sym) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN GEN_TAC 
THEN EQ_TAC 
THENL [STRIP_TAC THEN MP_TAC (SPECL[`p:A->A`; `x'':A`; `x:A`;`x':A`] orbit_trans) 
   THEN ASM_MESON_TAC[orbit_trans]; 
   STRIP_TAC THEN MP_TAC (SPECL[`p:A->A`; `x'':A`; `y:A`;`x':A`] orbit_trans) 
   THEN ASM_MESON_TAC[orbit_trans]]);;

let card_orbit_le = prove(`!f:A->A n:num x:A. ~(n = 0) /\ 
   (f POWER n) x = x ==> CARD(orbit_map f x) <= n`, 
REPEAT GEN_TAC 
THEN DISCH_THEN (fun th -> SUBST1_TAC (MATCH_MP orbit_cyclic th) 
THEN ASSUME_TAC (CONJUNCT1 th)) 
THEN MP_TAC (SPECL[`n:num`; `(\k. ((f:A->A) POWER k) (x:A))`] CARD_FINITE_SERIES_LE) 
THEN MESON_TAC[]);;


(* some properties of hypermap *)


let cyclic_maps = prove(`!D:A->bool e:A->A n:A->A f:A->A. 
   (FINITE D) /\ e permutes D /\ n permutes D /\ f permutes D /\ e o n o f = I 
    ==> (n o f o e = I) /\ (f o e o n = I)`, 
REPEAT STRIP_TAC 
THENL[ MP_TAC (ISPECL[`D:A->bool`;`e:A->A`; `(n:A->A) o (f:A->A)`; `I:A->A`]
   LEFT_INVERSE_EQUATION) THEN ASM_REWRITE_TAC[I_O_ID] 
   THEN FIND_ASSUM (ASSUME_TAC o CONJUNCT2 o MATCH_MP PERMUTES_INVERSES_o) `e:A->A permutes D:A->bool` 
   THEN DISCH_TAC 
   THEN MP_TAC (ISPECL[`(n:A->A)o(f:A->A)`;`inverse(e:A->A)`;`e:A->A` ] RIGHT_MULT_MAP) 
   THEN ASM_REWRITE_TAC[o_ASSOC]; 
   MP_TAC (ISPECL[`D:A->bool`;`(e:A->A)o(n:A->A)`;`(f:A->A)`; `I:A->A`] RIGHT_INVERSE_EQUATION) 
   THEN ASM_REWRITE_TAC[I_O_ID; GSYM o_ASSOC] 
   THEN DISCH_TAC  THEN MP_TAC (ISPECL[`D:A->bool`;`(e:A->A) o (n:A->A)`; `(f:A->A)`; `I:A->A`] RIGHT_INVERSE_EQUATION) 
   THEN ASM_REWRITE_TAC[GSYM o_ASSOC; I_O_ID] 
   THEN FIND_ASSUM (ASSUME_TAC o CONJUNCT1 o MATCH_MP PERMUTES_INVERSES_o) `f:A->A permutes D:A->bool` 
   THEN ASM_SIMP_TAC[]]);;


let cyclic_inverses_maps = prove(`!D:A->bool e:A->A n:A->A f:A->A. 
   (FINITE D) /\ e permutes D /\ n permutes D /\ f permutes D /\ e o n o f = I 
   ==> inverse n o inverse e o inverse f = I`, 
REPEAT STRIP_TAC THEN MP_TAC (ISPECL[`D:A->bool`; `e:A->A`; `n:A->A`; `f:A->A`] cyclic_maps) 
THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC 
THEN  MP_TAC (ISPECL[`D:A->bool`;`f:A->A`; `(e:A->A) o (n:A->A)`; `I:A->A`] LEFT_INVERSE_EQUATION) 
THEN ASM_REWRITE_TAC[I_O_ID] THEN STRIP_TAC 
THEN MP_TAC (ISPECL[`D:A->bool`;`e:A->A`; `(n:A->A)`; `inverse(f:A->A)`] LEFT_INVERSE_EQUATION) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
THEN  MP_TAC (ISPECL[`inverse(n:A->A)`; `n:A->A`; `inverse(e:A->A) o inverse(f:A->A)`] LEFT_MULT_MAP) 
THEN FIND_ASSUM (ASSUME_TAC o CONJUNCT2 o MATCH_MP PERMUTES_INVERSES_o) `n:A->A permutes D:A->bool` 
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[]);;


let lemmaZHQCZLX = prove(`!H:(A)hypermap. (simple_hypermap H /\ plain_hypermap H /\ (!x:A. x IN dart H ==> CARD (face H x) >= 3)) 
   ==> (!x:A. x IN dart H ==> ~(node_map H x = x))`,
GEN_TAC THEN REWRITE_TAC[simple_hypermap; plain_hypermap;face; node] 
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma)
THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "c2") (CONJUNCTS_THEN2 (LABEL_TAC "c3") (CONJUNCTS_THEN2 (LABEL_TAC "c4") (LABEL_TAC "c5")))))
THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c6") (CONJUNCTS_THEN2 (LABEL_TAC "c7") (LABEL_TAC "c8")))
THEN GEN_TAC THEN DISCH_THEN (LABEL_TAC "c9") 
THEN DISCH_THEN (LABEL_TAC "c10")
THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)`  
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
THEN USE_THEN "c2" (MP_TAC o (SPEC `x:A`) o MATCH_MP PERMUTES_IN_IMAGE)
THEN USE_THEN "c4" (MP_TAC o (SPEC `x:A`) o MATCH_MP PERMUTES_IN_IMAGE)
THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC 
THEN ABBREV_TAC `y:A = (f:A->A) (x:A)` THEN ABBREV_TAC `z:A = (e:A->A) (x:A)`
THEN USE_THEN "c7" MP_TAC THEN USE_THEN "c2" MP_TAC THEN REWRITE_TAC[IMP_IMP]
THEN DISCH_THEN (MP_TAC o MATCH_MP LEFT_INVERSE_EQUATION) 
THEN REWRITE_TAC[I_O_ID]
THEN DISCH_THEN(fun th -> (ASSUME_TAC (SYM th)) 
THEN (ASSUME_TAC (AP_THM (SYM th) `x:A`)))
THEN USE_THEN "c3" (MP_TAC o (SPECL[`x:A`;`x:A`]) o MATCH_MP PERMUTES_INVERSE_EQ)
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN USE_THEN "c5" MP_TAC
THEN USE_THEN "c2" MP_TAC THEN REWRITE_TAC[IMP_IMP]
THEN DISCH_THEN (MP_TAC o MATCH_MP LEFT_INVERSE_EQUATION) THEN REWRITE_TAC[I_O_ID]
THEN DISCH_THEN(fun th -> (ASSUME_TAC (SYM th)) 
THEN (MP_TAC (AP_THM (SYM th) `x:A`)))
THEN ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN (MP_TAC o SYM)
THEN MP_TAC (SPECL[`D:A->bool`; `e:A->A`; `n:A->A`; `f:A->A`] cyclic_maps)
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (fun th -> MP_TAC (AP_THM (CONJUNCT2 th) `x:A`))
THEN ASM_REWRITE_TAC[o_THM; I_THM] THEN DISCH_THEN (MP_TAC o AP_TERM `f:A->A`) 
THEN ASM_REWRITE_TAC[]
THEN DISCH_THEN (LABEL_TAC "c11") THEN DISCH_THEN (LABEL_TAC "c12")
THEN MP_TAC (SPECL[`f:A->A`; `2`; `z:A`; `y:A`] in_orbit_lemma) 
THEN ASM_REWRITE_TAC[POWER_2; o_THM]
THEN DISCH_TAC THEN MP_TAC (SPECL[`D:A->bool`; `f:A->A`; `y:A`; `z:A`] orbit_sym)
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "d1") 
THEN MP_TAC (SPECL[`n:A->A`; `1`; `y:A`; `z:A`] in_orbit_lemma)
THEN ASM_REWRITE_TAC[POWER_1] THEN DISCH_THEN (LABEL_TAC "d2")
THEN REMOVE_THEN "c6" (MP_TAC o (SPEC `y:A`))
THEN UNDISCH_TAC `(y:A) IN D` THEN ASM_REWRITE_TAC[IN] THEN STRIP_TAC
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THEN MP_TAC (SPECL[`orbit_map (n:A->A) (y:A)`;`orbit_map (f:A->A) (y:A)`;`z:A`] IN_INTER)
THEN ASM_REWRITE_TAC[IN_SING] THEN STRIP_TAC
THEN REMOVE_THEN "c11" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC (SPECL[`f:A->A`; `2`; `y:A`] card_orbit_le)
THEN ASM_REWRITE_TAC[ARITH; POWER_2; o_DEF] THEN DISCH_TAC
THEN REMOVE_THEN "c8" (MP_TAC o (SPEC `y:A`)) THEN ASM_REWRITE_TAC[IN]
THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;


(* Definition of connected *)

let connected_hypermap = new_definition `connected_hypermap (H:(A)hypermap) <=> number_of_components H = 1`;;

(* Some lemmas about counting the orbits of a permutation *)


let finite_orbits_lemma = prove(`!D:A->bool p:A->A. (FINITE D /\ p permutes D) ==> FINITE (set_of_orbits D p)`, 
REPEAT STRIP_TAC THEN SUBGOAL_THEN `IMAGE (\x:A. orbit_map (p:A->A) x) (D:A->bool) = set_of_orbits D p` ASSUME_TAC 
THENL[REWRITE_TAC[EXTENSION] THEN STRIP_TAC THEN EQ_TAC THENL[REWRITE_TAC[set_of_orbits;IMAGE;IN;IN_ELIM_THM];ALL_TAC] 
THEN REWRITE_TAC[set_of_orbits;IMAGE;IN;IN_ELIM_THM];ALL_TAC] 
THEN POP_ASSUM (fun th -> REWRITE_TAC[SYM th]) 
THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[]);;


let lemma_disjoints = prove(`!(s:(A->bool)->bool) (t:A->bool). (!(v:A->bool). v IN s ==> DISJOINT t v) ==> DISJOINT t (UNIONS s)`, SET_TAC[]);;


let SET_SIZE_CLAUSES = prove (`(!s. s HAS_SIZE 0 <=> (s = {})) /\(!s (n:num). s HAS_SIZE (SUC n) <=> ?a t. t HAS_SIZE n /\ ~(a IN t) /\ (s = a INSERT t))`,let lemma = SET_RULE `a IN s ==> (s = a INSERT (s DELETE a))` in REWRITE_TAC[HAS_SIZE_0] THEN REPEAT STRIP_TAC THEN EQ_TAC 
THENL [REWRITE_TAC[HAS_SIZE_SUC; GSYM MEMBER_NOT_EMPTY] THEN MESON_TAC[lemma; IN_DELETE]; 
SIMP_TAC[LEFT_IMP_EXISTS_THM; HAS_SIZE; CARD_CLAUSES; FINITE_INSERT]]);;


let TYPED_FINITE_UNIONS = prove
 (`!s:(A->bool)->bool. FINITE(s) ==> (FINITE(UNIONS s) <=> (!g:A->bool. g IN s ==> FINITE(g)))`,
  MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; UNIONS_0; UNIONS_INSERT] THEN
  REWRITE_TAC[FINITE_UNION; FINITE_RULES] THEN MESON_TAC[]);;


let lemma_card_ge = prove
   (`!(n:num) (s:(A->bool)->bool) (m:num). ((FINITE s /\ CARD(s) = n) /\ (!u:A->bool v:A->bool. (u IN s /\ v IN s) 
     ==> (u = v \/ DISJOINT u v)) /\ (!g:A->bool.(g IN s) ==> (FINITE g /\ CARD(g) >= m))) ==> (CARD(UNIONS s) >= m * CARD(s))`, 
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


let lemma_card_le = prove (`!(n:num) (s:(A->bool)->bool) (m:num). ((FINITE s /\ CARD(s) = n) /\ 
  (!u:A->bool v:A->bool. (u IN s /\ v IN s) ==> (u = v \/ DISJOINT u v)) /\ (!g:A->bool.(g IN s) 
   ==> (FINITE g /\ CARD(g) <= m))) ==> (CARD(UNIONS s) <= m * CARD(s))`, 
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


let lemma_partition = prove( `!s:A->bool p:A->A. FINITE s /\ p permutes s ==> s = UNIONS (set_of_orbits s p)`,
REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION;IN_UNIONS] THEN  GEN_TAC THEN EQ_TAC 
THENL[MP_TAC (ISPECL[`p:A->A`;`x:A`] orbit_reflect) THEN REWRITE_TAC[set_of_orbits] 
THEN REPEAT STRIP_TAC THEN EXISTS_TAC `(orbit_map p x):A->bool` THEN (SET_TAC[]); 
DISCH_THEN(X_CHOOSE_THEN `t:A->bool` MP_TAC) THEN REWRITE_TAC[IN_ELIM_THM;set_of_orbits] 
THEN STRIP_TAC THEN FIRST_ASSUM SUBST_ALL_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP  orbit_subset) THEN SET_TAC[]]);;


let lemma_card_eq = prove(`!(n:num) (s:(A->bool)->bool) (m:num). ((FINITE s /\ CARD(s) = n) /\ 
   (!u:A->bool v:A->bool. (u IN s /\ v IN s) ==> (u = v \/ DISJOINT u v)) /\ (!g:A->bool.(g IN s) 
    ==> (FINITE g /\ CARD(g) = m))) ==> (CARD(UNIONS s) = m * CARD(s))`, 
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


let lemma_orbits_ge = prove(`!D:A->bool p:A->A m:num. FINITE D /\ p permutes D /\ (!x:A. x IN D ==> CARD(orbit_map p x) >= m) 
   ==> (CARD D >= m * (number_of_orbits D p))`, 
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
 THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC]
THEN MP_TAC(ISPECL[`D:A->bool`; `p:A->A`] finite_orbits_lemma) THEN ASM_REWRITE_TAC[] 
THEN REPEAT STRIP_TAC THEN ABBREV_TAC `s = set_of_orbits (D:A->bool) (p:A->A)` THEN ABBREV_TAC `n = CARD(s:(A->bool)->bool)` 
THEN MP_TAC(ISPECL[`n:num`;`s:(A->bool)->bool`;`m:num`] lemma_card_ge) THEN ASM_REWRITE_TAC[]);;


let lemma_orbits_eq = prove(`!D:A->bool p:A->A m:num. FINITE D /\ p permutes D /\ (!x:A. x IN D ==> CARD(orbit_map p x) = m) 
   ==> (CARD D = m * (number_of_orbits D p))`, 
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
 THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC]
THEN MP_TAC(ISPECL[`D:A->bool`; `p:A->A`] finite_orbits_lemma) THEN ASM_REWRITE_TAC[] 
THEN REPEAT STRIP_TAC THEN ABBREV_TAC `s = set_of_orbits (D:A->bool) (p:A->A)` THEN ABBREV_TAC `n = CARD(s:(A->bool)->bool)` 
THEN MP_TAC(ISPECL[`n:num`;`s:(A->bool)->bool`;`m:num`] lemma_card_eq) THEN ASM_REWRITE_TAC[]);;


let lemma_card_atleast_one = prove(`!s:A->bool x:A. FINITE s /\ (x IN s) ==> CARD s >= 1`, 
REPEAT STRIP_TAC
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


let lemma_nondegenerate_convolution = prove(`!s:A->bool p:A->A. FINITE s /\ p permutes s /\ p o p = I /\ 
   (!x:A. x IN s ==> ~(p x = x)) ==> (!x:A. x IN s ==> FINITE (orbit_map p x) /\ CARD(orbit_map p x) = 2)`,
REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "F1") (CONJUNCTS_THEN2 (LABEL_TAC "F2")(CONJUNCTS_THEN2 (LABEL_TAC "F3")(LABEL_TAC "F4"))))
  THEN GEN_TAC THEN (DISCH_THEN(LABEL_TAC "F5")) THEN USE_THEN "F2"(MP_TAC o SPEC `x:A` o MATCH_MP orbit_subset) THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (LABEL_TAC "F6") THEN 
  USE_THEN "F1"(fun th1 -> (USE_THEN "F6"(fun th2 -> (MP_TAC(MATCH_MP FINITE_SUBSET (CONJ th1 th2))))))
  THEN DISCH_THEN(LABEL_TAC "F7") THEN ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL[`p:A->A`;`2`;`x:A`] card_orbit_le)
  THEN ASM_REWRITE_TAC[ARITH; SPEC `(p:A->A)` POWER_2;I_THM] THEN DISCH_THEN(LABEL_TAC "F8")
  THEN MP_TAC(ISPECL[`p:A->A`;`1`; `x:A`; `(p:A->A) (x:A)`] in_orbit_lemma) THEN REWRITE_TAC[POWER_1]
  THEN DISCH_THEN(LABEL_TAC "F9") THEN LABEL_TAC "F10" (ISPECL[`p:A->A`;`x:A`] orbit_reflect)
  THEN USE_THEN "F1"(fun th1 -> (USE_THEN "F6" (fun th2 -> LABEL_TAC "F11" (MATCH_MP FINITE_SUBSET (CONJ th1 th2) ))))
  THEN SUBGOAL_THEN `?u:A v:A. u IN orbit_map (p:A->A) (x:A) /\ v IN orbit_map p x /\ ~(u = v)` (LABEL_TAC "F12")
  THENL[EXISTS_TAC `(p:A->A) (x:A)` THEN EXISTS_TAC `x:A` THEN ASM_SIMP_TAC[];ALL_TAC]
  THEN USE_THEN "F11"(fun th1 -> USE_THEN "F12"(fun th2 -> MP_TAC(MATCH_MP lemma_card_atleast_2 (CONJ th1 th2))))
  THEN USE_THEN "F8"(MP_TAC) THEN ARITH_TAC);;


let lemmaTGJISOK = prove(`!H:(A)hypermap. connected_hypermap H /\ plain_hypermap H /\ planar_hypermap H /\
   (!x:A. x IN (dart H) ==> ~(edge_map H x = x)/\ (CARD(node H x) >= 3)) 
   ==> (CARD (dart H) <= (6*(number_of_faces H)-12))`,
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

(* We set up some lemmas on combinatorial commponents *)


let lemma_subpath = prove(`!H:(A)hypermap p:num->A n:num. is_path H p n ==> (!i. i <= n ==> is_path H p i)`,
REPLICATE_TAC 2 GEN_TAC THEN INDUCT_TAC THENL[ SIMP_TAC[is_path; ARITH_RULE `i <= 0 ==> i = 0`]; ALL_TAC] 
THEN STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[ARITH_RULE `i<=SUC n <=> i = SUC n \/ i <= n`] THEN STRIP_TAC  
THENL[ASM_REWRITE_TAC[]; UNDISCH_TAC `is_path (H:(A)hypermap) (p:num->A) (SUC n)` THEN ASM_REWRITE_TAC[is_path] THEN ASM_MESON_TAC[]]);;

let lemm_path_subset = prove(`!H:(A)hypermap x:A p:num->A n:num. (x IN dart H) /\ (p 0 = x) /\ (is_path H p n) ==> p n IN dart H`, 
REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THENL[SIMP_TAC[is_path;go_one_step];ALL_TAC] THEN POP_ASSUM(LABEL_TAC "F1") 
THEN STRIP_TAC THEN POP_ASSUM(fun th -> (MP_TAC(MATCH_MP lemma_subpath th) THEN LABEL_TAC "F2" th)) 
THEN REWRITE_TAC[LEFT_AND_FORALL_THM] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) 
THEN REWRITE_TAC[ARITH_RULE `n <= SUC n`] THEN  STRIP_TAC 
THEN REMOVE_THEN "F1" MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
THEN REMOVE_THEN "F2" MP_TAC THEN ASM_REWRITE_TAC[is_path;go_one_step] 
THEN STRIP_ASSUME_TAC(SPEC `H:(A)hypermap` hypermap_lemma) THEN ASM_REWRITE_TAC[] 
THEN STRIP_ASSUME_TAC(SPEC `H:(A)hypermap` hypermap_lemma) 
THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` 
THEN ABBREV_TAC `nn = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
THEN ABBREV_TAC `u = (p:num->A) (SUC n)` 
THEN ABBREV_TAC `v = (p:num->A) n` 
THEN MP_TAC(ISPECL[`e:A->A`; `D:A->bool`; `v:A`] PERMUTES_IN_IMAGE) 
THEN ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL[`nn:A->A`; `D:A->bool`; `v:A`] PERMUTES_IN_IMAGE) 
THEN ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL[`f:A->A`; `D:A->bool`; `v:A`] PERMUTES_IN_IMAGE) 
THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let lemma_component_subset = prove(`!H:(A)hypermap x:A. x IN dart H ==> combinatorial_component H x SUBSET dart H`, 
REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC(SPEC `H:(A)hypermap` hypermap_lemma) 
THEN REWRITE_TAC[SUBSET;IN_ELIM_THM;combinatorial_component] 
THEN GEN_TAC THEN REWRITE_TAC[is_in_component] THEN ASM_MESON_TAC[lemm_path_subset]);;

let lemma_component_reflect = prove(`!H:(A)hypermap x:A. x IN dart H ==> x IN combinatorial_component H x`, 
REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM; combinatorial_component;is_in_component] 
THEN EXISTS_TAC `(\k:num. x:A)` THEN EXISTS_TAC `0` THEN MESON_TAC[is_path]);;


(* The definition of path is exactly here *)


let lemma_def_path = prove(`!H:(A)hypermap p:num->A n:num.(is_path H p n <=> (!i:num. i < n ==> go_one_step H (p i) (p (SUC i))))`, 
REPLICATE_TAC 2 GEN_TAC THEN INDUCT_TAC 
THENL[REWRITE_TAC[is_path] THEN ARITH_TAC; ALL_TAC] 
THEN ASM_REWRITE_TAC[is_path] THEN EQ_TAC THENL[STRIP_TAC THEN  GEN_TAC 
THEN REWRITE_TAC[ARITH_RULE `i<SUC n <=> i = n \/ i < n`] THEN ASM_MESON_TAC[]; ALL_TAC] 
THEN REWRITE_TAC[ARITH_RULE `i<SUC n <=> i = n \/ i < n`] THEN STRIP_TAC 
THEN ASM_MESON_TAC[ARITH_RULE `n < SUC n /\ i < SUC n <=> (i = n \/ i < n)`]);;


(* some lemmas on concatenate paths *)


let lemma_edges_path = prove(`!(H:(A)hypermap) x:A. ?p:num->A. p 0 = x /\ (!k:num. (p k = ((edge_map H) POWER k) x) /\ is_path H p k)`,
REPEAT GEN_TAC THEN EXISTS_TAC `(\m:num. ((edge_map (H:(A)hypermap)) POWER m) (x:A))` THEN STRIP_TAC 
THENL[CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[POWER;I_THM];ALL_TAC] 
THEN STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[] 
THEN REWRITE_TAC[lemma_def_path] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[go_one_step] 
THEN DISJ1_TAC THEN REWRITE_TAC[COM_POWER;o_THM]);;

let lemma_nodes_path = prove(`!(H:(A)hypermap) x:A. ?p:num->A. p 0 = x /\ (!k:num. (p k = ((node_map H) POWER k) x) /\ is_path H p k)`,
REPEAT GEN_TAC THEN EXISTS_TAC `(\m:num. ((node_map (H:(A)hypermap)) POWER m) (x:A))` 
THEN STRIP_TAC THENL[CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[POWER;I_THM];ALL_TAC] 
THEN STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[] THEN REWRITE_TAC[lemma_def_path] 
THEN REPEAT STRIP_TAC THEN REWRITE_TAC[go_one_step] 
THEN DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC[COM_POWER;o_THM]);;

let lemma_faces_path = prove(`!(H:(A)hypermap) x:A. ?p:num->A. p 0 = x /\ (!k:num. (p k = ((face_map H) POWER k) x) /\ is_path H p k)`,
REPEAT GEN_TAC THEN EXISTS_TAC `(\m:num. ((face_map (H:(A)hypermap)) POWER m) (x:A))`
THEN STRIP_TAC THENL[CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[POWER;I_THM];ALL_TAC] 
THEN STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[] THEN 
REWRITE_TAC[lemma_def_path] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[go_one_step] 
THEN DISJ2_TAC THEN DISJ2_TAC THEN REWRITE_TAC[COM_POWER;o_THM]);;



let identify_path = prove(`!(H:(A)hypermap) p:num->A q:num->A n:num. is_path H p n /\ (!i:num. i<= n ==> p i = q i) ==> is_path H q n`,
REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THENL[STRIP_TAC THEN REWRITE_TAC[is_path]; ALL_TAC] 
THEN POP_ASSUM (LABEL_TAC "F1") THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F2") (LABEL_TAC "F3")) 
THEN REMOVE_THEN "F2" MP_TAC THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [is_path] 
THEN STRIP_TAC THEN REMOVE_THEN "F1" MP_TAC THEN ASM_REWRITE_TAC[] 
THEN SUBGOAL_THEN `!i:num. i <= (n:num) ==> (p:num->A) i = (q:num->A) i` ASSUME_TAC 
THENL[REPEAT STRIP_TAC THEN MP_TAC(ARITH_RULE `i:num <= n:num ==> i <= SUC n`) THEN ASM_REWRITE_TAC[]; ALL_TAC] 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[is_path] 
THEN SUBGOAL_THEN `(p:num->A) (n:num) = (q:num->A) (n:num)` ASSUME_TAC THENL[ASM_MESON_TAC[ARITH_RULE `n <= SUC n`];ALL_TAC]
THEN SUBGOAL_THEN `(p:num->A) (SUC(n:num)) = (q:num->A) (SUC(n:num))` ASSUME_TAC 
THENL[ASM_MESON_TAC[ARITH_RULE `SUC n <= SUC n`];ALL_TAC] 
THEN UNDISCH_THEN `go_one_step (H:(A)hypermap) ((p:num->A) (n:num)) ((p:num->A) (SUC n:num))` MP_TAC 
THEN ASM_REWRITE_TAC[]);;


let concatenate_paths = prove( `!H:(A)hypermap p:num->A q:num->A n:num m:num. is_path H p n /\ is_path H q m /\ (p n = q 0) ==> ?g:num->A. g 0 = p 0 /\ g (n+m) = q m /\ is_path H g (n+m)`, 
REPLICATE_TAC 4 GEN_TAC THEN INDUCT_TAC 
THENL[REPEAT STRIP_TAC THEN EXISTS_TAC `p:num->A` THEN ASM_REWRITE_TAC[ADD_0]; ALL_TAC] 
THEN POP_ASSUM (LABEL_TAC "F1") 
THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F2")(CONJUNCTS_THEN2 (LABEL_TAC "F3") (LABEL_TAC "F4"))) 
THEN USE_THEN "F3" (MP_TAC o SPEC `m:num` o MATCH_MP lemma_subpath) 
THEN SIMP_TAC [ARITH_RULE `m <= SUC m`] 
THEN DISCH_THEN (LABEL_TAC "F5") THEN REMOVE_THEN "F1" MP_TAC 
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `h:num->A` (LABEL_TAC "F6")) 
THEN EXISTS_TAC `(\k:num. if k = (n:num) + (SUC (m:num)) then (q:num->A) (SUC m) else (h:num->A) k)` 
THEN REPEAT STRIP_TAC 
THENL[REWRITE_TAC[ARITH_RULE `~(n+SUC m = 0)`] THEN ASM_REWRITE_TAC[]; REWRITE_TAC []; ALL_TAC] 
THEN REWRITE_TAC [ADD_SUC]
THEN ABBREV_TAC `t = (\k:num. if k = SUC ((n:num)+(m:num)) then (q:num->A) (SUC m) else (h:num->A) k)` 
THEN SUBGOAL_THEN `!i:num. i <= (n:num) + (m:num) ==> (h:num->A) i = (t:num->A) i` (LABEL_TAC "FA") 
THENL [REPEAT  STRIP_TAC THEN MP_TAC(ARITH_RULE `(i:num) <= (n:num)+(m:num) ==> ~(i = SUC (n+m))`) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "t" 
THEN POP_ASSUM (fun th -> REWRITE_TAC[th; COND_ELIM_THM]);ALL_TAC] 
THEN SUBGOAL_THEN `(t:num->A) (SUC((n:num) + (m:num))) = (q:num->A) (SUC m)` ASSUME_TAC 
THENL[EXPAND_TAC "t" THEN REWRITE_TAC[COND_ELIM_THM]; ALL_TAC] 
THEN REWRITE_TAC[] 
THEN MP_TAC(SPECL[`H:(A)hypermap`; `h:num->A`;`t:num->A`;`(n:num)+(m:num)` ] identify_path) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[is_path] THEN ASM_REWRITE_TAC[] 
THEN REMOVE_THEN "FA" (MP_TAC o SPEC `(n:num) + (m:num)`) 
THEN REWRITE_TAC[ARITH_RULE `(n:num) + (m:num) <= n + m`] 
THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] 
THEN REMOVE_THEN "F3" (fun th -> MESON_TAC[th; is_path]));;


let lemma_component_trans = prove(`!H:(A)hypermap x:A y:A z:A. y IN combinatorial_component H x /\ z IN combinatorial_component H y 
   ==> z IN combinatorial_component H x`, 
REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM; combinatorial_component; is_in_component] 
THEN REPEAT STRIP_TAC 
THEN MP_TAC(ISPECL[`H:(A)hypermap`; `p:num->A`;`p':num->A`;`n:num`;`n':num`] concatenate_paths) 
THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;


let lemma_reverse_path = prove(`!H:(A)hypermap p:num->A n:num. is_path H p n
   ==> ?q:num->A m:num. q 0 = p n /\ q m = p 0 /\ is_path H q m`, 
REPLICATE_TAC 2 GEN_TAC THEN INDUCT_TAC
THENL[STRIP_TAC THEN EXISTS_TAC `p:num->A` THEN EXISTS_TAC `0` 
THEN ASM_REWRITE_TAC[]; ALL_TAC] 
THEN DISCH_THEN (fun th-> (ASSUME_TAC th THEN MP_TAC(SPEC `n:num` (MATCH_MP lemma_subpath th)))) 
THEN ASM_REWRITE_TAC[ARITH_RULE `n <= SUC n`] 
THEN STRIP_TAC THEN STRIP_ASSUME_TAC(SPEC `H:(A)hypermap` hypermap_lemma) 
THEN ABBREV_TAC `D = dart (H:(A)hypermap)` THEN ABBREV_TAC `em = edge_map (H:(A)hypermap)` 
THEN ABBREV_TAC `nm = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `fm = face_map (H:(A)hypermap)` 
THEN FIRST_X_ASSUM(MP_TAC o check(is_imp o concl)) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN UNDISCH_TAC `is_path (H:(A)hypermap) (p:num->A) (SUC n)` 
THEN ASM_REWRITE_TAC[is_path; go_one_step] THEN STRIP_TAC 
THENL[MP_TAC (ISPECL[`D:A->bool`; `em:A->A`; `((p:num->A) (n:num)):A`; `((p:num->A) (SUC (n:num))):A`] inverse_relation) 
THEN ASM_REWRITE_TAC[] THEN 
POP_ASSUM(fun th -> ASM_REWRITE_TAC[SYM th]) 
THEN MP_TAC(SPECL[`H:(A)hypermap`;`(p:num->A) (SUC n)`] lemma_edges_path)
THEN REPEAT STRIP_TAC THEN MP_TAC(SPECL[`H:(A)hypermap`;`p':num->A`;`q:num->A`;`k:num`;`m:num`] concatenate_paths) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `g:num->A` THEN EXISTS_TAC `((k:num)+(m:num)):num` 
THEN ASM_REWRITE_TAC[]; 
MP_TAC (ISPECL[`D:A->bool`; `nm:A->A`; `((p:num->A) (n:num)):A`; `((p:num->A) (SUC (n:num))):A`] inverse_relation) 
THEN ASM_REWRITE_TAC[] THEN POP_ASSUM(fun th -> ASM_REWRITE_TAC[SYM th]) 
THEN MP_TAC(SPECL[`H:(A)hypermap`;`(p:num->A) (SUC n)`] lemma_nodes_path) 
THEN REPEAT STRIP_TAC THEN MP_TAC(SPECL[`H:(A)hypermap`;`p':num->A`;`q:num->A`;`k:num`;`m:num`] concatenate_paths) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
THEN EXISTS_TAC `g:num->A` THEN EXISTS_TAC `((k:num)+(m:num)):num` THEN ASM_REWRITE_TAC[]; ALL_TAC] 
THEN MP_TAC (ISPECL[`D:A->bool`; `fm:A->A`; `((p:num->A) (n:num)):A`; `((p:num->A) (SUC (n:num))):A`] inverse_relation) 
THEN ASM_REWRITE_TAC[] 
THEN POP_ASSUM(fun th -> ASM_REWRITE_TAC[SYM th]) THEN MP_TAC(SPECL[`H:(A)hypermap`;`(p:num->A) (SUC n)`] lemma_faces_path) 
THEN REPEAT STRIP_TAC THEN MP_TAC(SPECL[`H:(A)hypermap`;`p':num->A`;`q:num->A`;`k:num`;`m:num`] concatenate_paths) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `g:num->A` 
THEN EXISTS_TAC `((k:num)+(m:num)):num` THEN ASM_REWRITE_TAC[]);;


let lemma_component_symmetry = prove(`!H:(A)hypermap x:A y:A. y IN combinatorial_component H x 
   ==> x IN combinatorial_component H y`,
REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM; combinatorial_component; is_in_component] 
THEN REPEAT STRIP_TAC THEN POP_ASSUM (MP_TAC o MATCH_MP lemma_reverse_path) 
THEN ASM_REWRITE_TAC[]);;


let partition_components = prove(`!(H:(A)hypermap) x:A y:A. 
   combinatorial_component H x = combinatorial_component H y \/ combinatorial_component H x INTER combinatorial_component H y ={}`, 
REPEAT GEN_TAC THEN ASM_CASES_TAC `combinatorial_component (H:(A)hypermap) (x:A) INTER combinatorial_component H (y:A) ={}` 
THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] 
THEN DISCH_THEN (X_CHOOSE_THEN `t:A` MP_TAC) THEN REWRITE_TAC[INTER; IN_ELIM_THM] 
THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "F1") (LABEL_TAC "F2")) THEN REWRITE_TAC[EXTENSION] 
THEN GEN_TAC THEN  EQ_TAC THENL[USE_THEN "F1" (LABEL_TAC "F3"  o MATCH_MP lemma_component_symmetry) 
THEN DISCH_THEN (LABEL_TAC "F4") 
THEN REMOVE_THEN "F4"(fun th1 -> REMOVE_THEN "F3" (fun th2 -> MP_TAC (MATCH_MP lemma_component_trans (CONJ th2 th1)))) 
THEN DISCH_THEN(fun th1 -> (REMOVE_THEN "F2" (fun th2 -> MP_TAC (MATCH_MP lemma_component_trans (CONJ th2 th1))))) THEN REWRITE_TAC[];ALL_TAC] 
THEN USE_THEN "F2" (LABEL_TAC "F5"  o MATCH_MP lemma_component_symmetry) 
THEN DISCH_THEN (LABEL_TAC "F6") 
THEN REMOVE_THEN "F6"(fun th1 -> REMOVE_THEN "F5" (fun th2 -> MP_TAC (MATCH_MP lemma_component_trans (CONJ th2 th1)))) 
THEN DISCH_THEN(fun th1 -> (REMOVE_THEN "F1" (fun th2 -> MP_TAC (MATCH_MP lemma_component_trans (CONJ th2 th1))))) 
THEN REWRITE_TAC[]);;


(* We define the CONTOUR PATHS *)


let one_step_contour = new_definition `one_step_contour (H:(A)hypermap) (x:A) (y:A) <=> (y = (face_map H) x) \/ (y = (inverse (node_map H)) x)`;;

let is_contour= new_recursive_definition num_RECURSION  `(is_contour (H:(A)hypermap) (p:num->A) 0 <=> T)/\
(is_contour (H:(A)hypermap) (p:num->A) (SUC n) <=> ((is_contour H p n) /\ one_step_contour H (p n) (p (SUC n))))`;; 

let lemma_subcontour = prove(`!H:(A)hypermap p:num->A n:num. is_contour H p n ==> (!i. i <= n ==> is_contour H p i)`,
REPLICATE_TAC 2 GEN_TAC THEN INDUCT_TAC 
THENL[ SIMP_TAC[is_contour; ARITH_RULE `i <= 0 ==> i = 0`]; ALL_TAC] 
THEN STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[ARITH_RULE `i<=SUC n <=> i = SUC n \/ i <= n`] 
THEN STRIP_TAC 
THENL[ASM_REWRITE_TAC[]; 
UNDISCH_TAC `is_contour (H:(A)hypermap) (p:num->A) (SUC n)` THEN ASM_REWRITE_TAC[is_contour] THEN ASM_MESON_TAC[]]);;

let lemma_def_contour = prove(`!H:(A)hypermap p:num->A n:num.(is_contour H p n <=> (!i:num. i < n ==> one_step_contour H (p i) (p (SUC i))))`, 
REPLICATE_TAC 2 GEN_TAC THEN INDUCT_TAC 
THENL[REWRITE_TAC[is_contour] THEN ARITH_TAC; ALL_TAC] 
THEN ASM_REWRITE_TAC[is_contour] THEN EQ_TAC 
THENL[STRIP_TAC THEN  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `i<SUC n <=> i = n \/ i < n`] THEN ASM_MESON_TAC[]; ALL_TAC] 
THEN REWRITE_TAC[ARITH_RULE `i<SUC n <=> i = n \/ i < n`] 
THEN STRIP_TAC 
THEN ASM_MESON_TAC[ARITH_RULE `n < SUC n /\ i < SUC n <=> (i = n \/ i < n)`]);;


let identify_contour = prove(`!(H:(A)hypermap) p:num->A q:num->A n:num. is_contour H p n /\ (!i:num. i<= n ==> p i = q i) ==> is_contour H q n`,
REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC 
THENL[STRIP_TAC THEN REWRITE_TAC[is_contour]; ALL_TAC] 
THEN POP_ASSUM (LABEL_TAC "F1") 
THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F2") (LABEL_TAC "F3")) 
THEN REMOVE_THEN "F2" MP_TAC THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [is_contour] 
THEN STRIP_TAC THEN REMOVE_THEN "F1" MP_TAC THEN ASM_REWRITE_TAC[] 
THEN SUBGOAL_THEN `!i:num. i <= (n:num) ==> (p:num->A) i = (q:num->A) i` ASSUME_TAC 
THENL[REPEAT STRIP_TAC THEN MP_TAC(ARITH_RULE `i:num <= n:num ==> i <= SUC n`) THEN ASM_REWRITE_TAC[]; ALL_TAC] 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[is_contour] 
THEN SUBGOAL_THEN `(p:num->A) (n:num) = (q:num->A) (n:num)` ASSUME_TAC 
THENL[ASM_MESON_TAC[ARITH_RULE `n <= SUC n`];ALL_TAC] 
THEN SUBGOAL_THEN `(p:num->A) (SUC(n:num)) = (q:num->A) (SUC(n:num))` ASSUME_TAC 
THENL[ASM_MESON_TAC[ARITH_RULE `SUC n <= SUC n`];ALL_TAC] 
THEN UNDISCH_THEN `one_step_contour (H:(A)hypermap) ((p:num->A) (n:num)) ((p:num->A) (SUC n:num))` MP_TAC 
THEN ASM_REWRITE_TAC[]);;


let concatenate_contours = prove( `!H:(A)hypermap p:num->A q:num->A n:num m:num. is_contour H p n /\ is_contour H q m /\ (p n = q 0) ==> ?g:num->A. g 0 = p 0 /\ g (n+m) = q m /\ is_contour H g (n+m)`, 
REPLICATE_TAC 4 GEN_TAC THEN INDUCT_TAC 
THENL[REPEAT STRIP_TAC THEN EXISTS_TAC `p:num->A` THEN ASM_REWRITE_TAC[ADD_0]; ALL_TAC] 
THEN POP_ASSUM (LABEL_TAC "F1") 
THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F2")(CONJUNCTS_THEN2 (LABEL_TAC "F3") (LABEL_TAC "F4"))) 
THEN USE_THEN "F3" (MP_TAC o SPEC `m:num` o MATCH_MP lemma_subcontour) THEN SIMP_TAC [ARITH_RULE `m <= SUC m`] 
THEN DISCH_THEN (LABEL_TAC "F5") THEN REMOVE_THEN "F1" MP_TAC 
THEN ASM_REWRITE_TAC[] 
THEN DISCH_THEN(X_CHOOSE_THEN `h:num->A` (LABEL_TAC "F6")) 
THEN EXISTS_TAC `(\k:num. if k = (n:num) + (SUC (m:num)) then (q:num->A) (SUC m) else (h:num->A) k)` 
THEN REPEAT STRIP_TAC 
THENL[REWRITE_TAC[ARITH_RULE `~(n+SUC m = 0)`] THEN ASM_REWRITE_TAC[]; REWRITE_TAC []; ALL_TAC] 
THEN REWRITE_TAC [ADD_SUC] 
THEN ABBREV_TAC `t = (\k:num. if k = SUC ((n:num)+(m:num)) then (q:num->A) (SUC m) else (h:num->A) k)` 
THEN SUBGOAL_THEN `!i:num. i <= (n:num) + (m:num) ==> (h:num->A) i = (t:num->A) i` (LABEL_TAC "FA") 
 THENL[ REPEAT  STRIP_TAC THEN MP_TAC(ARITH_RULE `(i:num) <= (n:num)+(m:num) ==> ~(i = SUC (n+m))`) 
 THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "t" 
 THEN POP_ASSUM (fun th -> REWRITE_TAC[th; COND_ELIM_THM]); ALL_TAC]
THEN SUBGOAL_THEN `(t:num->A) (SUC((n:num) + (m:num))) = (q:num->A) (SUC m)` ASSUME_TAC 
THENL[ EXPAND_TAC "t" THEN REWRITE_TAC[COND_ELIM_THM]; ALL_TAC] THEN REWRITE_TAC[] 
THEN MP_TAC(SPECL[`H:(A)hypermap`; `h:num->A`;`t:num->A`;`(n:num)+(m:num)` ] identify_contour) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[is_contour] THEN ASM_REWRITE_TAC[] 
THEN REMOVE_THEN "FA" (MP_TAC o SPEC `(n:num) + (m:num)`) 
THEN REWRITE_TAC[ARITH_RULE `(n:num) + (m:num) <= n + m`] THEN 
DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] 
THEN REMOVE_THEN "F3" (fun th -> MESON_TAC[th; is_contour]));;


let lemma_nodes_contour = prove(
   `!(H:(A)hypermap) x:A. ?p:num->A. p 0 = x /\ (!k:num. (p k = ((inverse(node_map H)) POWER k) x) /\ is_contour H p k)`, 
REPEAT GEN_TAC 
THEN EXISTS_TAC `(\m:num. ((inverse (node_map (H:(A)hypermap))) POWER m) (x:A))` 
THEN STRIP_TAC THENL[CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[POWER;I_THM];ALL_TAC] 
THEN STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[] 
THEN REWRITE_TAC[lemma_def_contour] THEN REPEAT STRIP_TAC 
THEN REWRITE_TAC[one_step_contour] THEN DISJ2_TAC THEN REWRITE_TAC[COM_POWER;o_THM]);;


let lemma_faces_contour = prove(`!(H:(A)hypermap) x:A. ?p:num->A. p 0 = x /\ (!k:num. (p k = ((face_map H) POWER k) x) /\ is_contour H p k)`,
REPEAT GEN_TAC THEN EXISTS_TAC `(\m:num. ((face_map (H:(A)hypermap)) POWER m) (x:A))` THEN STRIP_TAC 
THENL[CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[POWER;I_THM];ALL_TAC] 
THEN STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[] 
THEN REWRITE_TAC[lemma_def_contour] THEN REPEAT STRIP_TAC 
THEN REWRITE_TAC[one_step_contour] THEN DISJ1_TAC 
THEN REWRITE_TAC[COM_POWER;o_THM]);;


let existence_contour = prove(`!H:(A)hypermap p:num->A n:num. is_path H p n 
   ==> ?q:num->A m:num. q 0 = p 0 /\ q m = p n /\ is_contour H q m`, 
REPLICATE_TAC 2 GEN_TAC THEN INDUCT_TAC 
THENL[STRIP_TAC THEN EXISTS_TAC `p:num->A` THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[is_contour]; ALL_TAC] 
THEN DISCH_THEN (fun th-> ((LABEL_TAC "F1" th) THEN MP_TAC(SPEC `n:num` (MATCH_MP lemma_subpath th)))) 
THEN ASM_REWRITE_TAC[ARITH_RULE `n <= SUC n`] 
THEN DISCH_THEN (LABEL_TAC "F2") THEN MP_TAC(SPEC `H:(A)hypermap` hypermap_lemma) 
THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `em = edge_map (H:(A)hypermap)` 
THEN ABBREV_TAC `nm = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `fm = face_map (H:(A)hypermap)` 
THEN DISCH_THEN(fun th -> (CONJUNCTS_THEN2 (LABEL_TAC "B1") (LABEL_TAC "B2") (MATCH_MP cyclic_maps th)) THEN ASSUME_TAC th) 
THEN POP_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "F3") (CONJUNCTS_THEN2 (LABEL_TAC "F4") (CONJUNCTS_THEN2 (LABEL_TAC "F5") (CONJUNCTS_THEN2 (LABEL_TAC "F6") (LABEL_TAC "F7" ))))) 
THEN FIRST_X_ASSUM(MP_TAC o check(is_imp o concl)) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REMOVE_THEN "F1" MP_TAC 
THEN ASM_REWRITE_TAC[is_path; go_one_step] THEN STRIP_TAC 
THENL[MP_TAC (ISPECL[`D:A->bool`;`nm:A->A`; `(fm:A->A) o (em:A->A)`; `I:A->A`] LEFT_INVERSE_EQUATION) 
THEN ASM_REWRITE_TAC[I_O_ID] THEN STRIP_TAC 
THEN MP_TAC (ISPECL[`D:A->bool`;`fm:A->A`; `em:A->A`; `inverse(nm:A->A)`] LEFT_INVERSE_EQUATION) 
THEN ASM_REWRITE_TAC[] 
THEN USE_THEN "F3"(fun th1 -> USE_THEN "F6"(fun th2 -> MP_TAC(MATCH_MP inverse_element_lemma (CONJ th1 th2)))) 
THEN DISCH_THEN (X_CHOOSE_THEN `l:num` SUBST1_TAC ) THEN DISCH_THEN (LABEL_TAC "F8")
THEN MP_TAC(SPECL[`H:(A)hypermap`;`((q:num->A) (m:num)):A`] lemma_nodes_contour) 
THEN DISCH_THEN (X_CHOOSE_THEN `pe:num->A` STRIP_ASSUME_TAC) 
THEN POP_ASSUM(MP_TAC o SPEC `1`) THEN ASM_REWRITE_TAC[POWER_1] THEN STRIP_TAC 
THEN MP_TAC(SPECL[`H:(A)hypermap`; `q:num->A`; `pe:num->A`; `m:num`; `1`] concatenate_contours) THEN ASM_REWRITE_TAC[] 
THEN DISCH_THEN(X_CHOOSE_THEN `qe:num->A` ASSUME_TAC) 
THEN MP_TAC(SPECL[`H:(A)hypermap`;`((qe:num->A) ((m:num)+1)):A`] lemma_faces_contour) 
THEN DISCH_THEN (X_CHOOSE_THEN `pf:num->A` STRIP_ASSUME_TAC) THEN POP_ASSUM(MP_TAC o SPEC `l:num`) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN 
MP_TAC(SPECL[`H:(A)hypermap`; `qe:num->A`; `pf:num->A`; `(m:num)+1`; `l:num`] concatenate_contours) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `g:num->A` 
THEN EXISTS_TAC `((m:num)+1)+(l:num)` THEN ASM_REWRITE_TAC[] 
THEN REWRITE_TAC[o_THM]; USE_THEN "F5"((LABEL_TAC "B3") o MATCH_MP PERMUTES_INVERSE) 
THEN USE_THEN "F3"(fun th1 -> USE_THEN "B3"(fun th2 -> MP_TAC(MATCH_MP inverse_element_lemma (CONJ th1 th2))))
THEN USE_THEN "F5"(ASSUME_TAC o MATCH_MP PERMUTES_INVERSE_INVERSE) 
THEN POP_ASSUM(fun th->REWRITE_TAC[th]) 
THEN DISCH_THEN (X_CHOOSE_THEN `l:num` (LABEL_TAC "F9" )) 
THEN MP_TAC(SPECL[`H:(A)hypermap`;`((q:num->A) (m:num)):A`] lemma_nodes_contour) 
THEN DISCH_THEN (X_CHOOSE_THEN `pe:num->A` STRIP_ASSUME_TAC) 
THEN POP_ASSUM(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
THEN MP_TAC(SPECL[`H:(A)hypermap`; `q:num->A`; `pe:num->A`; `m:num`; `l:num`] concatenate_contours) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `g:num->A` THEN EXISTS_TAC `((m+l):num)` THEN ASM_REWRITE_TAC[] 
THEN USE_THEN "F9" (fun th -> REWRITE_TAC[SYM th]); ALL_TAC] 
THEN MP_TAC(SPECL[`H:(A)hypermap`;`((q:num->A) (m:num)):A`] lemma_faces_contour) 
THEN DISCH_THEN (X_CHOOSE_THEN `pf:num->A` STRIP_ASSUME_TAC) THEN POP_ASSUM(MP_TAC o SPEC `1`) 
THEN ASM_REWRITE_TAC[POWER_1] THEN  STRIP_TAC 
THEN MP_TAC(SPECL[`H:(A)hypermap`; `q:num->A`; `pf:num->A`; `m:num`; `1`] concatenate_contours) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `g:num->A` THEN EXISTS_TAC `(m:num)+1` 
THEN ASM_REWRITE_TAC[]);;


let lemmaKDAEDEX = prove(`!H:(A)hypermap x:A y:A. y IN combinatorial_component H x 
   ==> ?p:num->A n:num. (p 0 = x) /\ (p n = y) /\ (is_contour H p n)`, 
REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM; combinatorial_component; is_in_component] 
THEN REPEAT STRIP_TAC THEN POP_ASSUM (MP_TAC o MATCH_MP existence_contour) 
THEN REPEAT STRIP_TAC THEN EXISTS_TAC `q:num->A` THEN EXISTS_TAC `m:num` 
THEN ASM_REWRITE_TAC[]);;


(* the definition of injectve contours *)

let is_inj_contour = new_recursive_definition num_RECURSION  `(is_inj_contour (H:(A)hypermap) (p:num->A) 0 <=> T) /\ 
        (is_inj_contour (H:(A)hypermap) (p:num->A) (SUC n) <=> ((is_inj_contour H p n) /\ one_step_contour H (p n) (p (SUC n)) /\ 
                 (!i:num. i <= n ==> ~(p i = p (SUC n))) ))`;; 

let lemma_sub_inj_contour = prove(`!H:(A)hypermap p:num->A n:num. is_inj_contour H p n
    ==> (!i. i <= n ==> is_inj_contour H p i)`,
REPLICATE_TAC 2 GEN_TAC THEN INDUCT_TAC 
THENL[ SIMP_TAC[is_inj_contour; ARITH_RULE `i <= 0 ==> i = 0`]; ALL_TAC] 
THEN STRIP_TAC THEN GEN_TAC THEN 
REWRITE_TAC[ARITH_RULE `i<=SUC n <=> i = SUC n \/ i <= n`] 
THEN STRIP_TAC  THENL[ASM_REWRITE_TAC[]; 
UNDISCH_TAC `is_inj_contour (H:(A)hypermap) (p:num->A) (SUC n)` 
THEN ASM_REWRITE_TAC[is_inj_contour] THEN ASM_MESON_TAC[]]);;


let identify_inj_contour = prove(`!(H:(A)hypermap) p:num->A q:num->A n:num. is_inj_contour H p n /\ (!i:num. i<= n ==> p i = q i) 
   ==> is_inj_contour H q n`, 
REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC 
THENL[STRIP_TAC THEN REWRITE_TAC[is_inj_contour]; ALL_TAC] 
THEN POP_ASSUM (LABEL_TAC "F1") 
THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F2") (LABEL_TAC "F3")) 
THEN REMOVE_THEN "F2" MP_TAC 
THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [is_inj_contour] 
THEN STRIP_TAC THEN REMOVE_THEN "F1" MP_TAC THEN ASM_REWRITE_TAC[] 
THEN SUBGOAL_THEN `!i:num. i <= (n:num) ==> (p:num->A) i = (q:num->A) i` ASSUME_TAC 
THENL[REPEAT STRIP_TAC THEN MP_TAC(ARITH_RULE `i:num <= n:num ==> i <= SUC n`) 
THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
THEN ASM_REWRITE_TAC[is_inj_contour] 
THEN SUBGOAL_THEN `(p:num->A) (n:num) = (q:num->A) (n:num)` (ASSUME_TAC o SYM) 
THENL[ASM_MESON_TAC[ARITH_RULE `n <= SUC n`]; ALL_TAC] 
THEN  SUBGOAL_THEN `(p:num->A) (SUC(n:num)) = (q:num->A) (SUC(n:num))`  (ASSUME_TAC o SYM) 
THENL[ASM_MESON_TAC[ARITH_RULE `SUC n <= SUC n`]; ALL_TAC] 
THEN UNDISCH_THEN `one_step_contour (H:(A)hypermap) ((p:num->A) (n:num)) ((p:num->A) (SUC n:num))` 
MP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPLICATE_TAC 2 STRIP_TAC 
THEN UNDISCH_THEN `!i:num. i <= (n:num) ==> (p:num->A) i = (q:num->A) i` (MP_TAC o SPEC `i:num`) 
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (SUBST1_TAC o SYM) 
THEN ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= SUC n`]);;


let lemma_def_inj_contour = prove(`!(H:(A)hypermap) p:num->A n:num. 
   is_inj_contour H p n <=> is_contour H p n /\ (!i:num j:num. i <= n /\ j < i ==> ~(p j = p i))`, 
REPLICATE_TAC 2 GEN_TAC THEN INDUCT_TAC 
THENL[REWRITE_TAC[is_inj_contour; is_contour] THEN ARITH_TAC; ALL_TAC] 
THEN POP_ASSUM (LABEL_TAC "B1") 
THEN ASM_REWRITE_TAC[is_inj_contour; is_contour] THEN EQ_TAC 
THENL[STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REMOVE_THEN "B1" MP_TAC 
   THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC 
   THEN ASM_CASES_TAC `i:num = SUC (n:num)` 
   THENL[POP_ASSUM SUBST_ALL_TAC THEN MP_TAC (ARITH_RULE `j:num < SUC (n:num) ==> j <= n`) 
   THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
   THEN UNDISCH_THEN `!i:num. i <= (n:num) ==> ~((p:num->A) i = p (SUC n))` (MP_TAC o SPEC `j:num`) 
   THEN ASM_REWRITE_TAC[]; ALL_TAC]
   THEN MP_TAC (ARITH_RULE `(i:num <= SUC (n:num)) /\ ~(i = SUC n) ==> i <= n`) 
   THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
   THEN UNDISCH_THEN `!(i:num) (j:num). i <= (n:num) /\ j < i ==> ~((p:num->A) j = p i)` (MP_TAC o ISPECL[`i:num`;`j:num`]) 
   THEN ASM_REWRITE_TAC[]; ALL_TAC] 
THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
THENL[ REPEAT STRIP_TAC THEN MP_TAC(ARITH_RULE `i:num <= n:num ==> i <= SUC n`) 
   THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN 
   UNDISCH_THEN `!i:num j:num. i <= SUC (n:num) /\ j < i ==> ~((p:num->A) j = p i)` (MP_TAC o SPECL[`i:num`;`j:num`]) 
   THEN ASM_REWRITE_TAC[]; ALL_TAC] 
THEN REPEAT STRIP_TAC THEN MP_TAC(ARITH_RULE `i:num <= n:num ==> i < SUC n`) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
THEN UNDISCH_THEN `!i:num j:num. i <= SUC (n:num) /\ j < i ==> ~((p:num->A) j = p i)` (MP_TAC o SPECL[`SUC(n:num)`;`i:num`]) 
THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;


let lemma3dot11 = prove(`!(H:(A)hypermap) p:num->A n:num. is_contour H p n 
   ==> ?q:num->A m:num. q 0 = p 0 /\ q m = p n /\ is_inj_contour H q m /\ (!i:num. (i < m)==>(?j:num. j < n /\ q i = p j /\ q (SUC i) = p (SUC j)) )`, 
REPLICATE_TAC 2 GEN_TAC THEN INDUCT_TAC 
THENL[STRIP_TAC THEN EXISTS_TAC `p:num->A` THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[is_inj_contour] THEN  ARITH_TAC; ALL_TAC]
THEN REWRITE_TAC[is_contour] THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F1") (LABEL_TAC "F2")) 
THEN FIRST_X_ASSUM(MP_TAC o check(is_imp o concl))
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_CASES_TAC `?k:num. k <= m:num /\ (q:num->A) k = p (SUC n:num)`
THENL[POP_ASSUM (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) 
THEN EXISTS_TAC `q:num->A` 
THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] 
THEN UNDISCH_THEN `is_inj_contour (H:(A)hypermap) (q:num->A) (m:num)` (MP_TAC o (SPEC `k:num`) o MATCH_MP lemma_sub_inj_contour) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] 
THEN REPEAT STRIP_TAC THEN MP_TAC(ARITH_RULE `k:num <= m:num /\ i < k ==> i < m`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
THEN UNDISCH_THEN `!(i:num). i < (m:num) ==> (?(j:num). j < (n:num) /\ (q:num->A) i = (p:num->A) j /\ q (SUC i) = p (SUC j))` (MP_TAC o SPEC `i:num`) 
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `j:num` MP_TAC) THEN STRIP_TAC THEN 
EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN UNDISCH_THEN `j:num < n:num` MP_TAC  THEN ARITH_TAC; ALL_TAC]
THEN REPLICATE_TAC 2 (POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC "F3") 
THEN DISCH_THEN (LABEL_TAC "F4") 
THEN EXISTS_TAC `(\l:num. if l = SUC (m:num) then (p:num->A) (SUC (n:num)) else (q:num->A) l)` 
THEN EXISTS_TAC `SUC (m:num)` 
THEN ABBREV_TAC `t = (\l:num. if l = SUC (m:num) then (p:num->A) (SUC (n:num)) else (q:num->A) l)` 
THEN SUBGOAL_THEN `!i:num. i <= m:num ==> (q:num->A) i= (t:num->A) i` (LABEL_TAC "B1")
   THENL[REPEAT STRIP_TAC THEN MP_TAC(ARITH_RULE `i:num <= m:num ==> ~(i = SUC m)`) THEN ASM_REWRITE_TAC[] 
   THEN EXPAND_TAC "t" THEN DISCH_THEN (fun th -> (REWRITE_TAC[th;COND_ELIM_THM])); ALL_TAC]
THEN SUBGOAL_THEN `(t:num->A) (SUC (m:num)) = (p:num->A) (SUC (n:num))` (LABEL_TAC "B2") 
THENL[EXPAND_TAC "t" THEN REWRITE_TAC[]; ALL_TAC]
THEN USE_THEN "B1" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[ARITH_RULE `0 <= m`] 
THEN DISCH_THEN (ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THENL[
UNDISCH_THEN `is_inj_contour (H:(A)hypermap) (q:num->A) (m:num)` (fun th1 -> USE_THEN "B1" (fun th2 -> ASSUME_TAC(MATCH_MP identify_inj_contour (CONJ th1 (th2))))) 
   THEN ASM_REWRITE_TAC[is_inj_contour] THEN USE_THEN "B1" (MP_TAC o SPEC `m:num`) 
   THEN REWRITE_TAC[ARITH_RULE `(m:num) <= m`] THEN DISCH_THEN (ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC[] 
   THEN REPEAT STRIP_TAC THEN REMOVE_THEN "F4" MP_TAC 
   THEN REWRITE_TAC[CONTRAPOS_THM] THEN EXISTS_TAC `i: num` THEN ASM_REWRITE_TAC[] 
   THEN REMOVE_THEN "B1" (MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[]; ALL_TAC]
THEN REPEAT STRIP_TAC THEN ASM_CASES_TAC `i:num = m:num`
THENL[EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[ARITH_RULE `n < SUC n`] 
   THEN USE_THEN "B1" (MP_TAC o SPEC `m:num`) 
   THEN REWRITE_TAC[ARITH_RULE `(m:num) <= m`] 
   THEN DISCH_THEN (ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC[]; ALL_TAC]
THEN MP_TAC(ARITH_RULE `i:num < SUC (m:num) /\ ~(i = m) ==> i < m`) THEN ASM_REWRITE_TAC[] 
THEN STRIP_TAC THEN REMOVE_THEN "F3" (MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] 
THEN DISCH_THEN (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `j:num` 
THEN MP_TAC(ARITH_RULE `j:num < n:num ==> j < SUC n`) THEN ASM_REWRITE_TAC[] 
THEN STRIP_TAC THEN MP_TAC(ARITH_RULE `i:num < m:num ==> i <= m`) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN USE_THEN "B1" (MP_TAC o SPEC `i:num`) 
THEN POP_ASSUM(fun th-> REWRITE_TAC[th]) THEN DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) 
THEN MP_TAC(ARITH_RULE `i:num < m:num ==> SUC i <= m`) THEN ASM_REWRITE_TAC[] 
THEN  STRIP_TAC THEN USE_THEN "B1" (MP_TAC o SPEC `SUC (i:num)`) 
THEN POP_ASSUM(fun th-> REWRITE_TAC[th]) 
THEN DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN ASM_REWRITE_TAC[] ) ;;


(* The theory of walkup in detail here with many trial facts *)

let isolated_dart = new_definition `isolated_dart (H:(A)hypermap) (x:A) <=> (edge_map H x = x /\ node_map H x = x /\ face_map H x = x)`;;

let is_edge_degenerate = new_definition `is_edge_degenerate (H:(A)hypermap) (x:A) 
   <=>  (edge_map H x = x) /\ ~(node_map H x = x) /\ ~(face_map H x = x)`;;

let is_node_degenerate = new_definition `is_node_degenerate (H:(A)hypermap) (x:A) 
   <=>  ~(edge_map H x = x) /\ (node_map H x = x) /\ ~(face_map H x = x)`;;

let is_face_degenerate = new_definition `is_face_degenerate (H:(A)hypermap) (x:A) 
   <=>  ~(edge_map H x = x) /\ ~(node_map H x = x) /\ (face_map H x = x)`;;


let degenerate_lemma = prove(`!(H:(A)hypermap) (x:A). dart_degenerate H x 
   <=> isolated_dart H x \/ is_edge_degenerate H x \/  is_node_degenerate H x \/  is_face_degenerate H x`, 
REPEAT GEN_TAC THEN STRIP_ASSUME_TAC (SPEC `H:(A)hypermap` hypermap_lemma) 
THEN REWRITE_TAC[dart_degenerate;isolated_dart; is_edge_degenerate; is_node_degenerate; is_face_degenerate] 
THEN POP_ASSUM (LABEL_TAC "F1") THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` 
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` 
THEN MP_TAC(SPECL[`D:A->bool`; `e:A->A`;`n:A->A`;`f:A->A`] cyclic_maps) THEN ASM_REWRITE_TAC[] 
THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F2") (LABEL_TAC "F3")) THEN EQ_TAC
THENL[STRIP_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `(n:A->A) (x:A) = x` 
   THENL[ASM_REWRITE_TAC[] THEN USE_THEN "F3" (fun th -> (MP_TAC(AP_THM th `x:A`))) 
   THEN ASM_REWRITE_TAC[o_THM;I_THM]; ASM_REWRITE_TAC[] THEN STRIP_TAC 
   THEN USE_THEN "F2" (fun th -> (MP_TAC(AP_THM th `x:A`))) 
   THEN ASM_REWRITE_TAC[o_THM;I_THM]] ; ASM_REWRITE_TAC[] 
   THEN ASM_CASES_TAC `(e:A->A) (x:A) = x` 
   THENL[ ASM_REWRITE_TAC[] THEN USE_THEN "F3" (fun th -> (MP_TAC(AP_THM th `x:A`))) 
   THEN ASM_REWRITE_TAC[o_THM;I_THM]; ASM_REWRITE_TAC[] THEN STRIP_TAC 
   THEN USE_THEN "F1" (fun th -> (MP_TAC(AP_THM th `x:A`))) THEN ASM_REWRITE_TAC[o_THM;I_THM]]; 
   ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `(e:A->A) (x:A) = x` 
   THENL[ASM_REWRITE_TAC[] THEN USE_THEN "F2" (fun th -> (MP_TAC(AP_THM th `x:A`))) 
   THEN ASM_REWRITE_TAC[o_THM;I_THM]; ASM_REWRITE_TAC[] THEN STRIP_TAC THEN 
   USE_THEN "F1" (fun th -> (MP_TAC(AP_THM th `x:A`))) THEN ASM_REWRITE_TAC[o_THM;I_THM]]]; 
MESON_TAC[]]);;

(* Some trivial lemmas on PAIRS *)

let label_4Gs_TAC th = CONJUNCTS_THEN2 (LABEL_TAC "G1") (CONJUNCTS_THEN2(LABEL_TAC "G2") (CONJUNCTS_THEN2 (LABEL_TAC "G3") (LABEL_TAC "G4"))) th;;


let label_hypermap_TAC th = CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2(LABEL_TAC "H2") (CONJUNCTS_THEN2 (LABEL_TAC "H3") (CONJUNCTS_THEN2 (LABEL_TAC "H4") (LABEL_TAC "H5")) )) (SPEC th hypermap_lemma);;

let label_hypermapG_TAC th = CONJUNCTS_THEN2 (LABEL_TAC "G1") (CONJUNCTS_THEN2(LABEL_TAC "G2") (CONJUNCTS_THEN2 (LABEL_TAC "G3") (CONJUNCTS_THEN2 (LABEL_TAC "G4") (LABEL_TAC "G5")) )) (SPEC th hypermap_lemma);;

let label_strip3A_TAC th = CONJUNCTS_THEN2 (LABEL_TAC "A1") (CONJUNCTS_THEN2(LABEL_TAC "A2")(LABEL_TAC "A3")) th;;

let lemma_pair_representation = prove(`!(S:((A->bool)#(A->A)#(A->A)#(A->A))). S = (FST S, FST (SND S), FST(SND(SND S)), SND(SND(SND S)))`,REWRITE_TAC[PAIR_SURJECTIVE]);;

let lemma_pair_eq = prove(`!(S:((A->bool)#(A->A)#(A->A)#(A->A))) (U:((A->bool)#(A->A)#(A->A)#(A->A))). ((FST S = FST U) /\ (FST (SND S) = FST (SND U)) /\ (FST(SND(SND S)) = FST(SND(SND U))) /\ (SND(SND(SND S))) = SND(SND(SND U))) ==>(S = U)`, ASM_MESON_TAC[lemma_pair_representation]);;


let lemma_hypermap_eq = prove(`!(H:(A)hypermap) (H':(A)hypermap). H = H' <=> dart H = dart H' /\ edge_map H = edge_map H' /\ node_map H = node_map H' /\ face_map H = face_map H'`, 
REPEAT GEN_TAC THEN  EQ_TAC 
THENL[ASM_MESON_TAC[hypermap_tybij; dart; edge_map; node_map; face_map]; ALL_TAC] 
THEN ASM_REWRITE_TAC[hypermap_tybij; dart; edge_map; node_map; face_map] 
THEN REPEAT STRIP_TAC 
THEN SUBGOAL_THEN `tuple_hypermap (H:(A)hypermap) = tuple_hypermap (H':(A)hypermap)` ASSUME_TAC 
THENL[ASM_MESON_TAC[lemma_pair_eq]; ASM_MESON_TAC[CONJUNCT1 hypermap_tybij]]);;


let lemma_hypermap_representation = prove(`!(D:A->bool) (e:A->A) (n:A->A) (f:A->A). (FINITE D /\ e permutes D /\ n permutes D /\ f permutes D /\ (e o n o f = I)) ==> ?(H:(A)hypermap). (H = hypermap (D, e, n, f)) /\ dart H = D /\ edge_map H = e /\ node_map H = n /\ face_map H = f `, 
REPEAT STRIP_TAC THEN EXISTS_TAC `hypermap (D:A->bool, e:A->A, n:A->A, f:A->A)` 
THEN REWRITE_TAC[] THEN REWRITE_TAC[dart; edge_map; node_map; face_map] 
THEN MP_TAC (SPEC `(D:A->bool, e:A->A, n:A->A, f:A->A)` (CONJUNCT2 hypermap_tybij)) 
THEN ASM_REWRITE_TAC[] THEN  STRIP_TAC THEN ASM_REWRITE_TAC[]);;


let shift = new_definition `shift (H:(A)hypermap) =  hypermap(dart H, node_map H, face_map H, edge_map H)`;;

let shift_lemma = prove(`!(H:(A)hypermap). dart H = dart (shift H) /\ edge_map H = face_map (shift H) /\ node_map H = edge_map (shift H) /\ face_map H = node_map (shift H)`, 
GEN_TAC THEN REWRITE_TAC [shift] 
THEN STRIP_ASSUME_TAC(SPEC `H:(A)hypermap` hypermap_lemma) 
THEN MP_TAC(SPECL[`dart (H:(A)hypermap)`; `edge_map (H:(A)hypermap)`; `node_map (H:(A)hypermap)`; `face_map (H:(A)hypermap)`] cyclic_maps) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
THEN MP_TAC (SPECL[`dart (H:(A)hypermap)`; `node_map (H:(A)hypermap)`; `face_map (H:(A)hypermap)`; `edge_map (H:(A)hypermap)`]  lemma_hypermap_representation) 
THEN ASM_REWRITE_TAC[] 
THEN ABBREV_TAC `G = hypermap(dart (H:(A)hypermap), node_map H, face_map H, edge_map H)` 
THEN STRIP_TAC THEN UNDISCH_THEN `H':(A)hypermap = G:(A)hypermap` SUBST_ALL_TAC 
THEN ASM_SIMP_TAC[]);;


let double_shift_lemma = prove( `!(H:(A)hypermap). dart H = dart (shift(shift H)) /\ edge_map H = node_map (shift(shift H)) /\ node_map H = face_map (shift(shift H)) /\ face_map H = edge_map (shift (shift H))`, 
GEN_TAC THEN STRIP_ASSUME_TAC(SPEC `shift(H:(A)hypermap)` shift_lemma) 
THEN STRIP_ASSUME_TAC(SPEC `H:(A)hypermap` shift_lemma) THEN ASM_REWRITE_TAC[]);;

let hypermap_cyclic = prove(`!(H:(A)hypermap). (node_map H) o (face_map H) o (edge_map H) = I /\ (face_map H) o (edge_map H) o (node_map H) = I`, 
GEN_TAC THEN label_hypermap_TAC `H:(A)hypermap`
THEN MP_TAC(SPECL[`dart (H:(A)hypermap)`; `edge_map (H:(A)hypermap)`; `node_map (H:(A)hypermap)`;`face_map (H:(A)hypermap)`] cyclic_maps) 
THEN ASM_REWRITE_TAC[]);;

let label_cyclic_maps_TAC th = CONJUNCTS_THEN2 (LABEL_TAC "H6") (LABEL_TAC "H7") (SPEC th hypermap_cyclic);;

let inverse_hypermap_maps = prove(`!(H:(A)hypermap). inverse(edge_map H) = (node_map H) o (face_map H) /\ inverse(node_map H) = (face_map H) o (edge_map H) /\ inverse(face_map H) = (edge_map H) o (node_map H)`,
GEN_TAC THEN label_hypermap_TAC `(H:(A)hypermap)` 
THEN label_cyclic_maps_TAC `(H:(A)hypermap)` THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` 
THEN MP_TAC (SPECL[`D:A->bool`;`e:A->A`; `(n:A->A) o (f:A->A)`; `I:A->A`] LEFT_INVERSE_EQUATION) 
THEN ASM_REWRITE_TAC[I_O_ID] THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th]) 
THEN MP_TAC (SPECL[`D:A->bool`;`n:A->A`; `(f:A->A) o (e:A->A)`; `I:A->A`] LEFT_INVERSE_EQUATION) 
THEN ASM_REWRITE_TAC[I_O_ID] THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th]) 
THEN MP_TAC (SPECL[`D:A->bool`;`f:A->A`; `(e:A->A) o (n:A->A)`; `I:A->A`] LEFT_INVERSE_EQUATION) 
THEN ASM_REWRITE_TAC[I_O_ID] THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th]));;


let inverse2_hypermap_maps = prove(`!(H:(A)hypermap). edge_map H = inverse (face_map H) o inverse (node_map H) /\ node_map H = inverse (edge_map H) o inverse (face_map H) /\ face_map H = inverse (node_map H) o inverse(edge_map H)`, 
GEN_TAC THEN label_hypermap_TAC `(H:(A)hypermap)` 
THEN label_strip3A_TAC (SPEC `H:(A)hypermap` inverse_hypermap_maps) 
THEN label_cyclic_maps_TAC `(H:(A)hypermap)` 
THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` 
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` 
THEN REMOVE_THEN "A1" ((LABEL_TAC "B1") o SYM) 
THEN MP_TAC (SPECL[`D:A->bool`;`n:A->A`; `(f:A->A)`; `inverse(e:A->A)`] LEFT_INVERSE_EQUATION) 
THEN ASM_REWRITE_TAC[I_O_ID] THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th]) 
THEN REMOVE_THEN "A2" ((LABEL_TAC "B2") o SYM) 
THEN MP_TAC (SPECL[`D:A->bool`;`f:A->A`; `(e:A->A)`; `inverse(n:A->A)`] LEFT_INVERSE_EQUATION) 
THEN ASM_REWRITE_TAC[I_O_ID] THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th]) THEN ASM_REWRITE_TAC[o_ASSOC] 
THEN REMOVE_THEN "H2" (MP_TAC o CONJUNCT2 o  MATCH_MP PERMUTES_INVERSES_o) THEN SIMP_TAC[I_O_ID]);;


(* the definition of walkups *)

let edge_walkup = new_definition `edge_walkup (H:(A)hypermap) (x:A) = hypermap((dart H) DELETE x,inverse(swap(x, face_map H x) o face_map H) o inverse(swap(x, node_map H x) o node_map H) , swap(x, node_map H x) o node_map H, swap(x, face_map H x) o face_map H)`;;


let node_walkup = new_definition `node_walkup (H:(A)hypermap) (x:A) = shift(shift(edge_walkup (shift H) x))`;;

let face_walkup = new_definition `face_walkup (H:(A)hypermap) (x:A) = shift(edge_walkup (shift (shift H)) x)`;;


let walkup_permutes = prove(`!(D:A->bool) (p:A->A) (x:A). FINITE D /\p permutes D ==> (swap(x, p x) o p) permutes (D DELETE x)`,
REPEAT STRIP_TAC THEN UNDISCH_THEN `FINITE (D:A->bool)` (fun th -> ASSUME_TAC th THEN MP_TAC(SPEC `x:A` (MATCH_MP FINITE_DELETE_IMP th))) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
THEN ASM_CASES_TAC `x:A IN (D:A->bool)` 
THENL[MP_TAC (SET_RULE `(x:A) IN (D:A->bool) ==> (D = x INSERT (D DELETE x))`) 
   THEN ASM_REWRITE_TAC[] THEN ABBREV_TAC `S = (D:A->bool) DELETE (x:A)` 
   THEN DISCH_THEN SUBST_ALL_TAC THEN MP_TAC(ISPECL[`p:A->A`;`x:A`;`(S:A->bool)`] PERMUTES_INSERT_LEMMA) 
   THEN ASM_REWRITE_TAC[]; ALL_TAC] 
THEN MP_TAC (SET_RULE `~((x:A) IN (D:A->bool)) ==> D DELETE x = D`) 
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC 
THEN UNDISCH_THEN `p:A->A permutes (D:A->bool)` (fun th -> ASSUME_TAC th THEN MP_TAC th) 
THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV) [permutes] 
THEN DISCH_THEN (MP_TAC o SPEC `x:A` o CONJUNCT1) THEN ASM_REWRITE_TAC[] 
THEN DISCH_THEN (fun th -> ASM_REWRITE_TAC[th; SWAP_REFL; I_O_ID]));;


let PERMUTES_COMPOSITION = prove
 (`!p q s. p permutes s /\ q permutes s ==> (q o p) permutes s`,
  REWRITE_TAC[permutes; o_THM] THEN MESON_TAC[]);;

let lemma_4functions = prove(`!f g h r. f o g o h o r = f o (g o h) o r `, REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM o_ASSOC]);;


let lemma_edge_walkup = prove(`!(H:(A)hypermap) (x:A). dart (edge_walkup H x) = dart H DELETE x /\ edge_map (edge_walkup H x) =  inverse(swap(x, face_map H x) o face_map H) o inverse(swap(x, node_map H x) o node_map H) /\ node_map (edge_walkup H x) =  swap(x, node_map H x) o node_map H /\ face_map (edge_walkup H x) =  swap(x, face_map H x) o face_map H`, 
REPEAT GEN_TAC THEN REWRITE_TAC[edge_walkup] 
THEN label_hypermap_TAC `H:(A)hypermap` 
THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` 
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` 
THEN ABBREV_TAC `n' = swap(x:A, (n:A->A) x) o n` 
THEN ABBREV_TAC `f' = swap(x:A, (f:A->A) x) o f` 
THEN ABBREV_TAC `D' = (D:A->bool) DELETE (x:A)` 
THEN MP_TAC(ISPECL[`D:A->bool`;`n:A->A`; `x:A`] walkup_permutes) 
THEN ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL[`D:A->bool`;`f:A->A`; `x:A`] walkup_permutes) 
THEN ASM_REWRITE_TAC[] 
THEN REPLICATE_TAC 2 STRIP_TAC 
THEN ABBREV_TAC `e' = inverse (f':A->A) o inverse (n':A->A)` 
THEN SUBGOAL_THEN `(e':A->A) permutes (D':A->bool)` MP_TAC 
THENL[UNDISCH_THEN `(n':A->A) permutes (D':A->bool)` (MP_TAC o MATCH_MP PERMUTES_INVERSE) 
   THEN UNDISCH_THEN `(f':A->A) permutes (D':A->bool)` (MP_TAC o MATCH_MP PERMUTES_INVERSE) 
   THEN REPEAT STRIP_TAC THEN MP_TAC (ISPECL[`inverse(n':A->A)`; `inverse(f':A->A)`; `D':A->bool`] 
   PERMUTES_COMPOSITION) THEN ASM_REWRITE_TAC[]; ALL_TAC] 
THEN STRIP_TAC THEN SUBGOAL_THEN `(e':A->A) o (n':A->A) o (f':A->A) = I` ASSUME_TAC 
THENL[MP_TAC ((ISPECL[`n':A->A`; `D':A->bool`] PERMUTES_INVERSES_o)) 
   THEN ASM_REWRITE_TAC[] THEN MP_TAC ((ISPECL[`f':A->A`; `D':A->bool`] PERMUTES_INVERSES_o)) 
   THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN EXPAND_TAC "e'" 
   THEN REWRITE_TAC[GSYM o_ASSOC] THEN REWRITE_TAC[lemma_4functions] 
   THEN POP_ASSUM (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[I_O_ID]; ALL_TAC] 
THEN MP_TAC (SPECL[`D':A->bool`; `e':A->A`; `n':A->A`; `f':A->A`]  lemma_hypermap_representation) 
THEN MP_TAC (ISPECL[`D:A->bool`; `x:A`] FINITE_DELETE_IMP) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] 
THEN ABBREV_TAC `G = hypermap(D':A->bool, e':A->A, n':A->A, f':A->A)` 
THEN STRIP_TAC THEN UNDISCH_THEN `H':(A)hypermap = G:(A)hypermap` SUBST_ALL_TAC 
THEN ASM_SIMP_TAC[]);;


let inverse_function = prove( `!s:A->bool p:A->A x:A y:A. p permutes s /\ p x = y ==> x = (inverse p) y`,
REPEAT STRIP_TAC THEN POP_ASSUM (MP_TAC o AP_TERM `inverse (p:A->A)`) THEN STRIP_TAC 
THEN MP_TAC (ISPECL[`inverse(p:A->A)`; `p:A->A`; `x:A`] o_THM) 
THEN POP_ASSUM (SUBST1_TAC o SYM) THEN POP_ASSUM (ASSUME_TAC o CONJUNCT2 o MATCH_MP PERMUTES_INVERSES_o) 
THEN POP_ASSUM SUBST1_TAC THEN REWRITE_TAC[I_THM]);;


let node_map_walkup = prove(`!(H:(A)hypermap) (x:A) (y:A). node_map (edge_walkup H x) x = x /\ node_map (edge_walkup H x) (inverse (node_map H) x) = node_map H x /\ (~(y = x) /\ ~(y = inverse (node_map H) x) ==> node_map (edge_walkup H x) y = node_map H y)`,
REPEAT GEN_TAC THEN LABEL_TAC "F1" (CONJUNCT1 (CONJUNCT2(CONJUNCT2(SPEC `H:(A)hypermap` hypermap_lemma)))) 
THEN REWRITE_TAC[CONJUNCT1 (CONJUNCT2(CONJUNCT2(SPECL[`H:(A)hypermap`; `x:A`] lemma_edge_walkup)))] 
THEN REWRITE_TAC[o_THM] THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` THEN STRIP_TAC 
THENL[ABBREV_TAC `z = (n:A->A) (x:A)` THEN REWRITE_TAC[swap] THEN ASM_CASES_TAC `z:A = x:A` THENL[ASM_MESON_TAC[]; ASM_MESON_TAC[]]; ALL_TAC]
THEN STRIP_TAC 
THENL[ SUBGOAL_THEN `(n:A->A)(inverse(n) (x:A)) = x` (fun th-> REWRITE_TAC[th]) 
   THENL[GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM o_THM] 
      THEN REMOVE_THEN "F1" (ASSUME_TAC o CONJUNCT1 o MATCH_MP PERMUTES_INVERSES_o) 
      THEN POP_ASSUM (fun th -> REWRITE_TAC[th; I_THM]); MESON_TAC[swap]];ALL_TAC]
THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN SUBGOAL_THEN `~((n:A->A) (y:A) = n (x:A))` MP_TAC
THENL[USE_THEN "F1"(MP_TAC o SPECL[`y:A`;`x:A`] o MATCH_MP PERMUTES_INJECTIVE) THEN ASM_REWRITE_TAC[]; ALL_TAC]
THEN STRIP_TAC THEN SUBGOAL_THEN `~((n:A->A) (y:A) = (x:A))` ASSUME_TAC
THENL[STRIP_TAC THEN POP_ASSUM(fun th1 -> (USE_THEN "F1"(fun th2 -> MP_TAC(MATCH_MP inverse_function (CONJ th2 th1))))) THEN ASM_REWRITE_TAC[]; ALL_TAC]
THEN ASM_MESON_TAC[swap]);;


let face_map_walkup = prove(`!(H:(A)hypermap) (x:A) (y:A). face_map (edge_walkup H x) x = x /\ face_map (edge_walkup H x) (inverse (face_map H) x) = face_map H x /\ (~(y = x) /\ ~(y = inverse (face_map H) x) ==> face_map (edge_walkup H x) y = face_map H y)`,
REPEAT GEN_TAC THEN LABEL_TAC "F1" (CONJUNCT1 (CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC `H:(A)hypermap` hypermap_lemma))))) 
THEN REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2(SPECL[`H:(A)hypermap`; `x:A`] lemma_edge_walkup)))] 
THEN REWRITE_TAC[o_THM] THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` THEN STRIP_TAC 
THENL[ABBREV_TAC `z = (n:A->A) (x:A)` THEN REWRITE_TAC[swap] THEN ASM_CASES_TAC `z:A = x:A` THENL[ASM_MESON_TAC[]; ASM_MESON_TAC[]]; ALL_TAC]
THEN STRIP_TAC 
THENL[ SUBGOAL_THEN `(f:A->A)(inverse(f) (x:A)) = x` (fun th-> REWRITE_TAC[th]) 
   THENL[GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM o_THM] 
      THEN REMOVE_THEN "F1" (ASSUME_TAC o CONJUNCT1 o MATCH_MP PERMUTES_INVERSES_o) 
      THEN POP_ASSUM (fun th -> REWRITE_TAC[th; I_THM]); MESON_TAC[swap]];ALL_TAC]
THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN SUBGOAL_THEN `~((f:A->A) (y:A) = f (x:A))` MP_TAC
THENL[USE_THEN "F1"(MP_TAC o SPECL[`y:A`;`x:A`] o MATCH_MP PERMUTES_INJECTIVE) THEN ASM_REWRITE_TAC[]; ALL_TAC]
THEN STRIP_TAC THEN SUBGOAL_THEN `~((f:A->A) (y:A) = (x:A))` ASSUME_TAC
THENL[STRIP_TAC THEN POP_ASSUM(fun th1 -> (USE_THEN "F1"(fun th2 -> MP_TAC(MATCH_MP inverse_function (CONJ th2 th1))))) THEN ASM_REWRITE_TAC[]; ALL_TAC]
THEN ASM_MESON_TAC[swap]);;

let lemma_edge_degenarate =  prove(`!(H:(A)hypermap) (x:A). (edge_map H x = x) <=> (face_map H x = (inverse (node_map H)) x)`,
REPEAT STRIP_TAC THEN label_hypermap_TAC `H:(A)hypermap` 
THEN MP_TAC(AP_THM (SYM (CONJUNCT1(CONJUNCT2(SPEC `H:(A)hypermap` inverse_hypermap_maps)))) `x:A`)
THEN ABBREV_TAC `D = dart (H:(A)hypermap)`
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` 
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
THEN REWRITE_TAC[o_THM] THEN DISCH_THEN (LABEL_TAC "F1") THEN EQ_TAC
THENL[DISCH_TAC THEN REMOVE_THEN "F1" MP_TAC THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC]
THEN DISCH_THEN (fun th1 -> (USE_THEN "F1" (fun th2 -> (MP_TAC (MATCH_MP EQ_TRANS (CONJ th2 (SYM th1)) )))))
THEN DISCH_TAC THEN USE_THEN "H4" (MP_TAC o ISPECL[`(e:A->A) (x:A)`; `x:A`] o MATCH_MP PERMUTES_INJECTIVE)
THEN POP_ASSUM (fun th -> REWRITE_TAC[th]));;

let lemma_node_degenarate =  prove(`!(H:(A)hypermap) (x:A). (node_map H x = x) <=> (edge_map H x = (inverse (face_map H)) x)`,
REPEAT STRIP_TAC THEN label_hypermap_TAC `H:(A)hypermap` 
THEN MP_TAC(AP_THM (SYM (CONJUNCT2(CONJUNCT2(SPEC `H:(A)hypermap` inverse_hypermap_maps)))) `x:A`)
THEN ABBREV_TAC `D = dart (H:(A)hypermap)`
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` 
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
THEN REWRITE_TAC[o_THM] THEN DISCH_THEN (LABEL_TAC "F1") THEN EQ_TAC
THENL[DISCH_TAC THEN REMOVE_THEN "F1" MP_TAC THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC]
THEN DISCH_THEN (fun th1 -> (USE_THEN "F1" (fun th2 -> (MP_TAC (MATCH_MP EQ_TRANS (CONJ th2 (SYM th1)) )))))
THEN DISCH_TAC THEN USE_THEN "H2" (MP_TAC o ISPECL[`(n:A->A) (x:A)`; `x:A`] o MATCH_MP PERMUTES_INJECTIVE)
THEN POP_ASSUM (fun th -> REWRITE_TAC[th]));;

let lemma_face_degenarate =  prove(`!(H:(A)hypermap) (x:A). (face_map H x = x) <=> (node_map H x = (inverse (edge_map H)) x)`,
REPEAT STRIP_TAC THEN label_hypermap_TAC `H:(A)hypermap` 
THEN MP_TAC(AP_THM (SYM (CONJUNCT1(SPEC `H:(A)hypermap` inverse_hypermap_maps))) `x:A`)
THEN ABBREV_TAC `D = dart (H:(A)hypermap)`
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` 
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
THEN REWRITE_TAC[o_THM] THEN DISCH_THEN (LABEL_TAC "F1") THEN EQ_TAC
THENL[DISCH_TAC THEN REMOVE_THEN "F1" MP_TAC THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC]
THEN DISCH_THEN (fun th1 -> (USE_THEN "F1" (fun th2 -> (MP_TAC (MATCH_MP EQ_TRANS (CONJ th2 (SYM th1)) )))))
THEN DISCH_TAC THEN USE_THEN "H3" (MP_TAC o ISPECL[`(f:A->A) (x:A)`; `x:A`] o MATCH_MP PERMUTES_INJECTIVE)
THEN POP_ASSUM (fun th -> REWRITE_TAC[th]));;


let fixed_point_lemma = prove(`!(D:A->bool) (p:A->A). p permutes D ==> (!(x:A). p x = x <=> inverse p x = x)`,
REPEAT STRIP_TAC THEN EQ_TAC
THENL[POP_ASSUM (fun th1 -> (DISCH_THEN(fun th2 -> (MP_TAC(MATCH_MP inverse_function (CONJ th1 th2))))))
   THEN DISCH_THEN (fun th-> REWRITE_TAC[SYM th]); ALL_TAC]
THEN DISCH_THEN (MP_TAC o AP_TERM `p:A->A`)
THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_THM]
THEN (POP_ASSUM (ASSUME_TAC o CONJUNCT1 o MATCH_MP PERMUTES_INVERSES_o))
THEN ASM_REWRITE_TAC[I_THM] THEN DISCH_THEN (fun th-> REWRITE_TAC[SYM th]));;

let non_fixed_point_lemma = prove(`!(s:A->bool) (p:A->A). p permutes s ==> (!(x:A). ~(p x = x) <=> ~(inverse p x = x))`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[TAUT `(~p <=> ~q) <=> (p <=> q)`] 
   THEN ASM_MESON_TAC[fixed_point_lemma]);;

let aux_permutes_conversion = prove(
`!(D:A->bool) (p:A->A) (q:A->A) (x:A) (y:A). (p permutes D) /\ (q permutes D) ==> ((inverse p)((inverse q) x) = y <=> q ( p y) = x)`,
REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F1") (LABEL_TAC "F2")) 
THEN USE_THEN "F1" (MP_TAC o ISPECL[`y:A`; `inverse(q:A->A) (x:A)`] o MATCH_MP PERMUTES_INVERSE_EQ)
THEN DISCH_THEN (fun th -> REWRITE_TAC[th]) 
THEN USE_THEN "F2" (MP_TAC o ISPECL[`(p:A->A) (y:A)`; `(x:A)`] o MATCH_MP PERMUTES_INVERSE_EQ)
THEN MESON_TAC[]);;


let  edge_map_walkup   = prove(`!(H:(A)hypermap) (x:A) (y:A). edge_map (edge_walkup H x) x = x /\ ( ~(node_map H x = x) /\ ~(edge_map H x = x) ==> edge_map (edge_walkup H x) (node_map H x) = edge_map H x) /\ (~(inverse (face_map H)  x = x) /\ ~(inverse(edge_map H) x = x)  ==> edge_map (edge_walkup H x) (inverse(edge_map H) x) = inverse(face_map H) x) /\ (~(y = x) /\ ~(y = (inverse (edge_map H)) x) /\ ~(y = (node_map H) x) ==> (edge_map (edge_walkup H x)) y = edge_map H y)`,
REPEAT GEN_TAC THEN label_hypermap_TAC `H:(A)hypermap` THEN label_hypermapG_TAC `(edge_walkup (H:(A)hypermap) (x:A))`
THEN LABEL_TAC "A1" (SPECL[`H:(A)hypermap`;`x:A`] node_map_walkup) THEN LABEL_TAC "A2" (SPECL[`H:(A)hypermap`;`x:A`] face_map_walkup)
THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` 
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
THEN ABBREV_TAC `G = edge_walkup (H:(A)hypermap) (x:A)` 
THEN ABBREV_TAC `D' = dart (G:(A)hypermap)`
THEN ABBREV_TAC `e' = edge_map (G:(A)hypermap)` 
THEN ABBREV_TAC `n' = node_map (G:(A)hypermap)` 
THEN ABBREV_TAC `f' = face_map (G:(A)hypermap)`
THEN MP_TAC(CONJUNCT1 (SPEC `G:(A)hypermap` inverse2_hypermap_maps))
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[o_THM] 
THEN STRIP_TAC
THENL[REMOVE_THEN "A1" (MP_TAC o CONJUNCT1 o SPEC `y:A`)
   THEN DISCH_THEN (fun th -> (USE_THEN "G3" (fun th1 ->MP_TAC (MATCH_MP inverse_function (CONJ th1 th)))))
   THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REMOVE_THEN "A2" (MP_TAC o CONJUNCT1 o SPEC `y:A`)
   THEN DISCH_THEN (fun th -> (USE_THEN "G4" (fun th1 ->MP_TAC (MATCH_MP inverse_function (CONJ th1 th)))))
   THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th]); ALL_TAC]
THEN STRIP_TAC 
THENL[MP_TAC (SPECL[`D':A->bool`; `f':A->A`; `n':A->A`; `(n:A->A) (x:A)`; `(e:A->A) (x:A)`] aux_permutes_conversion)
   THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (fun th-> REWRITE_TAC[th])
   THEN  STRIP_TAC 
   THEN SUBGOAL_THEN `~((e:A->A) (x:A) = inverse (f:A->A) x)` ASSUME_TAC
     THENL[UNDISCH_THEN `~((n:A->A) (x:A) = x)` (MP_TAC o GSYM)
     THEN REWRITE_TAC[CONTRAPOS_THM]
     THEN USE_THEN "H2" (MP_TAC o SYM o  SPECL[`x:A`; `inverse(f:A->A) x:A`] o  MATCH_MP PERMUTES_INVERSE_EQ)
     THEN DISCH_THEN(fun th -> REWRITE_TAC[th])
     THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_THM]
     THEN MP_TAC (CONJUNCT1(CONJUNCT2(SPECL[`H:(A)hypermap`] inverse2_hypermap_maps)))
     THEN ASM_REWRITE_TAC[]
     THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th])
     THEN DISCH_THEN (fun th -> MP_TAC (SYM th)) THEN SIMP_TAC[]; ALL_TAC]
   THEN REMOVE_THEN "A2" (MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `(e:A->A) (x:A)`)
   THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (fun th -> REWRITE_TAC[th])
   THEN MP_TAC(CONJUNCT1(CONJUNCT2(SPEC `H:(A)hypermap` inverse_hypermap_maps)))
   THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MP_TAC(SYM(AP_THM th `x:A`)))
   THEN REWRITE_TAC[o_THM] THEN DISCH_THEN (fun th -> REWRITE_TAC[th])
   THEN REMOVE_THEN "A1" (MP_TAC o CONJUNCT1 o CONJUNCT2 o SPEC `x:A`) THEN REWRITE_TAC[]; ALL_TAC]
THEN  STRIP_TAC
THENL[STRIP_TAC THEN MP_TAC (SPECL[`D':A->bool`; `f':A->A`; `n':A->A`; `inverse (e:A->A) (x:A)`; `inverse(f:A->A) (x:A)`] aux_permutes_conversion)
   THEN ASM_REWRITE_TAC[]
   THEN DISCH_THEN (fun th-> REWRITE_TAC[th])
   THEN SUBGOAL_THEN `~((f:A->A) (x:A) = inverse (n:A->A) x)` ASSUME_TAC
   THENL[POP_ASSUM MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM]
     THEN USE_THEN "H4" (MP_TAC o SYM o  SPECL[`x:A`; `inverse(n:A->A) x:A`] o  MATCH_MP PERMUTES_INVERSE_EQ)
     THEN DISCH_THEN(fun th -> REWRITE_TAC[th])
     THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_THM]
     THEN MP_TAC (CONJUNCT1(SPECL[`H:(A)hypermap`] inverse2_hypermap_maps))
     THEN ASM_REWRITE_TAC[]
     THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th])
     THEN STRIP_TAC THEN USE_THEN "H2" (MP_TAC o SPEC `x:A` o MATCH_MP fixed_point_lemma)
     THEN POP_ASSUM (fun th -> REWRITE_TAC[th]); ALL_TAC]
   THEN SUBGOAL_THEN `~((f:A->A) (x:A) = x)` ASSUME_TAC
   THENL[UNDISCH_TAC `~(inverse (f:A->A) (x:A) = x)`
     THEN REWRITE_TAC[CONTRAPOS_THM]
     THEN STRIP_TAC THEN USE_THEN "H4" (MP_TAC o SPEC `x:A` o MATCH_MP fixed_point_lemma)
     THEN POP_ASSUM (fun th -> REWRITE_TAC[th]); ALL_TAC]
   THEN REMOVE_THEN "A1" (MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `(f:A->A) (x:A)`)
   THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (fun th -> REWRITE_TAC[th])
   THEN GEN_REWRITE_TAC (LAND_CONV) [GSYM o_THM]
   THEN MP_TAC(CONJUNCT1(SPEC `H:(A)hypermap` inverse_hypermap_maps))
   THEN ASM_REWRITE_TAC[] THEN  DISCH_THEN(fun th -> REWRITE_TAC[SYM th]); ALL_TAC]
THEN STRIP_TAC THEN MP_TAC (ISPECL[`D':A->bool`; `f':A->A`; `n':A->A`; `y:A`; `(e:A->A) (y:A)`] aux_permutes_conversion)
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (fun th -> REWRITE_TAC[th])
THEN  SUBGOAL_THEN `~((e:A->A) (y:A) = (inverse (f:A->A)) (x:A))` ASSUME_TAC
THENL[STRIP_TAC THEN UNDISCH_THEN `~((y:A) = (n:A->A) (x:A))` MP_TAC THEN REWRITE_TAC[] 
   THEN POP_ASSUM (MP_TAC o AP_TERM `inverse (e:A->A)`)
   THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_THM]
   THEN USE_THEN "H2" (MP_TAC o CONJUNCT2 o MATCH_MP PERMUTES_INVERSES_o)
   THEN DISCH_THEN (fun th-> REWRITE_TAC[th; I_THM])
   THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_THM]
   THEN MP_TAC (CONJUNCT1(CONJUNCT2(SPEC `H:(A)hypermap` inverse2_hypermap_maps)))
   THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th]); ALL_TAC]
THEN SUBGOAL_THEN `~((e:A->A) (y:A) = (x:A))` ASSUME_TAC
THENL[ UNDISCH_TAC `~(y:A = inverse (e:A->A) (x:A))`
   THEN REWRITE_TAC[CONTRAPOS_THM] 
   THEN DISCH_THEN (fun th -> (USE_THEN "H2" (fun th1 -> (MP_TAC (MATCH_MP inverse_function (CONJ th1 th))))))
   THEN REWRITE_TAC[]; ALL_TAC]
THEN REMOVE_THEN "A2" (MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `(e:A->A) (y:A)`)
THEN ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_THM] 
THEN MP_TAC(CONJUNCT1(CONJUNCT2(SPEC `H:(A)hypermap` inverse_hypermap_maps)))
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th])
THEN  SUBGOAL_THEN `~(inverse (n:A->A) (y:A) = inverse (n:A->A) (x:A))` ASSUME_TAC
THENL[UNDISCH_TAC `~(y:A = x:A)` THEN REWRITE_TAC[CONTRAPOS_THM] THEN USE_THEN "H3" (MP_TAC o MATCH_MP PERMUTES_INVERSE)
   THEN DISCH_THEN (MP_TAC o ISPECL[`y:A`; `x:A`] o MATCH_MP PERMUTES_INJECTIVE)
   THEN MESON_TAC[]; ALL_TAC]
THEN SUBGOAL_THEN `~(inverse (n:A->A) (y:A) = x:A)` ASSUME_TAC
THENL[UNDISCH_TAC `~(y:A = (n:A->A) (x:A))` 
   THEN REWRITE_TAC[CONTRAPOS_THM]
   THEN DISCH_THEN (MP_TAC o AP_TERM `n:A->A`)
   THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_THM]
   THEN USE_THEN "H3" (MP_TAC o CONJUNCT1 o MATCH_MP PERMUTES_INVERSES_o)
   THEN DISCH_THEN (fun th -> REWRITE_TAC[th; I_THM]); ALL_TAC]
THEN  DISCH_TAC THEN REMOVE_THEN "A1" (MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `(inverse (n:A->A)) (y:A)`)
THEN ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_THM] 
THEN USE_THEN "H3" (MP_TAC o CONJUNCT1 o MATCH_MP PERMUTES_INVERSES_o)
THEN DISCH_THEN (fun th -> REWRITE_TAC[th; I_THM]));;


(* We describe the cycle structure for a permutation on a finite set *)


let CARD_SINGLETON = prove(`!x:A. CARD{x} = 1`,  GEN_TAC THEN ASSUME_TAC (CONJUNCT1 CARD_CLAUSES)
THEN ASSUME_TAC (CONJUNCT1 FINITE_RULES) THEN MP_TAC(SPECL[`x:A`;`{}:A->bool`] (CONJUNCT2 CARD_CLAUSES))
THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN ARITH_TAC);;

let FINITE_SINGLETON = prove(`!x:A. FINITE {x}`, 
  REPEAT STRIP_TAC THEN ASSUME_TAC (CONJUNCT1 FINITE_RULES)
  THEN MP_TAC (ISPECL[`x:A`; `{}:A->bool`] (CONJUNCT2 FINITE_RULES))
  THEN ASM_REWRITE_TAC[]);;

let CARD_TWO_ELEMENTS = prove(`!x:A y:A. ~(x = y) ==> CARD {x ,y} = 2`,
  REPEAT STRIP_TAC
  THEN ASSUME_TAC(SPEC `y:A` FINITE_SINGLETON)
  THEN ASSUME_TAC(SPEC `y:A` CARD_SINGLETON)
  THEN MP_TAC(SPECL[`x:A`; `{y:A}`] (CONJUNCT2 CARD_CLAUSES))
  THEN ASM_REWRITE_TAC[IN_SING; TWO]);;

let FINITE_TWO_ELEMENTS = prove(`!x:A y:A. FINITE {x ,y}`,
  REPEAT STRIP_TAC THEN ASSUME_TAC(SPEC `y:A` FINITE_SINGLETON)
  THEN MP_TAC(SPECL[`x:A`; `{y:A}`] (CONJUNCT2 FINITE_RULES))
  THEN ASM_REWRITE_TAC[]);;

let CARD_ATLEAST_1 = prove(`!s:A->bool x:A. FINITE s /\ x IN s ==> 1 <= CARD s`,
  REPEAT STRIP_TAC
  THEN SUBGOAL_THEN `{x:A} SUBSET s` ASSUME_TAC
  THENL[SET_TAC[]; ALL_TAC]
  THEN ASSUME_TAC(SPEC `x:A` CARD_SINGLETON)
  THEN MP_TAC (SPECL[`{x:A}`; `s:A->bool`] CARD_SUBSET)
  THEN ASM_REWRITE_TAC[]);;

let CARD_ATLEAST_2 = prove(`!s:A->bool x:A y:A. FINITE s /\ x IN s /\ y IN s /\ ~(x = y) ==> 2 <= CARD s`,
  REPEAT STRIP_TAC
  THEN SUBGOAL_THEN `{x:A, y:A} SUBSET s` ASSUME_TAC
  THENL[SET_TAC[]; ALL_TAC]
  THEN MP_TAC(SPECL[`x:A`;`y:A`] CARD_TWO_ELEMENTS)
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (SUBST1_TAC o SYM)
  THEN MP_TAC(SPECL[`{x:A, y:A}`; `s:A->bool`] CARD_SUBSET)
  THEN ASM_REWRITE_TAC[]);;

let elim_power_function = prove(
   `!s:A->bool p:A->A x:A n:num m:num. p permutes s /\ (p POWER (m+n)) x = (p POWER m) x 
   ==> (p POWER n) x = x`,
REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (MP_TAC)) 
THEN REWRITE_TAC[addition_exponents; o_THM] THEN DISCH_TAC 
THEN REMOVE_THEN "c1" (ASSUME_TAC o (SPEC `m:num`) o MATCH_MP power_permutation) 
THEN POP_ASSUM (MP_TAC o ISPECL[`((p:A->A) POWER (n:num)) (x:A)`; `x:A` ] o MATCH_MP PERMUTES_INJECTIVE) 
THEN ASM_REWRITE_TAC[]);;

let orbit_one_point = prove(`!f:A->A x:A. f x = x <=> orbit_map f x = {x}`,
REPEAT GEN_TAC THEN EQ_TAC
THENL[STRIP_TAC THEN REWRITE_TAC[EXTENSION;IN_SING] THEN GEN_TAC
  THEN REWRITE_TAC[orbit_map; IN_ELIM_THM]
  THEN EQ_TAC
  THENL[STRIP_TAC THEN MP_TAC(SPECL[`1`; `f:A->A`; `x:A`] power_map_fix_point)
     THEN ASM_REWRITE_TAC[POWER_1;MULT_CLAUSES]
     THEN DISCH_THEN (ASSUME_TAC o SPEC `n:num`)
     THEN ASM_REWRITE_TAC[]; ALL_TAC]
  THEN STRIP_TAC THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC [ARITH_RULE `0 >= 0`; POWER; I_THM]; ALL_TAC]
THEN STRIP_TAC THEN MP_TAC (SPECL[`f:A->A`; `1`; `(x:A)`; `(f:A->A) (x:A)`] in_orbit_lemma)
THEN ASM_REWRITE_TAC[POWER_1; IN_SING]);;

let inj_orbit = new_recursive_definition num_RECURSION 
   `(inj_orbit (p:A->A) (x:A) 0 <=> T) /\ (inj_orbit (p:A->A) (x:A) (SUC n) 
    <=> (inj_orbit p x n) /\ (!j:num. j <= n ==> ~((p POWER (SUC n)) x =  (p POWER j) x)))`;;

let lemma_def_inj_orbit = prove(`!(p:A->A) (x:A) (n:num). (inj_orbit p x n 
   <=> (!i:num j:num. i <= n /\ j < i ==> ~((p POWER i) x = (p POWER j) x)))`,
REPEAT  GEN_TAC THEN EQ_TAC 
THENL[SPEC_TAC(`n:num`, `n:num`) THEN INDUCT_TAC
  THENL[REWRITE_TAC[inj_orbit; LE] THEN ARITH_TAC; ALL_TAC]
  THEN POP_ASSUM (LABEL_TAC "F1") THEN REWRITE_TAC[inj_orbit]
  THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F2") (LABEL_TAC "F3"))
  THEN REMOVE_THEN "F1" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "F4")
  THEN REWRITE_TAC[LE] THEN REPEAT STRIP_TAC
  THENL[UNDISCH_THEN `i:num = SUC (n:num)` SUBST_ALL_TAC 
      THEN REMOVE_THEN "F3" (MP_TAC o SPEC `j:num`)
      THEN REWRITE_TAC[GSYM LT_SUC_LE] THEN ASM_REWRITE_TAC[]; ALL_TAC]
  THEN REMOVE_THEN "F4" (MP_TAC o SPECL[`i:num`; `j:num`])
  THEN ASM_REWRITE_TAC[]; ALL_TAC]
THEN SPEC_TAC(`n:num`, `n:num`) THEN INDUCT_TAC
THENL[REWRITE_TAC[inj_orbit; ARITH]; ALL_TAC]
THEN POP_ASSUM (LABEL_TAC "A1")
THEN DISCH_THEN (LABEL_TAC "A4")
THEN SUBGOAL_THEN `!i:num j:num. i <= (n:num) /\ j < i ==> ~((p POWER i)(x:A) = (p POWER j) x)` (LABEL_TAC "C1")
THENL[REPLICATE_TAC 3 STRIP_TAC THEN MP_TAC(ARITH_RULE `i:num <= n:num ==> i <= SUC n`)
   THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REMOVE_THEN "A4" (MP_TAC o SPECL[`i:num`; `j:num`])
   THEN ASM_SIMP_TAC[]; ALL_TAC]
THEN REMOVE_THEN "A1" MP_TAC
THEN POP_ASSUM (fun th -> REWRITE_TAC[th])
THEN STRIP_TAC THEN ASM_REWRITE_TAC[inj_orbit] THEN REPEAT STRIP_TAC
THEN REMOVE_THEN "A4" (MP_TAC o SPECL[`SUC (n:num)`; `j:num`])
THEN ASM_REWRITE_TAC[LE_REFL; LT_SUC_LE]);;

let lemma_sub_inj_orbit = prove(`!(p:A->A) x:A n:num. inj_orbit p x n ==> !m:num. m <= n ==> inj_orbit p x m`,
REPEAT GEN_TAC THEN REWRITE_TAC[lemma_def_inj_orbit] THEN REPEAT STRIP_TAC
THEN FIRST_X_ASSUM (MP_TAC o SPECL[`i:num`; `j:num`] o check (is_forall o concl))
THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `m:num <= n:num` THEN UNDISCH_TAC `i:num <= m:num` THEN ARITH_TAC);;


let inj_orbit_step = prove(`!(s:A->bool) (p:A->A) (x:A) (n:num). (p permutes s) /\ (inj_orbit p x n) /\ ~((p POWER (SUC n:num)) x = x) 
                            ==> (inj_orbit p x (SUC n))`,
REPEAT STRIP_TAC 
THEN REWRITE_TAC[inj_orbit] THEN ASM_REWRITE_TAC[]
THEN REPLICATE_TAC 2 STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o check(is_neg o concl))
THEN REWRITE_TAC[CONTRAPOS_THM]
THEN ASM_CASES_TAC `j:num = 0`
THENL[POP_ASSUM SUBST1_TAC THEN REWRITE_TAC[POWER_0; I_THM]; ALL_TAC]
THEN UNDISCH_TAC `j:num <= n:num` THEN REWRITE_TAC[GSYM LT_SUC_LE]
THEN REWRITE_TAC[LT_EXISTS] THEN DISCH_THEN(X_CHOOSE_THEN `d:num` (LABEL_TAC "G"))
THEN USE_THEN "G" SUBST1_TAC
THEN UNDISCH_THEN `(p:A->A) permutes (s:A->bool)` (fun th1 -> (DISCH_THEN (fun th2 -> (MP_TAC ( MATCH_MP elim_power_function (CONJ th1 th2))))))
THEN MP_TAC(ARITH_RULE `~(j = 0) /\ SUC (n:num) = j + SUC (d:num) ==> SUC d <= n`)
THEN ASM_REWRITE_TAC[]
THEN REPEAT STRIP_TAC 
THEN MP_TAC(SPECL[`p:A->A`; `x:A`; `n:num`] lemma_def_inj_orbit)
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPECL[`SUC (d:num)`; `0`])
THEN ASM_REWRITE_TAC[LT_NZ; POWER_0; ARITH; I_THM] THEN ARITH_TAC);;


let lemma_orbit_finite = prove(`!(s:A->bool) (p:A->A) (x:A). FINITE s /\ p permutes s ==> FINITE (orbit_map p x)`,
REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:A IN s:A->bool`
THENL[REPEAT STRIP_TAC 
   THEN UNDISCH_THEN `(p:A->A) permutes (s:A->bool)` (MP_TAC o SPEC `x:A` o MATCH_MP orbit_subset)
   THEN ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC]
THEN SUBGOAL_THEN `(p:A->A) x:A = x:A` MP_TAC
THENL[ASM_MESON_TAC[permutes]; ALL_TAC]
THEN ONCE_REWRITE_TAC[orbit_one_point] THEN DISCH_THEN SUBST1_TAC THEN ASSUME_TAC (CONJUNCT1 CARD_CLAUSES)
THEN ASSUME_TAC (CONJUNCT1 FINITE_RULES) THEN MP_TAC(SPECL[`x:A`;`{}:A->bool`] (CONJUNCT2 FINITE_RULES))
THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN ARITH_TAC);;


let lemma_subset_orbit = prove(`!(p:A->A) x:A n:num. {(p POWER (i:num)) x | i <= n} SUBSET orbit_map p x`,
REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN GEN_TAC 
THEN REWRITE_TAC[orbit_map; IN_ELIM_THM] THEN STRIP_TAC
THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;


let lemma_segment_orbit = prove(`!(s:A->bool) (p:A->A) (x:A). FINITE s /\ p permutes s ==> (!m:num. m < CARD(orbit_map p x) ==> inj_orbit p x m)`,
REPLICATE_TAC 4 STRIP_TAC THEN INDUCT_TAC
THENL[REWRITE_TAC[inj_orbit]; ALL_TAC]
THEN POP_ASSUM (LABEL_TAC "F1") THEN DISCH_THEN (LABEL_TAC "F2")
THEN MP_TAC (ARITH_RULE `SUC (m:num) < CARD (orbit_map (p:A->A) (x:A)) ==> m < CARD (orbit_map p x)`)
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REMOVE_THEN "F1" MP_TAC THEN POP_ASSUM (fun th-> REWRITE_TAC[th]) THEN STRIP_TAC
THEN MATCH_MP_TAC inj_orbit_step
THEN EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THEN MP_TAC(SPECL[`p:A->A`; `SUC (m:num)`; `x:A`] card_orbit_le)
THEN ASM_REWRITE_TAC[ARITH_RULE `~(SUC(d:num) = 0)`]
THEN  REMOVE_THEN "F2" MP_TAC THEN ARITH_TAC);;

let lemma_cycle_orbit = prove(`!(s:A->bool) (p:A->A) (x:A). FINITE s /\ p permutes s  ==> (p POWER (CARD(orbit_map p x))) x = x`,
REPEAT STRIP_TAC
THEN MP_TAC(SPECL[`s:A->bool`; `p:A->A`; `x:A`] lemma_segment_orbit)
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `PRE(CARD(orbit_map (p:A->A) (x:A)))`)
THEN ABBREV_TAC `n = CARD(orbit_map (p:A->A) (x:A))` THEN MP_TAC (SPECL[`p:A->A`; `x:A`] orbit_reflect) THEN ASM_REWRITE_TAC[]
THEN STRIP_TAC
THEN MP_TAC (SPECL[`s:A->bool`; `p:A->A`] lemma_orbit_finite) 
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[]
THEN STRIP_TAC THEN MP_TAC(SPECL[`orbit_map (p:A->A) (x:A)`;`x:A`] lemma_card_atleast_one) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THEN MP_TAC (ARITH_RULE `n:num >= 1 ==> PRE n < n`) THEN ASM_REWRITE_TAC[] 
THEN DISCH_THEN(fun th-> REWRITE_TAC[th])
THEN MP_TAC (ARITH_RULE `n:num >= 1 ==> n = (PRE n) + 1`)
THEN ABBREV_TAC `m = PRE (n:num)` THEN ASM_REWRITE_TAC[] 
THEN UNDISCH_THEN `(p:A->A) permutes (s:A->bool)` (LABEL_TAC "F1")
THEN DISCH_THEN (LABEL_TAC "F2")
THEN STRIP_TAC THEN MP_TAC(SPECL[`p:A->A`; `x:A`;`m:num`] lemma_def_inj_orbit)
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "F2") 
THEN UNDISCH_THEN `CARD(orbit_map (p:A->A) (x:A)) = n:num` MP_TAC
THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN STRIP_TAC THEN STRIP_TAC
THEN SUBGOAL_THEN `!i:num j:num. i < (m:num) + 2 /\ j < i ==> ~((p POWER i) (x:A) = (p POWER j) x)` ASSUME_TAC
THENL[REPEAT STRIP_TAC THEN MP_TAC(ARITH_RULE `i:num < (m:num) +2 ==> i = m + 1 \/ i <= m`)
   THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
   THENL[POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM MP_TAC
      THEN ASM_CASES_TAC `j:num = 0`
      THENL[POP_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[POWER; I_THM]; ALL_TAC]
      THEN UNDISCH_TAC `j:num <(m:num)+1`
      THEN REWRITE_TAC[LT_EXISTS] THEN DISCH_THEN( X_CHOOSE_THEN `d:num` ASSUME_TAC) 
      THEN MP_TAC(ARITH_RULE `(m:num)+1 = (j:num) + SUC (d:num) ==> m = j + d`)
      THEN POP_ASSUM(fun th->REWRITE_TAC[th])
      THEN DISCH_THEN SUBST_ALL_TAC THEN STRIP_TAC
      THEN MP_TAC(SPECL[`s:A->bool`; `p:A->A`; `x:A`; `SUC (d:num)`;`(j:num)`] elim_power_function)
      THEN ASM_REWRITE_TAC[] THEN  REMOVE_THEN "F2" (MP_TAC o SPECL[`SUC (d:num)`; `0`])
      THEN MP_TAC(ARITH_RULE `~(j:num = 0) ==> SUC (d:num) <= j + d`)
      THEN ASM_REWRITE_TAC[LT_0]
      THEN DISCH_THEN (fun th -> REWRITE_TAC[th])
      THEN REWRITE_TAC[POWER; I_THM]; ALL_TAC]
   THEN REMOVE_THEN "F2" (MP_TAC o SPECL[`i:num`; `j:num`])
   THEN ASM_REWRITE_TAC[]; ALL_TAC]
THEN MP_TAC (SPECL[`(m:num)+2`; `(\k:num. ((p:A->A) POWER k) (x:A))`] CARD_FINITE_SERIES_EQ)
THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `i:num < (m:num) + 2 <=> i <= m + 1`]
THEN STRIP_TAC THEN ASSUME_TAC(ISPECL[`p:A->A`; `x:A`; `(m:num) +1`] lemma_subset_orbit)
THEN MP_TAC (ISPECL[`{((p:A->A) POWER (i:num)) (x:A) | i <= (m:num) + 1}`;`orbit_map (p:A->A) (x:A)`] CARD_SUBSET)
THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let lemma_card_orbit = prove(`!(s:A->bool) (p:A->A) (x:A) (n:num). 
       (FINITE s /\ p permutes s /\ inj_orbit p x n) /\ (p POWER (SUC n)) x = x ==> CARD(orbit_map p x) = SUC n`,
REPEAT STRIP_TAC THEN ABBREV_TAC `m = CARD(orbit_map (p:A->A) (x:A))`
THEN  MP_TAC(SPECL[`p:A->A`; `SUC n:num`; `x:A`] card_orbit_le)
THEN ASM_REWRITE_TAC[ARITH_RULE `~(SUC (n:num) = 0)`]
THEN STRIP_TAC
THEN ASM_CASES_TAC `m:num = SUC n:num`
THENL[ASM_REWRITE_TAC[]; ALL_TAC]
THEN MP_TAC(ARITH_RULE `m:num <= SUC (n:num) /\ ~(m = SUC n) ==> m < SUC n`)
THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM]
THEN STRIP_TAC THEN MP_TAC(SPECL[`s:A->bool`; `p:A->A`; `x:A`] lemma_cycle_orbit)
THEN ASM_REWRITE_TAC[] THEN MP_TAC (SPECL[`orbit_map (p:A->A) (x:A)`; `x:A`] lemma_card_atleast_one)
THEN MP_TAC(SPECL[`p:A->A`; `x:A`]  orbit_reflect)
THEN MP_TAC (SPECL[`s:A->bool`; `p:A->A`; `x:A`] lemma_orbit_finite)
THEN ASM_REWRITE_TAC[] THEN REPLICATE_TAC 2 (DISCH_THEN(fun th -> REWRITE_TAC[th]))
THEN STRIP_TAC THEN UNDISCH_TAC `m:num < SUC (n:num)`
THEN REWRITE_TAC[LT_SUC_LE] THEN STRIP_TAC
THEN UNDISCH_TAC `inj_orbit (p:A->A) (x:A) (n:num)`
THEN REWRITE_TAC[lemma_def_inj_orbit]
THEN DISCH_THEN(MP_TAC o SPECL[`m:num`; `0:num`])
THEN MP_TAC (ARITH_RULE `m:num >= 1 ==> 0 < m`) THEN ASM_REWRITE_TAC[]
THEN DISCH_THEN (fun th -> SIMP_TAC[POWER_0; I_THM; th]) THEN SIMP_TAC[]);;

let lemma_add_exponent_function = prove(`!(p:A->A) m:num n:num x:A. (p POWER (m+n)) x =  (p POWER m) ((p POWER n) x)`, 
REPEAT STRIP_TAC THEN ASSUME_TAC (SPECL[`m:num`;`n:num`; `p:A->A`] addition_exponents)
THEN POP_ASSUM (fun th -> (MP_TAC(AP_THM th `x:A`))) THEN REWRITE_TAC[o_THM]);;

let iterate_map_valuation = prove(`!(p:A->A) (n:num) (x:A). p ((p POWER n) x) = (p POWER (SUC n)) x`,
REPEAT STRIP_TAC THEN ASSUME_TAC (SPECL[`n:num`; `p:A->A`] (GSYM COM_POWER))
THEN POP_ASSUM (fun th -> (MP_TAC (AP_THM th `x:A`)))
THEN REWRITE_TAC[o_THM]);;

let lemma_identity_segment = prove(`!(p:A->A) (q:A->A) (x:A) (n:num). 
   (!i:num. i <= n ==> (q POWER i) x = (p POWER i) x) /\  inj_orbit p x n  ==> inj_orbit q x n`,
REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC
THENL[REWRITE_TAC[inj_orbit]; ALL_TAC]
THEN POP_ASSUM (LABEL_TAC "F1") THEN REWRITE_TAC[inj_orbit]
THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F2") (LABEL_TAC "F3"))
THEN SUBGOAL_THEN `(!i:num. i <= n:num ==> ((q:A->A) POWER i) (x:A) = ((p:A->A) POWER i) x)` (LABEL_TAC "F4")
THENL[REPEAT STRIP_TAC
   THEN POP_ASSUM (ASSUME_TAC o MATCH_MP (ARITH_RULE `i:num <= n:num ==> i <= SUC n`))
   THEN REMOVE_THEN "F2" (MP_TAC o SPEC `i:num`)
   THEN ASM_REWRITE_TAC[]; ALL_TAC]
THEN REMOVE_THEN "F1" MP_TAC
THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (fun th -> REWRITE_TAC[th])
THEN REPLICATE_TAC 2 STRIP_TAC
THEN POP_ASSUM (fun th -> (ASSUME_TAC th THEN ASSUME_TAC(MATCH_MP (ARITH_RULE `i:num <= n:num ==> i <= SUC n`) th)))
THEN USE_THEN "F2" (MP_TAC o SPEC `j:num`)
THEN POP_ASSUM (fun th -> REWRITE_TAC[th])
THEN DISCH_THEN SUBST1_TAC
THEN USE_THEN "F2" (MP_TAC o SPEC `SUC (n:num)`)
THEN REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC
THEN REMOVE_THEN "F3" (MP_TAC o SPEC `j:num` o CONJUNCT2)
THEN POP_ASSUM (fun th -> REWRITE_TAC[th]));;

let is_edge_merge = new_definition `is_edge_merge (H:(A)hypermap) (x:A) <=> dart_nondegenerate H x /\ ~(node_map H x IN edge H x)`;;

let is_node_merge = new_definition `is_node_merge (H:(A)hypermap) (x:A) <=> dart_nondegenerate H x /\ ~(face_map H x IN node H x)`;;

let is_face_merge = new_definition `is_face_merge (H:(A)hypermap) (x:A) <=> dart_nondegenerate H x /\ ~(edge_map H x IN face H x)`;;

let is_edge_split = new_definition `is_edge_split (H:(A)hypermap) (x:A) <=> dart_nondegenerate H x /\  node_map H x IN edge H x`;;

let is_node_split = new_definition `is_node_split (H:(A)hypermap) (x:A) <=> dart_nondegenerate H x /\  face_map H x IN node H x`;;

let is_face_split = new_definition `is_face_split (H:(A)hypermap) (x:A) <=> dart_nondegenerate H x /\  edge_map H x IN face H x`;;


let INVERSE_EVALUATION = prove(`!s:A->bool p:A->A x:A. FINITE s /\ p permutes s ==> ?j:num. (inverse p) x = (p POWER j) x`,
  REPEAT STRIP_TAC
  THEN MP_TAC (SPECL[`s:A->bool`; `p:A->A`] inverse_element_lemma)
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (X_CHOOSE_THEN `j:num` (fun th -> (ASSUME_TAC (AP_THM th `x:A`))))
  THEN EXISTS_TAC `j:num`
  THEN ASM_REWRITE_TAC[]);;

let lemma_orbit_identity = prove(`!s:A->bool p:A->A  x:A y:A. FINITE s /\ p permutes s /\ y IN orbit_map p x 
   ==> orbit_map p x = orbit_map p y`,
  REPEAT STRIP_TAC
  THEN MP_TAC (SPECL[`s:A->bool`; `p:A->A`] partition_orbit)
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (MP_TAC o SPECL[`x:A`; `y:A`])
  THEN ASSUME_TAC (SPECL[`p:A->A`; `y:A`] orbit_reflect)
  THEN SUBGOAL_THEN `?z:A.z IN orbit_map (p:A->A) (x:A) INTER orbit_map (p:A->A) (y:A)` MP_TAC
  THENL[MP_TAC (ISPECL[`orbit_map (p:A->A) (x:A)`; `orbit_map (p:A->A) (y:A)`; `y:A`] IN_INTER)
	THEN ASM_REWRITE_TAC[]
	THEN DISCH_TAC THEN EXISTS_TAC `y:A`
	THEN POP_ASSUM (fun th -> REWRITE_TAC[th]); ALL_TAC]
  THEN REWRITE_TAC[MEMBER_NOT_EMPTY]
  THEN DISCH_THEN (fun th -> REWRITE_TAC[th]));;

let lemma_orbit_disjoint = prove(`!s:A->bool p:A->A  x:A y:A. FINITE s /\ p permutes s /\ ~(y IN orbit_map p x) 
   ==> orbit_map p x INTER orbit_map p y = {}`,
  REPEAT STRIP_TAC
  THEN MP_TAC (SPECL[`s:A->bool`; `p:A->A`] partition_orbit)
  THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPECL[`x:A`; `y:A`])
  THEN SUBGOAL_THEN `~(orbit_map (p:A->A) (x:A) = orbit_map (p:A->A) (y:A))` ASSUME_TAC
  THENL[POP_ASSUM MP_TAC
      THEN REWRITE_TAC[CONTRAPOS_THM]
      THEN DISCH_THEN SUBST1_TAC
      THEN REWRITE_TAC[orbit_reflect]; ALL_TAC]
  THEN ASM_REWRITE_TAC[]);;

let INVERSE_POWER_MAP = prove(`!s:A->bool p:A->A n:num. FINITE s /\ p permutes s 
  ==> (inverse p) o (p POWER (SUC n)) = p POWER n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COM_POWER; o_ASSOC]
  THEN POP_ASSUM (MP_TAC o CONJUNCT2 o  MATCH_MP PERMUTES_INVERSES_o)
  THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[I_O_ID]);;

let INVERSE_POWER_EVALUATION = prove(`!s:A->bool p:A->A x:A n:num. FINITE s /\ p permutes s 
   ==> (inverse p)((p POWER (SUC n)) x) = (p POWER n) x`,
  REPEAT STRIP_TAC
  THEN MP_TAC (SPECL[`s:A->bool`; `p:A->A`; `n:num`] INVERSE_POWER_MAP)
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (fun th -> (MP_TAC (AP_THM th `x:A`)))
  THEN REWRITE_TAC[o_THM]);;

let lemma_in_disjoint = prove(`!s:A->bool t:A->bool x:A. s INTER  t = {} /\ x IN s ==> ~(x IN t)`,
  REPEAT STRIP_TAC
  THEN MP_TAC(SPECL[`s:A->bool`; `t:A->bool`; `x:A`] IN_INTER)
  THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[NOT_IN_EMPTY]);;

let lemma_not_in_orbit = prove(`!s:A->bool p :A->A x:A y:A n:num. FINITE s /\ p permutes s /\ ~(y IN orbit_map p x) ==> ~(y = (p POWER n) x)`,
  REPEAT STRIP_TAC
  THEN FIRST_X_ASSUM (MP_TAC o check (is_neg o concl))
  THEN REWRITE_TAC[]
  THEN REWRITE_TAC[orbit_map; IN_ELIM_THM]
  THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[GE; LE_0]);;


(* merge case *)


let lemma_edge_merge = prove(`!(H:(A)hypermap) (x:A). x IN dart H /\ is_edge_merge H x 
   ==> {x} UNION (edge (edge_walkup H x) (node_map H x)) = (edge H x) UNION (edge H (node_map H x))`,
REPEAT GEN_TAC THEN  REWRITE_TAC[is_edge_merge; dart_nondegenerate; edge]
  THEN STRIP_TAC THEN label_hypermap_TAC `H:(A)hypermap`
  THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
  THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` 
  THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` 
  THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
  THEN ABBREV_TAC `G = edge_walkup (H:(A)hypermap) (x:A)` 
  THEN ABBREV_TAC `D' = dart (G:(A)hypermap)`
  THEN ABBREV_TAC `e' = edge_map (G:(A)hypermap)`
  THEN MP_TAC (SPECL[`e:A->A`; `1`; `x:A`; `(e:A->A) (x:A)`] in_orbit_lemma)
  THEN REWRITE_TAC[POWER_1]
  THEN DISCH_THEN (LABEL_TAC "F1")
  THEN MP_TAC(SPECL[`D:A->bool`; `e:A->A`; `x:A`] INVERSE_EVALUATION)
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (X_CHOOSE_THEN `j:num`((LABEL_TAC "F2") o MATCH_MP in_orbit_lemma ))
  THEN LABEL_TAC "F3" (SPECL[`e:A->A`; `x:A`] orbit_reflect)
  THEN USE_THEN "H1"(fun th1 -> (USE_THEN "H2" (fun th2 -> (LABEL_TAC "F4" (SPEC `x:A` (MATCH_MP lemma_orbit_finite (CONJ th1 th2)))))))
  THEN MP_TAC (SPECL[`orbit_map (e:A->A) (x:A)`; `x:A`; `(e:A->A) (x:A)`] CARD_ATLEAST_2)
  THEN ASM_REWRITE_TAC[LE_EXISTS; ADD_SYM]
  THEN DISCH_THEN (X_CHOOSE_THEN `r:num` (LABEL_TAC "F5"))
  THEN MP_TAC (SPECL[`e:A->A`; `1`; `(n:A->A) (x:A)`; `(inverse (f:A->A)) (x:A)`] in_orbit_lemma)
  THEN REWRITE_TAC[POWER_1]
  THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [POWER_1; GSYM o_THM]
  THEN REWRITE_TAC[GSYM inverse_hypermap_maps]
  THEN MP_TAC (CONJUNCT2(CONJUNCT2(SPEC `H:(A)hypermap` inverse_hypermap_maps)))
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (SUBST1_TAC o SYM)
  THEN REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "F6")
  THEN LABEL_TAC "F7" (SPECL[`e:A->A`; `(n:A->A) (x:A)`] orbit_reflect)
  THEN USE_THEN "H1"(fun th1 -> (USE_THEN "H2" (fun th2 -> (LABEL_TAC "F8" (SPEC `(n:A->A) (x:A)` (MATCH_MP lemma_orbit_finite (CONJ th1 th2)))))))
  THEN MP_TAC (SPECL[`orbit_map (e:A->A) ((n:A->A) (x:A))`; `(n:A->A) (x:A)`] CARD_ATLEAST_1)
  THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[LE_EXISTS; ADD_SYM]
  THEN DISCH_THEN (X_CHOOSE_THEN `l:num` (LABEL_TAC "F9"))
  THEN MP_TAC (SPECL[`D:A->bool`; `e:A->A`; `x:A`; `(n:A->A) (x:A)` ] lemma_orbit_disjoint)
   THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "F10")
   THEN MP_TAC(SPECL[`D:A->bool`; `e:A->A`; `(n:A->A) (x:A)`;  `(inverse (f:A->A)) (x:A)`] lemma_orbit_identity)
   THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC
   THEN MP_TAC(SPECL[`D:A->bool`; `e:A->A`; `(x:A)`;  `(e:A->A) (x:A)`] lemma_orbit_identity)
   THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC
   THEN MP_TAC (SPECL[`D:A->bool`; `e:A->A`; `(e:A->A) (x:A)`] lemma_cycle_orbit)
   THEN ASM_REWRITE_TAC[ARITH_RULE `(r:num)+2 = SUC (r+1)`]
   THEN DISCH_THEN (MP_TAC o AP_TERM `inverse (e:A->A)`)
   THEN MP_TAC(SPECL[`D:A->bool`; `e:A->A`; `(e:A->A) (x:A)`; `(r:num)+1`] INVERSE_POWER_EVALUATION)
   THEN ASM_REWRITE_TAC[]
   THEN DISCH_THEN SUBST1_TAC
   THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_THM]
   THEN USE_THEN "H2" (fun th-> (REWRITE_TAC[CONJUNCT2 (MATCH_MP PERMUTES_INVERSES_o th); I_THM]))
   THEN DISCH_THEN (fun th -> (LABEL_TAC "F11" th THEN MP_TAC th))
   THEN REWRITE_TAC[GSYM ADD1] THEN DISCH_THEN (MP_TAC o AP_TERM `inverse (e:A->A)`)
   THEN MP_TAC(SPECL[`D:A->bool`; `e:A->A`; `(e:A->A) (x:A)`; `r:num`] INVERSE_POWER_EVALUATION)
   THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC
   THEN DISCH_THEN (LABEL_TAC "F12")
   THEN MP_TAC (SPECL[`D:A->bool`; `e:A->A`; `(inverse(f:A->A)) (x:A)`] lemma_cycle_orbit)
  THEN ASM_REWRITE_TAC[GSYM ADD1]
  THEN DISCH_THEN (MP_TAC o AP_TERM `inverse (e:A->A)`)
  THEN MP_TAC(SPECL[`D:A->bool`; `e:A->A`; `inverse((f:A->A)) (x:A)`; `l:num`] INVERSE_POWER_EVALUATION)
  THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC
  THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_THM]
  THEN MP_TAC(CONJUNCT1 (CONJUNCT2(SPEC `H:(A)hypermap` inverse2_hypermap_maps)))
  THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (SUBST1_TAC o SYM)
  THEN DISCH_THEN (LABEL_TAC "F14")
   THEN SUBGOAL_THEN `!v:num. v <= r:num ==> (e POWER v) ((e:A->A) (x:A)) = (e' POWER v) (e x)` (LABEL_TAC "F15")
  THENL[INDUCT_TAC THENL [REWRITE_TAC[LE_0; POWER]; ALL_TAC]
   THEN DISCH_THEN (LABEL_TAC "G1")
   THEN FIRST_X_ASSUM (MP_TAC o check(is_imp o concl))
   THEN USE_THEN "G1"(fun th -> REWRITE_TAC[MATCH_MP (ARITH_RULE `SUC (v:num) <= r:num ==> v <= r`) th])
   THEN DISCH_THEN ((LABEL_TAC "G2") o SYM)
   THEN USE_THEN "H1" (fun th1 -> (USE_THEN "H2" (fun th2 -> (MP_TAC (SPECL[`(e:A->A) (x:A)`] (MATCH_MP lemma_segment_orbit (CONJ th1 th2)))))))
   THEN ASM_REWRITE_TAC[]
   THEN DISCH_THEN (LABEL_TAC "G3")
   THEN USE_THEN "G3" (MP_TAC o SPEC `(r:num)+1`)
   THEN REWRITE_TAC[ARITH_RULE `(r:num)+1 < r + 2`]
   THEN REWRITE_TAC[lemma_def_inj_orbit]
   THEN DISCH_THEN (MP_TAC o SPECL[`(r:num)+1`; `v:num`])
   THEN ASM_REWRITE_TAC[LE_REFL]
   THEN USE_THEN "G1" (fun th -> REWRITE_TAC[MP (ARITH_RULE `SUC (v:num) <= r ==> v < r + 1`) th])
   THEN DISCH_THEN (ASSUME_TAC o GSYM)
   THEN USE_THEN "G3" (MP_TAC o SPEC `r:num`)
   THEN REWRITE_TAC[ARITH_RULE `r:num < r + 2`]
   THEN REWRITE_TAC[lemma_def_inj_orbit]
   THEN DISCH_THEN (MP_TAC o SPECL[`r:num`; `v:num`])
   THEN ASM_REWRITE_TAC[LE_REFL]
   THEN USE_THEN "G1" (fun th -> REWRITE_TAC[MP (ARITH_RULE `SUC (v:num) <= r ==> v < r`) th])
   THEN DISCH_THEN (ASSUME_TAC o GSYM)
   THEN UNDISCH_THEN `~((n:A->A) (x:A) IN orbit_map e (e x))` (fun th1 -> (USE_THEN "H1" (fun th2 -> (USE_THEN "H2" (fun th3 -> (MP_TAC (SPEC `v:num` (MATCH_MP lemma_not_in_orbit (CONJ th2 (CONJ th3 th1))))))))))
   THEN DISCH_THEN (ASSUME_TAC o GSYM)
   THEN REWRITE_TAC[COM_POWER; o_THM]
   THEN REMOVE_THEN "G2" SUBST1_TAC
   THEN MP_TAC (CONJUNCT2(CONJUNCT2(CONJUNCT2(SPECL[`H:(A)hypermap`; `x:A`; `((e:A->A) POWER (v:num)) (e (x:A))`] edge_map_walkup))))
   THEN ASM_REWRITE_TAC[]
   THEN DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC]
    THEN ABBREV_TAC `y = (inverse (f:A->A)) (x:A)`
   THEN SUBGOAL_THEN `!v:num. v <= l:num ==> ((e:A->A) POWER v) (y:A) = ((e':A->A) POWER v) y` (LABEL_TAC "F16")
   THENL[ INDUCT_TAC THENL[REWRITE_TAC[LE_0; POWER]; ALL_TAC]
       THEN DISCH_THEN (LABEL_TAC "G1")
       THEN FIRST_X_ASSUM (MP_TAC o check(is_imp o concl))
       THEN USE_THEN "G1"(fun th -> REWRITE_TAC[MATCH_MP (ARITH_RULE `SUC (v:num) <= r:num ==> v <= r`) th])
       THEN DISCH_THEN ((LABEL_TAC "G2") o SYM)
       THEN USE_THEN "H1" (fun th1 -> (USE_THEN "H2" (fun th2 -> (MP_TAC (SPECL[`y:A`] (MATCH_MP lemma_segment_orbit (CONJ th1 th2)))))))
       THEN ASM_REWRITE_TAC[]
       THEN DISCH_THEN (LABEL_TAC "G3")
       THEN USE_THEN "G3" (MP_TAC o SPEC `l:num`)
       THEN REWRITE_TAC[ARITH_RULE `(l:num) < l + 1`]
       THEN REWRITE_TAC[lemma_def_inj_orbit]
       THEN DISCH_THEN (MP_TAC o SPECL[`l:num`; `v:num`])
       THEN ASM_REWRITE_TAC[LE_REFL]
       THEN USE_THEN "G1" (fun th -> REWRITE_TAC[MP (ARITH_RULE `SUC (v:num) <= l ==> v < l`) th])
       THEN DISCH_THEN (ASSUME_TAC o GSYM)
       THEN USE_THEN "F10" (fun th1 -> (USE_THEN "F3" (fun th2 -> (MP_TAC (MATCH_MP lemma_in_disjoint (CONJ th1 th2))))))
       THEN DISCH_THEN (fun th1 -> (USE_THEN "H1" (fun th2 -> (USE_THEN "H2" (fun th3 -> (MP_TAC (SPEC `v:num` (MATCH_MP lemma_not_in_orbit (CONJ th2 (CONJ th3 th1))))))))))
       THEN DISCH_THEN (ASSUME_TAC o GSYM)
       THEN USE_THEN "F10" (fun th1 -> (USE_THEN "F2" (fun th2 -> (MP_TAC (MATCH_MP lemma_in_disjoint (CONJ th1 th2))))))
       THEN DISCH_THEN (fun th1 -> (USE_THEN "H1" (fun th2 -> (USE_THEN "H2" (fun th3 -> (MP_TAC (SPEC `v:num` (MATCH_MP lemma_not_in_orbit (CONJ th2 (CONJ th3 th1))))))))))
       THEN DISCH_THEN (ASSUME_TAC o GSYM)
       THEN REWRITE_TAC[COM_POWER; o_THM]
       THEN REMOVE_THEN "G2" SUBST1_TAC
       THEN MP_TAC (CONJUNCT2(CONJUNCT2(CONJUNCT2(SPECL[`H:(A)hypermap`; `x:A`; `((e:A->A) POWER (v:num)) (y:A)`] edge_map_walkup))))
       THEN ASM_REWRITE_TAC[]
       THEN DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC]
   THEN ABBREV_TAC `z = (e:A->A) (x:A)`
   THEN MP_TAC (CONJUNCT1(CONJUNCT2(SPECL[`H:(A)hypermap`; `x:A`; `((e:A->A) POWER (l:num)) (y:A)`] edge_map_walkup)))
   THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "F17")
   THEN MP_TAC (CONJUNCT1(CONJUNCT2(CONJUNCT2(SPECL[`H:(A)hypermap`; `x:A`; `((e:A->A) POWER (r:num)) (z:A)`] edge_map_walkup))))
   THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "y"
   THEN USE_THEN "H2" (fun th -> (MP_TAC(SPEC `x:A` (MATCH_MP non_fixed_point_lemma th))))
   THEN USE_THEN "H4" (fun th -> (MP_TAC(SPEC `x:A` (MATCH_MP non_fixed_point_lemma th))))
   THEN ASM_REWRITE_TAC[]
   THEN DISCH_THEN (fun th -> REWRITE_TAC[th])
   THEN DISCH_THEN (fun th -> REWRITE_TAC[th])
   THEN DISCH_THEN (LABEL_TAC "F18")
   THEN USE_THEN "F15" (MP_TAC o SPEC `r:num`)
   THEN REWRITE_TAC[LE_REFL]
   THEN USE_THEN "F12" (fun th -> REWRITE_TAC[th])
   THEN DISCH_THEN (fun th -> (MP_TAC (AP_TERM `e':A->A` (SYM th))))
   THEN USE_THEN "F18" (fun th -> REWRITE_TAC[th])
   THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_THM]
   THEN REWRITE_TAC [GSYM COM_POWER; ADD1]
   THEN DISCH_THEN (LABEL_TAC "F19")
   THEN USE_THEN "F19"(MP_TAC o AP_TERM `(e':A->A) POWER (l:num)`)
   THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_THM]
   THEN REWRITE_TAC[GSYM addition_exponents]
   THEN USE_THEN "F16" (MP_TAC o SPEC `l:num`)
   THEN REWRITE_TAC[LE_REFL]
   THEN USE_THEN "F14" (fun th -> REWRITE_TAC[th])
   THEN DISCH_THEN (fun th -> (LABEL_TAC "F20"  (SYM th) THEN REWRITE_TAC[SYM th]))
   THEN DISCH_THEN (LABEL_TAC "F21")
   THEN MP_TAC (SPEC `G:(A)hypermap` hypermap_lemma)
   THEN ASM_REWRITE_TAC[]
   THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F22") (LABEL_TAC "F23" o CONJUNCT1))
   THEN MP_TAC(SPECL[`e':A->A`; `1`; `(n:A->A) (x:A)`; `z:A`] in_orbit_lemma)
   THEN REWRITE_TAC[POWER_1]
   THEN USE_THEN "F17" (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o  DEPTH_CONV) [SYM th])
   THEN REWRITE_TAC[]
   THEN DISCH_THEN (fun th1 -> (USE_THEN "F22" (fun th2 -> (USE_THEN "F23" (fun th3 -> (MP_TAC (MATCH_MP lemma_orbit_identity (CONJ th2 (CONJ th3 th1)))))))))
   THEN DISCH_THEN SUBST1_TAC
   THEN USE_THEN "F21" (MP_TAC o AP_TERM `e':A->A`)
   THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_THM]
   THEN REWRITE_TAC[GSYM COM_POWER; ARITH_RULE `SUC ((l:num) + (r:num) + 1) = l + r + 2`]
   THEN USE_THEN "F17" (fun th -> REWRITE_TAC[th])
   THEN DISCH_THEN ASSUME_TAC
   THEN MP_TAC (SPECL[`e':A->A`; `(l:num) + (r:num) + 2`; `z:A`] orbit_cyclic)
   THEN POP_ASSUM(fun th -> REWRITE_TAC[th; ARITH_RULE `~((l:num) + (r:num) + 2 = 0)`])
   THEN DISCH_THEN SUBST1_TAC
   THEN USE_THEN "H1" (fun th1 -> (USE_THEN "H2"(fun th2 -> (MP_TAC (SPEC `z:A` (MATCH_MP lemma_cycle_orbit (CONJ th1 th2)))))))
   THEN USE_THEN "F5" (fun th -> REWRITE_TAC[th])
   THEN DISCH_THEN ASSUME_TAC
   THEN MP_TAC (SPECL[`e:A->A`; `(r:num) + 2`; `z:A`] orbit_cyclic)
   THEN POP_ASSUM(fun th -> REWRITE_TAC[th; ARITH_RULE `~((r:num) + 2 = 0)`])
   THEN DISCH_THEN SUBST1_TAC
   THEN USE_THEN "H1" (fun th1 -> (USE_THEN "H2"(fun th2 -> (MP_TAC (SPEC `y:A` (MATCH_MP lemma_cycle_orbit (CONJ th1 th2)))))))
   THEN USE_THEN "F9" (fun th -> REWRITE_TAC[th])
   THEN DISCH_THEN ASSUME_TAC
   THEN MP_TAC (SPECL[`e:A->A`; `(l:num) + 1`; `y:A`] orbit_cyclic)
   THEN POP_ASSUM(fun th -> REWRITE_TAC[th; ARITH_RULE `~((l:num) + 1 = 0)`])
   THEN DISCH_THEN SUBST1_TAC
   THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_SING; IN_ELIM_THM]
   THEN STRIP_TAC THEN EQ_TAC
   THENL[STRIP_TAC
     THENL[DISJ1_TAC THEN EXISTS_TAC `(r:num)+1`
	     THEN POP_ASSUM (fun th -> REWRITE_TAC[ARITH_RULE `(r:num) + 1 < r + 2`; th])
	     THEN USE_THEN "F11" (fun th -> REWRITE_TAC[SYM th]); ALL_TAC]
     THEN POP_ASSUM SUBST1_TAC
     THEN ASM_CASES_TAC `k:num <= r:num`
     THENL[DISJ1_TAC THEN EXISTS_TAC `k:num`
	     THEN FIND_ASSUM (fun th -> (REWRITE_TAC[MP (ARITH_RULE `k:num <= (r:num) ==> k < r + 2`) th])) `k:num <= r:num`
	     THEN USE_THEN "F15" (MP_TAC o SPEC `k:num`)
	     THEN POP_ASSUM (fun th -> REWRITE_TAC[th])
	     THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th]); ALL_TAC]
     THEN DISJ2_TAC
     THEN POP_ASSUM MP_TAC
     THEN GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [NOT_LE; LT_EXISTS]
     THEN REWRITE_TAC[ADD1]
     THEN DISCH_THEN (X_CHOOSE_THEN `d:num` SUBST_ALL_TAC)
     THEN POP_ASSUM (fun th -> (ASSUME_TAC (MATCH_MP (ARITH_RULE `(r:num)+(d:num) + 1 < (l:num) + r + 2 ==> d < l + 1`) th)))
     THEN EXISTS_TAC `d:num`
     THEN FIND_ASSUM (fun th -> REWRITE_TAC[th]) `d:num < (l:num) + 1`
     THEN POP_ASSUM (fun th -> ASSUME_TAC (MATCH_MP (ARITH_RULE `d:num < (l:num) + 1 ==> d <= l`) th))
     THEN REWRITE_TAC[ARITH_RULE `(r:num)+(d:num) + 1 = d + (r + 1)`]
     THEN MP_TAC(SPECL[`e':A->A`; `d:num`; `(r:num) +1`; `z:A`] lemma_add_exponent_function)
     THEN USE_THEN "F19" SUBST1_TAC
     THEN DISCH_THEN SUBST1_TAC
     THEN USE_THEN "F16" (MP_TAC o SPEC `d:num`)
     THEN POP_ASSUM(fun th-> REWRITE_TAC[th])
     THEN DISCH_THEN(fun th -> REWRITE_TAC[SYM th]); ALL_TAC]
   THEN STRIP_TAC 
   THENL[ASM_CASES_TAC `k:num = (r:num) + 1`
       THENL[POP_ASSUM SUBST_ALL_TAC
	       THEN POP_ASSUM MP_TAC
	       THEN USE_THEN "F11" SUBST1_TAC
	       THEN SIMP_TAC[]; ALL_TAC]
       THEN DISJ2_TAC THEN EXISTS_TAC `k:num`
       THEN MP_TAC(ARITH_RULE `k:num < (r:num) + 2 ==> k < l + r + 2`)
       THEN FIND_ASSUM (fun th -> REWRITE_TAC[th]) `k:num < (r:num) + 2`
       THEN DISCH_THEN (fun th -> REWRITE_TAC[th])
       THEN UNDISCH_THEN `k:num < (r:num) + 2` (fun th1 -> (POP_ASSUM (fun th2 -> (MP_TAC (MATCH_MP (ARITH_RULE `k:num < (r:num) + 2 /\ ~(k = r+1) ==> k <= r`) (CONJ th1 th2))))))
       THEN POP_ASSUM SUBST1_TAC
       THEN DISCH_TAC
       THEN USE_THEN "F15" (MP_TAC o SPEC `k:num`)
       THEN POP_ASSUM(fun th -> REWRITE_TAC[th]); ALL_TAC]
   THEN DISJ2_TAC THEN EXISTS_TAC `(k:num)+ (r:num) +1`
  THEN POP_ASSUM SUBST1_TAC
  THEN MP_TAC (ARITH_RULE `(k:num) < (l:num) + 1 ==> k + (r:num) + 1 < l + r + 2`)
  THEN FIND_ASSUM (fun th-> REWRITE_TAC[th]) `k:num < (l:num) + 1`
  THEN DISCH_THEN (fun th -> REWRITE_TAC[th])
  THEN POP_ASSUM (fun th -> ASSUME_TAC (MP (ARITH_RULE `k:num < (l:num) + 1 ==> k <= l`) th))
  THEN USE_THEN "F16" (MP_TAC o SPEC `k:num`)
  THEN POP_ASSUM (fun th -> REWRITE_TAC[th])
  THEN DISCH_THEN SUBST1_TAC
  THEN USE_THEN "F19" (SUBST1_TAC o SYM)
  THEN REWRITE_TAC[GSYM lemma_add_exponent_function]);;


(* splitting case *)


let lemma_edge_split = prove(`!(H:(A)hypermap) (x:A). x IN dart H /\ is_edge_split H x 
   ==> (~((inverse(face_map H)) x IN edge (edge_walkup H x) (node_map H x))) /\
 (edge H x = {x} UNION (edge (edge_walkup H x) (node_map H x)) UNION (edge (edge_walkup H x) ((inverse (face_map H)) x)))`,
  REPEAT GEN_TAC THEN  REWRITE_TAC[is_edge_split; dart_nondegenerate; edge]
  THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "S1") (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "S2") (CONJUNCTS_THEN2 (LABEL_TAC "S3") (LABEL_TAC "S4"))) (LABEL_TAC "S5")))
 THEN label_hypermap_TAC `H:(A)hypermap`
  THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
  THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` 
  THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` 
  THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
  THEN ABBREV_TAC `G = edge_walkup (H:(A)hypermap) (x:A)` 
  THEN ABBREV_TAC `D' = dart (G:(A)hypermap)`
  THEN ABBREV_TAC `e' = edge_map (G:(A)hypermap)`
  THEN MP_TAC (SPECL[`e:A->A`; `1`; `x:A`; `(e:A->A) (x:A)`] in_orbit_lemma)
  THEN REWRITE_TAC[POWER_1]
  THEN DISCH_THEN (LABEL_TAC "F1")
  THEN MP_TAC(SPECL[`D:A->bool`; `e:A->A`; `x:A`] INVERSE_EVALUATION)
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (X_CHOOSE_THEN `j:num`((LABEL_TAC "F2") o MATCH_MP in_orbit_lemma ))
  THEN LABEL_TAC "F3" (SPECL[`e:A->A`; `x:A`] orbit_reflect)
  THEN USE_THEN "H1"(fun th1 -> (USE_THEN "H2" (fun th2 -> (LABEL_TAC "F4" (SPEC `x:A` (MATCH_MP lemma_orbit_finite (CONJ th1 th2)))))))
  THEN MP_TAC (SPECL[`orbit_map (e:A->A) (x:A)`; `x:A`; `(e:A->A) (x:A)`] CARD_ATLEAST_2)
  THEN ASM_REWRITE_TAC[LE_EXISTS; ADD_SYM]
  THEN DISCH_THEN (X_CHOOSE_THEN `r:num` (LABEL_TAC "F5"))
  THEN MP_TAC (SPECL[`e:A->A`; `1`; `(n:A->A) (x:A)`; `(inverse (f:A->A)) (x:A)`] in_orbit_lemma)
  THEN REWRITE_TAC[POWER_1]
  THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [POWER_1; GSYM o_THM]
  THEN MP_TAC (CONJUNCT2(CONJUNCT2(SPEC `H:(A)hypermap` inverse_hypermap_maps)))
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (SUBST1_TAC o SYM)
  THEN REWRITE_TAC[]
  THEN DISCH_THEN (fun th1 -> (USE_THEN "S5" (fun th2 -> (LABEL_TAC "F6" (MATCH_MP orbit_trans (CONJ th1 th2))))))
  THEN MP_TAC(SPECL[`D:A->bool`; `e:A->A`; `(x:A)`;  `(e:A->A) (x:A)`] lemma_orbit_identity)
  THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC
  THEN MP_TAC (SPECL[`D:A->bool`; `e:A->A`; `(e:A->A) (x:A)`] lemma_cycle_orbit)
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (fun th -> (LABEL_TAC "F7" th  THEN MP_TAC th))
  THEN REWRITE_TAC[ARITH_RULE `(r:num)+2 = SUC (r+1)`]
  THEN DISCH_THEN (MP_TAC o AP_TERM `inverse (e:A->A)`)
  THEN MP_TAC(SPECL[`D:A->bool`; `e:A->A`; `(e:A->A) (x:A)`; `(r:num)+1`] INVERSE_POWER_EVALUATION)
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN SUBST1_TAC
  THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_THM] 
  THEN USE_THEN "H2" (fun th-> (REWRITE_TAC[CONJUNCT2 (MATCH_MP PERMUTES_INVERSES_o th); I_THM]))
  THEN DISCH_THEN (fun th -> (LABEL_TAC "F8" th THEN MP_TAC th))
  THEN REWRITE_TAC[GSYM ADD1] THEN DISCH_THEN (MP_TAC o AP_TERM `inverse (e:A->A)`)
  THEN MP_TAC(SPECL[`D:A->bool`; `e:A->A`; `(e:A->A) (x:A)`; `r:num`] INVERSE_POWER_EVALUATION)
  THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC
  THEN DISCH_THEN (LABEL_TAC "F9")
  THEN MP_TAC (SPECL[`e:A->A`; `(r:num) + 2`; `(e:A->A) (x:A)`] orbit_cyclic)
  THEN USE_THEN "F7" (fun th -> REWRITE_TAC[th; ARITH_RULE `~((r:num) + 2 = 0)`])
  THEN DISCH_THEN (LABEL_TAC "F10")
  THEN SUBGOAL_THEN `?m:num d:num. (r:num) = m + d + 1 /\ ((e:A->A) POWER m) ((e:A->A) (x:A)) = (n:A->A) (x:A)` ASSUME_TAC
  THENL[USE_THEN "S5" MP_TAC
	THEN POP_ASSUM (fun th -> REWRITE_TAC[th])
	THEN REWRITE_TAC[IN_ELIM_THM]
	THEN DISCH_THEN (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)
	THEN UNDISCH_TAC `m:num < (r:num) + 2`
	THEN REWRITE_TAC[LT_EXISTS]
	THEN DISCH_THEN (X_CHOOSE_THEN `n:num` MP_TAC)
	THEN REWRITE_TAC[ADD1; ARITH_RULE `(r:num) + 2 = (m:num) + (n:num) + 1 <=> r + 1 = m + n`]
	THEN ASM_CASES_TAC `n = 0`
        THENL[POP_ASSUM SUBST1_TAC
		THEN REWRITE_TAC[ADD_0]
		THEN DISCH_THEN (SUBST_ALL_TAC o SYM)
		THEN POP_ASSUM MP_TAC
		THEN USE_THEN "F8" (fun th -> REWRITE_TAC[th])
		THEN USE_THEN "S3" (fun th -> REWRITE_TAC[th]); ALL_TAC]
	THEN POP_ASSUM MP_TAC
	THEN REWRITE_TAC[GSYM LT_NZ; LT_EXISTS; ADD1; ADD]
	THEN DISCH_THEN (X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC)
	THEN REWRITE_TAC[ARITH_RULE `(r:num)+1 = (m:num) + (n1:num) + 1 <=> r = m + n1`]
	THEN ASM_CASES_TAC `n1 = 0`
        THENL[POP_ASSUM SUBST1_TAC
		THEN REWRITE_TAC[ADD_0]
		THEN DISCH_THEN SUBST_ALL_TAC
		THEN POP_ASSUM MP_TAC
		THEN POP_ASSUM SUBST1_TAC
		THEN MP_TAC(SPECL[`H:(A)hypermap`; `x:A`] lemma_face_degenarate)
		THEN ASM_SIMP_TAC[]; ALL_TAC]
	THEN POP_ASSUM MP_TAC
	THEN REWRITE_TAC[GSYM LT_NZ; LT_EXISTS; ADD1; ADD]
	THEN DISCH_THEN (X_CHOOSE_THEN `d:num` SUBST_ALL_TAC)
	THEN DISCH_THEN ASSUME_TAC
	THEN EXISTS_TAC `m:num` THEN EXISTS_TAC `d:num`
	THEN ASM_REWRITE_TAC[]; ALL_TAC]
   THEN POP_ASSUM (X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `d:num` (CONJUNCTS_THEN2 (MP_TAC) (LABEL_TAC "F11"))))
   THEN REWRITE_TAC[ARITH_RULE `(m:num) + (d:num) + 1 = d + m + 1`]
   THEN DISCH_THEN SUBST_ALL_TAC
   THEN USE_THEN "F11" (MP_TAC o AP_TERM `e:A->A`)
   THEN REWRITE_TAC[iterate_map_valuation; ADD1]
   THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_THM]
   THEN MP_TAC(CONJUNCT2(CONJUNCT2(SPEC `H:(A)hypermap` inverse_hypermap_maps)))
   THEN ASM_REWRITE_TAC[]
   THEN DISCH_THEN (SUBST1_TAC o SYM)
   THEN DISCH_THEN (LABEL_TAC "F12")
   THEN ABBREV_TAC `y:A = (inverse (f:A->A)) (x:A)`
   THEN USE_THEN "F12" (MP_TAC o SYM o AP_TERM `(e:A->A) POWER (d:num)`)
   THEN MP_TAC (SPECL[`e:A->A`; `d:num`; `(m:num) +1`; `(e:A->A) (x:A)`] lemma_add_exponent_function)
   THEN DISCH_THEN (SUBST1_TAC o SYM)
   THEN ASM_REWRITE_TAC[]
   THEN DISCH_THEN (LABEL_TAC "F14")
   THEN SUBST_ALL_TAC (ARITH_RULE `((d:num) +(m:num) + 1)+1 = d + m + 2`)
   THEN SUBST_ALL_TAC (ARITH_RULE `((d:num) +(m:num) + 1)+2 = d + m + 3`)
   THEN ABBREV_TAC `z = (e:A->A) (x:A)`
   THEN USE_THEN "H1" (fun th1 -> (USE_THEN "H2" (fun th2 -> (MP_TAC (SPECL[`(e:A->A) (x:A)`] (MATCH_MP lemma_segment_orbit (CONJ th1 th2)))))))
   THEN FIND_ASSUM (fun th -> REWRITE_TAC[th]) `(e:A->A) (x:A) = z:A`
   THEN ASM_REWRITE_TAC[]
   THEN DISCH_THEN (LABEL_TAC "FINJ")
   THEN SUBGOAL_THEN `!v:num. v <= m:num ==> (e POWER v) (z:A) = (e' POWER v) z` (LABEL_TAC "F15")
   THENL[INDUCT_TAC THENL[REWRITE_TAC[LE_0; POWER]; ALL_TAC]
     THEN DISCH_THEN (LABEL_TAC "G1")
     THEN FIRST_X_ASSUM (MP_TAC o check(is_imp o concl))
     THEN USE_THEN "G1"(fun th -> REWRITE_TAC[MATCH_MP (ARITH_RULE `SUC (v:num) <= r:num ==> v <= r`) th])
     THEN DISCH_THEN ((LABEL_TAC "G2") o SYM)    
     THEN USE_THEN "FINJ" (MP_TAC o SPEC `(d:num) + (m:num)+1`)
     THEN REWRITE_TAC[ARITH_RULE `(d:num) + (m:num)+1 < d+ m + 3`]
     THEN REWRITE_TAC[lemma_def_inj_orbit]
     THEN DISCH_THEN (MP_TAC o SPECL[`(d:num) + (m:num)+1`; `v:num`])
     THEN ASM_REWRITE_TAC[LE_REFL]
     THEN USE_THEN "G1" (fun th -> REWRITE_TAC[MP (ARITH_RULE `SUC (v:num) <= (m:num) ==> v < (d:num) + m + 1`) th])
     THEN DISCH_THEN (ASSUME_TAC o GSYM)
     THEN USE_THEN "FINJ" (MP_TAC o SPEC `m:num`)
     THEN REWRITE_TAC[ARITH_RULE `m:num < (d:num) + m + 3`]
     THEN REWRITE_TAC[lemma_def_inj_orbit]
     THEN DISCH_THEN (MP_TAC o SPECL[`m:num`; `v:num`])
     THEN ASM_REWRITE_TAC[LE_REFL]
     THEN USE_THEN "G1" (fun th -> REWRITE_TAC[MP (ARITH_RULE `SUC (v:num) <= (m:num) ==> v < m`) th])
     THEN DISCH_THEN (ASSUME_TAC o GSYM)
     THEN USE_THEN "FINJ" (MP_TAC o SPEC `(d:num) + (m:num) + 2`)
     THEN REWRITE_TAC[ARITH_RULE `(d:num) + (m:num) + 2 < d + m + 3`]
     THEN REWRITE_TAC[lemma_def_inj_orbit]
     THEN DISCH_THEN (MP_TAC o SPECL[`(d:num) + (m:num) + 2`; `v:num`])
     THEN ASM_REWRITE_TAC[LE_REFL]
     THEN USE_THEN "G1" (fun th -> REWRITE_TAC[MP (ARITH_RULE `SUC (v:num) <= (m:num) ==> v < (d:num) + m + 2`) th])
     THEN DISCH_THEN (ASSUME_TAC o GSYM)
     THEN MP_TAC (CONJUNCT2(CONJUNCT2(CONJUNCT2(SPECL[`H:(A)hypermap`; `x:A`; `((e:A->A) POWER (v:num)) (e (x:A))`] edge_map_walkup))))
     THEN ASM_REWRITE_TAC[]
     THEN REWRITE_TAC[iterate_map_valuation]
     THEN USE_THEN "G2" (SUBST1_TAC o SYM)
     THEN REWRITE_TAC[iterate_map_valuation]
     THEN DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC]
   THEN SUBGOAL_THEN `!v:num. v <= d:num ==> ((e:A->A) POWER v) (y:A) = ((e':A->A) POWER v) y` (LABEL_TAC "F16")
   THENL[INDUCT_TAC THENL[REWRITE_TAC[LE_0; POWER]; ALL_TAC]
   THEN DISCH_THEN (LABEL_TAC "G1")
   THEN FIRST_X_ASSUM (MP_TAC o check(is_imp o concl))
   THEN USE_THEN "G1"(fun th -> REWRITE_TAC[MATCH_MP (ARITH_RULE `SUC (v:num) <= d:num ==> v <= d`) th])
   THEN DISCH_THEN ((LABEL_TAC "G2") o SYM)
   THEN USE_THEN "FINJ" (MP_TAC o SPEC `(v:num) + (m:num) + 1`)
   THEN USE_THEN "G1" (fun th -> REWRITE_TAC[MATCH_MP (ARITH_RULE `SUC (v:num) <= d:num ==> v + (m:num) + 1 < d + m + 3`) th])
   THEN REWRITE_TAC[lemma_def_inj_orbit]
   THEN DISCH_THEN (MP_TAC o SPECL[`(v:num)+(m:num) + 1`; `m:num`])
   THEN ASM_REWRITE_TAC[LE_REFL]
   THEN ASM_REWRITE_TAC[ARITH_RULE `m:num < (v:num) + m + 1 /\ m + 1 = SUC m`]
   THEN REWRITE_TAC[lemma_add_exponent_function]
   THEN ASM_REWRITE_TAC[ADD1]
   THEN DISCH_TAC
   THEN USE_THEN "FINJ" (MP_TAC o SPEC `(d:num) + (m:num) + 1`)
   THEN REWRITE_TAC[ARITH_RULE `d + (m:num) + 1 < d + m + 3`]
   THEN REWRITE_TAC[lemma_def_inj_orbit]
   THEN DISCH_THEN (MP_TAC o SPECL[`(d:num)+(m:num) + 1`; `(v:num)+(m:num) + 1`])
   THEN ASM_REWRITE_TAC[LE_REFL]
   THEN USE_THEN "G1" (fun th -> REWRITE_TAC[MATCH_MP (ARITH_RULE `SUC (v:num) <= d ==> (v:num) + m + 1 < d + m + 1`) th])
   THEN REWRITE_TAC[GSYM ADD1]
   THEN REWRITE_TAC[lemma_add_exponent_function]
   THEN ASM_REWRITE_TAC[ADD1]
   THEN DISCH_THEN (ASSUME_TAC o GSYM)
   THEN USE_THEN "FINJ" (MP_TAC o SPEC `(d:num) + (m:num) + 2`)
   THEN REWRITE_TAC[ARITH_RULE `d + (m:num) + 2 < d + m + 3`]
   THEN REWRITE_TAC[lemma_def_inj_orbit]
   THEN DISCH_THEN (MP_TAC o SPECL[`(d:num)+(m:num) + 2`; `(v:num)+(m:num) + 1`])
   THEN ASM_REWRITE_TAC[LE_REFL]
   THEN USE_THEN "G1" (fun th -> REWRITE_TAC[MATCH_MP (ARITH_RULE `SUC (v:num) <= d ==> (v:num) + m + 1 < d + m + 2`) th])
   THEN REWRITE_TAC[GSYM ADD1]
   THEN REWRITE_TAC[lemma_add_exponent_function]
   THEN ASM_REWRITE_TAC[ADD1]
   THEN DISCH_THEN (ASSUME_TAC o GSYM)
   THEN REWRITE_TAC[GSYM ADD1]
   THEN MP_TAC (CONJUNCT2(CONJUNCT2(CONJUNCT2(SPECL[`H:(A)hypermap`; `x:A`; `((e:A->A) POWER (v:num) ) (y:A)`] edge_map_walkup))))
   THEN ASM_REWRITE_TAC[]
   THEN REWRITE_TAC[COM_POWER; o_THM]
   THEN USE_THEN "G2" (SUBST1_TAC)
   THEN DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC]
   THEN MP_TAC (CONJUNCT1(CONJUNCT2(SPECL[`H:(A)hypermap`; `x:A`; `((e:A->A) POWER (m:num)) (x:A)`] edge_map_walkup)))
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (LABEL_TAC "F17")
  THEN MP_TAC (CONJUNCT1(CONJUNCT2(CONJUNCT2(SPECL[`H:(A)hypermap`; `x:A`; `((e:A->A) POWER ((d:num) + (m:num) + 1)) (x:A)`] edge_map_walkup))))
  THEN ASM_REWRITE_TAC[]
  THEN EXPAND_TAC "y"
  THEN USE_THEN "H2" (fun th -> (MP_TAC(SPEC `x:A` (MATCH_MP non_fixed_point_lemma th))))
  THEN USE_THEN "H4" (fun th -> (MP_TAC(SPEC `x:A` (MATCH_MP non_fixed_point_lemma th))))
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (fun th -> REWRITE_TAC[th])
  THEN DISCH_THEN (fun th -> REWRITE_TAC[th])
  THEN DISCH_THEN (LABEL_TAC "F18")
  THEN MP_TAC (SPEC `G:(A)hypermap` hypermap_lemma)
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F19") (LABEL_TAC "F20" o CONJUNCT1))
  THEN MP_TAC(SPECL[`e':A->A`; `1`; `(n:A->A) (x:A)`; `z:A`] in_orbit_lemma)
  THEN REWRITE_TAC[POWER_1]
  THEN USE_THEN "F17" (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o  DEPTH_CONV) [SYM th])
  THEN REWRITE_TAC[]
  THEN DISCH_THEN (fun th1 -> (USE_THEN "F19" (fun th2 -> (USE_THEN "F20" (fun th3 -> (MP_TAC (MATCH_MP lemma_orbit_identity (CONJ th2 (CONJ th3 th1)))))))))
  THEN DISCH_THEN SUBST1_TAC
   THEN USE_THEN "F16" (MP_TAC o GSYM o SPEC `d:num`)
   THEN REWRITE_TAC[LE_REFL]
   THEN DISCH_THEN (MP_TAC o AP_TERM `e':A->A`)
   THEN ASM_REWRITE_TAC[iterate_map_valuation; ADD1]
   THEN DISCH_TAC
   THEN MP_TAC(SPECL[`e':A->A`; `(d:num) + 1`; `y:A`] orbit_cyclic)
   THEN POP_ASSUM (fun th -> REWRITE_TAC[th; ARITH_RULE `~((d:num) + 1 = 0)`])
   THEN DISCH_THEN SUBST_ALL_TAC
   THEN USE_THEN "F15" (MP_TAC o GSYM o SPEC `m:num`)
   THEN REWRITE_TAC[LE_REFL]
   THEN DISCH_THEN (MP_TAC o AP_TERM `e':A->A`)
   THEN ASM_REWRITE_TAC[iterate_map_valuation; ADD1]
   THEN DISCH_TAC
   THEN MP_TAC(SPECL[`e':A->A`; `(m:num) + 1`; `z:A`] orbit_cyclic)
   THEN POP_ASSUM (fun th -> REWRITE_TAC[th; ARITH_RULE `~((m:num) + 1 = 0)`])
   THEN DISCH_THEN SUBST_ALL_TAC
   THEN STRIP_TAC
   THENL[REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM]
	   THEN REPEAT STRIP_TAC
	   THEN USE_THEN "FINJ" (MP_TAC o SPEC `(m:num) + 1`)
	   THEN REWRITE_TAC[ARITH_RULE `(m:num) + 1 < (d:num) + m + 3`]
	   THEN REWRITE_TAC[GSYM ADD1; inj_orbit]
	   THEN DISCH_TAC
	   THEN POP_ASSUM (MP_TAC o SPEC `k:num` o CONJUNCT2)
	   THEN FIND_ASSUM (fun th -> REWRITE_TAC[ADD1; MATCH_MP (ARITH_RULE `k:num < (m:num) + 1 ==> k <= m`) th]) `k:num < (m:num)+ 1`
	   THEN USE_THEN "F12" (fun th -> REWRITE_TAC[th])
	   THEN USE_THEN "F15" (MP_TAC o SPEC `k:num`)
	   THEN FIND_ASSUM (fun th -> REWRITE_TAC[MATCH_MP (ARITH_RULE `k:num < (m:num) + 1 ==> k <= m`) th]) `k:num < (m:num)+ 1`
	   THEN DISCH_THEN SUBST1_TAC
	   THEN POP_ASSUM(fun th -> REWRITE_TAC[th]); ALL_TAC]
   THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; IN_SING ]
   THEN GEN_TAC THEN EQ_TAC
   THENL[DISCH_THEN (X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 (LABEL_TAC "F30") (LABEL_TAC "F31")))
	  THEN ASM_CASES_TAC `k:num < (m:num) + 1`
	  THENL[POP_ASSUM (LABEL_TAC "F32")
		  THEN  DISJ2_TAC THEN DISJ1_TAC
		  THEN  EXISTS_TAC `k:num`
		  THEN  USE_THEN "F32" ( fun th -> REWRITE_TAC[th])
		  THEN  USE_THEN "F31" ( fun th -> REWRITE_TAC[th])
		  THEN  USE_THEN "F15" (MP_TAC o SPEC `k:num`)
		  THEN  USE_THEN "F32" (fun th -> REWRITE_TAC[MP (ARITH_RULE `k:num < (m:num) + 1 ==> k <= m`) th]); ALL_TAC]
	  THEN  ASM_CASES_TAC `k:num <=(d:num) + (m:num) + 1`
          THENL[DISJ2_TAC THEN DISJ2_TAC
		  THEN  UNDISCH_TAC `~((k:num) < (m:num) + 1)`
		  THEN  REWRITE_TAC[NOT_LT; LE_EXISTS]
		  THEN DISCH_THEN (X_CHOOSE_THEN `v:num` MP_TAC)
		  THEN REWRITE_TAC[ARITH_RULE `((m:num)+1) +(v:num) = v + m + 1`]
		  THEN POP_ASSUM (fun th -> (DISCH_THEN (fun th2 -> ((LABEL_TAC "F33" th2) THEN (LABEL_TAC "F34" (MP (ARITH_RULE `k:num <= (d:num) + (m:num) + 1 /\ k = (v:num) + m + 1 ==> v <= d`) (CONJ th th2)))))))
		  THEN EXISTS_TAC `v:num`
		  THEN USE_THEN "F34" ( fun th -> REWRITE_TAC[MP (ARITH_RULE `v:num <= d:num ==> v < d + 1`)th])
		  THEN USE_THEN "F16" (MP_TAC o SPEC `v:num`)
		  THEN USE_THEN "F34" (fun th -> REWRITE_TAC[th])
		  THEN DISCH_THEN (SUBST1_TAC o SYM)
		  THEN USE_THEN "F12" (SUBST1_TAC o SYM)
		  THEN REWRITE_TAC[GSYM ADD1]
		  THEN REWRITE_TAC[GSYM lemma_add_exponent_function; ADD1]
		  THEN USE_THEN "F33" (SUBST1_TAC o SYM)
		  THEN USE_THEN "F31" (fun th -> REWRITE_TAC[th]); ALL_TAC]
	  THEN DISJ1_TAC
	  THEN REMOVE_THEN "F30" (fun th1 -> (POP_ASSUM (fun th2 -> (ASSUME_TAC (MATCH_MP (ARITH_RULE `~(k:num <= (d:num) + (m:num) + 1) /\ k < d + m + 3 ==> k = d + m + 2`) (CONJ th2 th1))))))
	  THEN REMOVE_THEN "F31" MP_TAC
	  THEN POP_ASSUM SUBST1_TAC
	  THEN USE_THEN "F8" (fun th -> REWRITE_TAC[th]); ALL_TAC]
   THEN STRIP_TAC 
   THENL[EXISTS_TAC `(d:num) + (m:num) + 2`
	   THEN POP_ASSUM SUBST1_TAC 
	   THEN USE_THEN "F8" SUBST1_TAC
	   THEN ARITH_TAC;
           EXISTS_TAC `k:num`
	   THEN POP_ASSUM SUBST1_TAC
	   THEN FIND_ASSUM (fun th -> REWRITE_TAC[MP (ARITH_RULE `k:num < (m:num) + 1 ==> k < (d:num) + m + 3`) th]) `k:num < (m:num) + 1`
           THEN USE_THEN "F15" (MP_TAC o SPEC `k:num`)
	   THEN POP_ASSUM (fun th -> REWRITE_TAC[MP (ARITH_RULE `k:num < (m:num) + 1 ==> k <= m`) th])
	   THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th]);
           EXISTS_TAC `(k:num) + (m:num) + 1` 
           THEN FIND_ASSUM (fun th -> REWRITE_TAC[MP (ARITH_RULE `(k:num) < (d:num) + 1 ==> k + (m:num) + 1 < d + m + 3`) th]) `k:num < (d:num) + 1`
           THEN REWRITE_TAC[GSYM ADD1]
	   THEN REWRITE_TAC[lemma_add_exponent_function]
	   THEN REWRITE_TAC[ADD1]
	   THEN USE_THEN "F12" SUBST1_TAC
	   THEN POP_ASSUM SUBST1_TAC
	   THEN USE_THEN "F16" (MP_TAC o SPEC `k:num`)
	   THEN POP_ASSUM (fun th -> REWRITE_TAC[MP (ARITH_RULE `(k:num) < (d:num) + 1 ==> k <= d`) th])
	   THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th])]);;


(* Node *)


let lemma_shift_non_degenerate = prove(`!(H:(A)hypermap) (x:A). dart_nondegenerate H x <=>  dart_nondegenerate (shift H) x`,
    REPEAT GEN_TAC THEN REWRITE_TAC[dart_nondegenerate]
    THEN STRIP_ASSUME_TAC (SPEC `H:(A)hypermap` (GSYM shift_lemma))
    THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;


let lemma_change_node_walkup = prove(`!(H:(A)hypermap) (x:A). (is_node_merge H x ==> is_edge_merge (shift H) x) /\ (is_node_split H x ==> is_edge_split (shift H) x)`,
REPEAT GEN_TAC
  THEN STRIP_ASSUME_TAC (SPEC `H:(A)hypermap` (GSYM shift_lemma))
  THEN ASM_REWRITE_TAC[is_node_merge; is_edge_merge; is_node_split; is_edge_split; edge; node]
  THEN STRIP_TAC
  THENL[STRIP_TAC
	  THEN ONCE_ASM_REWRITE_TAC[GSYM lemma_shift_non_degenerate]
	  THEN ASM_REWRITE_TAC[]; ALL_TAC]
  THEN STRIP_TAC
  THEN ONCE_ASM_REWRITE_TAC[GSYM lemma_shift_non_degenerate]
  THEN ASM_REWRITE_TAC[]);;


let lemma_node_merge = prove(`!(H:(A)hypermap) (x:A). x IN dart H /\ is_node_merge H x 
   ==> {x} UNION (node (node_walkup H x) (face_map H x)) = (node H x) UNION (node H (face_map H x))`,
  REPEAT GEN_TAC
  THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F1") (ASSUME_TAC))
  THEN REWRITE_TAC[node_walkup] 
  THEN MP_TAC (CONJUNCT1 (SPECL[`H:(A)hypermap`; `x:A`] lemma_change_node_walkup))
  THEN POP_ASSUM (fun th -> REWRITE_TAC[th])
  THEN DISCH_THEN (LABEL_TAC "F2")
  THEN label_4Gs_TAC (SPEC `H:(A)hypermap` (GSYM shift_lemma))
  THEN REMOVE_THEN "F1" MP_TAC
  THEN USE_THEN "G1" (SUBST1_TAC o SYM)
  THEN DISCH_THEN (LABEL_TAC "F3")
  THEN MP_TAC(SPECL[`shift (H:(A)hypermap)`; `x:A`] lemma_edge_merge)
  THEN ASM_REWRITE_TAC[node; edge]
  THEN STRIP_ASSUME_TAC (GSYM (SPEC `edge_walkup (shift(H:(A)hypermap)) (x:A)` double_shift_lemma))
  THEN ASM_REWRITE_TAC[]);;


let lemma_node_split = prove(`!(H:(A)hypermap) (x:A). x IN dart H /\ is_node_split H x 
   ==> (~((inverse(edge_map H)) x IN node (node_walkup H x) (face_map H x))) /\
 (node H x = {x} UNION (node (node_walkup H x) (face_map H x)) UNION (node (node_walkup H x) ((inverse (edge_map H)) x)))`,
  
  REPEAT GEN_TAC
  THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F1") (ASSUME_TAC))
  THEN REWRITE_TAC[node_walkup] 
  THEN MP_TAC (CONJUNCT2 (SPECL[`H:(A)hypermap`; `x:A`] lemma_change_node_walkup))
  THEN POP_ASSUM (fun th -> REWRITE_TAC[th])
  THEN DISCH_THEN (LABEL_TAC "F2")
  THEN label_4Gs_TAC (SPEC `H:(A)hypermap` (GSYM shift_lemma))
  THEN REMOVE_THEN "F1" MP_TAC
  THEN USE_THEN "G1" (SUBST1_TAC o SYM)
  THEN DISCH_THEN (LABEL_TAC "F3")
  THEN MP_TAC(SPECL[`shift (H:(A)hypermap)`; `x:A`] lemma_edge_split)
  THEN ASM_REWRITE_TAC[node; edge]
  THEN STRIP_ASSUME_TAC (GSYM (SPEC `edge_walkup (shift(H:(A)hypermap)) (x:A)` double_shift_lemma))
  THEN ASM_REWRITE_TAC[]);;


(* face *)


let lemma_double_shift_non_degenerate = prove(`!(H:(A)hypermap) (x:A). dart_nondegenerate H x <=>  dart_nondegenerate (shift(shift H)) x`,
    REPEAT GEN_TAC THEN REWRITE_TAC[dart_nondegenerate]
    THEN STRIP_ASSUME_TAC (SPEC `H:(A)hypermap` (GSYM double_shift_lemma))
    THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;


let lemma_change_face_walkup = prove(`!(H:(A)hypermap) (x:A). (is_face_merge H x ==> is_edge_merge (shift(shift H)) x) /\ (is_face_split H x ==> is_edge_split (shift (shift H)) x)`,
REPEAT GEN_TAC
  THEN STRIP_ASSUME_TAC (SPEC `H:(A)hypermap` (GSYM double_shift_lemma))
  THEN ASM_REWRITE_TAC[is_face_merge; is_edge_merge; is_face_split; is_edge_split; edge; face]
  THEN STRIP_TAC
  THENL[STRIP_TAC
	  THEN ONCE_ASM_REWRITE_TAC[GSYM lemma_double_shift_non_degenerate]
	  THEN ASM_REWRITE_TAC[]; ALL_TAC]
  THEN STRIP_TAC
  THEN ONCE_ASM_REWRITE_TAC[GSYM lemma_double_shift_non_degenerate]
  THEN ASM_REWRITE_TAC[]);;

face_walkup;;

let lemma_face_merge = prove(`!(H:(A)hypermap) (x:A). x IN dart H /\ is_face_merge H x 
   ==> {x} UNION (face (face_walkup H x) (edge_map H x)) = (face H x) UNION (face H (edge_map H x))`,
  REPEAT GEN_TAC
  THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F1") (ASSUME_TAC))
  THEN REWRITE_TAC[face_walkup] 
  THEN MP_TAC (CONJUNCT1 (SPECL[`H:(A)hypermap`; `x:A`] lemma_change_face_walkup))
  THEN POP_ASSUM (fun th -> REWRITE_TAC[th])
  THEN DISCH_THEN (LABEL_TAC "F2")
  THEN label_4Gs_TAC (SPEC `H:(A)hypermap` (GSYM double_shift_lemma))
  THEN REMOVE_THEN "F1" MP_TAC
  THEN USE_THEN "G1" (SUBST1_TAC o SYM)
  THEN DISCH_THEN (LABEL_TAC "F3")
  THEN MP_TAC(SPECL[`shift(shift (H:(A)hypermap))`; `x:A`] lemma_edge_merge)
  THEN ASM_REWRITE_TAC[face; edge]
  THEN STRIP_ASSUME_TAC (GSYM (SPEC `edge_walkup (shift(shift(H:(A)hypermap))) (x:A)` shift_lemma))
  THEN ASM_REWRITE_TAC[]);;

let lemma_face_split = prove(`!(H:(A)hypermap) (x:A). x IN dart H /\ is_face_split H x 
   ==> (~((inverse(node_map H)) x IN face (face_walkup H x) (edge_map H x))) /\
 (face H x = {x} UNION (face (face_walkup H x) (edge_map H x)) UNION (face (face_walkup H x) ((inverse (node_map H)) x)))`,
  
  REPEAT GEN_TAC
  THEN DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "F1") (ASSUME_TAC))
  THEN REWRITE_TAC[face_walkup] 
  THEN MP_TAC (CONJUNCT2 (SPECL[`H:(A)hypermap`; `x:A`] lemma_change_face_walkup))
  THEN POP_ASSUM (fun th -> REWRITE_TAC[th])
  THEN DISCH_THEN (LABEL_TAC "F2")
  THEN label_4Gs_TAC (SPEC `H:(A)hypermap` (GSYM double_shift_lemma))
  THEN REMOVE_THEN "F1" MP_TAC
  THEN USE_THEN "G1" (SUBST1_TAC o SYM)
  THEN DISCH_THEN (LABEL_TAC "F3")
  THEN MP_TAC(SPECL[`shift(shift (H:(A)hypermap))`; `x:A`] lemma_edge_split)
  THEN ASM_REWRITE_TAC[face; edge]
  THEN STRIP_ASSUME_TAC (GSYM (SPEC `edge_walkup (shift(shift(H:(A)hypermap))) (x:A)` shift_lemma))
  THEN ASM_REWRITE_TAC[]);;


let lemmaFKSNTKR = prove(`!(H:(A)hypermap) (x:A). simple_hypermap H /\ x IN dart H /\ ~((edge_map H) x = x) /\ (dart_nondegenerate H x)
   /\ dart_nondegenerate H ((edge_map H) x) ==> ((edge_map H) ((edge_map H) x) = x ==> is_face_merge H x) /\ is_node_merge H x`,
  REPEAT GEN_TAC
  THEN REWRITE_TAC[simple_hypermap; dart_nondegenerate; is_face_merge; is_node_merge; node; face; o_THM]
  THEN STRIP_TAC
  THEN ASM_REWRITE_TAC[]
  THEN label_hypermap_TAC `H:(A)hypermap`
  THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
  THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` 
  THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` 
  THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
  THEN FIRST_X_ASSUM (MP_TAC o SPEC `(f:A->A) (x:A)` o check (is_forall o concl))
  THEN USE_THEN "H4" (MP_TAC o SYM o  SPEC `x:A` o MATCH_MP PERMUTES_IN_IMAGE)
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (fun th -> REWRITE_TAC[th])
  THEN DISCH_THEN (LABEL_TAC "FF")
  THEN STRIP_TAC
  THENL[USE_THEN "H2" (fun th2 -> (DISCH_THEN (fun th3 -> (MP_TAC(MATCH_MP inverse_function (CONJ th2 th3))))))
	  THEN MP_TAC(CONJUNCT1(SPEC `H:(A)hypermap` inverse_hypermap_maps))
	  THEN ASM_REWRITE_TAC[] 
	  THEN DISCH_THEN SUBST1_TAC
	  THEN REWRITE_TAC[o_THM]
	  THEN DISCH_TAC
	  THEN MP_TAC(SPECL[`n:A->A`; `1`;`(f:A->A) (x:A)`; `(e:A->A) (x:A)`] in_orbit_lemma)
	  THEN POP_ASSUM (fun th -> ((ASSUME_TAC (SYM th)) THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o DEPTH_CONV) [POWER_1; th]))
	  THEN SIMP_TAC[]
	  THEN DISCH_THEN (LABEL_TAC "F2")
	  THEN UNDISCH_TAC `~((n:A->A) ((e:A->A) (x:A)) = e x)`
	  THEN REWRITE_TAC[CONTRAPOS_THM]
	  THEN DISCH_THEN (LABEL_TAC "F3")
	  THEN MP_TAC(SPECL[`f:A->A`; `1`;`(x:A)`; `(f:A->A) (x:A)`] in_orbit_lemma)
	  THEN REWRITE_TAC[POWER_1]
	  THEN DISCH_THEN (fun th3 -> (USE_THEN "H1" (fun th1 -> (USE_THEN "H4" (fun th2 -> (MP_TAC (MATCH_MP lemma_orbit_identity (CONJ th1 (CONJ th2 th3)))))))))
	  THEN DISCH_THEN SUBST_ALL_TAC
	  THEN REMOVE_THEN "F2" (fun th1 -> (REMOVE_THEN "F3" (fun th2 -> MP_TAC (CONJ th1 th2))))
	  THEN REWRITE_TAC[GSYM IN_INTER]
	  THEN USE_THEN "FF"  SUBST1_TAC
	  THEN REWRITE_TAC[IN_SING]
	  THEN DISCH_THEN (MP_TAC o AP_TERM `n:A->A`)
	  THEN POP_ASSUM (fun th -> REWRITE_TAC[th]); ALL_TAC]
   THEN UNDISCH_TAC `~((f:A->A) (x:A) = x)`
   THEN REWRITE_TAC[CONTRAPOS_THM]
   THEN DISCH_TAC
   THEN USE_THEN "H1" (fun th1 -> (USE_THEN "H3" (fun th2 -> (MP_TAC (SPECL[`(f:A->A) (x:A)`; `x:A`] (MATCH_MP orbit_sym (CONJ th1 th2)))))))
   THEN POP_ASSUM (fun th -> REWRITE_TAC[th])
   THEN DISCH_THEN (LABEL_TAC "F8")
   THEN MP_TAC(SPECL[`f:A->A`; `1`; `x:A`;`(f:A->A) (x:A)`] in_orbit_lemma)
   THEN REWRITE_TAC[POWER_1]
   THEN DISCH_TAC
   THEN USE_THEN "H1" (fun th1 -> (USE_THEN "H4" (fun th2 -> (MP_TAC (SPECL[`(f:A->A) (x:A)`; `x:A`] (MATCH_MP orbit_sym (CONJ th1 th2)))))))
   THEN POP_ASSUM (fun th -> REWRITE_TAC[th])
   THEN DISCH_THEN (LABEL_TAC "F9")
   THEN REMOVE_THEN "F8" (fun th1 -> (REMOVE_THEN "F9" (fun th2 -> MP_TAC (CONJ th1 th2))))
   THEN REWRITE_TAC[GSYM IN_INTER]
   THEN POP_ASSUM SUBST1_TAC
   THEN REWRITE_TAC[IN_SING]
   THEN DISCH_THEN (fun th -> REWRITE_TAC[SYM th]));;


prioritize_real();;

