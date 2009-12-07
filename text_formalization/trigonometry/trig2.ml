
(* ========== QUANG TRUONG ========== *)
let cosV = new_definition` cosV u v = (u dot v) / (norm u * norm v) `;;
let sinV = new_definition` sinV u v = sqrt ( &1 - cosV u v pow 2 ) `;;


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

let PHA = REWRITE_TAC[ MESON[] ` (a/\b)/\c <=> a/\ b /\ c `; MESON[]`
a ==> b ==> c <=> a /\ b ==> c `];;

let NGOAC = REWRITE_TAC[ MESON[] ` a/\b/\c <=> (a/\b)/\c `];;

let DAO = NGOAC THEN REWRITE_TAC[ MESON[]` a /\ b <=> b /\ a`];;

let PHAT = REWRITE_TAC[ MESON[] ` (a\/b)\/c <=> a\/b\/c `];;

let NGOACT = REWRITE_TAC[ GSYM (MESON[] ` (a\/b)\/c <=> a\/b\/c `)];;

let KHANANG = PHA THEN REWRITE_TAC[ MESON[]` ( a\/ b ) /\ c <=> a /\ c \/ b /\ c `] THEN
REWRITE_TAC[ MESON[]` a /\ ( b \/ c ) <=> a /\ b \/ a /\ c `];;

let ATTACH thm = MATCH_MP (MESON[]` ! a b. ( a ==> b ) ==> ( a <=> a /\ b )`) thm;;

let NHANH tm = ONCE_REWRITE_TAC[ ATTACH (SPEC_ALL ( tm ))];;
let LET_TR = CONV_TAC (TOP_DEPTH_CONV let_CONV);;

let DOWN_TAC = REPEAT (FIRST_X_ASSUM MP_TAC) THEN REWRITE_TAC[IMP_IMP] THEN PHA;;
let IMP_IMP_TAC = REWRITE_TAC[GSYM IMP_IMP] ;;




let NOT_EQ_IMPCOS_ARC = prove(`~( v0 = (u:real^N) ) /\ ~ ( v0 = w ) ==> cos (arcV v0 u w) =
((u - v0) dot (w - v0)) / (norm (u - v0) * norm (w - v0))`,
REWRITE_TAC[GSYM VECTOR_SUB_EQ; GSYM NORM_EQ_0] THEN
NHANH (MESON[NORM_POS_LE]` ~(norm (x:real^N) = &0 ) ==> &0 <= norm x `) THEN
REWRITE_TAC[REAL_ARITH` ~ ( a = &0 ) /\ &0 <= a <=>
&0 < a `] THEN
SIMP_TAC[NORM_SUB] THEN
MP_TAC (SPECL[` u - (v0:real^N)`; `v0 - (w :real^N) `] NORM_CAUCHY_SCHWARZ_ABS) THEN
NHANH (REAL_LT_MUL) THEN PHA THEN
REWRITE_TAC[MESON[REAL_LE_DIV2_EQ; REAL_FIELD ` &0 < a ==> a / a = &1 `]` a <= b /\ l1 /\ l2 /\ &0 < b <=>
a / b <= &1 /\ l1 /\ l2 /\ &0 < b `] THEN
NHANH (MESON[REAL_LT_IMP_LE; REAL_ABS_REFL; REAL_ABS_DIV]`
abs b / a <= &1 /\ l1 /\ l2 /\ &0 < a ==>
abs ( b / a ) <= &1 `) THEN
ONCE_REWRITE_TAC[ GSYM REAL_ABS_NEG] THEN
REWRITE_TAC[REAL_ARITH` -- ( a / b ) = ( --a ) / b `;
VECTOR_ARITH` --((u - v0) dot (v0 - w)) = ((u - v0) dot (w - v0)) `] THEN
REWRITE_TAC[REAL_ABS_BOUNDS; arcV] THEN
SIMP_TAC[NORM_SUB] THEN MESON_TAC[COS_ACS]);;



let COLLINEAR_TRANSABLE = prove(
`collinear {(a:real^N), b, c} <=> collinear {vec 0, b - a, c - a}`,
REWRITE_TAC[collinear; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
[STRIP_TAC THEN EXISTS_TAC `u: real^N` THEN REPEAT GEN_TAC THEN
ASM_MESON_TAC[VECTOR_ARITH` ( a - c ) - ( b - c ) = a - (b:real^N)`;
VECTOR_SUB_REFL; VECTOR_ARITH` vec 0 - ( a - b ) = b - a `;
VECTOR_ARITH` a - vec 0 = a `]; STRIP_TAC THEN EXISTS_TAC `u:real^N`
THEN REPEAT GEN_TAC] THEN ASM_MESON_TAC[VECTOR_ARITH` ( a - c ) - ( b - c ) = a - (b:real^N)`;
VECTOR_SUB_REFL; VECTOR_ARITH` vec 0 - ( a - b ) = b - a `;
VECTOR_ARITH` a - vec 0 = a `]);;





let ALLEMI_COLLINEAR = prove(`((vc - v0) dot ((vc: real^N) - v0)) % (va - v0) =
((va - v0) dot (vc - v0)) % (vc - v0)
==> collinear {v0, vc, va}`,
ASM_CASES_TAC ` (vc - v0) dot (vc - (v0:real^N)) = &0 ` THENL
[FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[DOT_EQ_0; VECTOR_SUB_EQ] THEN
SIMP_TAC[INSERT_INSERT; COLLINEAR_2]; FIRST_X_ASSUM MP_TAC THEN
PHA THEN NHANH (MESON[]` ~( a = &0 ) /\ b = c ==> &1 / a % b =
&1 / a % c `) THEN SIMP_TAC[VECTOR_MUL_ASSOC] THEN PHA THEN
ONCE_REWRITE_TAC[MESON[]` a /\b ==> c <=> a ==> b ==> c `] THEN
SIMP_TAC[REAL_FIELD` ~ ( a = &0 ) ==> &1 / a * a = &1 `;
VECTOR_MUL_LID] THEN ONCE_REWRITE_TAC[COLLINEAR_TRANSABLE ] THEN
MESON_TAC[COLLINEAR_LEMMA]]);;


let NOT_VEC0_IMP_LE1 = prove(`~( x = vec 0 ) /\ ~( y = vec 0 ) ==>
abs (( x dot y )/ (( norm x ) * ( norm y ))) <= &1 `,
REWRITE_TAC[GSYM NORM_POS_LT; REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_NORM] THEN
NHANH (REAL_LT_MUL) THEN
SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; NORM_CAUCHY_SCHWARZ_ABS]);;

let sin_acs_t = prove(`! y. (-- &1 <= y /\ y <= &1) ==> (sin (acs(y)) = sqrt(&1 - y pow 2))`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC(GSYM SQRT_UNIQUE) THEN
ASM_SIMP_TAC[ACS_BOUNDS; SIN_POS_PI_LE; REAL_EQ_SUB_RADD] THEN
ASM_MESON_TAC[COS_ACS; SIN_CIRCLE]);;


let ABS_LE_1_IMP_SIN_ACS = prove(`!y. abs y <= &1 ==> sin (acs y) = sqrt (&1 - y pow 2)`,
SIMP_TAC[REAL_ABS_BOUNDS; sin_acs_t]);;


let NOT_2EQ_IMP_SIN_ARCV = prove(`~( v0 = va) /\ ~(v0 = (vb:real^N)) ==>
sin ( arcV v0 va vb ) = sqrt
(&1 -
(((va - v0) dot (vb - v0)) / (norm (va - v0) * norm (vb - v0))) pow 2) `,
REWRITE_TAC[arcV] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN NHANH (NOT_VEC0_IMP_LE1 ) THEN
SIMP_TAC[ABS_LE_1_IMP_SIN_ACS]);;


let ABS_NOT_EQ_NORM_MUL = prove(` ~ ( abs ( x dot y ) = norm x * norm y ) <=>
abs ( x dot y ) < norm x * norm y `,
SIMP_TAC[REAL_LT_LE; NORM_CAUCHY_SCHWARZ_ABS]);;



let SQUARE_NORM_CAUCHY_SCHWARZ_POW2 = prove(`((x:real^N) dot y) pow 2 <= (norm x * norm y) pow 2`,
REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
MESON_TAC[GSYM REAL_ABS_REFL; REAL_LE_MUL; NORM_POS_LE;
NORM_CAUCHY_SCHWARZ_ABS]);;

let REAL_LE_POW_2 = prove(` ! x. &0 <= x pow 2 `,
REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]);;

let SQRT_SEPARATED = prove(`sqrt (((norm x * norm y) pow 2 - ((x:real^N) dot y) pow 2) / (norm x * norm y) pow 2) =
sqrt ((norm x * norm y) pow 2 - (x dot y) pow 2) /
sqrt ((norm x * norm y) pow 2)`,
MP_TAC SQUARE_NORM_CAUCHY_SCHWARZ_POW2 THEN
ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN SIMP_TAC[REAL_LE_POW_2; SQRT_DIV]);;




let COMPUTE_NORM_OF_P = prove(`norm ((vc dot vc) % va - (va dot vc) % vc) =
sqrt ((vc dot vc) * ((va dot va) * (vc dot vc) - (va dot vc) pow 2))`,
REWRITE_TAC[vector_norm; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
MATCH_MP_TAC (MESON[]` a = b ==> P a = P b `) THEN SIMP_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;




let MOVE_NORM_OUT_OF_SQRT = prove(`sqrt (norm (vc:real^N) pow 2 * ((norm va * norm vc) pow 2 - (va dot vc) pow 2)) =
norm vc * sqrt ((norm va * norm vc) pow 2 - (va dot vc) pow 2)`,
MP_TAC (MESON[SQUARE_NORM_CAUCHY_SCHWARZ_POW2]`
((va: real^N) dot vc) pow 2 <= (norm va * norm vc) pow 2 `) THEN
ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
SIMP_TAC[REAL_LE_POW_2; SQRT_MUL; NORM_POS_LE; POW_2_SQRT]);;

let PI2_EQ_ACS0 = prove(` pi / &2 = acs ( &0 ) `,
MP_TAC (REAL_ARITH` -- &1 <= &0 /\ &0 <= &1 `) THEN
NHANH ACS_BOUNDS THEN STRIP_TAC THEN MATCH_MP_TAC COS_INJ_PI
THEN ASM_SIMP_TAC[COS_PI2; COS_ACS] THEN ASSUME_TAC PI_POS
THEN ASM_REAL_ARITH_TAC);;

let ANGLE_EQ_ARCV = prove(`! vap vbp. angle (vap,vec 0,vbp) = arcV (vec 0) vap vbp `,
REWRITE_TAC[arcV; angle; vector_angle] THEN REPEAT STRIP_TAC THEN
COND_CASES_TAC THENL [POP_ASSUM DISJ_CASES_TAC THENL [
ASM_SIMP_TAC[DOT_LZERO; REAL_ARITH` &0 / a = &0 `; PI2_EQ_ACS0];
ASM_SIMP_TAC[DOT_RZERO; REAL_ARITH` &0 / a = &0 `; PI2_EQ_ACS0]];
REWRITE_TAC[]]);;


let dihV = prove(`! w0 w1 w2 w3. dihV w0 w1 w2 w3 =
(let va = w2 - w0 in
let vb = w3 - w0 in
let vc = w1 - w0 in
let vap = (vc dot vc) % va - (va dot vc) % vc in
let vbp = (vc dot vc) % vb - (vb dot vc) % vc in arcV (vec 0) vap vbp)`,
SIMP_TAC[dihV; ANGLE_EQ_ARCV]);;
(* lemma 16 *)

let RLXWSTK = prove(`! (v0: real^N) va vb vc. let gam = dihV v0 vc va vb in
let a = arcV v0 vc vb in
let b = arcV v0 vc va in
let c = arcV v0 va vb in
~collinear {v0, vc, va} /\ ~collinear {v0, vc, vb}
==> cos gam = (cos c - cos a * cos b) / ( sin a * sin b )`,
REPEAT GEN_TAC THEN REPEAT LET_TAC THEN EXPAND_TAC "gam" THEN
REWRITE_TAC[dihV] THEN LET_TR THEN
NHANH (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] ALLEMI_COLLINEAR) THEN
ONCE_REWRITE_TAC[VECTOR_ARITH` a = b <=> vec 0 = a - b `] THEN
SIMP_TAC[NOT_EQ_IMPCOS_ARC; VECTOR_SUB_RZERO ] THEN
ABBREV_TAC ` (va_v0p: real^N) = ((vc - v0) dot (vc - v0)) % (va - v0) -
((va - v0) dot (vc - v0)) % (vc - v0) ` THEN
ABBREV_TAC ` (vb_v0p :real^N) = ((vc - v0) dot (vc - v0)) % (vb - v0) -
((vb - v0) dot (vc - v0)) % (vc - v0) ` THEN
EXPAND_TAC "c" THEN EXPAND_TAC "a" THEN EXPAND_TAC "b" THEN
NHANH (MESON[COLLINEAR_2; INSERT_INSERT; INSERT_AC]`
~collinear {v0, vc, va} ==> ~( v0 = vc) /\ ~( v0 = va ) `) THEN
SIMP_TAC[NOT_2EQ_IMP_SIN_ARCV; NOT_EQ_IMPCOS_ARC] THEN
ONCE_REWRITE_TAC[COLLINEAR_TRANSABLE] THEN
REWRITE_TAC[GSYM NORM_CAUCHY_SCHWARZ_EQUAL] THEN
ONCE_REWRITE_TAC[VECTOR_ARITH` a = b <=> b - a = vec 0`] THEN
SIMP_TAC[ GSYM NORM_EQ_0] THEN ONCE_REWRITE_TAC[ GSYM DE_MORGAN_THM] THEN
REWRITE_TAC[GSYM REAL_ENTIRE] THEN SIMP_TAC[REAL_FIELD`~ ( c = &0 ) ==>
&1 - ( b / c ) pow 2 = ( c pow 2 - b pow 2) / c pow 2 `] THEN
SIMP_TAC[SQRT_SEPARATED] THEN SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; POW_2_SQRT] THEN
SIMP_TAC[REAL_FIELD` x / (( b / a ) * ( c / aa )) = ( x * a * aa ) / ( b * c ) `] THEN
REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_MUL_AC; REAL_ENTIRE; DE_MORGAN_THM] THEN
SIMP_TAC[REAL_FIELD` ~( a = &0 ) /\ ~( b = &0 )
==> x / ( a * b ) * a * b * c = x * c `;
REAL_FIELD` ~( a = &0 ) /\ ~ ( b = &0 ) /\ ~ ( c = &0) ==>
x / ( a * c ) * y / ( b * c ) * a * b * c * c = x * y `] THEN
STRIP_TAC THEN EXPAND_TAC "va_v0p" THEN EXPAND_TAC "vb_v0p" THEN
REWRITE_TAC[COMPUTE_NORM_OF_P] THEN
REWRITE_TAC[ GSYM NORM_POW_2; REAL_ARITH` a pow 2 * b pow 2 = ( a * b ) pow 2`] THEN
ABBREV_TAC `vaa = ( va - (v0:real^N))` THEN
ABBREV_TAC `vbb = ( vb - (v0:real^N))` THEN
ABBREV_TAC `vcc = ( vc - (v0:real^N))` THEN
SIMP_TAC[MOVE_NORM_OUT_OF_SQRT; DOT_LSUB; DOT_RSUB] THEN
SIMP_TAC[MOVE_NORM_OUT_OF_SQRT; DOT_LSUB; DOT_RSUB;
DOT_LMUL; DOT_RMUL; DOT_SYM; GSYM NORM_POW_2] THEN
REWRITE_TAC[REAL_ARITH` ( a * b ) * a * c = a pow 2 * b * c `] THEN
REWRITE_TAC[REAL_FIELD` a / ( b * c ) = ( a / b ) / c `] THEN
MATCH_MP_TAC (MESON[]` a = b ==> a / c = b / c `) THEN
MATCH_MP_TAC (MESON[]` a = b ==> a / c = b / c `) THEN
REWRITE_TAC[REAL_ARITH` norm vcc pow 2 * norm vcc pow 2 * (vaa dot vbb) -
norm vcc pow 2 * (vbb dot vcc) * (vaa dot vcc) -
((vaa dot vcc) * norm vcc pow 2 * (vbb dot vcc) -
(vaa dot vcc) * (vbb dot vcc) * norm vcc pow 2) =
norm vcc pow 2 * ( norm vcc pow 2 * (vaa dot vbb) - (vaa dot vcc) * (vbb dot vcc) ) `] THEN
UNDISCH_TAC `~ ( norm (vcc:real^N) = &0 ) ` THEN CONV_TAC REAL_FIELD);;






let SIN_POW2_EQ_1_SUB_COS_POW2 = prove(` sin x pow 2 = &1 - cos x pow 2 `,
MP_TAC (SPEC_ALL SIN_CIRCLE) THEN REAL_ARITH_TAC);;




let LE_AND_NOT_0_EQ_LT = REAL_ARITH` &0 <= a /\ ~( a = &0 ) <=> &0 < a `;;

let ABS_REFL = REAL_ABS_REFL;;
let LT_IMP_ABS_REFL = MESON[REAL_ABS_REFL; REAL_LT_IMP_LE]`&0 < a ==> abs a = a`;;


let ABS_MUL = REAL_ABS_MUL;;
let NOT_COLLINEAR_IMP_NOT_SIN0 = prove(`~collinear {v0, va, vb} ==> ~(sin ( arcV v0 va vb ) = &0)`,
SIMP_TAC[] THEN NHANH (MESON[INSERT_AC; COLLINEAR_2]` ~collinear {v0, va, vb}
==> ~( v0 = va ) /\ ~(v0 = vb) `) THEN
SIMP_TAC[NOT_2EQ_IMP_SIN_ARCV] THEN
ONCE_REWRITE_TAC[VECTOR_ARITH` a = b <=> b - a = vec 0 `] THEN
SIMP_TAC[ GSYM NORM_POS_LT] THEN
STRIP_TAC THEN
MATCH_MP_TAC (MESON[SQRT_EQ_0]` &0 <= x /\ ~( x = &0 ) ==> ~( sqrt x = &0 ) `) THEN
DOWN_TAC THEN
ONCE_REWRITE_TAC[ COLLINEAR_TRANSABLE ] THEN
REWRITE_TAC[ GSYM NORM_CAUCHY_SCHWARZ_EQUAL; ABS_NOT_EQ_NORM_MUL;
LE_AND_NOT_0_EQ_LT ] THEN
SIMP_TAC[REAL_FIELD`&0 < a /\ &0 < aa ==> &1 - ( b / ( a * aa )) pow 2
= ( ( a * aa ) pow 2 - b pow 2 ) / ( a * aa ) pow 2 `] THEN
STRIP_TAC THEN
MATCH_MP_TAC (SPEC_ALL REAL_LT_DIV) THEN
REWRITE_TAC[REAL_SUB_LT; GSYM REAL_LT_SQUARE_ABS] THEN
ONCE_REWRITE_TAC[REAL_ARITH` &0 = &0 pow 2 `] THEN
DOWN_TAC THEN
REWRITE_TAC[REAL_SUB_LT; GSYM REAL_LT_SQUARE_ABS; REAL_ABS_0;
ABS_MUL] THEN
SIMP_TAC[LT_IMP_ABS_REFL; REAL_LT_MUL ]);;
let REAL_LE_LDIV =
MESON[REAL_LE_LDIV_EQ; REAL_MUL_LID]`
! x z. &0 < z /\ x <= z ==> x / z <= &1 `;;
let NOT_IDEN_IMP_ABS_LE = prove(`~(v0 = va) /\ ~(v0 = vb)
==> abs (((va - v0) dot (vb - v0)) / (norm (va - v0) * norm (vb - v0))) <=
&1`, ONCE_REWRITE_TAC[VECTOR_ARITH` a = b <=> b - a = vec 0`] THEN
SIMP_TAC[REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_NORM; GSYM NORM_POS_LT] THEN
STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LDIV
THEN ASM_SIMP_TAC[REAL_LT_MUL; REAL_MUL_LID;
REAL_DIV_1; NORM_CAUCHY_SCHWARZ_ABS]);;

let ABS_1 = REAL_ABS_1;;
let PROVE_SIN_LE = prove(`~(v0 = va) /\ ~(v0 = vb) ==> &0 <= sin ( arcV v0 va vb )`,
SIMP_TAC[NOT_2EQ_IMP_SIN_ARCV; arcV] THEN
NGOAC THEN NHANH (NOT_IDEN_IMP_ABS_LE ) THEN
SIMP_TAC[ABS_LE_1_IMP_SIN_ACS] THEN STRIP_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
DOWN_TAC THEN ONCE_REWRITE_TAC[ GSYM ABS_1] THEN
ASM_SIMP_TAC[REAL_SUB_LE; GSYM ABS_1; REAL_LE_SQUARE_ABS] THEN
SIMP_TAC[REAL_ARITH`( &1 ) pow 2 = &1`; ABS_1]);;



let MUL_POW2 = REAL_ARITH` (a*b) pow 2 = a pow 2 * b pow 2 `;;




let COMPUTE_SIN_DIVH_POW2 = prove(`! (v0: real^N) va vb vc.
let betaa = dihV v0 vc va vb in
let a = arcV v0 vc vb in
let b = arcV v0 vc va in
let c = arcV v0 va vb in
let p =
&1 - cos a pow 2 - cos b pow 2 - cos c pow 2 +
&2 * cos a * cos b * cos c in
~collinear {v0, vc, va} /\ ~collinear {v0, vc, vb} ==>
( sin betaa ) pow 2 = p / ((sin a * sin b) pow 2) `,

REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL RLXWSTK ) THEN
REPEAT LET_TAC THEN SIMP_TAC[SIN_POW2_EQ_1_SUB_COS_POW2 ] THEN
REPEAT STRIP_TAC THEN REPLICATE_TAC 2 (FIRST_X_ASSUM MP_TAC) THEN
NHANH (NOT_COLLINEAR_IMP_NOT_SIN0) THEN
EXPAND_TAC "a" THEN EXPAND_TAC "b" THEN PHA THEN
SIMP_TAC[REAL_FIELD` ~( a = &0 ) /\ ~ ( b = &0 ) ==>
&1 - ( x / ( a * b )) pow 2 = (( a * b ) pow 2 - x pow 2 ) / (( a * b ) pow 2 ) `] THEN
ASM_SIMP_TAC[] THEN STRIP_TAC THEN
MATCH_MP_TAC (MESON[]` a = b ==> a / x = b / x `) THEN
EXPAND_TAC "p" THEN SIMP_TAC[MUL_POW2; SIN_POW2_EQ_1_SUB_COS_POW2] THEN
REAL_ARITH_TAC);;




let PROVE_P_LE = prove(`!(v0:real^N) va vb vc.
let a = arcV v0 vc vb in
let b = arcV v0 vc va in
let c = arcV v0 va vb in
let p =
&1 - cos a pow 2 - cos b pow 2 - cos c pow 2 +
&2 * cos a * cos b * cos c in
~collinear {v0, vc, va} /\ ~collinear {v0, vc, vb} ==> &0 <= p`,
REPEAT GEN_TAC THEN MP_TAC (SPEC_ALL COMPUTE_SIN_DIVH_POW2 ) THEN
REPEAT LET_TAC THEN REWRITE_TAC[MESON[]` ( a ==> b ) ==> a ==> c <=>
a /\ b ==> c `] THEN NHANH (NOT_COLLINEAR_IMP_NOT_SIN0) THEN
ASM_SIMP_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MP_TAC THEN
ASM_SIMP_TAC[REAL_FIELD` ~( a = &0 ) /\ ~( b = &0 ) ==>
( x = y / ( a * b ) pow 2 <=> x * ( a * b ) pow 2 = y ) `] THEN
MESON_TAC[GSYM MUL_POW2; REAL_LE_POW_2]);;


let POW2_COND = MESON[REAL_ABS_REFL; REAL_LE_SQUARE_ABS]` ! a b. &0 <= a /\ &0 <= b ==>
( a <= b <=> a pow 2 <= b pow 2 ) `;;


let EQ_POW2_COND = prove(`!a b. &0 <= a /\ &0 <= b ==> (a = b <=> a pow 2 = b pow 2)`,
REWRITE_TAC[REAL_ARITH` a = b <=> a <= b /\ b <= a `] THEN SIMP_TAC[POW2_COND]);;

let NOT_COLLINEAR_IMP_2_UNEQUAL = MESON[INSERT_INSERT; COLLINEAR_2; INSERT_AC]`
~collinear {v0, va, vb} ==> ~(v0 = va) /\ ~(v0 = vb) `;;


let NOT_COLL_IM_SIN_LT = prove(`~collinear {v0, va, vb} ==> &0 < sin (arcV v0 va vb)`,
REWRITE_TAC[GSYM LE_AND_NOT_0_EQ_LT] THEN
NHANH (NOT_COLLINEAR_IMP_2_UNEQUAL ) THEN
SIMP_TAC[NOT_COLLINEAR_IMP_NOT_SIN0; PROVE_SIN_LE]);;

let ARC_SYM = prove(` arcV v0 vc vb = arcV v0 vb vc `,
SIMP_TAC[arcV; DOT_SYM; REAL_MUL_SYM]);;


let DIV_POW2 = REAL_FIELD` ( a / b ) pow 2 = a pow 2 / b pow 2 `;;


ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] ALLEMI_COLLINEAR;;

let SIN_MUL_EXPAND = prove(` !(v0:real^N) va vb vc.
let gam = dihV v0 vc va vb in
let bet = dihV v0 vb vc va in
let a = arcV v0 vc vb in
let b = arcV v0 vc va in
let c = arcV v0 va vb in
let p =
&1 - cos a pow 2 - cos b pow 2 - cos c pow 2 +
&2 * cos a * cos b * cos c in
~collinear {v0, vc, va} /\ ~collinear {v0, vc, vb} /\
~ collinear {v0,va,vb} ==>
sin gam * sin bet = p / ( sin b * sin c * ( sin a pow 2 )) `,
REPEAT GEN_TAC THEN
MP_TAC (COMPUTE_SIN_DIVH_POW2) THEN
REPEAT LET_TAC THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MESON[EQ_POW2_COND]` &0 <= a /\ &0 <= b /\ a pow 2 = b pow 2
==> a = b `) THEN
CONJ_TAC THENL [ REPLICATE_TAC 3 (FIRST_X_ASSUM MP_TAC) THEN
EXPAND_TAC "gam" THEN EXPAND_TAC "betaa" THEN
EXPAND_TAC "bet" THEN REWRITE_TAC[dihV] THEN LET_TR THEN
NHANH (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] ALLEMI_COLLINEAR) THEN
ONCE_REWRITE_TAC[SET_RULE` {a,b} = {b,a}`] THEN
NHANH (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] ALLEMI_COLLINEAR) THEN
ONCE_REWRITE_TAC[VECTOR_ARITH ` a = b <=> vec 0 = a - b `] THEN
REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
ASM_SIMP_TAC[PROVE_SIN_LE]; REWRITE_TAC[]] THEN
CONJ_TAC THENL [MP_TAC (SPEC_ALL PROVE_P_LE ) THEN
REPEAT LET_TAC THEN
DOWN_TAC THEN
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
STRIP_TAC THEN
FIRST_X_ASSUM MP_TAC THEN
ASM_SIMP_TAC[] THEN
MATCH_MP_TAC (MESON[]` (! a. a = b ==> &0 <= a ==> P a )
==> &0 <= b ==> P b `) THEN
GEN_TAC THEN STRIP_TAC THEN
UNDISCH_TAC `~collinear {v0, vc, (vb: real^N)}` THEN
UNDISCH_TAC `~collinear {v0, vc, (va: real^N)}` THEN
UNDISCH_TAC `~collinear {v0, va, (vb: real^N)}` THEN
NHANH (NOT_COLL_IM_SIN_LT ) THEN
NHANH (REAL_LT_IMP_LE) THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC REAL_LE_DIV THEN
ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; REWRITE_TAC[]] THEN
EXPAND_TAC "gam" THEN EXPAND_TAC "betaa" THEN EXPAND_TAC "bet" THEN
SIMP_TAC[MUL_POW2] THEN
REPLICATE_TAC 3 (FIRST_X_ASSUM MP_TAC) THEN
PHA THEN
FIRST_X_ASSUM MP_TAC THEN
SIMP_TAC[] THEN
DISCH_TAC THEN
ONCE_REWRITE_TAC[SET_RULE` {a,b} = {b,a}`] THEN
FIRST_X_ASSUM MP_TAC THEN
SIMP_TAC[] THEN
REWRITE_TAC[REAL_FIELD` a / x * aa / y = ( a * aa ) / ( x * y ) `] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC[ARC_SYM] THEN
ONCE_REWRITE_TAC[ARC_SYM] THEN
ASM_SIMP_TAC[] THEN
SIMP_TAC[DIV_POW2; REAL_ARITH` ((sin a * sin b) pow 2 * (sin c * sin a) pow 2) =
(sin b * sin c * sin a pow 2) pow 2 `] THEN
MATCH_MP_TAC (MESON[]` a = b ==> a / x = b / x `) THEN
EXPAND_TAC "p'" THEN
EXPAND_TAC "p" THEN
EXPAND_TAC "a" THEN
EXPAND_TAC "b" THEN
EXPAND_TAC "c" THEN
EXPAND_TAC "a'" THEN
EXPAND_TAC "b'" THEN
EXPAND_TAC "c'" THEN
SIMP_TAC[ARC_SYM] THEN
REAL_ARITH_TAC);;


let DIHV_SYM = prove(`dihV a b x y = dihV a b y x `,
REWRITE_TAC[dihV] THEN LET_TR THEN SIMP_TAC[DOT_SYM; ARC_SYM]);;

(* lemma 17 *)
let NLVWBBW = prove(` !(v0:real^N) va vb vc.
let al = dihV v0 va vb vc in
let ga = dihV v0 vc va vb in
let be = dihV v0 vb vc va in
let a = arcV v0 vc vb in
let b = arcV v0 vc va in
let c = arcV v0 va vb in
let p =
&1 - cos a pow 2 - cos b pow 2 - cos c pow 2 +
&2 * cos a * cos b * cos c in
~collinear {v0, vc, va} /\ ~collinear {v0, vc, vb} /\
~ collinear {v0,va,vb} ==>
cos c * sin al * sin be = cos ga + cos al * cos be `,
REPEAT GEN_TAC THEN MP_TAC RLXWSTK THEN REPEAT LET_TAC THEN
EXPAND_TAC "al" THEN EXPAND_TAC "be" THEN EXPAND_TAC "ga" THEN
EXPAND_TAC "gam" THEN SIMP_TAC[INSERT_AC] THEN STRIP_TAC THEN
MP_TAC SIN_MUL_EXPAND THEN REPEAT LET_TAC THEN EXPAND_TAC "bet" THEN
SIMP_TAC[INSERT_AC; DIHV_SYM; ARC_SYM] THEN
ONCE_REWRITE_TAC[MESON[DIHV_SYM]` aa * sin (dihV v0 va vb vc) * sin (dihV v0 vb va vc) =
aa * sin (dihV v0 va vc vb) * sin (dihV v0 vb vc va)`] THEN
DISCH_TAC THEN ONCE_REWRITE_TAC[MESON[INSERT_AC]`~collinear {v0, va, vc} /\
~collinear {v0, vb, vc} /\ ~collinear {v0, va, vb} <=>
~collinear {v0, vc, va} /\ ~collinear {v0, vb, va} /\
~collinear {v0, vc, vb} `] THEN FIRST_X_ASSUM MP_TAC THEN
SIMP_TAC[] THEN DOWN_TAC THEN SIMP_TAC[ARC_SYM; DIHV_SYM] THEN
STRIP_TAC THEN REPLICATE_TAC 3 (FIRST_X_ASSUM MP_TAC) THEN
NHANH (NOT_COLLINEAR_IMP_NOT_SIN0) THEN ASM_SIMP_TAC[ARC_SYM] THEN
REPEAT STRIP_TAC THEN UNDISCH_TAC `~( sin a = &0 )` THEN
UNDISCH_TAC `~( sin b = &0 )` THEN UNDISCH_TAC `~( sin c = &0 )` THEN
PHA THEN SIMP_TAC[REAL_FIELD `~(c = &0) /\ ~(b = &0) /\ ~(a = &0)
==> x / (a * b) + y / (b * c) * z / (c * a) = ( x * c pow 2 + y * z ) / ( b * a * c pow 2 ) `] THEN
STRIP_TAC THEN REWRITE_TAC[REAL_ARITH` a * ( x / y ) = ( a * x ) / y `] THEN
MATCH_MP_TAC (MESON[]` a = b ==> a / x = b / x `) THEN
SIMP_TAC[SIN_POW2_EQ_1_SUB_COS_POW2] THEN REAL_ARITH_TAC);;


let COMPUTE_NORM_POW2 = prove(`
norm ((vc dot vc) % vb - (vb dot vc) % vc ) pow 2 = ((norm vc pow 2 + norm vc pow 2) - dist (vc,vc) pow 2) / &2 *
(((norm vc pow 2 + norm vc pow 2) - dist (vc,vc) pow 2) / &2 *
((norm vb pow 2 + norm vb pow 2) - dist (vb,vb) pow 2) / &2 -
((norm vb pow 2 + norm vc pow 2) - dist (vb,vc) pow 2) / &2 *
((norm vb pow 2 + norm vc pow 2) - dist (vb,vc) pow 2) / &2) -
((norm vb pow 2 + norm vc pow 2) - dist (vb,vc) pow 2) / &2 *
(((norm vc pow 2 + norm vc pow 2) - dist (vc,vc) pow 2) / &2 *
((norm vc pow 2 + norm vb pow 2) - dist (vc,vb) pow 2) / &2 -
((norm vb pow 2 + norm vc pow 2) - dist (vb,vc) pow 2) / &2 *
((norm vc pow 2 + norm vc pow 2) - dist (vc,vc) pow 2) / &2) `,
MATCH_MP_TAC (MESON[]`(! c. c = b ==> a = c ) ==> a = b`) THEN REPEAT STRIP_TAC THEN
SIMP_TAC[NORM_POW_2] THEN SIMP_TAC[GSYM dist;
VECTOR_SUB_RZERO; DOT_LSUB; DOT_RSUB; DOT_LMUL;
DOT_RMUL; DOT_NORM_NEG] THEN ASM_SIMP_TAC[]);;


let UPS_X_AND_HERON = prove(`ups_x (x1 pow 2) (x2 pow 2) (x6 pow 2) =
(x1 + x2 + x6) * (x1 + x2 - x6) * (x2 + x6 - x1) * (x6 + x1 - x2)`,
SIMP_TAC[ups_x] THEN REAL_ARITH_TAC);;


let UPS_X_POS = prove(`dist (v0,v1) pow 2 = v01 /\
dist (v0,v2) pow 2 = v02 /\
dist (v1,v2) pow 2 = v12
==> &0 <= ups_x v01 v02 v12`,
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
SIMP_TAC[UPS_X_AND_HERON] THEN
DISCH_TAC THEN
MATCH_MP_TAC REAL_LE_MUL THEN
SIMP_TAC[DIST_POS_LE; REAL_LE_ADD] THEN
MATCH_MP_TAC REAL_LE_MUL THEN
CONJ_TAC THENL [
MESON_TAC[ONCE_REWRITE_RULE[REAL_ARITH` a <= b + c <=> &0 <= b + c - a `]
DIST_TRIANGLE; DIST_SYM; DIST_POS_LE];
MATCH_MP_TAC REAL_LE_MUL] THEN
MESON_TAC[ONCE_REWRITE_RULE[REAL_ARITH` a <= b + c <=> &0 <= b + c - a `]
DIST_TRIANGLE; DIST_SYM; DIST_POS_LE]);;


let DIST_TRANSABLE = prove(` dist ( a - v0, b ) = dist ( a , b + v0 ) `,
REWRITE_TAC[dist; VECTOR_ARITH` a - v0 - b = (a:real^N) - ( b + v0 ) `]);;

prove(` v2 - v0 = va /\
v3 - v0 = vb ==> dist (va,vb) = dist ( v2,v3) `,
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
SIMP_TAC[DIST_TRANSABLE; VECTOR_ARITH` a - b + b = ( a:real^N)`]);;
let REAL_LE_SQUARE_POW =
MESON[REAL_POW_2; REAL_LE_SQUARE]`! x. &0 <= x pow 2 `;;
g ` dist ((v0:real^N),v1) pow 2 = v01 /\
dist (v0,v2) pow 2 = v02 /\
dist (v0,v3) pow 2 = v03 /\
dist (v1,v2) pow 2 = v12 /\
dist (v1,v3) pow 2 = v13 /\
dist (v2,v3) pow 2 = v23 /\
~collinear {v0, v1, v2} /\
~collinear {v0, v1, v3}
==> (let va = v2 - v0 in
let vb = v3 - v0 in
let vc = v1 - v0 in
let vap = (vc dot vc) % va - (va dot vc) % vc in
let vbp = (vc dot vc) % vb - (vb dot vc) % vc in
(((vap - vec 0) dot (vbp - vec 0)) /
(norm (vap - vec 0) * norm (vbp - vec 0)))) =
(delta_x4 v01 v02 v03 v23 v13 v12 /
sqrt (ups_x v01 v02 v12 * ups_x v01 v03 v13))`;;
e (REPEAT LET_TAC THEN STRIP_TAC);;
e (EXPAND_TAC "vap" THEN EXPAND_TAC "vbp");;
e (ONCE_REWRITE_TAC[MESON[NORM_POS_LE; POW_2_SQRT]` norm x = sqrt ( norm x pow 2 ) `] THEN
REWRITE_TAC[MESON[REAL_LE_POW_2; SQRT_MUL]` sqrt ( x pow 2 ) *
sqrt ( y pow 2 ) = sqrt ( x pow 2 * y pow 2 ) `]);;
e (SIMP_TAC[VECTOR_SUB_RZERO; COMPUTE_NORM_POW2 ] THEN
REWRITE_TAC[GSYM (MESON[NORM_POS_LE; POW_2_SQRT]` norm x = sqrt ( norm x pow 2 ) `)] THEN
REWRITE_TAC[DIST_REFL; REAL_SUB_RZERO; REAL_ARITH` &0 pow 2 = &0`] THEN
EXPAND_TAC "va" THEN EXPAND_TAC "vb" THEN
EXPAND_TAC "vc" THEN SIMP_TAC[VECTOR_ARITH` a - b - (c - b ) = a -(c:real^N)`; GSYM dist] THEN
FIRST_X_ASSUM MP_TAC);;
e (NHANH (MESON[COLLINEAR_2; INSERT_INSERT]` ~ collinear {a,b,c}
==> ~( a = b ) `) THEN REWRITE_TAC[DIST_NZ] THEN
NHANH (REAL_FIELD` &0 < a ==> &1 = ( &1 / &4 * (a pow 2 ))/ ( &1 / &4 * (a pow 2 )) `) THEN
ONCE_REWRITE_TAC[MESON[REAL_MUL_LID]` l ==> a = b <=> l ==> a
= &1 * b `]);;
e (ABBREV_TAC ` as = (&1 / &4 * dist ((v0:real^N),v1) pow 2 ) ` THEN
SIMP_TAC[REAL_FIELD` a / b * aa / bb = ( a * aa ) / ( b * bb ) `] THEN
STRIP_TAC THEN MATCH_MP_TAC (MESON[]` a = aa /\ b = bb ==>
a / b = aa / bb `));;
e (CONJ_TAC THENL [ SIMP_TAC[GSYM NORM_POW_2; GSYM dist] THEN
ASM_SIMP_TAC[] THEN
SIMP_TAC[DIST_SYM; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
SIMP_TAC[DOT_NORM_NEG] THEN EXPAND_TAC "va" THEN
EXPAND_TAC "vb" THEN EXPAND_TAC "vc" THEN
REWRITE_TAC[ VECTOR_ARITH` a - b - ( c - b ) = a - (c:real^N)`] THEN
REWRITE_TAC[GSYM dist] THEN EXPAND_TAC "as" THEN
UNDISCH_TAC `&1 / &4 * dist ((v0:real^N),v1) pow 2 = as` THEN
FIRST_X_ASSUM MP_TAC THEN PHA THEN
MATCH_MP_TAC (MESON[]` a ==> b ==> a `) THEN
ASM_SIMP_TAC[DIST_SYM; DIST_REFL; delta_x4] THEN
REAL_ARITH_TAC; UNDISCH_TAC`&1 / &4 * dist ((v0:real^N),v1) pow 2 = as`]
THEN MP_TAC (SPEC ` dist ((v0:real^N),v1)` REAL_LE_POW_2) THEN
PHA THEN NHANH (REAL_ARITH `&0 <= a /\ &1 / &4 * a = as ==> &0 <= as `) THEN
REWRITE_TAC[MESON[POW_2_SQRT]` da /\ &0 <= a ==> p1 = a * p2 <=>
da /\ &0 <= a ==> p1 = sqrt ( a pow 2 ) * p2 `] THEN DOWN_TAC THEN
NHANH (MESON[UPS_X_POS; DIST_SYM ]`dist (v0,v1) pow 2 = v01 /\
dist (v0,v2) pow 2 = v02 /\ dist (v0,v3) pow 2 = v03 /\
dist (v1,v2) pow 2 = v12 /\ dist (v1,v3) pow 2 = v13 /\
dist (v2,v3) pow 2 = v23 /\ l ==> &0 <= ups_x v01 v02 v12
/\ &0 <= ups_x v01 v03 v13 `) THEN NHANH (REAL_LE_MUL));;

e (SIMP_TAC[REAL_LE_SQUARE_POW; GSYM SQRT_MUL] THEN
STRIP_TAC THEN MATCH_MP_TAC (MESON[]` a = b ==> p a = p b `) THEN
REPLICATE_TAC 6 (FIRST_X_ASSUM MP_TAC) THEN
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DIST_SYM] THEN DOWN_TAC THEN
NHANH (MESON[prove(` v2 - v0 = va /\
v3 - v0 = vb ==> dist (va,vb) = dist ( v2,v3) `,
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
SIMP_TAC[DIST_TRANSABLE; VECTOR_ARITH` a - b + b = ( a:real^N)`]); DIST_SYM]`
v2 - v0 = va /\ v3 - v0 = vb /\
v1 - v0 = vc /\ l ==> dist (va,vb ) = dist (v2,v3) /\ dist (vb,vc) =
dist(v1,v3) /\ dist (va,vc) = dist (v1,v2)`) THEN SIMP_TAC[ups_x] THEN
STRIP_TAC THEN REAL_ARITH_TAC);;
let PROVE_DELTA_OVER_SQRT_2UPS = top_thm();;



let FOR_LEMMA19 = prove(`!(v0:real^N) v1 v2 v3.
let ga = dihV v0 v1 v2 v3 in
let v01 = dist (v0,v1) pow 2 in
let v02 = dist (v0,v2) pow 2 in
let v03 = dist (v0,v3) pow 2 in
let v12 = dist (v1,v2) pow 2 in
let v13 = dist (v1,v3) pow 2 in
let v23 = dist (v2,v3) pow 2 in
~collinear {v0, v1, v2} /\ ~collinear {v0, v1, v3}
==> ga =
acs
(delta_x4 v01 v02 v03 v23 v13 v12 /
sqrt (ups_x v01 v02 v12 * ups_x v01 v03 v13))`,
REPEAT STRIP_TAC THEN REPEAT LET_TAC THEN EXPAND_TAC "ga" THEN
SIMP_TAC[dihV; arcV] THEN REPEAT LET_TAC THEN REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MESON[]` a = b ==> p a = p b `) THEN MP_TAC
PROVE_DELTA_OVER_SQRT_2UPS THEN REPEAT LET_TAC THEN
ASM_MESON_TAC[]);;


let COMPUTE_DELTA_OVER = prove(`dist ((v0:real^N),v1) pow 2 = v01 /\
dist (v0,v2) pow 2 = v02 /\
dist (v0,v3) pow 2 = v03 /\
dist (v1,v2) pow 2 = v12 /\
dist (v1,v3) pow 2 = v13 /\
dist (v2,v3) pow 2 = v23 /\
~collinear {v0, v1, v2} /\
~collinear {v0, v1, v3}
==> ((((v1 - v0) dot (v1 - v0)) % (v2 - v0) -
((v2 - v0) dot (v1 - v0)) % (v1 - v0)) dot
(((v1 - v0) dot (v1 - v0)) % (v3 - v0) -
((v3 - v0) dot (v1 - v0)) % (v1 - v0))) /
(norm
(((v1 - v0) dot (v1 - v0)) % (v2 - v0) -
((v2 - v0) dot (v1 - v0)) % (v1 - v0)) *
norm
(((v1 - v0) dot (v1 - v0)) % (v3 - v0) -
((v3 - v0) dot (v1 - v0)) % (v1 - v0))) =
delta_x4 v01 v02 v03 v23 v13 v12 /
sqrt (ups_x v01 v02 v12 * ups_x v01 v03 v13)`,
MP_TAC PROVE_DELTA_OVER_SQRT_2UPS THEN REWRITE_TAC[VECTOR_ARITH` a - vec 0 = a `]
THEN LET_TR THEN SIMP_TAC[]);;








let POS_COMPATIBLE_WITH_ATN2 = prove(` &0 < a ==> atn2 (x,y) = atn2 (a * x,a * y)`,
SIMP_TAC[atn2; REAL_FIELD` &0 < a ==> ( a * b ) / (a * c ) = b / c `] THEN
SIMP_TAC[ABS_MUL] THEN REWRITE_TAC[REAL_ARITH` a * y < &0 <=> &0 < a * ( -- y )`;
REAL_ARITH` b < &0 <=> &0 < -- b `] THEN
SIMP_TAC[ABS_MUL; LT_IMP_ABS_REFL; REAL_LT_LMUL_EQ; REAL_LT_MUL_EQ]);;



let NOT_COLLINEAR_IMP_UPS_LT = new_axiom `
~( collinear {(v0:real^N),v1,v2} ) ==>
let v01 = dist (v0,v1) pow 2 in
let v02 = dist (v0,v2) pow 2 in
let v12 = dist (v1,v2) pow 2 in
&0 < ups_x v01 v02 v12 `;;

(* Jason have proved the following lemma in the first half
of this file *)
let acs_atn2_t = `!y. (-- &1 <= y /\ y <= &1) ==> (acs y = pi/(&2) - atn2(sqrt(&1 - y pow 2),y))`;;
let acs_atn2 = new_axiom acs_atn2_t;;

let REAL_LT_DIV_0 = prove(` ! a b. &0 < b ==> ( &0 < a / b <=> &0 < a ) `,
REPEAT STRIP_TAC THEN EQ_TAC THENL
[ASSUME_TAC (UNDISCH (SPEC `b:real` REAL_LT_IMP_NZ)) THEN
ASM_MESON_TAC[REAL_LT_MUL; REAL_DIV_LMUL];
ASM_SIMP_TAC[REAL_LT_DIV]]);;

let REAL_LE_RDIV_0 = prove(` ! a b. &0 < b ==> ( &0 <= a / b <=> &0 <= a ) `,
REWRITE_TAC[REAL_ARITH ` &0 <= a <=> &0 < a \/ a = &0 `] THEN
SIMP_TAC[REAL_LT_DIV_0] THEN
SIMP_TAC[REAL_FIELD `&0 < b ==> ( a / b = &0 <=> a = &0 ) `]);;

let POW_2 = REAL_POW_2;;

let NOT_ZERO_EQ_POW2_LT = prove(` ~( a = &0 ) <=> &0 < a pow 2 `,
SIMP_TAC[GSYM LE_AND_NOT_0_EQ_LT; POW_2;
REAL_ENTIRE; REAL_LE_SQUARE]);;




(* lemma 18 *)
let OJEKOJF = prove(`!(v0:real^N) v1 v2 v3.
let ga = dihV v0 v1 v2 v3 in
let v01 = dist (v0,v1) pow 2 in
let v02 = dist (v0,v2) pow 2 in
let v03 = dist (v0,v3) pow 2 in
let v12 = dist (v1,v2) pow 2 in
let v13 = dist (v1,v3) pow 2 in
let v23 = dist (v2,v3) pow 2 in
~collinear {v0, v1, v2} /\ ~collinear {v0, v1, v3}
==> ga =
acs
(delta_x4 v01 v02 v03 v23 v13 v12 /
sqrt (ups_x v01 v02 v12 * ups_x v01 v03 v13)) /\
ga = pi / &2 - atn2( sqrt ( &4 * v01 * delta_x v01 v02 v03 v23 v13 v12 ),
delta_x4 v01 v02 v03 v23 v13 v12 ) `, REPEAT STRIP_TAC THEN
MP_TAC (SPEC_ALL FOR_LEMMA19 ) THEN REPEAT LET_TAC THEN
SIMP_TAC[] THEN DOWN_TAC THEN NGOAC THEN REWRITE_TAC[MESON[]`l/\ ( a ==> b ) <=>
( a ==> b ) /\ l `] THEN PHA THEN NHANH (COMPUTE_DELTA_OVER ) THEN
NHANH (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] ALLEMI_COLLINEAR) THEN
ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
ABBREV_TAC ` (w1:real^N) = ((v1 - v0) dot (v1 - v0)) % (v2 - v0) -
((v2 - v0) dot (v1 - v0)) % (v1 - v0)` THEN
ABBREV_TAC ` (w2:real^N) = ((v1 - v0) dot (v1 - v0)) % (v3 - v0) -
((v3 - v0) dot (v1 - v0)) % (v1 - v0) ` THEN
ONCE_REWRITE_TAC[MESON[]`( a/\ b ) /\ c /\ d <=>
a /\ c /\ b /\ d `] THEN NHANH (NOT_VEC0_IMP_LE1) THEN PHA THEN
REWRITE_TAC[MESON[]` P a /\ a = b <=> a = b /\ P b `] THEN
SIMP_TAC[REAL_ABS_BOUNDS; acs_atn2; REAL_ARITH ` a - x =
a - y <=> x = y `] THEN NHANH (NOT_COLLINEAR_IMP_UPS_LT ) THEN
LET_TR THEN PHA THEN NHANH (MESON[REAL_LT_MUL]` &0 < x /\ a1 /\ &0 < y /\ a2 ==>
&0 < x * y `) THEN STRIP_TAC THEN FIRST_X_ASSUM MP_TAC THEN
ASM_SIMP_TAC[] THEN NHANH SQRT_POS_LT THEN
SIMP_TAC[MESON[POS_COMPATIBLE_WITH_ATN2]` &0 < a ==>
atn2 ( x, y / a ) = atn2 ( a * x , a * ( y / a ) ) `] THEN
SIMP_TAC[REAL_FIELD` &0 < a ==> a * ( y / a ) = y `] THEN
REPLICATE_TAC 2 (FIRST_X_ASSUM MP_TAC) THEN
PHA THEN NGOAC THEN REWRITE_TAC[GSYM REAL_ABS_BOUNDS] THEN
ONCE_REWRITE_TAC[GSYM ABS_1] THEN
SIMP_TAC[REAL_LE_SQUARE_ABS; REAL_ARITH` a <= &1 <=>
&0 <= &1 - a `; REAL_ARITH` ( &1 ) pow 2 = &1 `; ABS_1] THEN
DAO THEN ONCE_REWRITE_TAC[GSYM IMP_IMP] THEN
SIMP_TAC[REAL_FIELD` &0 < a ==> &1 - ( b / a ) pow 2
= ( a pow 2 - b pow 2 ) / ( a pow 2 ) `] THEN
NHANH (REAL_LT_IMP_NZ) THEN NHANH (REAL_LT_IMP_LE) THEN
SIMP_TAC[NOT_ZERO_EQ_POW2_LT; REAL_LE_RDIV_0 ; SQRT_DIV] THEN
NHANH (REAL_LT_IMP_LE) THEN SIMP_TAC[SQRT_DIV; REAL_LE_POW2] THEN
SIMP_TAC[SQRT_DIV; REAL_LE_POW2; POW_2_SQRT; REAL_FIELD` &0 < a ==>
a * b / a = b `] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC
(MESON[]` a = b ==> atn2 ( sqrt a, c ) = atn2 ( sqrt b, c ) `) THEN
ASM_SIMP_TAC[SQRT_WORKS; ups_x; delta_x4; delta_x] THEN
REAL_ARITH_TAC);;





let LEMMA16_INTERPRETE = prove(`!(v0: real^N) va vb vc.
~collinear {v0, vc, va} /\ ~collinear {v0, vc, vb}
==> cos (dihV v0 vc va vb) =
(cos (arcV v0 va vb) -
cos (arcV v0 vc vb) * cos (arcV v0 vc va)) /
(sin (arcV v0 vc vb) * sin (arcV v0 vc va))`,
MP_TAC RLXWSTK THEN REPEAT LET_TAC THEN SIMP_TAC[]);;



let NOT_COLLINEAR_IMP_VEC_FOR_DIHV = ONCE_REWRITE_RULE[GSYM VECTOR_SUB_EQ]
(ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] ALLEMI_COLLINEAR);;

let ACS = ACS_BOUNDS;;
let NOT_COLLINEAR_IMP_DIHV_BOUNDED = prove(
` ~( collinear {v0,v1,v2} ) /\ ~( collinear {v0,v1,v3} )
==> &0 <= dihV v0 v1 v2 v3 /\ dihV v0 v1 v2 v3 <= pi`,
REWRITE_TAC[dihV; arcV] THEN REPEAT LET_TAC THEN
NHANH (NOT_COLLINEAR_IMP_VEC_FOR_DIHV ) THEN
ASM_SIMP_TAC[VECTOR_SUB_RZERO] THEN
ONCE_REWRITE_TAC[MESON[]` ( a/\b) /\c /\d <=>
a /\c/\b/\d`] THEN NHANH (NOT_VEC0_IMP_LE1) THEN
SIMP_TAC[REAL_ABS_BOUNDS; ACS]) ;;



let DIHV_FORMULAR = prove(` dihV v0 v1 v2 v3 = arcV (vec 0)
(((v1 - v0) dot (v1 - v0)) % (v2 - v0) -
((v2 - v0) dot (v1 - v0)) % (v1 - v0))
(((v1 - v0) dot (v1 - v0)) % (v3 - v0) -
((v3 - v0) dot (v1 - v0)) % (v1 - v0)) `, REWRITE_TAC[dihV]
THEN REPEAT LET_TAC THEN REWRITE_TAC[]);;


let COS_POW2_INTER = prove(` cos x pow 2 = &1 - sin x pow 2 `,
MP_TAC (SPEC_ALL SIN_CIRCLE) THEN REAL_ARITH_TAC);;

(* lemma 19 *)
let ISTYLPH = prove(` ! (v0:real^N) v1 v2 v3.
&0 <= cos (arcV (v0:real^N) v2 v3) /\
dihV v0 v3 v1 v2 = pi / &2 /\
~ collinear {v0,v1,v2} /\
~ collinear {v0,v1,v3} /\
~ collinear {v0,v2,v3} /\
psi = arcV v0 v2 v3 /\
tte = arcV v0 v1 v2 ==>
dihV v0 v1 v2 v3 = beta psi tte `,
REPEAT GEN_TAC THEN
ONCE_REWRITE_TAC[MESON[]` a /\ b ==> c <=>
a ==> b ==> c `] THEN
DISCH_TAC THEN
ONCE_REWRITE_TAC[SET_RULE` {a,b} = {b,a} `] THEN
REWRITE_TAC[ MESON[]` a /\ b /\ c /\ d /\ e <=>
a /\ b /\ (c /\ d )/\ e`] THEN
NHANH (LEMMA16_INTERPRETE ) THEN
PURE_ONCE_REWRITE_TAC[MESON[]` a = b /\ P a <=> a = b
/\ P b `] THEN
SIMP_TAC[COS_PI2] THEN
NHANH (NOT_COLLINEAR_IMP_NOT_SIN0) THEN
PHA THEN
ONCE_REWRITE_TAC[MESON[REAL_ENTIRE]`~( a = &0 ) /\ a1 /\ ~( b = &0 ) /\ &0 = l /\ ll
<=> a1 /\ ~ ( b * a = &0 ) /\ &0 = l /\ ll`] THEN
ONCE_REWRITE_TAC[SET_RULE` {a,b} = {b,a} `] THEN
ONCE_REWRITE_TAC[MESON[]`a /\ ~( aa = &0 ) /\ b /\ c <=>
~( aa = &0 ) /\ c /\ a /\ b `] THEN
ABBREV_TAC `TU = sin (arcV v0 v3 v2) * sin (arcV v0 v3 (v1:real^N))` THEN
ABBREV_TAC `MA = (cos (arcV v0 v1 v2) - cos (arcV v0 v3 v2) * cos (arcV v0 v3 (v1:real^N)))` THEN
NHANH (MESON[REAL_FIELD`~( b = &0 ) /\ a / b = &0 ==> a = &0 `]`
~(TU = &0) /\
&0 = MA / TU /\ ll ==> MA = &0 `) THEN
REWRITE_TAC[dihV;beta; arcV] THEN
REPEAT LET_TAC THEN
STRIP_TAC THEN
MATCH_MP_TAC (MESON[]` a = b ==> P a = P b `) THEN
REPLICATE_TAC 2 (FIRST_X_ASSUM MP_TAC) THEN
NHANH ( NOT_COLLINEAR_IMP_VEC_FOR_DIHV ) THEN
ASM_SIMP_TAC[] THEN
PHA THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
SIMP_TAC[GSYM NOT_EQ_IMPCOS_ARC] THEN
DOWN_TAC THEN
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
SIMP_TAC[] THEN
STRIP_TAC THEN
EXPAND_TAC "va" THEN
EXPAND_TAC "vb" THEN
EXPAND_TAC "vc" THEN
UNDISCH_TAC `vb' = v2 - (v0:real^N)` THEN
UNDISCH_TAC `va' = v1 - (v0:real^N)` THEN
UNDISCH_TAC `vc' = v3 - (v0:real^N)` THEN
PHA THEN SIMP_TAC[GSYM DIHV_FORMULAR] THEN
ASM_SIMP_TAC[LEMMA16_INTERPRETE] THEN
DISCH_TAC THEN
UNDISCH_TAC `&0 = MA ` THEN
ASM_SIMP_TAC[REAL_ARITH` &0 = a - b <=> a = b `; ARC_SYM;
REAL_ARITH` a * b * a = b * a pow 2 `] THEN
SIMP_TAC[COS_POW2_INTER; REAL_SUB_LDISTRIB; REAL_MUL_RID;
REAL_ARITH` a - ( a - b ) = b `] THEN
UNDISCH_TAC `~collinear {v0, v1,(v3:real^N)}` THEN
NHANH (NOT_COLLINEAR_IMP_NOT_SIN0) THEN
PHA THEN SIMP_TAC[REAL_FIELD` ~( a = &0 ) ==>
( b * a pow 2) / ( a * c ) = (b * a) / c `] THEN
UNDISCH_TAC` ~collinear {v0, v1, (v2:real^N)}` THEN
NHANH (NOT_COLL_IM_SIN_LT) THEN
NHANH (REAL_LT_IMP_LE) THEN
UNDISCH_TAC `&0 <= cos (arcV v0 v2 (v3:real^N))` THEN
PHA THEN
NHANH (MESON[REAL_LE_MUL; REAL_LE_DIV]`
&0 <= a1 /\aa /\aa1/\
&0 <= a3 /\aa2/\aa3/\
&0 <= a2 /\ lll ==> &0 <= ( a1 * a2 )/ a3 `) THEN
STRIP_TAC THEN
FIRST_X_ASSUM MP_TAC THEN
SIMP_TAC[MESON[POW_2_SQRT]`&0 <= a ==> ( a = b
<=> sqrt ( a pow 2 ) = b )`] THEN
STRIP_TAC THEN
MATCH_MP_TAC (MESON[]` a = b ==> P a = P b `) THEN
EXPAND_TAC "psi" THEN
EXPAND_TAC "tte" THEN
UNDISCH_TAC `va' = (vc:real^N)` THEN
UNDISCH_TAC `vb' = (va:real^N)` THEN
UNDISCH_TAC `vc' = (vb:real^N)` THEN
UNDISCH_TAC ` vb = v3 - v0 /\ vc = v1 - v0 /\ va = v2 - (v0 :real^N)` THEN
PHA THEN SIMP_TAC[GSYM arcV] THEN
STRIP_TAC THEN
SIMP_TAC[REAL_FIELD` ( a / b ) pow 2 = a pow 2 / b pow 2 `] THEN
MATCH_MP_TAC (MESON[]` a = b /\ aa = bb ==> a / aa
= b / bb `) THEN
SIMP_TAC[SIN_POW2_EQ_1_SUB_COS_POW2; GSYM POW_2] THEN
SIMP_TAC[REAL_ARITH`(A * B ) pow 2 = A pow 2 *
B pow 2 `; SIN_POW2_EQ_1_SUB_COS_POW2] THEN
ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;









let INTERS_SUBSET = SET_RULE` P a ==> INTERS { x | P x } SUBSET a `;;

let AFFINE_SET_GENERARTED2 = prove(` affine {x | ? t. x = t % u + ( &1 - t ) % v } `,
REWRITE_TAC[affine; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
EXISTS_TAC `t * u' + (t':real) * v'` THEN FIRST_X_ASSUM MP_TAC THEN
SIMP_TAC[REAL_ARITH` a + b = c <=> a = c - b `] THEN
DISCH_TAC THEN ASM_SIMP_TAC[] THEN CONV_TAC VECTOR_ARITH);;

let BASED_POINT2 = prove(` {(u:real^N),v} SUBSET {x | ? t. x = t % u + ( &1 - t ) % v } `,
SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
[EXISTS_TAC ` &1 ` THEN CONV_TAC VECTOR_ARITH; EXISTS_TAC ` &0 `] THEN
CONV_TAC VECTOR_ARITH);;

let AFFINE_AFF = prove(` affine ( aff s ) `,
SIMP_TAC[aff; AFFINE_AFFINE_HULL]);;

let INSERT_EMPTY_SUBSET = prove(`(x INSERT s SUBSET t <=> x IN t /\ s SUBSET t)
/\ (!s. {} SUBSET s)`, SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET]);;



let IN_P_HULL_INSERT = prove(`a IN P hull (a INSERT s)`,
MATCH_MP_TAC (SET_RULE` a IN A /\ A SUBSET P hull A ==> a IN P hull A `) THEN
SIMP_TAC[IN_INSERT; HULL_SUBSET]);;

let UV_IN_AFF2 = MESON[INSERT_AC;IN_P_HULL_INSERT ]`
u IN affine hull {u,v}/\ v IN affine hull {u,v}`;;


let AFF2 = prove(` ! u (v:real^N). aff {u,v} = {x | ? t. x = t % u + ( &1 - t ) % v } `,
SIMP_TAC[GSYM SUBSET_ANTISYM_EQ] THEN REPEAT STRIP_TAC THENL
[SIMP_TAC[aff; hull] THEN MATCH_MP_TAC (INTERS_SUBSET) THEN
SIMP_TAC[BASED_POINT2 ;AFFINE_SET_GENERARTED2 ];
SIMP_TAC[SUBSET; IN_ELIM_THM]] THEN REPEAT STRIP_TAC THEN
MP_TAC (MESON[AFFINE_AFF]` affine ( aff {u, (v:real^N)})`) THEN
ASM_SIMP_TAC[aff; affine] THEN
MESON_TAC[UV_IN_AFF2; REAL_RING` a + &1 - a = &1 `]);;


GEN_ALL (SPECL [`p - (v0:real^N)`;`(u:real^N) - v0 `]
VECTOR_SUB_PROJECT_ORTHOGONAL);;

SPECL[` (u - (v:real^N))`;` (p:real^N)`]
VECTOR_SUB_PROJECT_ORTHOGONAL;;


let EXISTS_PROJECTING_POINT = prove(
`! (p:real^N) u v. ? pp. (u + pp ) IN aff {u,v} /\ (p - pp ) dot ( u - v ) = &0 `,
REPEAT STRIP_TAC THEN MP_TAC (SPECL[` (u - (v:real^N))`;` (p:real^N)`]
VECTOR_SUB_PROJECT_ORTHOGONAL) THEN STRIP_TAC THEN
EXISTS_TAC `((u - v) dot p) / ((u - v) dot (u - v)) % (u - (v:real^N))` THEN
ONCE_REWRITE_TAC[DOT_SYM] THEN
CONJ_TAC THENL [SIMP_TAC[AFF2; IN_ELIM_THM; VECTOR_ARITH` a + x % ( a - b ) =
(&1 + x ) % a + ( &1 - ( &1 + x )) % b `] THEN MESON_TAC[] ;
ASM_MESON_TAC[DOT_SYM]]);;


let UV_IN_AFF2_IMP_TRANSABLE = prove(`! v0 v1 u v.
u IN aff {v0,v1} /\ v IN aff {v0,v1} ==>
( ( u - v0 ) dot ( v1 - v0 )) * ( ( v - v0) dot ( v1 - v0 )) =
(( v1 - v0 ) dot ( v1 - v0 ) ) * ((u - v0 ) dot ( v - v0 )) `,
REPEAT GEN_TAC THEN REWRITE_TAC[AFF2; IN_ELIM_THM] THEN
STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_ARITH`(t % v0 + (&1 - t) % v1) - v0
= ( &1 - t ) % ( v1 - v0 )`] THEN SIMP_TAC[DOT_LMUL; DOT_RMUL] THEN
REAL_ARITH_TAC);;

let WHEN_K_POS_ARCV_STABLE = prove(` &0 < k ==>
arcV ( vec 0 ) u v = arcV ( vec 0 ) u ( k % v ) `,
REWRITE_TAC[arcV; VECTOR_SUB_RZERO; DOT_RMUL; NORM_MUL] THEN
SIMP_TAC[LT_IMP_ABS_REFL; REAL_FIELD`&0 < a ==> ( a * b ) /
( d * a * s ) = b / ( d * s ) `]);;


let ARCV_VEC0_FORM = prove(`arcV v0 u v = arcV (vec 0) (u - v0) (v - v0)`,
REWRITE_TAC[arcV; VECTOR_SUB_RZERO]);;

let WHEN_K_POS_ARCV_STABLE2 = prove(` k < &0 ==>
arcV ( vec 0 ) u v = arcV ( vec 0 ) u ( ( -- k) % v ) `,
REWRITE_TAC[REAL_ARITH` n < &0 <=> &0 < -- n `;
WHEN_K_POS_ARCV_STABLE ]);;

let WHEN_K_DIFF0_ARCV = prove(` ~ ( k = &0 ) ==>
arcV ( vec 0 ) u v = arcV ( vec 0 ) u ( ( abs k ) % v ) `,
REWRITE_TAC[REAL_ABS_NZ; WHEN_K_POS_ARCV_STABLE ]);;



let PITHAGO_THEOREM = prove(`x dot y = &0
==> norm (x + y) pow 2 = norm x pow 2 + norm y pow 2 /\
norm (x - y) pow 2 = norm x pow 2 + norm y pow 2`,
SIMP_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_RSUB; DOT_LSUB; DOT_SYM] THEN
REAL_ARITH_TAC);;


let NORM_SUB_INVERTABLE = NORM_ARITH` norm (x - y) = norm (y - x)`;;



let OTHORGONAL_WITH_COS = prove(` ! v0 v1 w (p:real^N).
~(v0 = w) /\
~(v0 = v1) /\
(w - p) dot (v1 - v0) = &0
==> cos (arcV v0 v1 w) =
((p - v0) dot (v1 - v0)) / (norm (v1 - v0) * norm (w - v0))`,
REPEAT GEN_TAC THEN SIMP_TAC[NOT_EQ_IMPCOS_ARC] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MESON[]` a = b ==> a / c = b / c `) THEN
ONCE_REWRITE_TAC[REAL_RING` a = b <=> a - b = &0 `] THEN
ONCE_REWRITE_TAC[MESON[DOT_SYM]` a dot b - c = b dot a - c `] THEN
FIRST_X_ASSUM MP_TAC THEN SIMP_TAC[GSYM DOT_LSUB; VECTOR_ARITH`
w - v0 - (p - v0) = w - (p:real^N)`; REAL_SUB_RZERO; DOT_SYM]);;


let SIMPLIZE_COS_IF_OTHOR = prove(` ! v0 v1 w (p:real^N).
~(v0 = w) /\
~(v0 = v1) /\ ( p - v0 ) = k % (v1 - v0 ) /\
(w - p) dot (v1 - v0) = &0
==> cos (arcV v0 v1 w) =
k * norm ( v1 - v0 ) / norm (w - v0) `,
SIMP_TAC[OTHORGONAL_WITH_COS; DOT_LMUL; GSYM NORM_POW_2] THEN
REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN REWRITE_TAC[GSYM NORM_POS_LT]
THEN CONV_TAC REAL_FIELD);;


let SIN_EQ_SQRT_ONE_SUB = prove(` ~((v0:real^N) = va) /\ ~(v0 = vb) ==>
sin ( arcV v0 va vb ) = sqrt ( &1 - cos ( arcV v0 va vb ) pow 2 ) `,
DISCH_TAC THEN MATCH_MP_TAC (SIN_COS_SQRT) THEN ASM_SIMP_TAC[PROVE_SIN_LE]);;



let SIN_DI_HOC = prove(`~((v0:real^N) = w) /\ ~(v0 = vb) /\ p IN aff {v0, w} /\ (p - vb) dot (w - v0) = &0
==> sin (arcV v0 w vb) = norm (p - vb) / norm (vb - v0)`,
SIMP_TAC[SIN_EQ_SQRT_ONE_SUB] THEN ONCE_REWRITE_TAC[REAL_ARITH` a = &0 <=> -- a = &0 `] THEN
SIMP_TAC[GSYM DOT_LNEG; VECTOR_NEG_SUB; OTHORGONAL_WITH_COS] THEN
SIMP_TAC[AFF2; IN_ELIM_THM; VECTOR_ARITH` p = t % v0 + (&1 - t) % w
<=> p - v0 = (&1 - t ) % ( w - v0 ) `] THEN
STRIP_TAC THEN ASM_SIMP_TAC[DOT_LMUL; GSYM NORM_POW_2] THEN
ONCE_REWRITE_TAC[MESON[REAL_LE_DIV; POW_2_SQRT; NORM_POS_LE]`
norm a / norm b = sqrt (( norm a / norm b ) pow 2 ) `] THEN
MATCH_MP_TAC (MESON[]` a = b ==> p a = p b `) THEN
UNDISCH_TAC` ~(v0 = (w:real^N))` THEN UNDISCH_TAC`~(v0 = (vb:real^N))` THEN
ONCE_REWRITE_TAC[VECTOR_ARITH` a = b <=> (b:real^N) - a = vec 0 `] THEN
SIMP_TAC[ GSYM NORM_POS_LT; REAL_FIELD` &0 < a ==>
( c * a pow 2 ) / ( a * b ) = (c * a )/ b /\
&1 - ( b / a ) pow 2 = ( a pow 2 - b pow 2 ) / a pow 2 `] THEN
REPEAT STRIP_TAC THEN SIMP_TAC[DIV_POW2] THEN
MATCH_MP_TAC (MESON[]` a = b ==> a / x = b / x `) THEN
SIMP_TAC[MUL_POW2] THEN ONCE_REWRITE_TAC[MESON[REAL_POW2_ABS]`
a pow 2 * t = ( abs a ) pow 2 * t`] THEN
SIMP_TAC[GSYM MUL_POW2; GSYM NORM_MUL] THEN DOWN_TAC THEN
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN SIMP_TAC[] THEN
NHANH (MESON[]` a = b ==> ( vb - (p:real^N)) dot a
= ( vb - (p:real^N)) dot b `) THEN
REWRITE_TAC[DOT_RMUL; MESON[]` ( a /\ x * t = c ) /\
&0 = t /\ l <=> a /\ c = x * ( &0 ) /\ t = &0 /\ l `;
REAL_MUL_RZERO] THEN NHANH (PITHAGO_THEOREM) THEN
SIMP_TAC[VECTOR_ARITH` vb - p + p - v0 = vb - (v0:real^N)`] THEN
STRIP_TAC THEN SIMP_TAC[NORM_SUB] THEN REAL_ARITH_TAC );;


let CHANG_BIET_GI = prove(`pu - p = (&1 - t) % (w - p) ==> pu IN aff {p, w}`,
REWRITE_TAC[AFF2; IN_ELIM_THM; VECTOR_ARITH`pu - p = (&1 - t) % (w - p) <=>
pu = t % p + ( &1 - t ) % w `] THEN MESON_TAC[]);;


let SUB_DOT_EQ_0_INVERTALE = prove(` ( a - b ) dot c = &0 <=> ( b - a ) dot c = &0 `,
SIMP_TAC[DOT_LSUB] THEN REAL_ARITH_TAC);;


let SIN_DI_HOC2 = ONCE_REWRITE_RULE[SUB_DOT_EQ_0_INVERTALE] SIN_DI_HOC;;



let KEY_LEMMA_FOR_ANGLES = prove(`! (p:real^N) u v w pu pv. pu IN aff {p,w} /\ pv IN aff {p,w} /\
( u - pu ) dot (w - p ) = &0 /\
( v - pv ) dot (w - p ) = &0 /\
~( p = u \/ p = v \/ p = w ) ==>
cos ( arcV p w u + arcV p w v ) - cos ( arcV p u v ) =
(-- ( v - pv ) dot ( u - pu ) - norm ( v - pv ) * norm ( u - pu )) /
(norm ( p - u ) * norm ( p - v ))`,
SIMP_TAC[COS_ADD; AFF2; IN_ELIM_THM; VECTOR_ARITH` pu = t % p + (&1 - t) % w <=> pu - p = ( &1 - t ) % (w - p ) `;
DE_MORGAN_THM] THEN
REPEAT STRIP_TAC THEN
DOWN_TAC THEN
NHANH (MESON[SIMPLIZE_COS_IF_OTHOR]` pu - p = (&1 - t) % (w - p) /\
pv - p = (&1 - t') % (w - p) /\
(u - pu) dot (w - p) = &0 /\
(v - pv) dot (w - p) = &0 /\
~(p = u) /\
~(p = v) /\
~(p = w) ==> cos (arcV p w u) =
(&1 - t ) * norm (w - p) / norm (u - p) /\
cos (arcV p w v) =
( &1 - t') * norm (w - p ) / norm ( v - p ) `) THEN
NHANH (CHANG_BIET_GI) THEN
NHANH (MESON[SIN_DI_HOC2]`(a11 /\ pu IN aff {p, w}) /\
(a22 /\ pv IN aff {p, w}) /\
(u - pu) dot (w - p) = &0 /\
(v - pv) dot (w - p) = &0 /\
~(p = u) /\
~(p = v) /\
~(p = w) ==>
sin (arcV p w u) = norm ( pu - u ) / norm ( u - p ) /\
sin (arcV p w v) = norm ( pv - v ) / norm ( v - p ) `) THEN
STRIP_TAC THEN
ASM_SIMP_TAC[NOT_EQ_IMPCOS_ARC; REAL_FIELD` a / b * aa / bb
= ( a * aa ) / ( b * bb ) `; REAL_RING` (a * b ) * c * d = a * c * b * d `;
REAL_FIELD` a * b / c = ( a * b ) / c `; REAL_FIELD ` a / b - c / b
= ( a - c ) / b `; NORM_SUB] THEN
MATCH_MP_TAC (MESON[]` a = b ==> a / x = b / x `) THEN
SIMP_TAC[NORM_SUB; REAL_MUL_SYM; REAL_ARITH` a - b - c = v - b <=>
a - c - v = &0 `] THEN
REWRITE_TAC[MESON[VECTOR_ARITH` a - b = a - x + x - (b:real^N)`]`
a - (u - p) dot (v - p) = a - (u - pu + pu - p) dot (v - pv + pv - p) `;
DOT_LADD; DOT_RADD] THEN
ASM_SIMP_TAC[DOT_LMUL; DOT_RMUL; DOT_SYM; REAL_MUL_RZERO;
REAL_ADD_RID; GSYM NORM_POW_2; GSYM POW_2; NORM_SUB;DOT_LNEG;
REAL_ADD_LID] THEN REAL_ARITH_TAC);;





let ARCV_BOUNDED = prove(` ~( v0 = u ) /\ ~ ( v0 = v ) ==>
&0 <= arcV v0 u v /\ arcV v0 u v <= pi`,
NHANH (NOT_IDEN_IMP_ABS_LE) THEN REWRITE_TAC[arcV; REAL_ABS_BOUNDS]
THEN SIMP_TAC[ACS_BOUNDS]);;


(* This lemma in Multivariate/transc.ml
let COS_MONO_LT_EQ = new_axiom
`!x y. &0 <= x /\ x <= pi /\ &0 <= y /\ y <= pi
==> (cos(x) < cos(y) <=> y < x)`;;
*)


let COS_MONOPOLY = prove(
` ! a b. &0 <= a /\ a <= pi /\ &0 <= b /\ b <= pi ==>
( a < b <=> cos b < cos a ) `, MESON_TAC[COS_MONO_LT_EQ]);;

let COS_MONOPOLY_EQ = prove(
` ! a b. &0 <= a /\ a <= pi /\ &0 <= b /\ b <= pi ==>
( a <= b <=> cos b <= cos a ) `,
REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT]
THEN ASM_MESON_TAC[COS_MONOPOLY ]);;


let END_POINT_ADD_IN_AFF2 = prove(`!k (u:real^N) v. u + k % (u - v) IN aff {u, v} /\
u + k % (v - u ) IN aff {u,v} `,
REWRITE_TAC[AFF2; VECTOR_ARITH` u + k % (u - v) =
( &1 + k ) % u + ( &1 - ( &1 + k )) % v `] THEN
SIMP_TAC[VECTOR_ARITH` u + k % (v - u) =
(&1 - k) % u + (&1 - (&1 - k)) % v`] THEN SET_TAC[]);;

let EXISTS_PROJECTING_POINT2 = prove(`!(p:real^N) u v0 . ?pp. pp IN aff {u, v0} /\ (p - pp) dot (u - v0) = &0`,
REPEAT GEN_TAC THEN MP_TAC (SPECL[` u - (v0:real^N) `; `p - ( v0 :real^N)`]
VECTOR_SUB_PROJECT_ORTHOGONAL) THEN
SIMP_TAC[DOT_SYM; VECTOR_ARITH` a - b - c = a - ( b + (c:real^N))`] THEN
ONCE_REWRITE_TAC[INSERT_AC] THEN MESON_TAC[END_POINT_ADD_IN_AFF2 ]);;


let KEY_LEMMA_FOR_ANGLES1 =
ONCE_REWRITE_RULE[ INSERT_AC] KEY_LEMMA_FOR_ANGLES;;

SPECL[`p:real^N`; `u:real^N`; `v:real^N`;`x:real^N`;`ux:real^N`;`vx:real^N`]
KEY_LEMMA_FOR_ANGLES1;;

let ARCV_INEQUALTY = prove(`! p u v (x:real^N). ~ ( p = x ) /\ ~( p = u ) /\ ~( p = v ) ==>
arcV p u v <= arcV p u x + arcV p x v `,
NHANH (ARCV_BOUNDED) THEN
REPEAT GEN_TAC THEN
ASM_CASES_TAC` pi <= arcV p u x + arcV p x (v:real^N)` THENL
[ASM_MESON_TAC[REAL_LE_TRANS];
PHA THEN
NHANH (MESON[ARCV_BOUNDED ]`~(p = x) /\ ~(p = u) /\ ~(p = v) /\ l
==> &0 <= arcV p u x /\ &0 <= arcV p x v `) THEN
NHANH (REAL_LE_ADD) THEN
DOWN_TAC THEN
NHANH (REAL_ARITH` ~(a <= b ) ==> b <= a `) THEN
SIMP_TAC[COS_MONOPOLY_EQ ] THEN
MP_TAC (MESON[EXISTS_PROJECTING_POINT2]` ? (ux:real^N) vx.
ux IN aff {x,p} /\ vx IN aff {x,p} /\
( u - ux ) dot (x - p ) = &0 /\
( v - vx ) dot ( x - p ) = &0 `) THEN
REPEAT STRIP_TAC THEN
DOWN_TAC THEN
REWRITE_TAC[MESON[]` ux IN aff {x, p} /\
vx IN aff {x, p} /\
(u - ux) dot (x - p) = &0 /\
(v - vx) dot (x - p) = &0 /\a11/\a22 /\
~(p = x) /\
~(p = u) /\
~(p = v) /\ l <=> a11 /\ a22 /\ l /\ ux IN aff {x, p} /\
vx IN aff {x, p} /\
(u - ux) dot (x - p) = &0 /\
(v - vx) dot (x - p) = &0 /\
~(p = u \/ p = v \/ p = x) `] THEN
NHANH (SPECL[`p:real^N`; `u:real^N`; `v:real^N`;`x:real^N`;`ux:real^N`;`vx:real^N`]
KEY_LEMMA_FOR_ANGLES1) THEN
ONCE_REWRITE_TAC[REAL_ARITH` a <= b <=> a - b <= &0 `] THEN
SIMP_TAC[ARC_SYM; DE_MORGAN_THM] THEN
ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
SIMP_TAC[GSYM NORM_POS_LT; REAL_FIELD` a / ( b * c ) = ( a / b) / c `] THEN
SIMP_TAC[REAL_ARITH` (a/ b ) / c <= &0 <=> &0 <= (( -- a ) / b ) / c `;
REAL_LE_RDIV_0] THEN
STRIP_TAC THEN
REWRITE_TAC[REAL_ARITH`&0 <= -- ( a - b ) <=> a <= b `] THEN
MESON_TAC[NORM_NEG; NORM_CAUCHY_SCHWARZ]]);;

let KEITDWB = ARCV_INEQUALTY;;
(* June *)

g `! (p:real^N) (n:num) fv.
2 <= n /\ (!i. i <= n ==> ~(p = fv i))
==> arcV p (fv 0) (fv n) <=
sum (0..n - 1) (\i. arcV p (fv i) (fv (i + 1)))`;;
e (GEN_TAC);;
e (INDUCT_TAC);;
e (SIMP_TAC[ARITH_RULE` ~( 2 <= 0 ) `]);;
e (SPEC_TAC (`n:num`,` a:num`));;
e (INDUCT_TAC);;
e (SIMP_TAC[ONE; ARITH_RULE` ~(2 <= SUC 0) `]);;
e (SPEC_TAC(`a:num`,`u:num`));;
e (INDUCT_TAC);;
e (SIMP_TAC[ARITH_RULE` 2 <= 2 `;ARITH_RULE `SUC ( SUC 0 ) = 2 ` ]);;
e (SIMP_TAC[ARITH_RULE` 0 < 1 /\ 2 - 1 = 1 `;ARITH_RULE` 0 <= 1 `;
SUM_CLAUSES_RIGHT]);;
e (SIMP_TAC[SUB_REFL; SUM_SING_NUMSEG; ADD; ARITH_RULE` 1 + 1 = 2 `;
ARITH_RULE` i <= 2 <=> i = 0 \/ i = 1 \/ i = 2 `]);;
e (SIMP_TAC[MESON[]` (! a. a = x \/ a = y \/ a = z ==> Q a ) <=>
Q x /\ Q y /\ Q z `]);;
e (MP_TAC ARCV_INEQUALTY );;
e (SIMP_TAC[IN_INSERT; NOT_IN_EMPTY]);;
e (GEN_TAC);;
e (MP_TAC (ARITH_RULE` 2 <= SUC ( SUC u )`));;
e (ABBREV_TAC ` ed = ( SUC (SUC u ))`);;
e (REWRITE_TAC[ADD1; ARITH_RULE` a <= b + 1 <=> a <= b \/
a = b + 1 `; MESON[]` (! x. p x \/ x = a ==> h x ) <=>
(! x. p x ==> h x ) /\ h a `]);;
e (PHA);;
e (ONCE_REWRITE_TAC[MESON[]` a /\ b/\ c/\ d <=> b /\ d /\ a /\ c `]);;
e (REPLICATE_TAC 2 (FIRST_X_ASSUM MP_TAC));;
e (PHA);;
e (NHANH (MESON[]`(!fv. 2 <= ed /\ (!i. i <= ed ==> ~(p = fv i))
==> Q fv) /\a1 /\a2 /\a3 /\ 2 <= ed /\ (!i. i <= ed ==> ~(p = fv i)) ==> Q fv `));;
e (NHANH (ARITH_RULE` 2 <= d ==> 0 < d - 1 + 1 /\ 0 <= d - 1 + 1 `));;
e (SIMP_TAC[ARITH_RULE` 2 <= a ==> ( a + 1 ) - 1 = a - 1 + 1 `;
SUM_CLAUSES_RIGHT]);;
e (ASM_SIMP_TAC[ARITH_RULE` (ed - 1 + 1) - 1 = ed - 1 `]);;
e (SIMP_TAC[ARITH_RULE` 2 <= d ==> d - 1 + 1 = d `]);;
e (PHA);;
e (REWRITE_TAC[MESON[ARITH_RULE` 2 = ed + 1 ==> ~( 2 <= ed ) `]`
( a \/ 2 = ed + 1) /\ aa /\
2 <= ed /\ ll <=> a /\ aa /\
2 <= ed /\ ll `]);;
e (STRIP_TAC THEN FIRST_X_ASSUM MP_TAC);;
e (MATCH_MP_TAC (REAL_ARITH` a <= b + c ==> b <= x ==> a <= x + c `));;
e (FIRST_X_ASSUM MP_TAC);;
e (NHANH (MESON[LE_REFL; LE_0]` (! i. i <= d ==> p i ) ==> p ( 0 ) /\
p ( d ) `));;
e (MP_TAC (ARCV_INEQUALTY));;
e (ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY]);;
let FGNMPAV = top_thm();;




let IMP_TAC = ONCE_REWRITE_TAC[MESON[]` a/\ b ==> c
<=> a ==> b ==> c `];;

g ` &0 <= t12 /\ t12 < &2 * pi /\ t12 = &2 * pi * real_of_int k12
==> t12 = &0 `;;
e (ASM_CASES_TAC` (k12:int) < &0 `);;
e (MP_TAC (PI_POS));;
e (DOWN_TAC);;
e (SIMP_TAC[GSYM REAL_NEG_GT0; int_lt; int_of_num_th]);;
e (NGOAC THEN NHANH (REAL_LT_MUL));;
e (REWRITE_TAC[REAL_ARITH` &0 < -- a * b <=> &2 * b * a < &0 `]);;
e (MESON_TAC[REAL_ARITH` ~( a < &0 /\ &0 <= a ) `]);;
e (ASM_CASES_TAC `(k12:int) = &0 `);;
e (ASM_SIMP_TAC[int_of_num_th; REAL_MUL_RZERO]);;
e (DOWN_TAC);;
e (NGOAC);;
e (REWRITE_TAC[ARITH_RULE` ~(k12 < &0) /\ ~((k12:int) = &0) <=> &1 <= k12 `]);;
e (SIMP_TAC[int_le; int_of_num_th]);;
e (MP_TAC PI_POS);;
e (PHA);;
e (ONCE_REWRITE_TAC[MESON[REAL_LE_LMUL_EQ]` &0 < pi /\
&1 <= aa /\ l <=> &0 < pi /\ pi * &1 <= pi * aa /\ l `]);;
e (REWRITE_TAC[REAL_ARITH` a * &1 <= b <=> &2 * a <= &2 * b `]);;
e (MESON_TAC[REAL_ARITH` ~( a < b /\ b <= a ) `]);;
let IN_A_PERIOD_IDE0 = top_thm();;


let UNIQUE_PROPERTY_IN_A_PERIOD = prove(
`&0 <= t12 /\ t12 < &2 * pi /\ &0 <= a /\ a < &2 * pi /\
t12 = a + &2 * pi * real_of_int k12 ==> t12 = a `,
NHANH (REAL_FIELD` &0 <= t12 /\
t12 < &2 * pi /\
&0 <= a /\
a < &2 * pi /\ ll ==> t12 + -- a < &2 * pi /\
-- ( t12 + -- a ) < &2 * pi `) THEN
ASM_CASES_TAC` &0 <= t12 + -- a ` THENL [
REWRITE_TAC[REAL_ARITH` a = b + c <=> a + -- b = c `] THEN
STRIP_TAC THEN
ONCE_REWRITE_TAC[REAL_ARITH` a = b <=> a + -- b = &0 `] THEN
DOWN_TAC THEN
MESON_TAC[IN_A_PERIOD_IDE0 ];
SIMP_TAC[REAL_ARITH` a = b + c * d * e <=>
-- ( a + -- b ) = c * d * ( -- e ) `; GSYM int_neg_th] THEN
STRIP_TAC THEN
ONCE_REWRITE_TAC[REAL_ARITH` a = b <=> -- ( a + -- b ) = &0 `] THEN
DOWN_TAC THEN
NHANH (REAL_ARITH` ~(&0 <= b ) ==> &0 <= -- b `) THEN
MESON_TAC[IN_A_PERIOD_IDE0 ]]);;








g `!t1 t2 k12 k21.
&0 <= t1 /\
t1 < &2 * pi /\
&0 <= t2 /\
t2 < &2 * pi /\
&0 <= t12 /\
t12 < &2 * pi /\
&0 <= t21 /\
t21 < &2 * pi /\
t12 = t1 - t2 + &2 * pi * real_of_int k12 /\
t21 = t2 - t1 + &2 * pi * real_of_int k21
==> (t1 = t2 ==> t12 + t21 = &0) /\ (~(t1 = t2) ==> t12 + t21 = &2 * pi)`;;
e (REPEAT STRIP_TAC);;
e (DOWN_TAC);;
e (DAO);;
e (IMP_TAC);;
e (SIMP_TAC[REAL_SUB_REFL; REAL_ADD_LID; REAL_ADD_RID]);;
e (NHANH (MESON[IN_A_PERIOD_IDE0]` t21 = &2 * pi * real_of_int k21 /\
t12 = &2 * pi * real_of_int k12 /\
t21 < &2 * pi /\
&0 <= t21 /\
t12 < &2 * pi /\
&0 <= t12 /\ l ==> &0 = t12 /\ &0 = t21 `));;
e (ONCE_REWRITE_TAC[EQ_SYM_EQ]);;
e (SIMP_TAC[REAL_ADD_LID]);;


e (DOWN_TAC);;
e (SPEC_TAC(`t1:real`,` t1:real`));;
e (SPEC_TAC(`t2:real`,` t2:real`));;
e (SPEC_TAC(`t12:real`,` t12:real`));;
e (SPEC_TAC(`t21:real`,` t21:real`));;
e (SPEC_TAC(`k12:int`,` k12:int`));;
e (SPEC_TAC(`k21:int`,` k21:int`));;
e (MATCH_MP_TAC (MESON[REAL_ARITH` a <= b \/ b <= a `]` (! a1 b1 a2 b2 a b.
P a1 b1 a2 b2 a b <=> P b1 a1 b2 a2 b a ) /\
(! a2 b2. L a2 b2 <=> L b2 a2 ) /\
(! a1 b1 a2 b2 a b.
P a1 b1 a2 b2 a b /\ a <= (b:real) ==> L a2 b2 )
==> (! a1 b1 a2 b2 a b. P a1 b1 a2 b2 a b ==>
L a2 b2 ) `));;
e (CONJ_TAC);;
e (MESON_TAC[]);;

e (CONJ_TAC);;
e (SIMP_TAC[REAL_ADD_SYM]);;
e (NHANH (REAL_FIELD` &0 <= t1 /\
t1 < &2 * pi /\
&0 <= t2 /\
t2 < &2 * pi /\
&0 <= t12 /\
t12 < &2 * pi /\ l ==> t1 - t2 < &2 * pi`));;
e (REPEAT STRIP_TAC);;
e (REPLICATE_TAC 3 (FIRST_X_ASSUM MP_TAC));;
e (ONCE_REWRITE_TAC[REAL_ARITH` a <= b <=> &0 <= b - a `]);;
e (PHA);;
e (ONCE_REWRITE_TAC[GSYM REAL_SUB_0]);;
e (NHANH (REAL_FIELD` ~( t2 = &0) /\
t2 < pp /\
&0 <= t2 ==> &0 <= pp - t2 /\ pp - t2 < pp `));;
e (FIRST_X_ASSUM MP_TAC);;
e (ONCE_REWRITE_TAC[REAL_ARITH` a - b + &2* pi * c =
&2 * pi - ( b - a ) + &2 * pi * ( c - &1 ) `]);;
e (ABBREV_TAC ` ttt = &2 * pi - (t1 - t2)`);;
e (ONCE_REWRITE_TAC[MESON[int_of_num_th]` &1 = real_of_int (&1)`]);;
e (DOWN_TAC);;
e (REWRITE_TAC[GSYM int_sub_th]);;
e (NHANH (MESON[UNIQUE_PROPERTY_IN_A_PERIOD]`
&0 <= t12 /\
t12 < &2 * pi /\
&0 <= t21 /\
t21 < &2 * pi /\
t12 = t1 - t2 + &2 * pi * real_of_int k12 /\
&2 * pi - (t1 - t2) = ttt /\
t21 = ttt + &2 * pi * real_of_int (k21 - &1) /\
~(t1 - t2 = &0) /\
t1 - t2 < &2 * pi /\
&0 <= t1 - t2 /\
&0 <= ttt /\
ttt < &2 * pi ==> t1 - t2 = t12 /\ ttt = t21 `));;
e (ONCE_REWRITE_TAC[EQ_SYM_EQ]);;
e (SIMP_TAC[]);;
e (STRIP_TAC);;
e (CONV_TAC REAL_RING);;

let PDPFQUK = top_thm();;
(* June, 2009 *)


(* June, 2009 *)
let QAFHJNM = prove(`! (v:real^N) w x .
let e3 = ( &1 / norm ( w - v )) % (w - v ) in
let r = norm ( x - v ) in
let phi = arcV v w x in
~( v = x ) /\ ~ ( v = w )
==> (? u'. u' dot e3 = &0 /\
x = v + u' + ( r * cos phi ) % e3 ) `,
NHANH (MESON[EXISTS_PROJECTING_POINT2]`l /\ ~(v = w) ==> (?pp. (pp:real^N) IN aff {w, v}
/\ (x - pp) dot (w - v) = &0 ) `) THEN REPEAT STRIP_TAC THEN REPEAT LET_TAC THEN
SIMP_TAC[AFF2; IN_ELIM_THM; VECTOR_ARITH` pp = t % w + (&1 - t) % v <=> pp - v = t % ( w - v ) `]
THEN EXPAND_TAC "phi" THEN STRIP_TAC THEN EXISTS_TAC ` x - (pp:real^N)` THEN
REPLICATE_TAC 4 (FIRST_X_ASSUM MP_TAC) THEN PHA THEN NHANH (SIMPLIZE_COS_IF_OTHOR) THEN
EXPAND_TAC "e3" THEN SIMP_TAC[DOT_RMUL; REAL_MUL_RZERO; VECTOR_MUL_ASSOC] THEN
ONCE_REWRITE_TAC[VECTOR_ARITH` a = b <=> b - a = vec 0 `] THEN
SIMP_TAC[GSYM NORM_EQ_0] THEN EXPAND_TAC "r" THEN SIMP_TAC[GSYM NORM_EQ_0; REAL_FIELD`
~(x = &0) /\ ~(w = &0) ==> ( x * t * w / x ) * &1 / w = t `] THEN
SIMP_TAC[VECTOR_ARITH` (v + x - pp + tt ) - x = (tt: real^N) - (pp - v) `]);;

(* August, 2009 *)
let YBXRVTS = prove(`! v w (u:real^3) x.
~collinear {v,w,u} /\
n = (w - v) cross (u - v ) /\
x IN aff {v,w,u} ==>
angle (( v + n ), v, x) = pi / &2 `,
REWRITE_TAC[aff;AFFINE_HULL_3; IN_ELIM_THM;angle; vector_angle] THEN
REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [REWRITE_TAC[];
UNDISCH_TAC ` u' + v' + w' = &1 ` THEN
ASM_SIMP_TAC[VECTOR_ARITH`(a + b ) - a = (b:real^N)`; REAL_ARITH` a + b = &1 <=> a = &1 - b `;
VECTOR_ARITH` ((&1 - (v' + w')) % v + v' % w + w' % u) - v = v' % ( w - v ) + w' % ( u - v ) `;
DOT_RADD; DOT_RMUL; DOT_CROSS_SELF;REAL_MUL_RZERO ;REAL_ADD_RID; REAL_ARITH` &0 / a = &0`; PI2_EQ_ACS0]]);;




let types_thm th = let cl = concl th in
List.map dest_var (frees cl );;

let seans_fn () =
let (tms,tm) = top_goal () in
let vss = map frees (tm::tms) in
let vs = setify (flat vss) in
map dest_var vs;;



(* ========= NEW RULES and TAC TIC ============================= *)
(* ============================================================= *)
(* ============================================================= *)


let PAT_REWRITE_TAC tm thms =
(CONV_TAC (PAT_CONV tm (REWRITE_CONV thms )));;

let FOR_ASM th =
let th1 = REWRITE_RULE[MESON[]` a /\ b ==> c <=>
a ==> b ==> c `] th in
let th2 = SPEC_ALL th1 in UNDISCH_ALL th2;;

(* change a th having form |- A ==> t to the form A |- t
to get ready to some other commands


|- A ==> t
----------- FOR_ASM
A |- t
*)

let ASSUME_TAC2 = ASSUME_TAC o FOR_ASM;;


let PAT_ONCE_REWRITE_TAC tm thms =
(CONV_TAC (PAT_CONV tm (ONCE_REWRITE_CONV thms )));;

let ASM_PAT_RW_TAC tm thms = EVERY_ASSUM (fun th ->
(CONV_TAC (PAT_CONV tm (ONCE_REWRITE_CONV
( th ::[ thms ] )))));;

let PAT_TH_TAC tm th =
(CONV_TAC (PAT_CONV tm (REWRITE_CONV[th] )));;

(* rewurte a goal with one theorem *)

let IMP_TO_EQ_RULE th = MATCH_MP (TAUT` (a ==> b ) ==>
( a <=> a /\ b )`) (SPEC_ALL th);;

let NHANH_PAT tm th = PAT_ONCE_REWRITE_TAC tm
[ IMP_TO_EQ_RULE th ];;



let USE_FIRST tm tac = UNDISCH_TAC tm THEN DISCH_TAC THEN
FIRST_ASSUM tac;;


let ONCE_SIMP_IDENT tm tth = (UNDISCH_TAC tm) THEN
DISCH_TAC THEN FIRST_ASSUM ( fun th ->
ONCE_REWRITE_TAC[(MATCH_MP tth th)] );;


let SIMP_TAC1 th = SIMP_TAC[ th];;

let SIMP_TACC1 th = ASSUME_TAC2 th THEN FIRST_X_ASSUM
SIMP_TAC1;;

let SIMP_IDENT thms tm = UNDISCH_TAC tm THEN (SIMP_TAC thms)
THEN DISCH_TAC;;
USE_FIRST;;




let ELIM_IDENTS th = ASSUME_TAC2 th THEN FIRST_X_ASSUM
( fun thh -> SIMP_TAC[ thh]);;

(* ============================================================== *)
(* ============================================================== *)
(* ============================================================== *)





let GIVEN_POINT_EXISTS_2_NOT_COLLINEAR = prove(` !(x:real^3). ? y z. ~ collinear {x,y,z} `,
GEOM_ORIGIN_TAC `x:real^3` THEN EXISTS_TAC` (vector [&1; &0; &0 ]) : real^3` THEN
EXISTS_TAC` (vector [&0; &1; &0 ]) : real^3` THEN
REWRITE_TAC[GSYM CROSS_EQ_0; cross; VECTOR_3] THEN
CONV_TAC REAL_RAT_REDUCE_CONV THEN
REWRITE_TAC[VECTOR_EQ; DOT_LZERO; DOT_3; VECTOR_3] THEN REAL_ARITH_TAC);;


let NOT_BASISES_EQ_VEC0 = prove(` ~( basis 1 = ((vec 0): real^3) \/
basis 2 = ((vec 0): real^3) \/ basis 3 = ((vec 0): real^3) ) `,
REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THENL [
MATCH_MP_TAC BASIS_NONZERO THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC; CONJ_TAC THENL [
MATCH_MP_TAC BASIS_NONZERO THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
MATCH_MP_TAC BASIS_NONZERO THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC]]);;


let TOW_DISTINCT_POINTS_EXISTS_RD_NOT_COLLINEAR = prove(
`! x (y: real^3). ~( x = y ) ==> (? z. ~ collinear {x,y,z} )`,
GEOM_ORIGIN_TAC `x:real^3` THEN GEOM_BASIS_MULTIPLE_TAC 1 `y:real^3` THEN
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
REPEAT STRIP_TAC THEN EXISTS_TAC ` (basis 2) :real^3` THEN
REWRITE_TAC[GSYM CROSS_EQ_0; CROSS_LMUL; CROSS_BASIS] THEN
REWRITE_TAC[VECTOR_MUL_EQ_0] THEN FIRST_X_ASSUM MP_TAC THEN
SIMP_TAC[REWRITE_RULE[DE_MORGAN_THM] NOT_BASISES_EQ_VEC0 ]);;


let SUBSET_IMP_SUBSET_HULL = prove(`a SUBSET b ==> a SUBSET P hull b `,
MATCH_MP_TAC (SET_RULE`b SUBSET P hull b ==> a SUBSET b ==> a SUBSET P hull b `) THEN
REWRITE_TAC[HULL_SUBSET]);;


let THREE_POINT_IMP_EXISTS_3 = prove(`! (v1:real^3) v2 v3. ? w2 w3.
~( collinear {v1,w2,w3} ) /\ {v1,v2,v3} SUBSET affine hull {v1,w2,w3} `,
REPEAT GEN_TAC THEN ASM_CASES_TAC` collinear {(v1: real^3),v2,v3} ` THENL
[FIRST_X_ASSUM MP_TAC THEN GEOM_ORIGIN_TAC `v1: real^3` THEN
REPEAT GEN_TAC THEN PAT_REWRITE_TAC `\x. x ==> _ ` [COLLINEAR_LEMMA] THEN
SPEC_TAC (`v3:real^3`,`v3: real^3`) THEN SPEC_TAC (`v2:real^3`,`v2: real^3`) THEN
MATCH_MP_TAC (MESON[]`(!a b. P a b <=> P b a) /\ (!v w. v = vec 0 \/ l v w ==> P v w)
==> (!v w. v = vec 0 \/ w = vec 0 \/ l v w ==> P v w)`) THEN
SIMP_TAC[INSERT_AC] THEN REPEAT STRIP_TAC THENL [
ONCE_REWRITE_TAC[SET_RULE` {a,b,c} = {c,a,b} `] THEN
ASM_CASES_TAC `(v3:real^3) = vec 0 ` THENL [
MP_TAC (SPEC`(vec 0) :real^3` GIVEN_POINT_EXISTS_2_NOT_COLLINEAR) THEN
STRIP_TAC THEN
EXISTS_TAC `y: real^3` THEN
EXISTS_TAC `z: real^3` THEN
ASM_SIMP_TAC[INSERT_EMPTY_SUBSET] THEN
MATCH_MP_TAC HULL_INC THEN
SET_TAC[];
FIRST_X_ASSUM MP_TAC THEN NHANH TOW_DISTINCT_POINTS_EXISTS_RD_NOT_COLLINEAR THEN
STRIP_TAC THEN
EXISTS_TAC `v3: real^3` THEN
EXISTS_TAC `z: real^3` THEN
FIRST_X_ASSUM MP_TAC THEN
SIMP_TAC[INSERT_COMM] THEN
STRIP_TAC THEN
MATCH_MP_TAC SUBSET_IMP_SUBSET_HULL THEN
ASM_SIMP_TAC[] THEN
SET_TAC[]]; ONCE_REWRITE_TAC[SET_RULE` {a,b,c} = {c,a,b} `] THEN
ASM_CASES_TAC`v2: real^3 = vec 0 ` THENL [UNDISCH_TAC `v3 = c % (v2: real^3)` THEN
MATCH_MP_TAC (TAUT` a ==> b ==> a `) THEN
ASM_CASES_TAC `(v3:real^3) = vec 0 ` THENL [
MP_TAC (SPEC`(vec 0) :real^3` GIVEN_POINT_EXISTS_2_NOT_COLLINEAR) THEN
STRIP_TAC THEN
EXISTS_TAC `y: real^3` THEN
EXISTS_TAC `z: real^3` THEN
ASM_SIMP_TAC[INSERT_EMPTY_SUBSET] THEN
MATCH_MP_TAC HULL_INC THEN
SET_TAC[];
FIRST_X_ASSUM MP_TAC THEN NHANH TOW_DISTINCT_POINTS_EXISTS_RD_NOT_COLLINEAR THEN
STRIP_TAC THEN
EXISTS_TAC `v3: real^3` THEN
EXISTS_TAC `z: real^3` THEN
FIRST_X_ASSUM MP_TAC THEN
SIMP_TAC[INSERT_COMM] THEN
STRIP_TAC THEN
MATCH_MP_TAC SUBSET_IMP_SUBSET_HULL THEN
ASM_SIMP_TAC[] THEN
SET_TAC[]]; FIRST_X_ASSUM MP_TAC] THEN
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
NHANH TOW_DISTINCT_POINTS_EXISTS_RD_NOT_COLLINEAR THEN
STRIP_TAC THEN
EXISTS_TAC`v2:real^3` THEN
EXISTS_TAC`z:real^3` THEN
ASM_SIMP_TAC[INSERT_EMPTY_SUBSET] THEN
ASM_SIMP_TAC[INSERT_EMPTY_SUBSET; IN_P_HULL_INSERT] THEN
ONCE_REWRITE_TAC[INSERT_AC] THEN
ASM_SIMP_TAC[AFFINE_HULL_3; IN_P_HULL_INSERT; IN_ELIM_THM] THEN
EXISTS_TAC `c: real` THEN
EXISTS_TAC `&1 - (c: real)` THEN
EXISTS_TAC `&0` THEN
SIMP_TAC[REAL_ARITH`c + &1 - c + &0 = &1 `] THEN
CONV_TAC VECTOR_ARITH]; ASM_MESON_TAC[HULL_SUBSET]]);;



let SUBSET_AFFINE_HULL3_EQ_SUB_PLANE = prove(`
(? (u: real^3 ) v w. S SUBSET affine hull {u, v, w}) <=> (?x. plane x /\ S SUBSET x)`,
REWRITE_TAC[plane] THEN EQ_TAC THENL [STRIP_TAC THEN
MP_TAC (SPECL [`u: real^3`;`v:real^3`;`w:real^3`] THREE_POINT_IMP_EXISTS_3) THEN
STRIP_TAC THEN EXISTS_TAC` affine hull {u, w2, (w3: real^3)}` THEN CONJ_TAC THENL [
ASM_MESON_TAC[]; FIRST_X_ASSUM MP_TAC THEN
NHANH_PAT `\x. x ==> y ` (MESON[HULL_MONO]` s SUBSET t ==> affine hull s SUBSET affine hull t`)
THEN ASM_SIMP_TAC[HULL_HULL] THEN ASM_MESON_TAC[SUBSET_TRANS]]; MESON_TAC[]]);;

let coplanar2 = coplanar;;



let NOT_COPLANAR_0_4_IMP_INDEPENDENT = prove
(`!v1 v2 v3:real^N. ~coplanar {vec 0,v1,v2,v3} ==> independent {v1,v2,v3}`,
REPEAT GEN_TAC THEN REWRITE_TAC[independent; CONTRAPOS_THM] THEN
REWRITE_TAC[dependent] THEN
SUBGOAL_THEN
`!v1 v2 v3:real^N. v1 IN span {v2,v3} ==> coplanar{vec 0,v1,v2,v3}`
ASSUME_TAC THENL
[REPEAT STRIP_TAC THEN REWRITE_TAC[coplanar] THEN
MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `v2:real^N`; `v3:real^N`] THEN
SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INSERT] THEN
REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
ASM_SIMP_TAC[SPAN_SUPERSET; IN_INSERT] THEN
POP_ASSUM MP_TAC THEN SPEC_TAC(`v1:real^N`,`v1:real^N`) THEN
REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC SPAN_MONO THEN SET_TAC[];
REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
FIRST_X_ASSUM SUBST_ALL_TAC THENL
[FIRST_X_ASSUM(MP_TAC o SPECL [`v1:real^N`; `v2:real^N`; `v3:real^N`]);
FIRST_X_ASSUM(MP_TAC o SPECL [`v2:real^N`; `v3:real^N`; `v1:real^N`]);
FIRST_X_ASSUM(MP_TAC o SPECL [`v3:real^N`; `v1:real^N`; `v2:real^N`])]
THEN REWRITE_TAC[INSERT_AC] THEN DISCH_THEN MATCH_MP_TAC THEN
FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
`a IN s ==> s SUBSET t ==> a IN t`)) THEN
MATCH_MP_TAC SPAN_MONO THEN SET_TAC[]]);;

let NONCOPLANAR_3_BASIS = prove
(`!v1 v2 v3 v0 v:real^3.
~coplanar {v0, v1, v2, v3}
==> ?t1 t2 t3.
v = t1 % (v1 - v0) + t2 % (v2 - v0) + t3 % (v3 - v0) /\
(!ta tb tc.
v = ta % (v1 - v0) + tb % (v2 - v0) + tc % (v3 - v0)
==> ta = t1 /\ tb = t2 /\ tc = t3)`,
GEN_GEOM_ORIGIN_TAC `v0:real^3` ["v"] THEN REPEAT GEN_TAC THEN
MAP_EVERY (fun t ->
ASM_CASES_TAC t THENL [ASM_REWRITE_TAC[INSERT_AC; COPLANAR_3]; ALL_TAC])
[`v1:real^3 = vec 0`; `v2:real^3 = vec 0`; `v3:real^3 = vec 0`;
`v2:real^3 = v1`; `v3:real^3 = v1`; `v3:real^3 = v2`] THEN
DISCH_THEN(ASSUME_TAC o MATCH_MP NOT_COPLANAR_0_4_IMP_INDEPENDENT) THEN
REWRITE_TAC[VECTOR_SUB_RZERO] THEN
MP_TAC(ISPECL [`(:real^3)`; `{v1,v2,v3}:real^3->bool`]
CARD_GE_DIM_INDEPENDENT) THEN
ASM_REWRITE_TAC[SUBSET_UNIV; DIM_UNIV; DIMINDEX_3] THEN
ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH; SUBSET; IN_UNIV] THEN
DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN
REWRITE_TAC[SPAN_BREAKDOWN_EQ; SPAN_EMPTY; IN_SING] THEN
REWRITE_TAC[VECTOR_ARITH `a - b:real^3 = c <=> a = b + c`] THEN
REWRITE_TAC[VECTOR_ADD_RID] THEN
MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t1:real` THEN
MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t2:real` THEN
MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t3:real` THEN
DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
MAP_EVERY X_GEN_TAC [`ta:real`; `tb:real`; `tc:real`] THEN DISCH_TAC THEN
FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INDEPENDENT_EXPLICIT]) THEN
REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
DISCH_THEN(MP_TAC o SPEC
`(\x. if x = v1 then t1 - ta
else if x = v2 then t2 - tb else t3 - tc):real^3->real`) THEN
REWRITE_TAC[FORALL_IN_INSERT] THEN
SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; VECTOR_ADD_RID] THEN
REWRITE_TAC[REAL_ARITH `s - t = &0 <=> t = s`] THEN
DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC
`t1 % v1 + t2 % v2 + t3 % v3:real^3 = ta % v1 + tb % v2 + tc % v3` THEN
VECTOR_ARITH_TAC);;


let coplanar = prove(` ! (S:real^3 -> bool ). coplanar S <=> (?x. plane x /\ S SUBSET x)`,
REWRITE_TAC[SUBSET_AFFINE_HULL3_EQ_SUB_PLANE; coplanar]);;


let COPLANAR_DET_EQ_0 = prove
(`!v0 v1 (v2: real^3) v3.
coplanar {v0,v1,v2,v3} <=>
det(vector[v1 - v0; v2 - v0; v3 - v0]) = &0`,
REPEAT GEN_TAC THEN REWRITE_TAC[DET_EQ_0_RANK; RANK_ROW] THEN
REWRITE_TAC[rows; row; LAMBDA_ETA] THEN
ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
REWRITE_TAC[GSYM numseg; DIMINDEX_3] THEN
CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
SIMP_TAC[IMAGE_CLAUSES; VECTOR_3] THEN EQ_TAC THENL
[REWRITE_TAC[coplanar; plane; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
MAP_EVERY X_GEN_TAC
[`p:real^3->bool`; `a:real^3`; `b:real^3`; `c:real^3`] THEN
DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
FIRST_X_ASSUM SUBST1_TAC THEN
W(MP_TAC o PART_MATCH lhand AFFINE_HULL_INSERT_SUBSET_SPAN o
rand o lhand o snd) THEN
REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
DISCH_THEN(MP_TAC o MATCH_MP SUBSET_TRANS) THEN
DISCH_THEN(MP_TAC o ISPEC `\x:real^3. x - a` o MATCH_MP IMAGE_SUBSET) THEN
ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
REWRITE_TAC[IMAGE_CLAUSES; GSYM IMAGE_o; o_DEF; VECTOR_ADD_SUB; IMAGE_ID;
SIMPLE_IMAGE] THEN
REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
GEN_REWRITE_TAC LAND_CONV [GSYM DIM_SPAN] THEN MATCH_MP_TAC LET_TRANS THEN
EXISTS_TAC `CARD {b - a:real^3,c - a}` THEN
CONJ_TAC THENL
[MATCH_MP_TAC SPAN_CARD_GE_DIM;
SIMP_TAC[CARD_CLAUSES; FINITE_RULES] THEN ARITH_TAC] THEN
REWRITE_TAC[FINITE_INSERT; FINITE_RULES] THEN
GEN_REWRITE_TAC RAND_CONV [GSYM SPAN_SPAN] THEN
MATCH_MP_TAC SPAN_MONO THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
MP_TAC(VECTOR_ARITH `!x y:real^3. x - y = (x - a) - (y - a)`) THEN
DISCH_THEN(fun th -> REPEAT CONJ_TAC THEN
GEN_REWRITE_TAC LAND_CONV [th]) THEN
MATCH_MP_TAC SPAN_SUB THEN ASM_REWRITE_TAC[];


DISCH_TAC THEN
MP_TAC(ISPECL [`{v1 - v0,v2 - v0,v3 - v0}:real^3->bool`; `2`]
LOWDIM_EXPAND_BASIS) THEN
ASM_REWRITE_TAC[ARITH_RULE `n <= 2 <=> n < 3`; DIMINDEX_3; ARITH] THEN
DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool`
(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN
DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
REWRITE_TAC[coplanar; plane] THEN
EXISTS_TAC `affine hull {v0,v0 + a,v0 + b}:real^3->bool` THEN
CONJ_TAC THENL
[MAP_EVERY EXISTS_TAC [`v0:real^3`; `v0 + a:real^3`; `v0 + b:real^3`] THEN
REWRITE_TAC[COLLINEAR_3; COLLINEAR_LEMMA;
VECTOR_ARITH `--x = vec 0 <=> x = vec 0`;
VECTOR_ARITH `u - (u + a):real^3 = --a`;
VECTOR_ARITH `(u + b) - (u + a):real^3 = b - a`] THEN
REWRITE_TAC[DE_MORGAN_THM; VECTOR_SUB_EQ;
VECTOR_ARITH `b - a = c % -- a <=> (c - &1) % a + &1 % b = vec 0`] THEN
ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
[ASM_MESON_TAC[IN_INSERT; INDEPENDENT_NONZERO]; ALL_TAC] THEN
DISCH_THEN(X_CHOOSE_TAC `u:real`) THEN
FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [independent]) THEN
REWRITE_TAC[DEPENDENT_EXPLICIT] THEN
MAP_EVERY EXISTS_TAC [`{a:real^3,b}`;
`\x:real^3. if x = a then u - &1 else &1`] THEN
REWRITE_TAC[FINITE_INSERT; FINITE_RULES; SUBSET_REFL] THEN
CONJ_TAC THENL
[EXISTS_TAC `b:real^3` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
REAL_ARITH_TAC;
ALL_TAC] THEN
SIMP_TAC[VSUM_CLAUSES; FINITE_RULES] THEN
ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; VECTOR_ADD_RID];
ALL_TAC] THEN
W(MP_TAC o PART_MATCH (lhs o rand) AFFINE_HULL_INSERT_SPAN o
rand o snd) THEN
ANTS_TAC THENL
[REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
REWRITE_TAC[VECTOR_ARITH `u = u + a <=> a = vec 0`] THEN
ASM_MESON_TAC[INDEPENDENT_NONZERO; IN_INSERT];
ALL_TAC] THEN
DISCH_THEN SUBST1_TAC THEN
ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; IMAGE_ID; VECTOR_ADD_SUB] THEN
MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
`IMAGE (\v:real^3. v0 + v) (span{v1 - v0, v2 - v0, v3 - v0})` THEN
ASM_SIMP_TAC[IMAGE_SUBSET] THEN
REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_IMAGE] THEN CONJ_TAC THENL
[EXISTS_TAC `vec 0:real^3` THEN REWRITE_TAC[SPAN_0] THEN VECTOR_ARITH_TAC;
REWRITE_TAC[VECTOR_ARITH `v1:real^N = v0 + x <=> x = v1 - v0`] THEN
REWRITE_TAC[UNWIND_THM2] THEN REPEAT CONJ_TAC THEN
MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_INSERT]]]);;


let det_vec3 = new_definition ` det_vec3 (a:real^3) (b:real^3) (c:real^3) =
a$1 * b$2 * c$3 + b$1 * c$2 * a$3 + c$1 * a$2 * b$3 -
( a$1 * c$2 * b$3 + b$1 * a$2 * c$3 + c$1 * b$2 * a$3 ) `;;


let DET_VEC3_EXPAND = prove
(`det (vector [a; b; (c:real^3)] ) = det_vec3 a b c`,
REWRITE_TAC[det_vec3; DET_3; VECTOR_3] THEN REAL_ARITH_TAC);;

let COPLANAR_DET_VEC3_EQ_0 = prove( `!v0 v1 (v2: real^3) v3.
coplanar {v0,v1,v2,v3} <=>
det_vec3 ( v1 - v0 ) ( v2 - v0 ) ( v3 - v0 ) = &0`, REWRITE_TAC[COPLANAR_DET_EQ_0; DET_VEC3_EXPAND]);;


let coplanar1 = coplanar;;
let coplanar = coplanar2;;



let DET_VEC3_AS_CROSS_DOT = prove(` det_vec3 v1 v2 v3 = (v1 cross v2 ) dot v3 `,
REWRITE_TAC[det_vec3; cross; DOT_3; VECTOR_3]
THEN REAL_ARITH_TAC);;


let ORTHONORMAL_IMP_NONZERO = prove
(`!e1 e2 e3. orthonormal e1 e2 e3
==> ~(e1 = vec 0) /\ ~(e2 = vec 0) /\ ~(e3 = vec 0)`,
REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
ASM_REWRITE_TAC[orthonormal; DOT_LZERO] THEN REAL_ARITH_TAC);;

let ORTHONORMAL_IMP_DISTINCT = prove
(`!e1 e2 e3. orthonormal e1 e2 e3 ==> ~(e1 = e2) /\ ~(e1 = e3) /\ ~(e2 = e3)`,
REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
ASM_REWRITE_TAC[orthonormal; DOT_LZERO] THEN REAL_ARITH_TAC);;

let ORTHONORMAL_IMP_INDEPENDENT = prove
(`!e1 e2 e3. orthonormal e1 e2 e3 ==> independent {e1,e2,e3}`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[ORTHONORMAL_IMP_NONZERO]] THEN
RULE_ASSUM_TAC(REWRITE_RULE[orthonormal]) THEN
REWRITE_TAC[pairwise; IN_INSERT; NOT_IN_EMPTY] THEN
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[orthogonal] THEN
ASM_MESON_TAC[DOT_SYM]);;

let ORTHONORMAL_IMP_SPANNING = prove
(`!e1 e2 e3. orthonormal e1 e2 e3 ==> span {e1,e2,e3} = (:real^3)`,
REPEAT STRIP_TAC THEN
MP_TAC(ISPECL [`(:real^3)`; `{e1:real^3,e2,e3}`] CARD_EQ_DIM) THEN
ASM_SIMP_TAC[ORTHONORMAL_IMP_INDEPENDENT; SUBSET_UNIV] THEN
REWRITE_TAC[DIM_UNIV; DIMINDEX_3; HAS_SIZE; FINITE_INSERT; FINITE_EMPTY] THEN
SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT] THEN
FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHONORMAL_IMP_DISTINCT) THEN
ASM_REWRITE_TAC[NOT_IN_EMPTY; ARITH] THEN SET_TAC[]);;

let th = prove
(`!e1 e2 e3.
orthonormal e1 e2 e3
==> !x. ?t1 t2 t3.
x = t1 % e1 + t2 % e2 + t3 % e3 /\
!tt1 tt2 tt3.
x = tt1 % e1 + tt2 % e2 + tt3 % e3
==> tt1 = t1 /\ tt2 = t2 /\ tt3 = t3`,
REPEAT STRIP_TAC THEN
FIRST_ASSUM(MP_TAC o MATCH_MP ORTHONORMAL_IMP_SPANNING) THEN
DISCH_THEN(MP_TAC o AP_TERM `(IN) (x:real^3)`) THEN
REWRITE_TAC[IN_UNIV; SPAN_BREAKDOWN_EQ; SPAN_EMPTY; IN_SING] THEN
SIMP_TAC[VECTOR_ARITH `x - a - b - c = vec 0 <=> x:real^3 = a + b + c`] THEN
MAP_EVERY (fun t -> MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC t)
[`t1:real`; `t2:real`; `t3:real`] THEN
DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
ONCE_REWRITE_TAC[REAL_ARITH `x:real = y <=> y - x = &0`] THEN
REWRITE_TAC[VECTOR_ARITH
`a % x + b % y + c % z:real^3 = a' % x + b' % y + c' % z <=>
(a - a') % x + (b - b') % y + (c - c') % z = vec 0`] THEN
DISCH_TAC THEN
FIRST_ASSUM(MP_TAC o MATCH_MP ORTHONORMAL_IMP_INDEPENDENT) THEN
REWRITE_TAC[INDEPENDENT_EXPLICIT] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
DISCH_THEN(MP_TAC o SPEC
`\x:real^3. if x = e1 then t1 - tt1:real
else if x = e2 then t2 - tt2
else t3 - tt3`) THEN
FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHONORMAL_IMP_DISTINCT) THEN
ASM_SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; VECTOR_ADD_RID] THEN
DISCH_THEN(fun th -> MAP_EVERY (MP_TAC o C SPEC th)
[`e1:real^3`; `e2:real^3`; `e3:real^3`]) THEN
ASM_SIMP_TAC[]);;

(* the following lemma are in collect_geom.ml *)
(* Hi Truong,

In the very latest snapshot there is a theorem COPLANAR_DET_EQ_0
(I think I proved it because you asked for it some time ago). By
combing that with DET_3 you should be able to get your first
theorem COPLANAR_DET_VEC3_EQ_0.

I will work on the other one NONCOPLANAR_3_BASIS and send it later
today.*)


(*
Hi Truong,

Here is the other theorem. Fortunately I proved the rather tedious
lemma NOT_COPLANAR_0_4_IMP_INDEPENDENT earlier in this week for use
in the volume properties.

John.

have been in trig.ml

let NOT_COPLANAR_0_4_IMP_INDEPENDENT = prove
(`!v1 v2 v3:real^N. ~coplanar {vec 0,v1,v2,v3} ==> independent {v1,v2,v3}`,
REPEAT GEN_TAC THEN REWRITE_TAC[independent; CONTRAPOS_THM] THEN
REWRITE_TAC[dependent] THEN
SUBGOAL_THEN
`!v1 v2 v3:real^N. v1 IN span {v2,v3} ==> coplanar{vec 0,v1,v2,v3}`
ASSUME_TAC THENL
[REPEAT STRIP_TAC THEN REWRITE_TAC[coplanar] THEN
MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `v2:real^N`; `v3:real^N`] THEN
SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INSERT] THEN
REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
ASM_SIMP_TAC[SPAN_SUPERSET; IN_INSERT] THEN
POP_ASSUM MP_TAC THEN SPEC_TAC(`v1:real^N`,`v1:real^N`) THEN
REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC SPAN_MONO THEN SET_TAC[];
REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
FIRST_X_ASSUM SUBST_ALL_TAC THENL
[FIRST_X_ASSUM(MP_TAC o SPECL [`v1:real^N`; `v2:real^N`; `v3:real^N`]);
FIRST_X_ASSUM(MP_TAC o SPECL [`v2:real^N`; `v3:real^N`; `v1:real^N`]);
FIRST_X_ASSUM(MP_TAC o SPECL [`v3:real^N`; `v1:real^N`; `v2:real^N`])]
THEN REWRITE_TAC[INSERT_AC] THEN DISCH_THEN MATCH_MP_TAC THEN
FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
`a IN s ==> s SUBSET t ==> a IN t`)) THEN
MATCH_MP_TAC SPAN_MONO THEN SET_TAC[]]);;

let NONCOPLANAR_3_BASIS = prove
(`!v1 v2 v3 v0 v:real^3.
~coplanar {v0, v1, v2, v3}
==> ?t1 t2 t3.
v = t1 % (v1 - v0) + t2 % (v2 - v0) + t3 % (v3 - v0) /\
(!ta tb tc.
v = ta % (v1 - v0) + tb % (v2 - v0) + tc % (v3 - v0)
==> ta = t1 /\ tb = t2 /\ tc = t3)`,
GEN_GEOM_ORIGIN_TAC `v0:real^3` ["v"] THEN REPEAT GEN_TAC THEN
MAP_EVERY (fun t ->
ASM_CASES_TAC t THENL [ASM_REWRITE_TAC[INSERT_AC; COPLANAR_3]; ALL_TAC])
[`v1:real^3 = vec 0`; `v2:real^3 = vec 0`; `v3:real^3 = vec 0`;
`v2:real^3 = v1`; `v3:real^3 = v1`; `v3:real^3 = v2`] THEN
DISCH_THEN(ASSUME_TAC o MATCH_MP NOT_COPLANAR_0_4_IMP_INDEPENDENT) THEN
REWRITE_TAC[VECTOR_SUB_RZERO] THEN
MP_TAC(ISPECL [`(:real^3)`; `{v1,v2,v3}:real^3->bool`]
CARD_GE_DIM_INDEPENDENT) THEN
ASM_REWRITE_TAC[SUBSET_UNIV; DIM_UNIV; DIMINDEX_3] THEN
ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH; SUBSET; IN_UNIV] THEN
DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN
REWRITE_TAC[SPAN_BREAKDOWN_EQ; SPAN_EMPTY; IN_SING] THEN
REWRITE_TAC[VECTOR_ARITH `a - b:real^3 = c <=> a = b + c`] THEN
REWRITE_TAC[VECTOR_ADD_RID] THEN
MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t1:real` THEN
MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t2:real` THEN
MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t3:real` THEN
DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
MAP_EVERY X_GEN_TAC [`ta:real`; `tb:real`; `tc:real`] THEN DISCH_TAC THEN
FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INDEPENDENT_EXPLICIT]) THEN
REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
DISCH_THEN(MP_TAC o SPEC
`(\x. if x = v1 then t1 - ta
else if x = v2 then t2 - tb else t3 - tc):real^3->real`) THEN
REWRITE_TAC[FORALL_IN_INSERT] THEN
SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; VECTOR_ADD_RID] THEN
REWRITE_TAC[REAL_ARITH `s - t = &0 <=> t = s`] THEN
DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC
`t1 % v1 + t2 % v2 + t3 % v3:real^3 = ta % v1 + tb % v2 + tc % v3` THEN
VECTOR_ARITH_TAC);;


*)



let DIV_POW2 = REAL_FIELD` (a/b) pow 2 = a pow 2 / (b pow 2 )`;;



let REAL_LE_SQUARE_POW = REWRITE_RULE[GSYM REAL_POW_2] REAL_LE_SQUARE;;


let NOT_EQ0_IMP_TRIGIZABLE = prove(` ~( x = &0 /\ y = &0 ) ==>
( x / sqrt ( x pow 2 + y pow 2 )) pow 2
+ ( y / sqrt ( x pow 2 + y pow 2 )) pow 2 = &1 `,REWRITE_TAC[DIV_POW2] THEN
ASSUME_TAC (MESON [REAL_LE_SQUARE_POW; REAL_LE_ADD]`
&0 <= x pow 2 + y pow 2 `) THEN
ASM_SIMP_TAC[SQRT_POW_2; REAL_FIELD` a / (m:real) + b / m =
( a + b ) / m `;GSYM REAL_SOS_EQ_0; REAL_DIV_REFL]);;



let POW2_1 = REAL_ARITH` ( &1 ) pow 2 = &1`;;

let ABS_BOUNDS = REAL_ABS_BOUNDS;;

let POW2_1_BOUNDED = prove(
` a pow 2 + b pow 2 = &1 ==> -- &1 <= a /\ a <= &1 `,
REWRITE_TAC[REAL_ARITH` a + b = c <=> b = c - a `] THEN
NHANH ( MESON[REAL_LE_POW_2]`a pow 2 = x ==> &0 <= x `) THEN
ONCE_REWRITE_TAC[REAL_ARITH` &1 = &1 pow 2 `] THEN
REWRITE_TAC[REAL_SUB_LE; GSYM REAL_LE_SQUARE_ABS; ABS_1; POW2_1;
ABS_BOUNDS] THEN SIMP_TAC[]);;

let POW2_1_BOUNDED =
MESON[REAL_ADD_SYM; POW2_1_BOUNDED; REAL_ABS_BOUNDS]`
a pow 2 + b pow 2 = &1 ==> abs a <= &1 /\ abs b <= &1 `;;

let SIN_COMPLEMENTIVE = prove(` sin x = sin ( pi - x ) `,
REWRITE_TAC[SIN_COS; REAL_ARITH` a / &2 - ( a - x ) =
-- ( a / &2 - x )`; COS_NEG]);;


let CYLINDER_CORDINATE = prove(` ! w u e1 e2 (e3:real^3) x.
orthonormal e1 e2 e3 /\
e3 = ( &1 / norm ( w - u )) % ( w - u ) /\
~ ( x IN aff {w,u} ) /\ ~( w = u )
==>
(? r phi h. &0 < r /\
x = u + (r * ( cos phi )) % e1 +
( r * sin phi) % e2
+ h % ( w - u ) ) `,
REPEAT GEN_TAC THEN
REWRITE_TAC[orthonormal; GSYM DET_VEC3_AS_CROSS_DOT] THEN
NHANH (REAL_LT_IMP_NZ) THEN
ONCE_REWRITE_TAC[MESON[VECTOR_SUB_RZERO]` fv a b c = fv ( a - vec 0 ) ( b - vec 0 )
( c - vec 0 ) `] THEN
REWRITE_TAC[GSYM COPLANAR_DET_VEC3_EQ_0] THEN
NHANH (SPECL [`e1 : real^3`;` e2 :real^3`; `e3 :real^3`;
`(vec 0 : real^3)`; `(x : real^3) - u` ] NONCOPLANAR_3_BASIS) THEN
REWRITE_TAC[VECTOR_SUB_RZERO] THEN
STRIP_TAC THEN
ASM_CASES_TAC` t1 = &0 /\ t2 = &0 ` THENL [
FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) THEN
(ASSUME_TAC o FOR_ASM ) (prove(` t1 = &0 /\ t2 = &0 /\
x - u= t1 % e1 + t2 % e2 + t3 % e3
==> (x:real^3) - u = t3 % e3 `,
SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID])) THEN
FIRST_X_ASSUM MP_TAC THEN
UNDISCH_TAC` e3 = &1 / norm (w - u) % (w - (u:real^3))` THEN
SIMP_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH`
a -(b:real^n) = n % ( c - b )<=> a = n % c +
( &1 - n ) % b `] THEN
UNDISCH_TAC ` ~( x IN aff {w,(u:real^3)} )` THEN
REWRITE_TAC[AFF2; IN_ELIM_THM] THEN
MESON_TAC[];
FIRST_X_ASSUM MP_TAC] THEN
NHANH NOT_EQ0_IMP_TRIGIZABLE THEN
NHANH CIRCLE_SINCOS THEN
SIMP_TAC[GSYM REAL_SOS_EQ_0] THEN
ONCE_REWRITE_TAC[MESON[]` a /\b ==> c <=> a ==> b ==> c `] THEN
SIMP_TAC[GSYM SQRT_EQ_0; MESON[REAL_LE_POW_2;
REAL_LE_ADD]` &0 <= t1 pow 2 + t2 pow 2 `; REAL_FIELD`
~ ( a = &0 ) ==> (t / a = d <=> t = a * d ) `] THEN
REPEAT STRIP_TAC THEN
UNDISCH_TAC`x - u = t1 % e1 + t2 % e2 + t3 % (e3: real^3)` THEN
REPLICATE_TAC 2 (FIRST_X_ASSUM MP_TAC) THEN
UNDISCH_TAC` e3 = &1 / norm (w - u) % (w - (u:real^3))` THEN
PURE_ONCE_REWRITE_TAC[MESON[]` a = b ==> P a <=> a = b ==>
P b `] THEN
ABBREV_TAC `tt = t1 pow 2 + t2 pow 2 ` THEN
SIMP_TAC[] THEN
REPLICATE_TAC 3 DISCH_TAC THEN
REWRITE_TAC[VECTOR_ARITH` a - b = c <=> a = b + (c:real^N)`;
VECTOR_MUL_ASSOC] THEN REWRITE_TAC[REAL_ARITH` &0 < r /\ ~( r = &0 ) <=> &0 < r `] THEN
ASSUME_TAC2 (MESON[SQRT_POS_LE; REAL_LE_POW_2; REAL_LE_ADD]` t1 pow 2 +
t2 pow 2 = tt ==> &0 <= sqrt tt `) THEN
ASSUME_TAC2 (REAL_ARITH` ~ ( sqrt tt = &0 ) /\ &0 <= sqrt tt
==> &0 < sqrt tt `) THEN FIRST_ASSUM MP_TAC THEN MESON_TAC[]);;




(* NOT NEED AT ALL
let arith_lemma = prove
(`!a d x. &0 < d ==>
?y. (a <= y /\ y <= a + d) /\ ?n. y = x + &n * d \/ x = y + &n * d`,
REPEAT STRIP_TAC THEN DISJ_CASES_TAC (SPEC `(x - a):real` REAL_LE_NEGTOTAL)
THEN IMP_RES_THEN (IMP_RES_THEN STRIP_ASSUME_TAC) REAL_ARCH_LEAST THENL
[ EXISTS_TAC `x - &n * d` THEN STRIP_TAC THENL
[ (POP_ASSUM MP_TAC) THEN (POP_ASSUM MP_TAC) THEN
REWRITE_TAC [GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC ;
EXISTS_TAC `n:num` THEN REAL_ARITH_TAC ] ;
EXISTS_TAC `x + &(SUC n) * d` THEN STRIP_TAC THENL
[ (POP_ASSUM MP_TAC) THEN (POP_ASSUM MP_TAC) THEN
REWRITE_TAC [GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC ;
EXISTS_TAC `(SUC n):num` THEN REAL_ARITH_TAC ]]);;
*)


let COS_SUM_2PI = prove(
`! x. cos x = cos ( &2 * pi - x ) `, GEN_TAC THEN
ONCE_REWRITE_TAC[GSYM COS_NEG] THEN
PAT_ONCE_REWRITE_TAC `\x. _ = x ` [GSYM COS_PERIODIC] THEN
REWRITE_TAC[REAL_ARITH` --( a - b) + a = b `; COS_NEG]);;



let POW2_EQ_0 = prove(` ! a. a pow 2 = &0 <=> a = &0 `,
GEN_TAC THEN MP_TAC REAL_LE_POW_2 THEN
ASSUME_TAC (GEN_ALL NOT_ZERO_EQ_POW2_LT) THEN
REWRITE_TAC[REAL_LE_LT] THEN
FIRST_ASSUM (fun th -> REWRITE_TAC[GSYM th] ) THEN
ASM_MESON_TAC[]);;


let UNIT_BOUNDED_IN_TOW_FORMS = prove(`-- &1 <= a /\ a <= &1 ==> &0 <= &1 - a pow 2 `,
DISCH_TAC THEN REWRITE_TAC[REAL_ARITH` &1 - a pow 2 = (&1 - a ) * ( &1 + a )`] THEN
MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;


let COS_TOTAL = prove(`-- &1 <= a /\ a <= &1 ==> (?!x. &0 <= x /\ x <= pi /\ cos x = a ) `,
NHANH (UNIT_BOUNDED_IN_TOW_FORMS) THEN NHANH_PAT `\a. a ==> _` SQRT_WORKS THEN
ONCE_REWRITE_TAC[REAL_ARITH` a = &1 - b pow 2 <=> b pow 2 + a = &1 `] THEN
SIMP_TAC[EXISTS_UNIQUE] THEN NHANH SINCOS_TOTAL_PI THEN
STRIP_TAC THEN EXISTS_TAC` t:real` THEN ASM_SIMP_TAC[] THEN
ASM_MESON_TAC[COS_INJ_PI]);;




let SUM_POW2_EQ1_UNIQUE_TRIG = prove(` ! a b. a pow 2 + b pow 2 = &1 ==> (?!x. &0 <= x /\
x < &2 * pi /\ cos x = a /\ sin x = b )`,
REPEAT GEN_TAC THEN NHANH (POW2_1_BOUNDED) THEN
REWRITE_TAC[REAL_ABS_BOUNDS] THEN
NHANH_PAT `\x. _ /\ x /\ _ ==> h ` COS_TOTAL THEN
PAT_REWRITE_TAC `\x. _ /\ _ /\ x ==> _ ` [REAL_ARITH`
-- &1 <= b /\ b <= &1 <=> -- &1 <= b /\ b < &0 \/ &0 <= b /\
b <= &1 `] THEN REWRITE_TAC[EXISTS_UNIQUE] THEN STRIP_TAC
THENL [ASSUME_TAC PI_POS THEN ASM_CASES_TAC ` x = &0 ` THENL [
FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC ` &0` THEN
SUBST_ALL_TAC COS_0 THEN FIRST_X_ASSUM (SUBST_ALL_TAC o SYM )
THEN UNDISCH_TAC `&1 pow 2 + b pow 2 = &1 ` THEN
REWRITE_TAC[REAL_ARITH` &1 pow 2 + b = &1 <=>
b = &0 `; POW2_EQ_0] THEN DISCH_TAC THEN
ASM_MESON_TAC[REAL_ARITH` b < &0 /\ b = &0 ==> F `];
EXISTS_TAC ` &2 * pi - x ` THEN ASSUME_TAC2 (
REAL_ARITH` x <= pi /\ &0 < pi ==> &0 <= &2 * pi - x `) THEN
FIRST_X_ASSUM SIMP_TAC1 THEN
ASSUME_TAC2 (REAL_ARITH` &0 <= x /\ ~( x = &0 ) ==> &0 < x `) THEN
REWRITE_TAC[REAL_ARITH` a - b < a <=> &0 < b `] THEN
FIRST_X_ASSUM SIMP_TAC1 THEN
REWRITE_TAC[GSYM COS_SUM_2PI; REAL_ARITH` a - b =
-- b + a `; SIN_PERIODIC; SIN_NEG] THEN
SIMP_TACC1 (TAUT` cos x = a ==> cos x = a `) THEN
SIMP_IDENT[] `cos x = a ` THEN
ASSUME_TAC2 (REAL_ARITH` b < &0 ==> b <= &0 `) THEN
ASSUME_TAC (SPEC_ALL SIN_CIRCLE) THEN
USE_FIRST `cos x = a` SUBST_ALL_TAC THEN
ASSUME_TAC2 (REAL_ARITH` sin x pow 2 + a pow 2 = &1 /\
a pow 2 + b pow 2 = &1 ==> sin x pow 2 = b pow 2 `) THEN
SUBST_ALL_TAC (REAL_ARITH` b pow 2 = ( -- b ) pow 2 `) THEN
ASSUME_TAC2 (REAL_ARITH` b < &0 ==> &0 <= -- b `) THEN
ASSUME_TAC2 (SPEC_ALL SIN_POS_PI_LE) THEN
ASSUME_TAC2 (MESON[EQ_POW2_COND]` &0 <= -- b /\
&0 <= sin x /\sin x pow 2 = -- b pow 2 ==> sin x = -- b `) THEN
SIMP_IDENT[REAL_NEGNEG] `sin x = -- b ` THEN
REPEAT STRIP_TAC THEN
UNDISCH_TAC `y < &2 * pi ` THEN
ONCE_SIMP_IDENT ` &0 < pi ` (REAL_ARITH` &0 < p ==> ( x
< &2 * p <=> x <= p \/ p < x /\ x < &2 * p )`) THEN
STRIP_TAC] THENL [
ASSUME_TAC2 (SPEC `y:real` SIN_POS_PI_LE) THEN
ASSUME_TAC2 (REAL_ARITH` sin y = b /\ &0 <= sin y ==>
&0 <= b `) THEN UNDISCH_TAC ` b < &0 ` THEN
SIMP_IDENT[REAL_ARITH` &0 <= b <=> ~(b < &0 )`] `&0 <= b`;
REWRITE_TAC[REAL_ARITH` y = -- x + b <=> b - y = x `] THEN
REPLICATE_TAC 2 (FIRST_X_ASSUM MP_TAC) THEN PHA THEN
REWRITE_TAC[REAL_ARITH` a < x /\ x < &2 * a <=>
&0 < &2 * a - x /\ &2 * a - x < a `] THEN
UNDISCH_TAC ` cos y = a ` THEN
ONCE_REWRITE_TAC[COS_SUM_2PI] THEN
NHANH (REAL_LT_IMP_LE) THEN
UNDISCH_TAC `!y. &0 <= y /\ y <= pi /\ cos y = a ==> y = x` THEN
MESON_TAC[]];EXISTS_TAC `x:real` THEN
SIMP_IDENT[] `&0 <= x ` THEN
SIMP_IDENT[]` cos x = a ` THEN
ASSUME_TAC PI_POS THEN
ASSUME_TAC2 (REAL_ARITH` x <= pi /\ &0 < pi ==>
x < &2 * pi `) THEN
SIMP_IDENT[]` x < &2 * pi` THEN
ASSUME_TAC (SPEC_ALL SIN_CIRCLE) THEN
USE_FIRST `cos x = a ` SUBST_ALL_TAC THEN
ASSUME_TAC2 (REAL_ARITH` a pow 2 + b pow 2 = &1 /\
sin x pow 2 + a pow 2 = &1 ==> b pow 2 = sin x pow 2 `) THEN
ASSUME_TAC2 (SPEC_ALL SIN_POS_PI_LE) THEN
ASSUME_TAC2 (MESON[EQ_POW2_COND]` b pow 2 = sin x pow 2
/\ &0 <= sin x /\ &0 <= b ==> sin x = b `) THEN
SIMP_IDENT[]` sin x = b ` THEN
ONCE_SIMP_IDENT ` &0 < pi ` (REAL_ARITH` &0 < p ==> ( x
< &2 * p <=> x <= p \/ p < x /\ x < &2 * p )`) THEN
REPEAT STRIP_TAC THENL [ASM_MESON_TAC[];
ASSUME_TAC2 (REAL_ARITH` pi < y /\ y < &2 * pi ==>
&0 < y - pi /\ y - pi < pi `)] THEN
ASSUME_TAC (UNDISCH (SPEC ` y - pi ` SIN_POS_PI)) THEN
UNDISCH_TAC ` &0 < sin ( y - pi )` THEN
ONCE_REWRITE_TAC[GSYM SIN_PERIODIC] THEN
REWRITE_TAC[REAL_ARITH` a - b + &2 * b = a + b `;
SIN_PERIODIC_PI] THEN ASM_REWRITE_TAC[] THEN
SIMP_IDENT[REAL_ARITH` &0 <= a ==> ~( &0 < -- a )`]
` &0 <= b `]);;




let PERIODIC_AT0_IMP_ANY = prove(
` ! f p t. &0 < p /\
(! x. f x = f ( x + p )) ==>
((?!x. &0 <= x /\ x < p /\ f x ) <=> (! t. &0 <= t /\
t < p ==> (?!x. t <= x /\
x < t + p /\ f x )))`,
REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_UNIQUE] THEN
EQ_TAC THENL [REPEAT STRIP_TAC
THEN ASM_CASES_TAC ` t <= (x:real) ` THENL [
EXISTS_TAC `x:real` THEN SIMP_IDENT[] `t <= x `
THEN SIMP_IDENT[] `(f: real -> bool) x` THEN
ELIM_IDENTS (REAL_ARITH` x < p /\ &0 <= t ==>
x < t + p `) THEN REPEAT STRIP_TAC THEN
ASM_CASES_TAC ` y < (p:real)` THENL [
ASSUME_TAC2 (REAL_ARITH` &0 <= t /\ t <= y ==>
&0 <= y `) THEN ASM_MESON_TAC[];
DOWN_TAC THEN REWRITE_TAC[REAL_ARITH` ~( a < b ) <=>
&0 <= a - b `; REAL_ARITH` a < b + c <=>
a - c < b `] THEN STRIP_TAC THEN
ASSUME_TAC2 (REAL_ARITH` y - p < t /\ t < p ==>
y - p < p `) THEN
ASSUME_TAC2 (prove(`(! a. f a <=> f ( a + (p:real)) )/\ f y ==>
f ( y - p )`, PAT_ONCE_REWRITE_TAC `\x. _ /\ x ==> _`
[REAL_ARITH` a = a - p + p `] THEN MESON_TAC[])) THEN
SUBST_ALL_TAC (
MESON[]`(!y. &0 <= y /\ y < p /\ f y ==> y = x)
<=> (!y. &0 <= y ==> y < p ==> f y ==> y = x)`) THEN
ASSUME_TAC2 (
MESON[]`(!(y:real). &0 <= y ==> y < p ==> f y ==> y = x) /\
&0 <= y - p /\y - p < p /\ f ((y:real) - p) ==> x = y - p `) THEN
REWRITE_TAC[REAL_ARITH` y = y - p <=> p = &0 `] THEN
ASM_MESON_TAC[REAL_ARITH` y < t /\ x = y ==>
~( t <= x ) `]];EXISTS_TAC `x + p ` THEN
SUBST_ALL_TAC (REAL_ARITH` ~( t <= x ) <=> x < t `) THEN
ELIM_IDENTS (REAL_ARITH` t < p /\ &0 <= x /\ x < t ==>
t <= x + p /\ x + p < t + p `) THEN
ELIM_IDENTS (MESON[]`(!x. f x <=> f ( x + (p:real)))
/\ f x ==> f ( x + p )`) THEN
REWRITE_TAC[REAL_ARITH` a < b + c <=> a - c < b `] THEN
REPEAT STRIP_TAC THEN
ASM_CASES_TAC ` &0 <= y - p ` THEN
ASSUME_TAC2 (REAL_ARITH` y - p < t /\ t < p ==>
y - p < p `) THEN
ASSUME_TAC2 (prove(`(! a. f a <=> f ( a + (p:real)) )/\ f y ==>
f ( y - p )`, PAT_ONCE_REWRITE_TAC `\x. _ /\ x ==> _`
[REAL_ARITH` a = a - p + p `] THEN MESON_TAC[]))]
THENL [SUBST_ALL_TAC (
MESON[]`(!y. &0 <= y /\ y < p /\ f y ==> y = x)
<=> (!y. &0 <= y ==> y < p ==> f y ==> y = x)`) THEN
ASSUME_TAC2 (
MESON[]`(!y. &0 <= y ==> y < p ==> f y ==> y = x) /\
&0 <= y - p /\ y - p < p /\ f ( y - p) ==> y - p
= x `) THEN
(SIMP_IDENT[REAL_ARITH` a - b = c <=> a = b + c `]
`y - p = (x:real) `) THEN SIMP_TAC[REAL_ADD_SYM];
SUBST_ALL_TAC (REAL_ARITH`~( &0 <= y - p ) <=> y < p `) THEN
ASSUME_TAC2 (REAL_ARITH` &0 <= t /\ t <= y ==>
&0 <= y `) THEN SUBST_ALL_TAC (
MESON[]`(!y. &0 <= y /\ y < p /\ f y ==> y = x)
<=> (!y. &0 <= y ==> y < p ==> f y ==> y = x)`) THEN
ASSUME_TAC2 (MESON[]`(!y. &0 <= y ==> y < p ==> f y ==> y = x)/\
f y /\ y < p /\ &0 <= y ==> y = x `) THEN
(CONTR_TAC o UNDISCH_ALL o REAL_ARITH) ` y = x ==> x < t ==> t <= y ==> F `];
DISCH_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o (SPEC
` &0 ` )) THEN ASSUME_TAC (REAL_ARITH` &0 <= &0 `)
THEN DOWN_TAC THEN REWRITE_TAC[REAL_ADD_LID]
THEN MESON_TAC[]]);;






let SUM_TWO_POW2S = MESON[REAL_LE_POW_2; REAL_LE_ADD]` &0 <= a pow 2 + b pow 2 `;;



let IDENT_WHEN_IDENT_SIN_COS = prove(`
&0 <= x' /\ x' < &2 * pi /\ &0 <= p /\ p < &2 * pi /\
cos x' = cos p /\ sin x' = sin p ==> p = x' `,
MP_TAC SIN_CIRCLE THEN
ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
MESON_TAC[SUM_POW2_EQ1_UNIQUE_TRIG]);;







let UNIQUE_EXISTSENCE_OF_RPHIH =
prove(`!w u (e1: real^3) e2 e3 x.
orthonormal e1 e2 e3 /\
e3 = &1 / norm (w - u) % (w - u) /\
~(x IN aff {w, u}) /\
~(w = u)
==> (?r phii h.
(&0 <= phii /\
phii < &2 * pi /\
&0 < r /\
x =
u + (r * cos phii) % e1 + (r * sin phii) % e2 + h % (w - u)) /\
(!rr p hh.
&0 <= p /\
p < &2 * pi /\
&0 < rr /\
x =
u + (rr * cos p) % e1 + (rr * sin p) % e2 + hh % (w - u)
==> rr = r /\ p = phii /\ hh = h))`,
REPEAT GEN_TAC THEN
REWRITE_TAC[orthonormal; GSYM DET_VEC3_AS_CROSS_DOT] THEN
NHANH (REAL_LT_IMP_NZ) THEN
ONCE_REWRITE_TAC[MESON[VECTOR_SUB_RZERO]` fv a b c = fv ( a - vec 0 ) ( b - vec 0 )
( c - vec 0 ) `] THEN
REWRITE_TAC[GSYM COPLANAR_DET_VEC3_EQ_0] THEN
NHANH (SPECL [`e1 : real^3`;` e2 :real^3`; `e3 :real^3`;
`(vec 0 : real^3)`; `(x : real^3) - u` ] NONCOPLANAR_3_BASIS) THEN
REWRITE_TAC[VECTOR_SUB_RZERO] THEN
STRIP_TAC THEN
ASM_CASES_TAC` t1 = &0 /\ t2 = &0 ` THENL [
FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) THEN
(ASSUME_TAC o FOR_ASM ) (prove(` t1 = &0 /\ t2 = &0 /\
x - u= t1 % e1 + t2 % e2 + t3 % e3
==> (x:real^3) - u = t3 % e3 `,
SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID])) THEN
FIRST_X_ASSUM MP_TAC THEN
UNDISCH_TAC` e3 = &1 / norm (w - u) % (w - (u:real^3))` THEN
SIMP_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH`
a -(b:real^n) = n % ( c - b )<=> a = n % c +
( &1 - n ) % b `] THEN
UNDISCH_TAC ` ~( x IN aff {w,(u:real^3)} )` THEN
REWRITE_TAC[AFF2; IN_ELIM_THM] THEN
MESON_TAC[];
FIRST_X_ASSUM MP_TAC THEN
NHANH NOT_EQ0_IMP_TRIGIZABLE THEN
NHANH SUM_POW2_EQ1_UNIQUE_TRIG THEN
PAT_REWRITE_TAC `\x. _ /\ _ /\ x ==> _ `
[REAL_ARITH` a < &2 * b <=> a < &0 + &2 * b `] THEN
SIMP_TAC[GSYM REAL_SOS_EQ_0] THEN
ONCE_REWRITE_TAC[MESON[]` a /\b ==> c <=> a ==> b ==> c `] THEN
SIMP_TAC[GSYM SQRT_EQ_0; MESON[REAL_LE_POW_2;
REAL_LE_ADD]` &0 <= t1 pow 2 + t2 pow 2 `; REAL_FIELD`
~ ( a = &0 ) ==> (d = t / a <=> t = a * d ) `] THEN
REWRITE_TAC[EXISTS_UNIQUE] THEN
REPEAT STRIP_TAC THEN
UNDISCH_TAC`x - u = t1 % e1 + t2 % e2 + t3 % (e3: real^3)` THEN
ABBREV_TAC ` tt = t1 pow 2 + t2 pow 2 ` THEN
UNDISCH_TAC ` t1 = sqrt tt * cos x' ` THEN
UNDISCH_TAC ` t2 = sqrt tt * sin x' ` THEN
SIMP_TAC[] THEN
REWRITE_TAC[VECTOR_ARITH` a - b = c <=> a = b + (c:real^N)`] THEN
REPEAT STRIP_TAC THEN
EXISTS_TAC ` sqrt tt ` THEN
EXISTS_TAC ` x' :real ` THEN
EXISTS_TAC ` t3 * ( &1 / norm ( (w:real^3) - u )) ` THEN
CONJ_TAC THENL [
UNDISCH_TAC`x = u + (sqrt tt * cos x') % e1 +
(sqrt tt * sin x') % e2 + t3 % (e3 : real^3 )` THEN
UNDISCH_TAC` e3 = &1 / norm (w - u) % (w - (u:real^3))` THEN
REWRITE_TAC[REAL_ARITH` &0 < a /\ ~( a = &0 ) <=> &0 < a `] THEN
ASSUME_TAC2 (REAL_ARITH` x' < &0 + &2 * pi ==> x' <
&2 * pi `) THEN
ASSUME_TAC2 (MESON[SQRT_POS_LE; REAL_LE_POW_2; REAL_LE_ADD]` t1 pow 2 +
t2 pow 2 = tt ==> &0 <= sqrt tt `) THEN
ASSUME_TAC2 (REAL_ARITH` ~ ( sqrt tt = &0 ) /\ &0 <= sqrt tt
==> &0 < sqrt tt `) THEN
UNDISCH_TAC ` &0 < sqrt tt ` THEN
UNDISCH_TAC ` x' < &2 * pi ` THEN
UNDISCH_TAC ` &0 <= x' ` THEN
SIMP_TAC[VECTOR_MUL_ASSOC];
IMP_TAC THEN IMP_TAC THEN IMP_TAC THEN IMP_TAC THEN
REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
UNDISCH_TAC `!ta tb tc.
x - (u:real^3) = ta % e1 + tb % e2 + tc % e3
==> ta = t1 /\ tb = t2 /\ tc = t3` THEN
FIRST_X_ASSUM MP_TAC THEN
UNDISCH_TAC`x = u + (sqrt tt * cos x') % e1
+ (sqrt tt * sin x') % e2 + t3 % (e3:real^3)` THEN
REWRITE_TAC[VECTOR_ARITH` a - b = (c:real^N)
<=> a = b + c `] THEN
UNDISCH_TAC`e3 = &1 / norm (w - u) % (w - (u:real^3))` THEN
UNDISCH_TAC` ~(w = (u:real^3) )` THEN
PHA THEN
PAT_ONCE_REWRITE_TAC `\x. x /\ _ ==> _ `
[VECTOR_ARITH` ( a = (b:real^N))
<=> ( a - b = vec 0 )`] THEN
REWRITE_TAC[ GSYM NORM_POS_LT] THEN
NHANH (MESON[REAL_FIELD ` &0 < a ==> a * &1 / a = &1`;
VECTOR_MUL_ASSOC]` &0 < a /\ aa = &1 / a % bb /\ l ==>
a % aa = ( &1 )% bb `) THEN
REWRITE_TAC[VECTOR_MUL_LID] THEN
DAO THEN
IMP_TAC THEN
DISCH_THEN (ASSUME_TAC o SYM) THEN
FIRST_ASSUM ( fun th -> PAT_ONCE_REWRITE_TAC `
\x. _ /\ x /\ _ ==> _ ` [ th]) THEN
REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
NHANH (MESON[]` (!ta tb tc.
x = u + ta % e1 + tb % e2 + tc % e3 ==> tc = t3 /\ ta = t1 /\ tb = t2 ) /\
x = u + h1 % e1 + h2 % e2 + h3 % e3 /\
x = u + l1 % e1 + l2 % e2 + l3 % e3 /\ ll ==>
l1 = h1 /\ l2 = h2 /\ l3 = h3 `) THEN
STRIP_TAC THEN
ELIM_IDENTS (REAL_FIELD` &0 < norm ((w:real^3) - u) /\ t3 = hh * norm ( w - u )
==> hh = t3 * &1 / norm ( w - u ) `) THEN
REPLICATE_TAC 3 (FIRST_X_ASSUM MP_TAC) THEN
PHA THEN
NHANH (MESON[]` a = b /\ aa = bb /\ l ==> a pow 2 + aa pow 2 =
b pow 2 + bb pow 2 `) THEN
REWRITE_TAC[REAL_ARITH` (a * b ) pow 2 + (a * c ) pow 2 =
a pow 2 * ( c pow 2 + b pow 2 ) `; SIN_CIRCLE; REAL_MUL_RID] THEN
ASSUME_TAC2 (MESON[SUM_TWO_POW2S]` t1 pow 2 + t2 pow 2 = tt
==> &0 <= tt `) THEN
ASSUME_TAC2 (SPEC `tt:real` SQRT_POS_LE) THEN
ASSUME_TAC2 (SPECL[` &0`;` rr:real `] REAL_LT_IMP_LE) THEN
ASSUME_TAC2 (SPECL[` rr:real `;` sqrt tt `] EQ_POW2_COND) THEN
FIRST_X_ASSUM (MP_TAC o SYM) THEN
PAT_ONCE_REWRITE_TAC `\x. (x <=> _ ) ==> _` [EQ_SYM_EQ] THEN
SIMP_TAC[] THEN
REPEAT STRIP_TAC THEN
FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
ASSUME_TAC2 (REAL_FIELD` &0 < rr /\ rr * cos x' = rr * cos p /\
rr * sin x' = rr * sin p ==>
cos x' = cos p /\ sin x' = sin p `) THEN
SUBST_ALL_TAC (REAL_ARITH` x' < &0 + &2 * pi <=> x' < &2 * pi `) THEN
FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) THEN
ELIM_IDENTS IDENT_WHEN_IDENT_SIN_COS]]);;



let REAL_EXISTS_UNIQUE_TRANSABLE =
prove(` ! f (t:real). (?!x. f x ) <=> (?!x. f (x - t))`,
REWRITE_TAC[EXISTS_UNIQUE] THEN REPEAT GEN_TAC THEN EQ_TAC THENL [
STRIP_TAC THEN EXISTS_TAC `x + (t:real)` THEN
ASM_REWRITE_TAC[REAL_ARITH` (a + b ) - b = a `] THEN
ASM_MESON_TAC[REAL_EQ_SUB_RADD; REAL_ARITH` (a + b ) - b = a `];
STRIP_TAC THEN EXISTS_TAC ` x - (t:real)` THEN
ASM_REWRITE_TAC[] THEN GEN_TAC THEN ONCE_REWRITE_TAC
[REAL_ARITH` x = ( x + t ) - t `] THEN DISCH_TAC THEN
SUBGOAL_THEN ` y + t = (x:real)` ASSUME_TAC THENL
[ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]]);;

(* ==================================================================== *)
(* in thms_doing_works.ml *)
(* ==================================================================== *)
(* ==================================================================== *)



let COND_FOR_EXISTS_ANY_PERI = prove(` &0 < p /\ (!x. f x <=> f (x + p))
/\ (?!x. &0 <= x /\ x < p /\ f x) ==>
(! t . &0 <= t /\ t < p ==> (?!x. t <= x /\ x < t + p /\ f x)) `,
ASSUME_TAC (SPEC_ALL PERIODIC_AT0_IMP_ANY) THEN ASM_MESON_TAC[]);;



let IN_ORIGIN_PERIOD_IMP_UNIQUENESS =
prove(` ! x t. &0 <= t /\ t < &2 * pi ==> (?!gg. &0 <= gg /\
gg < &2 * pi /\ cos x = cos ( t + gg )
/\ sin x = sin ( t + gg )) `, REPEAT STRIP_TAC THEN
MP_TAC (ONCE_REWRITE_RULE[REAL_ADD_SYM] (SPEC_ALL SIN_CIRCLE)) THEN
NHANH SUM_POW2_EQ1_UNIQUE_TRIG THEN STRIP_TAC THEN
ONCE_REWRITE_TAC[REAL_EXISTS_UNIQUE_TRANSABLE] THEN
REWRITE_TAC[REAL_SUB_LE; REAL_LT_SUB_RADD; REAL_SUB_ADD2 ] THEN
ASSUME_TAC SIN_PERIODIC THEN ASSUME_TAC COS_PERIODIC THEN
MP_TAC PI_POS THEN
PAT_ONCE_REWRITE_TAC `\x. x ==> _ ` [REAL_ARITH` &0 < a <=>
&0 < &2 * a `] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
DISCH_TAC THEN UNDISCH_TAC ` t < &2 * pi ` THEN
UNDISCH_TAC ` &0 <= t ` THEN PHA THEN
SPEC_TAC (`t:real`,`t:real`) THEN
MATCH_MP_TAC COND_FOR_EXISTS_ANY_PERI THEN ASM_MESON_TAC[]);;



let GIVEN_VALUED_IMP_UNIQUE_EXISTENCE = prove(
`! x0. (?!x. &0 <= x /\ x < &2 * pi /\ cos x = cos x0 /\
sin x = sin x0 )`, REPEAT STRIP_TAC THEN
MP_TAC (ONCE_REWRITE_RULE[REAL_ADD_SYM] SIN_CIRCLE) THEN
NHANH SUM_POW2_EQ1_UNIQUE_TRIG THEN SIMP_TAC[]);;



let EYFCXPP = prove(` !w u e1 e2 e3 (x1:real ^3 ) x2.
orthonormal e1 e2 e3 /\
e3 = &1 / norm (w - u) % (w - u) /\
~(x1 IN aff {w, u}) /\
~(x2 IN aff {w,u}) /\
~(w = u)
==> (? r1 r2 phii ssi h1 h2.
((&0 <= phii /\
phii < &2 * pi /\
&0 <= ssi /\ ssi < &2 * pi /\
&0 < r1 /\ &0 < r2 /\
x1 =
u +
(r1 * cos phii) % e1 +
(r1 * sin phii) % e2 +
h1 % (w - u) /\
x2 = u +
(r2 * cos (phii + ssi )) % e1 +
(r2 * sin (phii + ssi )) % e2 +
h2 % (w - u))) /\
(! rr1 rr2 pphii ssii h11 h22.
(&0 <= pphii /\
pphii < &2 * pi /\
&0 <= ssii /\ ssii < &2 * pi /\
&0 < rr1 /\ &0 < rr2 /\
x1 =
u +
(rr1 * cos pphii) % e1 +
(rr1 * sin pphii) % e2 +
h11 % (w - u) /\
x2 = u +
(rr2 * cos (pphii + ssii )) % e1 +
(rr2 * sin (pphii + ssii )) % e2 +
h22 % (w - u)) ==>
rr1 = r1 /\ rr2 = r2 /\ pphii = phii /\
ssii = ssi /\ h11 = h1 /\ h22 = h2 ) )`,
ONCE_REWRITE_TAC[MESON[]` a1 /\a2/\a3/\a4 /\a5 <=>
(a1/\a2/\a3/\a5) /\ a4 `] THEN
NHANH UNIQUE_EXISTSENCE_OF_RPHIH THEN
ONCE_REWRITE_TAC[MESON[]` (( a1 /\a2/\a3/\a4) /\ss)/\a5 <=>
(a1/\a2/\a5/\a4)/\a3/\ss`] THEN
NHANH UNIQUE_EXISTSENCE_OF_RPHIH THEN REPEAT STRIP_TAC THEN
UNDISCH_TAC ` phii' < &2 * pi ` THEN UNDISCH_TAC ` &0 <= phii' ` THEN
PHA THEN NHANH_PAT `\x. x ==> _ ` (SPEC `phii: real` IN_ORIGIN_PERIOD_IMP_UNIQUENESS)
THEN REWRITE_TAC[EXISTS_UNIQUE] THEN STRIP_TAC THEN
EXISTS_TAC `r': real` THEN EXISTS_TAC `r:real` THEN
EXISTS_TAC ` phii': real` THEN EXISTS_TAC `gg: real` THEN
EXISTS_TAC ` h': real` THEN EXISTS_TAC ` h: real` THEN
ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN REWRITE_TAC[TAUT`
a /\ b ==> c <=> a ==> b ==> c`] THEN REPEAT DISCH_TAC THEN
REPLICATE_TAC 3 (FIRST_X_ASSUM MP_TAC) THEN
UNDISCH_TAC ` (x2: real^3 ) = u + (r * cos phii) % e1 +
(r * sin (phii)) % e2 + h % (w - u)` THEN
UNDISCH_TAC `(x1 : real^3) = u + (r' * cos phii') % e1 +
(r' * sin phii') % e2 + h' % (w - u)` THEN
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]
THEN REPEAT DISCH_TAC THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
ASSUME_TAC2 (UNDISCH (MESON[]`(!rr p hh. &0 <= p /\ p < &2 * pi /\ &0 < rr /\
(x1: real^3) = u + (rr * cos p) % e1 + (rr * sin p) % e2 + hh % (w - u)
==> rr = r' /\ p = phii' /\ hh = h') ==>
u + (rr1 * cos pphii) % e1 + (rr1 * sin pphii) % e2 + h11 % (w - u) =
x1 /\ &0 <= pphii /\ pphii < &2 * pi /\ &0 < rr1 ==>
rr1 = r' /\ pphii = phii' /\ h11 = h' `)) THEN ASM_REWRITE_TAC[]
THEN REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
MP_TAC (SPEC `pphii + (ssii: real)`
GIVEN_VALUED_IMP_UNIQUE_EXISTENCE) THEN
REWRITE_TAC[EXISTS_UNIQUE] THEN STRIP_TAC THEN
UNDISCH_TAC ` (u: real^3) + (rr2 * cos (pphii + ssii)) % e1 +
(rr2 * sin (pphii + ssii)) % e2 + h22 % (w - u) = x2` THEN
REPLICATE_TAC 3 (FIRST_X_ASSUM MP_TAC) THEN
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN SIMP_TAC[] THEN
PHA THEN STRIP_TAC THEN
ASSUME_TAC2 ((UNDISCH o MESON[])`(!rr p hh. &0 <= p /\ p < &2 * pi /\ &0 < rr /\
(x2: real^3) = u + (rr * cos p) % e1 + (rr * sin p) % e2 + hh % (w - u)
==> rr = r /\ p = phii /\ hh = h) ==>
&0 < rr2 /\ &0 <= x /\ x < &2 * pi /\
x2 = u + (rr2 * cos x) % e1 + (rr2 * sin x) % e2 + h22 % (w - u)
==> r = rr2 /\ h = h22 /\ x = phii `) THEN
FIRST_ASSUM (fun x -> REWRITE_TAC[ x]) THEN
USE_FIRST `(pphii: real) = phii' ` SUBST_ALL_TAC THEN
REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
FIRST_X_ASSUM SUBST_ALL_TAC THEN
ELIM_IDENTS ((UNDISCH o MESON[])`(!y. &0 <= y /\
y < &2 * pi /\ cos phii = cos (phii' + y) /\
sin phii = sin (phii' + y) ==> y = gg) ==>
cos (phii' + ssii) = cos phii /\
sin (phii' + ssii) = sin phii /\ &0 <= ssii /\ ssii < &2 * pi
==> gg = ssii `));;



(* ========================== *)
(* ========================== *)


let INTERGRAL_UNIONS_INTERVALS =
prove(`! N. UNIONS {{x | &(n - 1) <= x /\ x < &n} | 0 < n /\ n <= N} =
{x | &0 <= x /\ x < &N}`, INDUCT_TAC THENL
[REWRITE_TAC[ARITH_RULE`~( 0 < b /\ b <= 0 )`; REAL_ARITH`~( &0 <= x /\ x < &0 )`] THEN
SET_TAC[];
REWRITE_TAC[ARITH_RULE`0 < n /\ n <= SUC N <=> 0 < n /\ n <= N \/ n = N + 1`; SET_RULE` UNIONS
{ f x | h x \/ x = N} = ( UNIONS { f x | h x }) UNION ( f N ) `] THEN
REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD; REAL_ARITH` &0 <= x /\ x < &N + &1 <=>
&0 <= x /\ x < &N \/ &N <= x /\ x < &N + &1 `] THEN
ASM_SIMP_TAC[ARITH_RULE` (a + 1) - 1 = a `] THEN SET_TAC[]]);;


let REAL_LE_EQ_OR_LT = REAL_ARITH` &0 <= a <=> a = &0 \/ &0 < a `;;


let EXISTS_IN_UNIT_INTERVAL = prove(`!x. ?n. &0 <= x + real_of_int n /\ x + real_of_int n < &1`,
MATCH_MP_TAC (MESON[REAL_ARITH` &0 <= a \/ &0 <= -- a `]` (! a. P a ==> P ( -- a ))
/\ (! a. &0 <= a ==> P a ) /\ (! a. a = -- ( -- a )) ==> (! a . P a )`) THEN CONJ_TAC THENL [
GEN_TAC THEN REWRITE_TAC[REAL_LE_EQ_OR_LT ] THEN STRIP_TAC THENL [
EXISTS_TAC ` -- (n:int)` THEN
ASM_REWRITE_TAC[int_neg_th; GSYM REAL_NEG_ADD; REAL_NEG_EQ_0] THEN REAL_ARITH_TAC;
EXISTS_TAC ` -- n + (&1: int)` THEN
ASM_REWRITE_TAC[int_neg_th; GSYM REAL_NEG_ADD; REAL_NEG_EQ_0;int_add_th; int_of_num_th]
THEN ASM_REAL_ARITH_TAC];REWRITE_TAC[REAL_NEGNEG] THEN GEN_TAC THEN
CHOOSE_TAC (SPEC `x: real` (MATCH_MP REAL_ARCH (REAL_ARITH` &0 < &1 `))) THEN
ASSUME_TAC (SPEC `n: num ` INTERGRAL_UNIONS_INTERVALS) THEN
DOWN_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN
NHANH (SET_RULE` x < &n /\ aa = {x | &0 <= x /\ x < &n} /\
&0 <= x ==> x IN aa `) THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
STRIP_TAC THEN EXISTS_TAC` -- ( &(n' - 1): int) ` THEN
REPLICATE_TAC 2 (FIRST_X_ASSUM MP_TAC) THEN
PHA THEN NHANH (SET_RULE` t = {x| P x } /\ x IN t ==> P x `) THEN
REWRITE_TAC[int_neg_th; int_of_num_th] THEN STRIP_TAC THEN
REPLICATE_TAC 2 (FIRST_X_ASSUM MP_TAC) THEN
ASSUME_TAC2 (ARITH_RULE` 0 < n' ==> 1 <= n'`) THEN
ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REAL_ARITH_TAC]);;

let TWO_PI_POS = prove(` &0 < &2 * pi `, MP_TAC PI_POS THEN REAL_ARITH_TAC);;


let MOVE_TO_UNIT_INTERVAL = prove(`!x. ?n. &0 <= x + ( real_of_int n )* &2 * pi /\ x + ( real_of_int n) * &2 * pi < &2 * pi`,
ONCE_REWRITE_TAC [GSYM (MATCH_MP REAL_LE_RDIV_0 TWO_PI_POS)] THEN
ONCE_REWRITE_TAC[GSYM (MATCH_MP REAL_LT_DIV2_EQ TWO_PI_POS)] THEN
REWRITE_TAC[REAL_ARITH` ( a + b ) / c = a / c + b / c `; MATCH_MP (REAL_FIELD` &0 < a ==> a / a = &1 `) TWO_PI_POS;
MATCH_MP (REAL_FIELD` &0 < c ==> (a * c ) / c = a `) TWO_PI_POS] THEN MESON_TAC[EXISTS_IN_UNIT_INTERVAL ]);;



let SIN_TOTAL_PERIODIC = prove(`! n. sin (x + &n * &2 * pi) = sin x `,
INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
ASM_REWRITE_TAC[ADD1;GSYM REAL_OF_NUM_ADD;
REAL_ARITH` x + (&n + &1) * a = (x + &n * a ) + a `; SIN_PERIODIC]);;


let SIN_PERIODIC_IN_WHOLE = prove(` !n. sin ( x + real_of_int n * &2 * pi ) = sin x `,
GEN_TAC THEN ASM_CASES_TAC` &0 <= (n: int) ` THENL [
ASSUME_TAC2 (SPEC `n: int ` INT_OF_NUM_OF_INT) THEN EXPAND_TAC "n" THEN
REWRITE_TAC[int_of_num_th; SIN_TOTAL_PERIODIC ]; FIRST_X_ASSUM MP_TAC] THEN
NHANH (ARITH_RULE` ~( &0 <= (n: int) ) ==> &0 <= -- n `) THEN STRIP_TAC THEN
ASSUME_TAC2 (SPEC `-- n: int ` INT_OF_NUM_OF_INT) THEN
ONCE_REWRITE_TAC[ARITH_RULE` (a: int) = -- -- a `] THEN
ONCE_REWRITE_TAC[int_neg_th] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
REWRITE_TAC[int_of_num_th; REAL_MUL_LNEG] THEN
MESON_TAC[SIN_TOTAL_PERIODIC; REAL_ARITH`(a + -- b ) + (b:real) = a `]);;



let COS_PERIODIC_IN_WHOLE = prove(` cos ( x + real_of_int n * &2 * pi ) = cos x `,
REWRITE_TAC[COS_SIN; REAL_ARITH` a - (b + c ) = a - b - c `] THEN
MESON_TAC[REAL_ARITH` x = x - y + y `; SIN_PERIODIC_IN_WHOLE]);;


let SIN_COS_PERIODIC_IN_WHOLE =
GEN_ALL (CONJ (SPEC_ALL SIN_PERIODIC_IN_WHOLE) COS_PERIODIC_IN_WHOLE);;


let SIN_COS_IDEN_IFF_DIFFER_PERS = prove(`! x y. cos x = cos y /\ sin x = sin y <=> (? k. x = y + real_of_int k * &2 * pi ) `,
REPEAT GEN_TAC THEN EQ_TAC THENL [CHOOSE_TAC (SPEC` x:real` MOVE_TO_UNIT_INTERVAL ) THEN
CHOOSE_TAC (SPEC` y:real` MOVE_TO_UNIT_INTERVAL ) THEN
ASSUME_TAC (GSYM (SPECL[`n:int`;`x:real`] SIN_COS_PERIODIC_IN_WHOLE)) THEN
FIRST_X_ASSUM (fun x -> PAT_ONCE_REWRITE_TAC`\x. x = _ /\ x = _ ==> _ ` [x]) THEN
ASSUME_TAC (GSYM (SPECL[`n':int`;`y:real`] SIN_COS_PERIODIC_IN_WHOLE)) THEN
FIRST_X_ASSUM (fun x -> PAT_ONCE_REWRITE_TAC `\x. _ = x /\ _ = x ==> _ ` [x]) THEN
DOWN_TAC THEN NHANH IDENT_WHEN_IDENT_SIN_COS THEN
REWRITE_TAC[REAL_ARITH`y + a * t = x + b * t <=> x = y + (a -b ) * t`; GSYM int_sub_th] THEN
STRIP_TAC THEN EXISTS_TAC ` n' - (n:int)` THEN ASM_REWRITE_TAC[];
STRIP_TAC THEN ASM_SIMP_TAC[SIN_COS_PERIODIC_IN_WHOLE ]]);;


let NOT_EQ_IMP_AFF_AND_COLL3 = prove(`! v (w:real^N) u. ~( v = w ) ==>
( u IN aff {v,w} <=> collinear {v,w,u}) `, ONCE_REWRITE_TAC[COLLINEAR_3] THEN
REWRITE_TAC[COLLINEAR_LEMMA; VECTOR_SUB_EQ] THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MESON[]` (P ==> Q) /\ (Q <=> L) ==> (L <=> P \/ Q)`) THEN CONJ_TAC THENL [
STRIP_TAC THEN EXISTS_TAC `&0` THEN
ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_REFL]; REWRITE_TAC[AFF2; IN_ELIM_THM] THEN
EQ_TAC THENL [STRIP_TAC THEN EXISTS_TAC `c:real` THEN FIRST_X_ASSUM MP_TAC THEN
VECTOR_ARITH_TAC; STRIP_TAC THEN EXISTS_TAC `t:real` THEN FIRST_X_ASSUM MP_TAC THEN
VECTOR_ARITH_TAC]]);;

let R_SIN_CIRCLE = prove(` ! r x. ( r * cos x ) pow 2 + ( r * sin x ) pow 2 = r pow 2 `,
REPEAT GEN_TAC THEN MP_TAC (SPEC_ALL SIN_CIRCLE) THEN CONV_TAC REAL_RING);;


let R_SIN_COS_IDENT = prove(`! r rr x y. &0 <= r /\ &0 <= rr /\
r * cos x = rr * cos y /\ r * sin x = rr * sin y ==> r = rr /\ (
r = &0 \/ cos x = cos y /\ sin x = sin y ) `,
NHANH (MESON[R_SIN_CIRCLE ]`r * cos x = rr * cos y /\ r * sin x = rr * sin y ==>
r pow 2 = rr pow 2 `) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
SUBGOAL_THEN `r = (rr: real)` ASSUME_TAC THENL [ASM_SIMP_TAC[EQ_POW2_COND];
ASM_SIMP_TAC[]] THEN ASM_CASES_TAC ` rr = &0 ` THENL [ASM_SIMP_TAC[]; DISJ2_TAC] THEN
FIRST_X_ASSUM SUBST_ALL_TAC THEN DOWN_TAC THEN
REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN MESON_TAC[]);;


let R_POS_SIN_COS_IDENT = prove(`! r rr x y. &0 < r /\ &0 < rr /\
r * cos x = rr * cos y /\ r * sin x = rr * sin y ==> r = rr /\
cos x = cos y /\ sin x = sin y `,
MESON_TAC[REAL_LT_IMP_LE; R_SIN_COS_IDENT; REAL_ARITH` &0 < a ==> ~( a = &0 )`]);;


let BEGIN_POINT_PERIODIC = prove(` ! x k. &0 <= x /\ x < &2 * pi /\ x = real_of_int k * &2 * pi ==> x = &0 `,
REPEAT GEN_TAC THEN ASSUME_TAC (SPEC` &0` REAL_LE_REFL) THEN ASSUME_TAC TWO_PI_POS THEN
STRIP_TAC THEN FIRST_X_ASSUM MP_TAC THEN
PAT_ONCE_REWRITE_TAC `\x. _ = x ==> _` [REAL_ARITH` a = &0 + a `] THEN
ASM_MESON_TAC[SIN_COS_PERIODIC_IN_WHOLE; IDENT_WHEN_IDENT_SIN_COS]);;


let BODE_YEU_ANH_DI = prove(`! k. &0 <= ppsssi /\ ppsssi < &2 * pi /\
&0 <= ppsssi1 /\ ppsssi1 < &2 * pi /\ &0 <= aa /\
aa < &2 * pi /\
aa = ppsssi - ppsssi1 + real_of_int k * &2 * pi ==>
( aa = &0 <=> ppsssi = ppsssi1 ) `,
REPEAT STRIP_TAC THEN
EQ_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ARITH` a - b + c = &0 <=> b = a + c `]
THEN ASM_MESON_TAC[IDENT_WHEN_IDENT_SIN_COS; SIN_COS_IDEN_IFF_DIFFER_PERS];
DISCH_THEN SUBST_ALL_TAC THEN DOWN_TAC THEN REWRITE_TAC[REAL_SUB_REFL; REAL_ADD_LID] THEN
MESON_TAC[BEGIN_POINT_PERIODIC ]]);;



(* ====================== *)
(* ====================== *)
(* ========= LEMMA 1.31 =========== *)




let ORTHONORMAL_BASIS = prove(
` orthonormal ( basis 1 ) (basis 2 ) ( basis 3 ) `,
MP_TAC (MESON[DOT_BASIS_BASIS]`! i j. 1 <= i /\ i <= dimindex (:3) /\ 1 <= j /\ j <= dimindex (:3)
==> ((basis i): real^3) dot basis j = (if i = j then &1 else &0)`) THEN
REWRITE_TAC[orthonormal; DIMINDEX_3; ARITH_RULE` 1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3 `] THEN
NGOAC THEN
REWRITE_TAC[ARITH_RULE` 1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3 `] THEN
KHANANG THEN
REWRITE_TAC[TAUT`(a \/ v) \/ c <=> a \/ v \/ c `] THEN
SIMP_TAC[TAUT`(a \/ v) \/ c <=> a \/ v \/ c `; MESON[]`(! i j. i = a /\ j = b \/ Q i j ==> R i j)
<=> R a b /\ (! i j. Q i j ==> R i j)`; ARITH_RULE` ~(1 = 2 )/\ ~( 1 = 3 ) /\ ~( 2 = 3 )` ] THEN
STRIP_TAC THEN
FIRST_X_ASSUM (MP_TAC o (SPECL[` 3`;`3`])) THEN
SIMP_TAC[] THEN
SIMP_TAC[CROSS_BASIS; REAL_ARITH` &0 < &1 `]);;




let ORTHO_IMP_NORM_CROSS_PRODUCT =
prove(`! x y. x dot y = &0 ==> norm (x cross y) pow 2 = (norm x * norm y) pow 2 `,
REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL NORM_CROSS_DOT) THEN
ASM_SIMP_TAC[REAL_ARITH` a + &0 pow 2 = a `]);;


let TWO_UNIT_ORTH_VECTORS_IMP_ORTHONORMAL = prove(`! e1 (e3:real^3). norm e1 = &1 /\ norm e3 = &1 /\ e1 dot e3 = &0 ==> (? e2.
orthonormal e1 e2 e3 ) `,
REPEAT STRIP_TAC THEN
EXISTS_TAC ` e3 cross e1 ` THEN
ASM_SIMP_TAC[DOT_CROSS_SELF; orthonormal; CROSS_LAGRANGE; DOT_LSUB;
DOT_LMUL; DOT_SQUARE_NORM; DOT_SYM] THEN
ASM_SIMP_TAC[DOT_RSUB; DOT_RMUL; GSYM NORM_POW_2; DOT_SYM] THEN
FIRST_X_ASSUM (MP_TAC o (ONCE_REWRITE_RULE[DOT_SYM])) THEN
NHANH ORTHO_IMP_NORM_CROSS_PRODUCT THEN
ASM_SIMP_TAC[] THEN
REAL_ARITH_TAC);;

let ORTHONORMAL_BASIS3 = REWRITE_RULE[orthonormal] ORTHONORMAL_BASIS;;

let EXISTS_OTHOR_VECTOR_DIFFF_VEC0 = prove(
`! (u: real^3). ? v . ~(v = vec 0) /\ u dot v = &0 `,
GEOM_BASIS_MULTIPLE_TAC 1 `u:real^3` THEN REPEAT STRIP_TAC THEN
EXISTS_TAC `( basis 2): real^3` THEN MP_TAC ORTHONORMAL_BASIS THEN
SIMP_TAC[orthonormal; DOT_LMUL; REAL_MUL_RZERO;
REWRITE_RULE[DE_MORGAN_THM] NOT_BASISES_EQ_VEC0]);;

let INVERT_NORM_POS_LE = prove(` ! (x: real^N). &0 <= &1 / norm x `,
GEN_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC);;

let NOT_0_INVERTABLE = REAL_FIELD` ~( a = &0) <=> &1 / a * a = &1 `;;


let NOT_VEC0_UNITABLE = prove(`! (u: real^N). ~( u = vec 0 ) <=> norm ( &1 / norm u % u ) = &1 `,
SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; ABS_1; GSYM NORM_EQ_0; NOT_0_INVERTABLE]);;


let EXISTS_UNIT_OTHOR_VECTOR = prove(` !(u: real^3). ?v. norm v = &1 /\ u dot v = &0 `,
GEN_TAC THEN (CHOOSE_TAC (SPEC` u:real^3 ` EXISTS_OTHOR_VECTOR_DIFFF_VEC0)) THEN
EXISTS_TAC ` &1 / norm v % ( v:real^3) ` THEN ASM_SIMP_TAC[GSYM NOT_VEC0_UNITABLE; DOT_RMUL; REAL_MUL_RZERO]);;



let AFF3_TRANSLATION_IMAGE = prove(
` aff (IMAGE (\x. (v:real^N) + x) {v1, v2, v3}) = IMAGE (\x. v + x) ( aff {v1,v2,v3} ) `,
REWRITE_TAC[IMAGE_CLAUSES; aff; AFFINE_HULL_3; FUN_EQ_THM; IN_ELIM_THM] THEN
GEN_TAC THEN EQ_TAC THENL [PAT_ONCE_REWRITE_TAC ` \x. _ ==> x ` [GSYM IN] THEN
STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
EXISTS_TAC ` u % v1 + v' % v2 + w % (v3:real^N)` THEN
CONJ_TAC THENL [DOWN_TAC THEN SIMP_TAC[REAL_ARITH` a + b = &1 <=> a = &1 - b `]
THEN DISCH_TAC THEN VECTOR_ARITH_TAC; ASM_MESON_TAC[]];
PAT_ONCE_REWRITE_TAC ` \x. x ==> _ ` [GSYM IN]] THEN
REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN STRIP_TAC THEN EXISTS_TAC `u:real` THEN
EXISTS_TAC `v':real` THEN EXISTS_TAC `w:real` THEN
ASM_SIMP_TAC[VECTOR_ARITH` u % (v + v1) + v' % (v + v2) + w % (v + v3) = (u + v' + w ) % v +
u % v1 + v' % v2 + w % v3 `; VECTOR_MUL_LID]);;


let IMAGE_INTER_AFF3 = prove(`IMAGE (\x. (v:real^N) + x) s INTER aff (IMAGE (\x. v + x) {v1,v2,v3}) =
IMAGE (\x. v + x) (s INTER aff {v1,v2,v3})`,
SUBGOAL_THEN ` ! x y. (\x. (v:real^N) + x) y = (\x. v + x) x ==> y = x ` MP_TAC THENL [
REWRITE_TAC[BETA_THM; VECTOR_ARITH` a + b = a + c ==> b = (c:real^N)`];
SIMP_TAC[AFF3_TRANSLATION_IMAGE; GSYM IMAGE_INTER_INJ]]);;


let DIHV_TRASABLE = prove(`! (v: real^N). dihV (v + u) (v + w) (v + v1) (v + v2) = dihV u w v1 v2`,
REWRITE_TAC[dihV; VECTOR_ARITH` ((v:real^N) + v1) - (v + u) = v1 - u `]);;


let VECTOR_MUL_R_TO_L = REWRITE_RULE[IMP_IMP] (prove(`!a (x:real^N) y. ~(a = &0) ==> a % x = y ==> x = &1 / a % y`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC `a :real` THEN
ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_FIELD` ~( a = &0) ==> ( a * &1 / a ) = &1 `
; VECTOR_MUL_LID]));;


let AFF2_VEC0 = prove(` aff {vec 0, (w: real^N)} = { x | ? k. x = k % w }`,
REWRITE_TAC[AFF2; FUN_EQ_THM; IN_ELIM_THM] THEN
GEN_TAC THEN EQ_TAC THENL [STRIP_TAC THEN EXISTS_TAC ` &1 - t ` THEN
EVERY_ASSUM MP_TAC THEN SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID];
STRIP_TAC THEN EXISTS_TAC ` &1 - k ` THEN
ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; REAL_ARITH` a - ( a - b ) = b `]]);;


let PERPENCULAR_PART_IDENT0 = prove(`~(w = vec 0) /\ (w dot w) % v1 - (v1 dot w) % w = vec 0
==> v1 IN aff {vec 0, w}`, PAT_REWRITE_TAC `\x. x /\ _ ==> _ `[GSYM DOT_EQ_0] THEN
REWRITE_TAC[VECTOR_SUB_EQ] THEN NHANH (VECTOR_MUL_R_TO_L) THEN
REWRITE_TAC[AFF2_VEC0; IN_ELIM_THM; VECTOR_MUL_ASSOC] THEN MESON_TAC[]);;


let INSERT_INTER_EMPTY = SET_RULE` {} INTER s = {} /\ (( a INSERT s ) INTER ss = {} <=>
~( a IN ss ) /\ s INTER ss = {} )`;;

(*

Hi Truong,

There is a related theorem AZIM_SPECIAL_SCALE already there in
"Multivariate/flyspeck.ml". This only covers scaling of one of the
arguments, but the proof can be generalized to handle all of them;
see the proof script below.

Since the definition of "azim" has multiple quantifier alternations, I
handle things in a more automatic way using the same quantifier
modification conversion PARTIAL_EXPAND_QUANTS_CONV that is used inside
the "without loss of generality" tactics.

John.



let COLLINEAR_SCALE_ALL = prove
(`!a b v w. ~(a = &0) /\ ~(b = &0)
==> (collinear {vec 0,a % v,b % w} <=> collinear {vec 0,v,w})`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COLLINEAR_SPECIAL_SCALE] THEN
ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {a,c,b}`] THEN
ASM_SIMP_TAC[COLLINEAR_SPECIAL_SCALE]);;

let AZIM_SCALE_ALL = prove
(`!a v w1 w2.
&0 < a /\ &0 < b /\ &0 < c
==> azim (vec 0) (a % v) (b % w1) (c % w2) = azim (vec 0) v w1 w2`,
let lemma = MESON[REAL_LT_IMP_NZ; REAL_DIV_LMUL]
`!a. &0 < a ==> (!y. ?x. a * x = y)` in
let SCALE_QUANT_TAC side asm avoid =
MP_TAC(MATCH_MP lemma (ASSUME asm)) THEN
DISCH_THEN(MP_TAC o MATCH_MP QUANTIFY_SURJECTION_THM) THEN
DISCH_THEN(CONV_TAC o side o PARTIAL_EXPAND_QUANTS_CONV avoid) in
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC[azim_def; COLLINEAR_SCALE_ALL; REAL_LT_IMP_NZ] THEN
COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN
ASM_SIMP_TAC[DIST_0; NORM_MUL; GSYM VECTOR_MUL_ASSOC] THEN
ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`; VECTOR_MUL_LCANCEL] THEN
ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN
SCALE_QUANT_TAC RAND_CONV `&0 < a` ["psi"; "r1"; "r2"] THEN
SCALE_QUANT_TAC LAND_CONV `&0 < b` ["psi"; "h2"; "r2"] THEN
SCALE_QUANT_TAC LAND_CONV `&0 < c` ["psi"; "h1"; "r1"] THEN
ASM_SIMP_TAC[GSYM VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_LDISTRIB;
VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ; REAL_LT_MUL_EQ] THEN
REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_AC]);;

let AZIM_SCALE_INV_NORM = prove
(`!w v1 v2.
~(w = vec 0) /\ ~(v1 = vec 0) /\ ~(v2 = vec 0)
==> azim (vec 0) w v1 v2 =
azim (vec 0) (&1 / norm w % w) (&1 / norm v1 % v1)
(&1 / norm v2 % v2)`,
REWRITE_TAC[real_div; REAL_MUL_LID] THEN
SIMP_TAC[REAL_LT_INV_EQ; NORM_POS_LT; AZIM_SCALE_ALL]);;

*)



let ARCV_VEC0_ABS = prove(` ~(ku = &0) /\ ~( kv = &0 ) ==> arcV (vec 0) (u: real^N) v =
arcV (vec 0) ( abs ku % u ) (abs kv % v)`, STRIP_TAC THEN
ABBREV_TAC ` ahah = arcV (vec 0) (abs ku % (u: real^N)) (abs kv % v) ` THEN
FIRST_X_ASSUM (fun x -> ONCE_REWRITE_TAC[MATCH_MP WHEN_K_DIFF0_ARCV x]) THEN
ONCE_REWRITE_TAC[ARC_SYM] THEN FIRST_X_ASSUM (fun x -> ONCE_REWRITE_TAC[MATCH_MP WHEN_K_DIFF0_ARCV x])
THEN EXPAND_TAC "ahah" THEN SIMP_TAC[ARC_SYM]);;

let WHEN_A_B_POS_ARCV_STABLE = MESON[ARC_SYM; WHEN_K_POS_ARCV_STABLE]
` ! a b (x: real^N) y. &0 < a /\ &0 < b ==> arcV ( vec 0 ) x y = arcV ( vec 0 ) ( a % x ) ( b % y ) `;;

let THREE_POS_IMP_DIHV_STABLE = prove(`!x y z.
&0 < a /\ &0 < b /\ &0 < c
==> dihV (vec 0) x y z = dihV (vec 0) (a % x) (b % y) (c % z)`,
REWRITE_TAC[DIHV_FORMULAR; VECTOR_SUB_RZERO] THEN
REWRITE_TAC[DOT_LMUL; DOT_RMUL; VECTOR_MUL_ASSOC] THEN
REWRITE_TAC[REAL_ARITH` ((a * a * xx) * b) = ( a pow 2 * b ) * xx `;
REAL_ARITH` (b * a * c) * a = ( a pow 2 * b ) * c `] THEN
ONCE_REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
REWRITE_TAC[REAL_ARITH` ((a * a * xx) * b) = ( a pow 2 * b ) * xx `;
REAL_ARITH` (b * a * c) * a = ( a pow 2 * b ) * c `; GSYM VECTOR_SUB_LDISTRIB] THEN
REPEAT STRIP_TAC THEN MATCH_MP_TAC WHEN_A_B_POS_ARCV_STABLE THEN
CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN
ASM_SIMP_TAC[POW_2; REAL_LT_MUL];MATCH_MP_TAC REAL_LT_MUL THEN
ASM_SIMP_TAC[POW_2; REAL_LT_MUL]]);;


let VECTOR_OF_DIHV_ORTHONORMAL = prove(` ((w dot w) % (v1: real^N) - (v1 dot w) % w ) dot w = &0 `,
REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN REAL_ARITH_TAC);;

let ORTHOGORNAL_UNITIZE = prove(` ! x (y:real^N). x dot y = &0 ==> ( &1 / norm x % x ) dot ( &1 / norm y % y ) = &0 `,
REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN SIMP_TAC[REAL_MUL_RZERO]);;

let NOT_MUL_EQ0_EQ = MESON[REAL_ENTIRE]`!x y. ~( x * y = &0 ) <=> ~( x = &0 ) /\ ~( y = &0) `;;

let UNITS_NOT_EQ_0 = MESON[NOT_MUL_EQ0_EQ; REAL_ARITH` ~( &1 = &0 )`]`! x y. x * y = &1 ==> ~( x = &0 ) /\ ~( y = &0) `;;

let REAL_MUL_LRINV =
let t1 = UNDISCH (SPEC_ALL REAL_MUL_LINV) in
let t2 = UNDISCH (SPEC_ALL REAL_MUL_RINV) in
let t3 = CONJ t1 t2 in DISCH ` ~( x = &0 ) ` t3;;

let NOT_EQ0_IMP_NEITHER_INVERT = prove(` ~( a = &0 ) ==> ~( &1 / a = &0 ) `,
REWRITE_TAC[NOT_0_INVERTABLE; REAL_FIELD` &1 / ( &1 / a ) = a `] THEN SIMP_TAC[REAL_MUL_SYM]);;


let PROJECTOR_NOT_EQ_VEC0 = prove(`! w v1. ~( (w:real^N) = vec 0 ) /\ ~(v1 IN aff {vec 0, w}) <=>
~( (w dot w) % v1 - (v1 dot w) % w = vec 0 ) `, REPEAT GEN_TAC THEN
EQ_TAC THENL [REWRITE_TAC[GSYM DE_MORGAN_THM; CONTRAPOS_THM] THEN
ASM_CASES_TAC ` (w:real^N) = vec 0 ` THENL [ASM_SIMP_TAC[];
ASM_SIMP_TAC[PERPENCULAR_PART_IDENT0]];
ASM_CASES_TAC ` (w:real^N) = vec 0 ` THENL [
ASM_SIMP_TAC[DOT_RZERO; VECTOR_MUL_LZERO; VECTOR_SUB_RZERO];
ASM_SIMP_TAC[CONTRAPOS_THM; AFF2_VEC0; IN_ELIM_THM]] THEN STRIP_TAC THEN
ASM_SIMP_TAC[VECTOR_MUL_ASSOC; DOT_LMUL; REAL_MUL_SYM; VECTOR_SUB_REFL]]);;

let NOT_EQ_VEC0_IMP_EQU_AFF_COLL = prove(` ! (w:real^N) u. ~( w = vec 0 ) ==> ( u IN aff {vec 0, w } <=> collinear {vec 0, w, u}) `,
REPEAT STRIP_TAC THEN EQ_TAC THENL [REWRITE_TAC[AFF2_VEC0; IN_ELIM_THM; COLLINEAR_LEMMA] THEN
MESON_TAC[]; REWRITE_TAC[AFF2_VEC0; IN_ELIM_THM; COLLINEAR_LEMMA] THEN
STRIP_TAC THENL [ASM_MESON_TAC[]; EXISTS_TAC `&0 ` THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO];
ASM_MESON_TAC[]]]);;


let NOT_EQ_IMP_EXISTS_BASIC = prove(`! v (w:real^3). ~( v = w ) ==> 
  (? e1 e2 e3. orthonormal e1 e2 e3 /\ dist (w,v) % e3 = w - v)`,
REPEAT STRIP_TAC THEN 
CHOOSE_TAC (SPEC `w - (v:real^3)` EXISTS_UNIT_OTHOR_VECTOR) THEN
DOWN_TAC THEN ONCE_REWRITE_TAC[MESON[]` ~( a = b ) <=> ~ (b = a )`]
THEN PAT_ONCE_REWRITE_TAC`\ x. x ==> y ` [GSYM VECTOR_SUB_EQ] THEN
REWRITE_TAC[NOT_VEC0_UNITABLE] THEN 
ABBREV_TAC` e1 = &1 / norm ( w - v ) % ( w - (v:real^3))`
THEN REWRITE_TAC[DOT_LNEG; REAL_NEG_EQ_0] THEN 
NHANH (MESON[REAL_MUL_RZERO] ` a = &0 ==>
 (&1 / norm ( w  - (v:real^3))) * a = &0 `) THEN 
ASM_REWRITE_TAC[GSYM DOT_LMUL] THEN 
MATCH_MP_TAC (MESON[]` ( a /\ b /\ d ==> e ) ==> a /\ b 
/\ c /\ d ==> e `) THEN 
NHANH TWO_UNIT_ORTH_VECTORS_IMP_ORTHONORMAL THEN 
STRIP_TAC THEN EXISTS_TAC` e2:real^3` THEN 
EXISTS_TAC` v' : real^3` THEN EXISTS_TAC` e1: real^3` THEN 
FIRST_X_ASSUM MP_TAC THEN SIMP_TAC[ORTHONORMAL_PERMUTE] THEN 
STRIP_TAC THEN UNDISCH_TAC ` norm (e1:real^3) = &1 ` THEN 
EXPAND_TAC "e1" THEN 
REWRITE_TAC[GSYM NOT_VEC0_UNITABLE; GSYM NORM_EQ_0;
VECTOR_MUL_ASSOC; dist] THEN 
SIMP_TAC[REAL_FIELD`~ ( a = &0 ) ==> ( a * &1 / a ) = &1 `;
 VECTOR_MUL_LID]);;

(* 19 aug 2009 *)
(* =========================================== *)
(* =========================================== *)
let YVREJIS = prove(`! (v: real^3) w w1 w2.
cyclic_set {w1, w2} v w
==> (azim v w w1 w2 = &0 ==> azim v w w1 w2 + azim v w w2 w1 = &0) /\
(~(azim v w w1 w2 = &0)
==> azim v w w1 w2 + azim v w w2 w1 = &2 * pi)`,
REWRITE_TAC[cyclic_set] THEN
NHANH NOT_EQ_IMP_EXISTS_BASIC THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
ASSUME_TAC (SPECL[`v:real^3`;` w:real^3`] azim ) THEN
ASM_REWRITE_TAC[] THEN FIRST_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
FIRST_X_ASSUM MP_TAC THEN STRIP_TAC THEN
UNDISCH_TAC `~(v = w:real^3)` THEN
UNDISCH_TAC `dist (w,v) % e3 = w - (v:real^3)` THEN
UNDISCH_TAC `orthonormal e1 e2 e3` THEN PHA THEN
ONCE_REWRITE_TAC[MESON[]`~(a = b ) <=> ~( b = a )`] THEN
FIRST_ASSUM NHANH THEN FIRST_X_ASSUM MP_TAC THEN
FIRST_X_ASSUM (ASSUME_TAC o (SPECL[`w2:real^3`;` w1:real^3`])) THEN
REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
REPEAT (FIRST_X_ASSUM CHOOSE_TAC) THEN
FIRST_ASSUM (NHANH_PAT `\x. _ ==> x `) THEN
STRIP_TAC THEN STRIP_TAC THEN UNDISCH_TAC `w1 - v =
(r2 * cos (psi + azim v w w2 w1)) % e1 +
(r2 * sin (psi + azim v w w2 w1)) % e2 +
h2' % (w - v)` THEN
UNDISCH_TAC `w1 - (v: real^3) = (r1' * cos psi') % e1 +
(r1' * sin psi') % e2 + h1 % (w - v)` THEN
USE_FIRST ` dist (w,v) % e3 = w - (v:real^3)` (SUBST1_TAC o SYM) THEN
UNDISCH_TAC `orthonormal e1 e2 (e3: real^3)` THEN PHA THEN
REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
NHANH (MESON[th]` orthonormal e1 e2 e3 /\ x = a1 % e1 + a2 % e2 + a3 % e3 /\
x = aa1 %e1 + aa2 % e2 + aa3 % e3 ==> a1 = aa1 /\ a2 = aa2 /\ a3 = aa3 `) THEN
STRIP_TAC THEN
UNDISCH_TAC` w2 - (v: real^3) = (r1 * cos psi) % e1 + (r1 * sin psi) % e2 + h1' % (w - v)` THEN
UNDISCH_TAC` w2 - v =
(r2' * cos (psi' + azim v w w1 w2)) % e1 +
(r2' * sin (psi' + azim v w w1 w2)) % e2 + h2 % (w - v)` THEN
UNDISCH_TAC `orthonormal e1 e2 (e3: real^3)` THEN
USE_FIRST ` dist (w,v) % e3 = w - (v:real^3)` (SUBST1_TAC o SYM) THEN
REWRITE_TAC[VECTOR_MUL_ASSOC] THEN PHA THEN
NHANH (MESON[th]` orthonormal e1 e2 e3 /\ x = a1 % e1 + a2 % e2 + a3 % e3 /\
x = aa1 %e1 + aa2 % e2 + aa3 % e3 ==> a1 = aa1 /\ a2 = aa2 /\ a3 = aa3 `) THEN STRIP_TAC THEN
UNDISCH_TAC`{w1, w2} INTER affine hull {(v: real^3), w} = {}` THEN
REWRITE_TAC[ GSYM aff; SET_RULE` {a,b} INTER s = {} <=> ~( a IN s ) /\ ~( b IN s ) `] THEN
UNDISCH_TAC `~(w = (v:real^3))` THEN
SIMP_TAC[EQ_SYM_EQ; NOT_EQ_IMP_AFF_AND_COLL3] THEN
STRIP_TAC THEN STRIP_TAC THEN
ASSUME_TAC2 (MESON[]`~collinear {v, w, w2} /\ (~collinear {(v:real^3), w, w2} ==> &0 < r1) ==>
&0 < r1 `) THEN
ASSUME_TAC2 (MESON[]`~collinear {v, w, w2} /\ (~collinear {(v:real^3), w, w2} ==> &0 < r2') ==>
&0 < r2' `) THEN
ASSUME_TAC2 (MESON[]`~collinear {v, w, w1} /\ (~collinear {(v:real^3), w, w1} ==> &0 < r1') ==>
&0 < r1' `) THEN
ASSUME_TAC2 (MESON[]`~collinear {v, w, w1} /\ (~collinear {(v:real^3), w, w1} ==> &0 < r2) ==>
&0 < r2 `) THEN
UNDISCH_TAC` r2' * sin (psi' + azim (v: real^3) w w1 w2) = r1 * sin psi` THEN
UNDISCH_TAC`r2' * cos (psi' + azim v w w1 w2) = r1 * cos psi` THEN
UNDISCH_TAC`&0 < r1` THEN UNDISCH_TAC`&0 < r2'` THEN PHA THEN
NHANH R_POS_SIN_COS_IDENT THEN
REWRITE_TAC[SIN_COS_IDEN_IFF_DIFFER_PERS ] THEN STRIP_TAC THEN
UNDISCH_TAC` r1' * sin psi' = r2 * sin (psi + azim v w w2 w1)` THEN
UNDISCH_TAC` r1' * cos psi' = r2 * cos (psi + azim v w w2 w1)` THEN
UNDISCH_TAC` &0 < r2 ` THEN UNDISCH_TAC` &0 < r1' ` THEN
PHA THEN NHANH R_POS_SIN_COS_IDENT THEN
REWRITE_TAC[SIN_COS_IDEN_IFF_DIFFER_PERS ] THEN STRIP_TAC THEN
CHOOSE_TAC (SPEC` psi: real` MOVE_TO_UNIT_INTERVAL ) THEN
CHOOSE_TAC (SPEC` psi': real` MOVE_TO_UNIT_INTERVAL ) THEN
SUBST_ALL_TAC (REWRITE_RULE[GSYM int_add_th;GSYM int_sub_th] (REAL_ARITH` psi' + azim v w w1 w2 = psi + real_of_int k * &2 * pi <=>
azim v w w1 w2 = ( psi + real_of_int n * &2 * pi) - ( psi' + real_of_int n' * &2 * pi)
+ (real_of_int k + real_of_int n' - real_of_int n )* &2 * pi `)) THEN
SUBST_ALL_TAC (REWRITE_RULE[GSYM int_add_th;GSYM int_sub_th] (REAL_ARITH` psi' = (psi + azim v w w2 w1) + real_of_int k' * &2 * pi <=>
azim v w w2 w1 = (psi' + real_of_int n' * &2 * pi) - (psi + real_of_int n * &2 * pi)
+ (real_of_int n - real_of_int k' - real_of_int n') * &2 * pi `)) THEN
ABBREV_TAC ` ppsssi = psi + real_of_int n * &2 * pi ` THEN
ABBREV_TAC ` ppsssi1 = psi' + real_of_int n' * &2 * pi ` THEN
REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
ASSUME_TAC2 (SPECL [` azim v w w1 w2 `;` k + n' - (n: int) `] (GEN `aa: real` BODE_YEU_ANH_DI)) THEN
REWRITE_TAC[MESON[]` a = b ==> b + c = &0 <=> a = b ==> a + c = &0`] THEN
FIRST_X_ASSUM SUBST1_TAC THEN
UNDISCH_TAC `azim v w w2 w1 = ppsssi1 - ppsssi + real_of_int (n - k' - n') * &2 * pi` THEN
UNDISCH_TAC `azim v w w1 w2 = ppsssi - ppsssi1 + real_of_int (k + n' - n) * &2 * pi` THEN
UNDISCH_TAC` azim v w w2 w1 < &2 * pi ` THEN
UNDISCH_TAC` &0 <= azim v w w2 w1 ` THEN UNDISCH_TAC` azim v w w1 w2 < &2 * pi ` THEN
UNDISCH_TAC` &0 <= azim v w w1 w2 ` THEN UNDISCH_TAC` ppsssi1 < &2 * pi ` THEN
UNDISCH_TAC`&0 <= ppsssi1 ` THEN UNDISCH_TAC` ppsssi < &2 * pi ` THEN
UNDISCH_TAC`&0 <= ppsssi ` THEN PHA THEN
REWRITE_TAC[REWRITE_RULE[REAL_ARITH` &2 * a * b = b * &2 * a `] PDPFQUK]);;


let QQZKTXU = prove(`! v w v1 (v2:real^3). let gammma = dihV v w v1 v2 in {v1,v2} INTER aff {v,w} = {} /\
~( v = w ) ==> cos ( azim v w v1 v2 ) = cos gammma `,
GEOM_ORIGIN_TAC `v:real^3` THEN
ONCE_REWRITE_TAC[SET_RULE`{a} = {a,a}`] THEN
REWRITE_TAC[IMAGE_INTER_AFF3] THEN
REWRITE_TAC[IMAGE_CLAUSES] THEN
REWRITE_TAC[IMAGE_CLAUSES; IMAGE_EQ_EMPTY; INSERT_INSERT] THEN
ONCE_REWRITE_TAC[SPEC ` -- v:real^N` (GSYM DIHV_TRASABLE)] THEN
REWRITE_TAC[VECTOR_ARITH` -- a + a + b = (b:real^N)`] THEN
REPEAT STRIP_TAC THEN
LET_TAC THEN
MP_TAC (SPECL [`(vec 0): real^3`;`w:real^3`; `v1:real^3`;`v2:real^3`] azim) THEN
REPEAT STRIP_TAC THEN
EXPAND_TAC "gammma" THEN
REWRITE_TAC[DIHV_FORMULAR; VECTOR_SUB_RZERO] THEN
REPLICATE_TAC 2 (FIRST_X_ASSUM MP_TAC) THEN PHA THEN
REWRITE_TAC[INSERT_INTER_EMPTY] THEN
DAO THEN NGOAC THEN
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
NHANH (MATCH_MP (MESON[]`(a /\ b ==> c) ==> ( a /\ ~ c ==> ~ b ) `)
PERPENCULAR_PART_IDENT0) THEN
NHANH (MATCH_MP (MESON[]` a dot b = &0 ==> ~( a = vec 0) ==> a dot b = &0`)
VECTOR_OF_DIHV_ORTHONORMAL) THEN
NHANH ORTHOGORNAL_UNITIZE THEN
REWRITE_TAC[NOT_VEC0_UNITABLE] THEN
ABBREV_TAC `e11 = &1 / norm ((w dot w) % v1 - (v1 dot w) % w) %
((w dot w) % v1 - (v1 dot w) % (w: real^3))` THEN
ABBREV_TAC ` e33 = &1 / norm w % (w:real^3)` THEN
STRIP_TAC THEN
UNDISCH_TAC `e11 dot (e33: real^3) = &0` THEN
UNDISCH_TAC` norm ( e33: real^3) = &1 ` THEN
UNDISCH_TAC` norm ( e11: real^3) = &1 ` THEN
PHA THEN
NHANH TWO_UNIT_ORTH_VECTORS_IMP_ORTHONORMAL THEN
EXPAND_TAC "e33" THEN
REWRITE_TAC[GSYM NOT_VEC0_UNITABLE] THEN
REWRITE_TAC[GSYM NOT_VEC0_UNITABLE; GSYM NORM_POS_LT] THEN
NHANH REAL_LT_IMP_NZ THEN
NHANH NOT_EQ0_IMP_NEITHER_INVERT THEN
ASM_REWRITE_TAC[] THEN
STRIP_TAC THEN
UNDISCH_TAC ` &1 / norm w % w = (e33:real^3)` THEN
UNDISCH_TAC ` ~(&1 / norm (w:real^3) = &0)` THEN
PHA THEN NHANH VECTOR_MUL_R_TO_L THEN
REWRITE_TAC[REAL_FIELD` &1 / ( &1 / a ) = a `; GSYM DIST_0] THEN
SUBST_ALL_TAC (MESON[NORM_POS_LT]` &0 < norm (w:real^3) <=> ~(w = vec 0)`) THEN
SIMP_TAC[DIST_SYM] THEN
REWRITE_TAC[VECTOR_ARITH` a = b % x <=> b % x = a - vec 0 `] THEN
STRIP_TAC THEN
UNDISCH_TAC `~((w:real^3) = vec 0)` THEN
FIRST_X_ASSUM MP_TAC THEN
UNDISCH_TAC ` orthonormal e11 e2 e33 ` THEN
PHA THEN FIRST_X_ASSUM NHANH THEN
STRIP_TAC THEN
UNDISCH_TAC ` ~(v1 IN aff {vec 0, (w:real^3)})` THEN
UNDISCH_TAC ` ~((w:real^3) = vec 0)` THEN
UNDISCH_TAC `~(v2 IN aff {vec 0, (w:real^3)})` THEN
ONCE_REWRITE_TAC[MESON[]` ~( a = b ) <=> ~( a = b ) /\ ~( a = b )`] THEN
PHA THEN
ONCE_REWRITE_TAC[TAUT` a /\ b/\ c/\ d <=> b /\ ( b /\ a ) /\c /\ d `] THEN
REWRITE_TAC[PROJECTOR_NOT_EQ_VEC0 ] THEN
REWRITE_TAC[VECTOR_ADD_RID; VECTOR_ARITH` ( a + b ) - a = (b:real^N)`] THEN
SIMP_TAC[NOT_EQ_IMPCOS_ARC; VECTOR_SUB_RZERO] THEN DOWN_TAC THEN
REWRITE_TAC[NOT_EQ_IMPCOS_ARC; VECTOR_SUB_RZERO] THEN
ABBREV_TAC ` azz = azim (vec 0) w v1 v2 ` THEN STRIP_TAC THEN
USE_FIRST `v2 =
(r2 * cos (psi + azz)) % e11 + (r2 * sin (psi + azz)) % e2 + h2 % (w:real^3)` SUBST1_TAC THEN
USE_FIRST `v1 = (r1 * cos psi) % e11 + (r1 * sin psi) % e2 + h1 % (w:real^3)` SUBST1_TAC THEN
UNDISCH_TAC ` orthonormal e11 e2 e33 ` THEN
SIMP_TAC[DOT_LADD; DOT_LMUL; orthonormal] THEN
ABBREV_TAC ` ww = w dot (w:real^3)` THEN
EXPAND_TAC "w" THEN
SIMP_TAC[DOT_SYM; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_LID; VECTOR_ADD_LDISTRIB] THEN
SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_SYM; VECTOR_ARITH`(a + c + b ) - b = (a:real^N) + c`] THEN
SIMP_TAC[vector_norm; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; REAL_MUL_RZERO; DOT_SYM;
REAL_ADD_RID; REAL_MUL_RID; REAL_ADD_LID; GSYM POW_2; REAL_ARITH`( a * b * c ) pow 2 + ( a * b
* d ) pow 2 = ( a * b ) pow 2 * ( d pow 2 + c pow 2 ) `; SIN_CIRCLE] THEN
STRIP_TAC THEN UNDISCH_TAC `~(ww % (v2: real^3) - (v2 dot w) % w = vec 0)` THEN
UNDISCH_TAC `~(ww % (v1: real^3) - (v1 dot w) % w = vec 0)` THEN
EXPAND_TAC "ww" THEN REWRITE_TAC[GSYM PROJECTOR_NOT_EQ_VEC0] THEN
NHANH (MATCH_MP (MESON[]` (a ==> ( b <=> c )) ==> (a /\ ~ b ==> ~ c) `) (SPEC_ALL NOT_EQ_VEC0_IMP_EQU_AFF_COLL)) THEN
FIRST_X_ASSUM NHANH THEN FIRST_X_ASSUM NHANH THEN
REWRITE_TAC[GSYM DOT_POS_LT] THEN STRIP_TAC THEN STRIP_TAC THEN
ASSUME_TAC2 (SPECL [`(w:real^3) dot w `;` r1: real `] REAL_LT_MUL) THEN
ASSUME_TAC2 (SPECL [`(w:real^3) dot w `;` r2: real `] REAL_LT_MUL) THEN
REPLICATE_TAC 2 (FIRST_X_ASSUM MP_TAC) THEN
NHANH REAL_LT_IMP_LE THEN PHA THEN SIMP_TAC[POW_2_SQRT] THEN
REWRITE_TAC[REAL_ARITH` ((w dot w) * r1 * a) * (w dot w) * r2 * b +
((w dot w) * r1 * c) * (w dot w) * r2 * d =
(((w dot w) * r1) * (w dot w) * r2) * (b * a + d * c) `] THEN
SIMP_TAC[REAL_FIELD` &0 < a /\ &0 < b ==> (( a * b ) * c ) / ( a * b ) = c `] THEN
REWRITE_TAC[GSYM COS_SUB; REAL_ARITH` (a + b ) - a = b`]);;


(*
("SIMPLIZE_COS_IF_OTHOR ",
|- !v0 v1 w p.
~(v0 = w) /\
~(v0 = v1) /\
p - v0 = k % (v1 - v0) /\
(w - p) dot (v1 - v0) = &0
==> cos (arcV v0 v1 w) = k * norm (v1 - v0) / norm (w - v0))]
*)
(* Lemma $100 promised with John *)
(* ============================= *)
(* ============================= *)

let real_itv = new_definition ` real_itv a b  = { x | a <= x /\ x < b } `;;
let tri_itv = new_definition ` tri_itv x <=> ( x IN real_itv ( &0 ) ( &2 * pi )) `;;

(*
parse_as_infix("regular_lt",(12,"right"));;

let regular_lt = new_definition
` (a:real) regular_lt (b:real) <=> a < b /\ a = &0 `;;

*)

parse_as_infix("polar_lt",(12,"right"));;


let polar_lt = new_definition 
`(a: real^2) polar_lt (b: real^2) <=>  
          (!ra aa rb ab.
              &0 < ra /\
              &0 < rb /\
              a = vector [ra * cos aa; ra * sin aa] /\
              b = vector [rb * cos ab; rb * sin ab] /\
              tri_itv aa /\
              tri_itv ab
              ==> aa < ab \/ aa = ab /\ ra < rb) `;;


parse_as_infix("polar_le",(12,"right"));;

let polar_le = new_definition 
` a polar_le b <=> a polar_lt b \/ a = b `;;


parse_as_infix("polar_cycle_on",(12,"right"));;

let polar_cycle_on = new_definition
` f polar_cycle_on (W: real^2 -> bool ) <=>
         (!x. x IN W ==> f x IN W) /\
         (!x. x IN W
             ==> x polar_lt f x /\
            (!y. y IN W ==> ~(x polar_lt y /\ y polar_lt f x)) \/
            (!y. y IN W ==> f x polar_le y /\ y polar_le x)) `;;

let pl_angle = new_definition` pl_angle (x: real^2) = 
 (@ u. tri_itv u /\ ( ?t. &0 < t /\ x = 
       vector [ t * cos u; t * sin u ])) `;;

let arg_diff = new_definition ` arg_diff a b = 
 let dd =  pl_angle b - pl_angle a in
 if a polar_le b then dd else dd + &2 * pi `;;

let VEC2_PRE_TRIG_FORM = prove(` ! (x:real^2). ~( x = vec 0) ==> ( x$1 / ( sqrt (x$1 * x$1 + x$2 * x$2))) pow 2 + 
  ( x$2 / ( sqrt (x$1 * x$1 + x$2 * x$2))) pow 2 = &1 `,
REWRITE_TAC[DIV_POW2; GSYM POW_2] THEN 
SIMP_TAC[GSYM NORM_EQ_0; vector_norm; DOT_2;GSYM POW_2; SUM_TWO_POW2S; SQRT_EQ_0; SQRT_POW_2]
THEN GEN_TAC THEN CONV_TAC REAL_FIELD);;


let PRE_TRIG_FORM_VEC2 = prove(`!(x: real^2). ~(x = vec 0)
     ==> (?u. tri_itv u /\  x = vector [( norm x ) * cos u ; ( norm x ) * sin u])`,
NHANH VEC2_PRE_TRIG_FORM  THEN 
REWRITE_TAC[GSYM NORM_POS_LT; vector_norm; DOT_2] THEN 
NHANH SUM_POW2_EQ1_UNIQUE_TRIG THEN 
REWRITE_TAC[EXISTS_UNIQUE] THEN 
GEN_TAC THEN STRIP_TAC THEN 
EXISTS_TAC `x': real` THEN 
SIMP_TAC[vector_norm; DOT_2;GSYM POW_2] THEN 
ASM_REWRITE_TAC[] THEN 
UNDISCH_TAC ` &0 < sqrt ((x:real^2)$1 * x$1 + x$2 * x$2)` THEN 
NHANH REAL_LT_IMP_NZ THEN 
SIMP_TAC[REAL_DIV_LMUL; POW_2] THEN 
REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; tri_itv; real_itv; IN_ELIM_THM] THEN 
ASM_REWRITE_TAC[]);;


let PL_ANGLE_PROPERTY = prove(`!(x: real^2). ~(x = vec 0)
     ==> tri_itv (pl_angle x) /\
  (? t. &0 < t /\ x = vector [ t * cos (pl_angle x); t * sin ( pl_angle x )])`,
NHANH PRE_TRIG_FORM_VEC2 THEN 
PAT_REWRITE_TAC `\x. !y. x ==> _ ` [GSYM NORM_POS_LT; RIGHT_AND_EXISTS_THM] THEN
NHANH (MESON[]`(?u. &0 < norm x /\ L u /\ P u ( norm x )) ==> (?u. 
  L u /\ (?t. &0 < t /\ P u t ))`) THEN 
REWRITE_TAC[pl_angle] THEN MESON_TAC[EXISTS_THM]);;

let POLAR_LT_IMP_NOT_EQ = 
prove(` ~( x = vec 0 ) /\ ~((y:real^2) = vec 0 ) ==>
 x polar_lt y ==> ~( x = y ) `,
STRIP_TAC THEN REWRITE_TAC[polar_lt] THEN
ONCE_REWRITE_TAC[TAUT` a ==> ~ b <=> b ==> ~ a `] THEN 
SIMP_TAC[ NOT_FORALL_THM] THEN 
ASSUME_TAC2 (SPEC `y: real^2 ` PRE_TRIG_FORM_VEC2) THEN 
FIRST_X_ASSUM CHOOSE_TAC THEN STRIP_TAC THEN 
REWRITE_TAC[TAUT` ~ ( a ==> b ) <=> a /\ ~ b `] THEN 
EXISTS_TAC `norm (y:real^2)` THEN EXISTS_TAC `u: real` THEN 
EXISTS_TAC `norm (y:real^2)` THEN EXISTS_TAC `u:real` THEN 
ASM_SIMP_TAC[NORM_POS_LT] THEN DOWN_TAC THEN STRIP_TAC THEN 
ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; 
REWRITE_TAC[REAL_LT_REFL]]);;

let CART2_EQ = prove(` vector [a1; a2] = (vector [b1; b2]): real^2 
<=> a1 = b1 /\ a2 = b2 `,
REWRITE_TAC[CART_EQ; DIMINDEX_2; ARITH_RULE` 1 <= x /\ x <= 2 <=>
x = 1 \/ x = 2 `; MESON[]`(! x. x = a \/ x = b ==> P x ) <=>
 P a /\ P b `; VECTOR_2]);;


let SE_ASM_TAC = FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC);;
let SE_ALL_TAC = REPEAT SE_ASM_TAC;;


let POLAR_LT_TRANS = prove(`~( x = vec 0 ) /\ 
 ~ ((y:real^2) = vec 0 ) /\ ~ ( z = vec 0 ) /\
 x polar_lt y /\ y polar_lt z ==> x polar_lt z `,
REWRITE_TAC[polar_lt] THEN NHANH PL_ANGLE_PROPERTY THEN 
STRIP_TAC THEN DOWN_TAC THEN REWRITE_TAC[polar_lt] THEN 
REPEAT STRIP_TAC THEN UNDISCH_TAC` tri_itv ab ` THEN 
UNDISCH_TAC` tri_itv ( pl_angle y ) ` THEN 
UNDISCH_TAC`(z:real^2) = vector [rb * cos ab; rb * sin ab]` THEN 
UNDISCH_TAC`(y:real^2) = vector [t' * cos (pl_angle y); t' * sin (pl_angle y)]` THEN 
UNDISCH_TAC` &0 < rb ` THEN UNDISCH_TAC` &0 < t' ` THEN 
PHA THEN FIRST_X_ASSUM NHANH THEN DISCH_TAC THEN 
REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
UNDISCH_TAC` tri_itv ( pl_angle y ) ` THEN 
UNDISCH_TAC `tri_itv aa ` THEN 
UNDISCH_TAC`(y:real^2) = vector [t' * cos (pl_angle y); t' * sin (pl_angle y)]` THEN 
UNDISCH_TAC`(x:real^2) = vector [ra * cos aa; ra * sin aa]` THEN 
UNDISCH_TAC` &0 < t' ` THEN UNDISCH_TAC` &0 < ra ` THEN 
PHA THEN FIRST_X_ASSUM NHANH THEN DISCH_TAC THEN SE_ALL_TAC
THEN ASSUME_TAC2 (
REAL_ARITH `(pl_angle y < ab \/ pl_angle y = ab /\ t' < rb ) /\
( aa < pl_angle y \/ aa = pl_angle y /\ ra < t' ) ==>
 aa < ab \/ aa = ab /\ ra < rb `) THEN FIRST_ASSUM ACCEPT_TAC);;



let EXISTS_MAX_ELEMENT = prove
 (`!S (lt:A->A->bool).
       FINITE S /\ ~(S = {}) /\
       (!x y z. lt x y /\ lt y z ==> lt x z) /\
       (!x. ~(lt x x)) /\
       (!x y. S x /\ S y /\ ~( x = y ) ==> lt x y \/ lt y x )
       ==> ?m:A. S m /\ ( ! x. S x ==> lt x m \/ x = m )`,
 REPEAT STRIP_TAC THEN
 MP_TAC(ISPEC `\x:A y:A. x IN S /\ y IN S /\ lt y x` WF_FINITE) THEN
 ASM_SIMP_TAC[FINITE_RESTRICT] THEN
 ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
 REWRITE_TAC[WF] THEN DISCH_THEN(MP_TAC o SPEC `S:A->bool`) THEN
 ASM SET_TAC[]);;


let NO_V0_IMP_NOT_SELF_POLLAR = MESON[POLAR_LT_IMP_NOT_EQ]
` ~ ( x = vec 0 ) ==> ~ ( x polar_lt  x ) `;;

let SET_TAC = let basicthms =
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
MESON_TAC ths ;;

(* =========== improved SET_RULE ============= *)
let SET_RULE a = fun x -> prove(x, SET_TAC a );;

let POLAR_CYCLIC_FUN_IMP_ALL_BELONG = 
prove(` W p /\ f polar_cycle_on W ==> ! n. ITER n f p IN W `,
REWRITE_TAC[polar_cycle_on] THEN STRIP_TAC THEN INDUCT_TAC THENL [REWRITE_TAC[ITER] THEN 
ASM SET_TAC[]; REWRITE_TAC[ITER] THEN ASM SET_TAC[]]);;

let EXISTS_MIN_IN_ORDERED_FINITE_SET = 
prove(`!(S: A -> bool) lt.
         FINITE S /\
         ~(S = {}) /\ (! x. lt x x ) /\
         (!x y z. lt x y /\ lt y z ==> lt x z) /\
         (! x y. lt x y /\ lt y x ==> x = y ) /\
         (!x y. lt x y \/ lt y x)
         ==> (?m. S m /\ (!x. S x ==> lt m x ))`,
REPEAT STRIP_TAC THEN MP_TAC (ISPEC`\(x : A ) ( y: A).
 S x /\ S y /\ lt x y /\ ~ ( x = y )` WF_FINITE) THEN 
ASM_SIMP_TAC[REWRITE_RULE[IN] FINITE_RESTRICT] THEN 
ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[WF]] THEN 
DISCH_THEN (MP_TAC o SPEC `S: A -> bool `) THEN 
ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN 
EXISTS_TAC `x: A` THEN ASM REWRITE_TAC[] THEN ASM_MESON_TAC[]);;


let EXISTS_MA_OR_FI_SET = BETA_RULE (SPECL[` S : A -> bool `;
`(\x y. (lt: A -> A ->  bool) y x ) `] EXISTS_MIN_IN_ORDERED_FINITE_SET);;
(* EXISTS_MA_OR_FI_SET
  |- FINITE S /\
     ~(S = {}) /\
     (!x. lt x x) /\
     (!x y z. lt y x /\ lt z y ==> lt z x) /\
     (!x y. lt y x /\ lt x y ==> x = y) /\
     (!x y. lt y x \/ lt x y)
     ==> (?m. S m /\ (!x. S x ==> lt x m)) *)


let tri_itv = let t1 = CONJ tri_itv real_itv in CONJ t1 IN_ELIM_THM;;

let DOWN = FIRST_X_ASSUM MP_TAC;;

let WHILE_POLAR_LT_IMP_ST = prove(` p0 polar_lt p  ==>
~ ( {y | ?N. y = ITER N f p0 /\
          (!n. 0 <= n /\ n < N ==> ITER n f p0 polar_lt y) /\
          y polar_lt p } = {} )`,
REWRITE_TAC[SET_RULE[]`~( x = {} ) <=> ? y. y IN x `; IN_ELIM_THM] THEN 
STRIP_TAC THEN EXISTS_TAC` p0: real^2` THEN EXISTS_TAC `0 ` THEN 
ASM_SIMP_TAC[ITER; ARITH_RULE`~( 0 <= a /\ a < 0 )`]);;


let DOT_ITSELF_2 = prove( ` (x:real^2) = vector[ a; b ]
 ==> x dot x = a pow 2 + b pow 2 `,
SIMP_TAC[dot; DIMINDEX_2; SUM_2; VECTOR_2] THEN 
DISCH_TAC THEN REAL_ARITH_TAC);;


let NORM_VECTOR2_TRIG = 
prove(` (x:real^2) = vector [a * cos t ; a * sin t ]
/\ &0 <= a ==> norm x = a `, STRIP_TAC THEN UNDISCH_TAC ` &0 <= a `
THEN SIMP_TAC[NORM_POS_LE; EQ_POW2_COND; NORM_POW_2] THEN 
DOWN_TAC THEN NHANH DOT_ITSELF_2 THEN STRIP_TAC THEN 
DOWN THEN DOWN THEN PHA THEN SIMP_TAC[] THEN 
DISCH_TAC THEN REWRITE_TAC[R_SIN_CIRCLE]);;


let NOT_EQ_IMP_TOTAL_ORDER = prove(
` ! x y. ~( x = y ) ==> x polar_lt y \/ y polar_lt
x `, REWRITE_TAC[polar_lt] THEN REPEAT STRIP_TAC THEN 
ASM_CASES_TAC `(x:real^2) = vec 0 \/ (y:real^2)
= vec 0 ` THENL [ DISJ1_TAC THEN REPEAT GEN_TAC THEN 
NHANH REAL_LT_IMP_LE THEN NHANH (
MESON[NORM_VECTOR2_TRIG]`(aaa /\ &0 <= ra) /\
 (ac/\ &0 <= rb) /\
 (x:real^2) = vector [ra * cos aa; ra * sin aa] /\
 (y:real^2) = vector [rb * cos ab; rb * sin ab]/\ gg
==> norm x = ra /\ norm y = rb `) THEN DOWN THEN 
REWRITE_TAC[GSYM NORM_EQ_0] THEN SIMP_TAC[] THEN 
MESON_TAC[REAL_ARITH`~( a = &0 /\ &0 < a ) `]; ALL_TAC]
THEN DOWN THEN REWRITE_TAC[DE_MORGAN_THM] THEN 
NHANH PRE_TRIG_FORM_VEC2 THEN STRIP_TAC THEN 
DOWN_TAC THEN REWRITE_TAC[GSYM polar_lt] THEN 
MP_TAC (REAL_ARITH` u < u' \/ u = u' \/ u' < u `) THEN 
SPEC_TAC (`u:real`,`u:real`) THEN
SPEC_TAC (`u':real`,`u':real`) THEN 
SPEC_TAC (`x:real^2`,`x:real^2`) THEN 
SPEC_TAC (`y:real^2`,`y:real^2`) THEN 
MATCH_MP_TAC (
MESON[]`(! y x u' u. P1 u u' /\ M x y u u' ==>
Q x y ) /\ ((! y x u' u. P1 u u' /\ M x y u u' ==>
Q x y ) ==> (! y x u' u. P1 u' u /\ M x y u u' ==>
Q y x )) /\ (! y x u' u. u = u' /\ M x y u u' ==>
Q x y \/ Q y x) ==> (! y x u' u.
P1 u u' \/ u = u' \/ P1 u' u ==>
M x y u u' ==> Q x y \/ Q y x ) `) THEN CONJ_TAC
THENL [REPEAT STRIP_TAC THEN UNDISCH_TAC ` u < (u':real)`
THEN DISCH_TAC THEN REWRITE_TAC[polar_lt] THEN REPEAT STRIP_TAC THEN DISJ1_TAC THEN 
UNDISCH_TAC`(x:real^2) = vector [norm x * cos u; norm x * sin u]` THEN 
UNDISCH_TAC` (y:real^2) = vector [norm y * cos u'
; norm y * sin u' ]` THEN 
EVERY_ASSUM (fun x -> PAT_REWRITE_TAC `\v. v = h ==> v = h ==> gg `
[x ]) THEN REWRITE_TAC[CART2_EQ] THEN 
REPEAT DISCH_TAC THEN 
ASSUME_TAC2 (REAL_ARITH` &0 < ra /\ &0 < rb ==>
&0 <= ra /\ &0 <= rb `) THEN SE_ALL_TAC THEN 
UNDISCH_TAC ` &0 <= ra ` THEN UNDISCH_TAC `(x:real^2) = vector 
[ra * cos aa; ra * sin aa]` THEN 
PHA THEN NHANH NORM_VECTOR2_TRIG THEN STRIP_TAC THEN 
FIRST_X_ASSUM SUBST_ALL_TAC THEN UNDISCH_TAC ` &0 <= rb `
THEN UNDISCH_TAC `(y:real^2) = vector 
[rb * cos ab; rb * sin ab]` THEN PHA THEN 
NHANH NORM_VECTOR2_TRIG THEN STRIP_TAC THEN 
FIRST_X_ASSUM SUBST_ALL_TAC THEN 
REPLICATE_TAC 8 DOWN THEN PHA THEN 
ASM_SIMP_TAC[MESON[REAL_ARITH` &0 < a ==> ~( a = &0 )`; REAL_EQ_MUL_LCANCEL]`
&0 < a ==> ( a * x = a * y <=> x = y ) `] THEN 
UNDISCH_TAC` tri_itv aa ` THEN UNDISCH_TAC ` tri_itv u ` THEN 
UNDISCH_TAC`tri_itv u'` THEN UNDISCH_TAC` tri_itv ab` THEN 
REWRITE_TAC[tri_itv; real_itv; IN_ELIM_THM] THEN 
REPEAT STRIP_TAC THEN SUBGOAL_THEN` aa = (u: real) /\ ab = (u': real)` ASSUME_TAC
THENL [ASM_MESON_TAC[IDENT_WHEN_IDENT_SIN_COS];
ASM_REWRITE_TAC[]]; 
CONJ_TAC THENL [MESON_TAC[]; REPEAT GEN_TAC]] THEN 
IMP_TAC THEN DISCH_THEN ( fun x -> REWRITE_TAC[ SYM x ]) THEN 
ASM_CASES_TAC ` norm (x:real^2) = norm (y:real^2)` 
THENL [ASM_REWRITE_TAC[] THEN MESON_TAC[]; DOWN] THEN 
REWRITE_TAC[REAL_ARITH` ~( a = b ) <=> a < b \/ 
b < a `] THEN SPEC_TAC (`x:real^2`,`x:real^2`) THEN 
SPEC_TAC (`y:real^2`,`y:real^2`) THEN 
MATCH_MP_TAC (MESON[]`(! x y. P x y /\ R x y ==> Q x y ) /\
((! x y. P x y /\ R x y ==> Q x y ) ==>
(! x y. P y x /\ R x y ==> Q y x ) ) ==>
(! x y. P x y \/ P y x ==> R x y ==> Q x y \/ Q y x)`) THEN 
CONJ_TAC THENL [
REPEAT STRIP_TAC THEN REWRITE_TAC[polar_lt] THEN 
REPEAT GEN_TAC THEN NHANH_PAT `\x. x ==> h ` REAL_LT_IMP_LE THEN 
DISCH_TAC THEN SUBGOAL_THEN `norm (y':real^2) = ra /\ 
norm (y:real^2) = rb ` ASSUME_TAC THENL [
FIRST_X_ASSUM ( fun x -> MESON_TAC[x; NORM_VECTOR2_TRIG])
; REPEAT STRIP_TAC] THEN DISJ2_TAC THEN 
UNDISCH_TAC `(y': real^2) = 
vector [norm y' * cos u; norm y' * sin u]` THEN 
UNDISCH_TAC `(y: real^2) = 
vector [norm y * cos u; norm y * sin u]` THEN 
EVERY_ASSUM (fun x -> PAT_REWRITE_TAC `\x.
x = y ==> x = z ==> l ` [x]) THEN 
REWRITE_TAC[CART2_EQ] THEN DOWN_TAC THEN 
SIMP_TAC[GSYM NORM_POS_LT] THEN STRIP_TAC THEN 
SUBGOAL_THEN ` ab = (u:real) /\ aa = u ` ASSUME_TAC
THENL [REPLICATE_TAC  4 DOWN THEN PHA THEN ASM_REWRITE_TAC[] THEN 
ASM_SIMP_TAC[MESON[REAL_EQ_MUL_LCANCEL; REAL_ARITH` &0 < a ==>
~ ( a = &0 )`]` &0 < a ==> ( a * x = a * y <=> x = y ) `] THEN 
UNDISCH_TAC` tri_itv aa ` THEN UNDISCH_TAC ` tri_itv ab ` THEN 
UNDISCH_TAC `tri_itv u ` THEN PHA THEN REWRITE_TAC[tri_itv] THEN 
MESON_TAC[IDENT_WHEN_IDENT_SIN_COS];
ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
MESON_TAC[]]);;




let PROVE_XISTS_MAX_ELEMENT_LT_P = prove(
` ! W:real^2 -> bool. (! x. W x ==> ~ ( x = vec 0 )) /\
   FINITE W /\
   W p0 /\ 
   f polar_cycle_on W /\ 
   p0 polar_lt p /\
   SS = { y | ? N. y = ITER N f p0 /\
                ( ! n . 0 <= n /\ n <  N ==> ITER n f p0 polar_lt y ) /\
                y polar_lt p }
==> (? mx. mx IN SS /\ ( ! x. SS x ==> x polar_lt mx \/ x = mx)) `,
ONCE_REWRITE_TAC[TAUT`aa /\ a /\ b /\ c /\ d <=> aa /\ 
a /\ (b /\ c ) /\ d `] THEN 
NHANH POLAR_CYCLIC_FUN_IMP_ALL_BELONG THEN REPEAT STRIP_TAC THEN 
FIRST_X_ASSUM MP_TAC THEN 
SUBGOAL_THEN `(! y n. y = ITER n f p0 ==> W (y:real^2))` ASSUME_TAC
THENL [ASM SET_TAC[]; FIRST_ASSUM NHANH] THEN 
REWRITE_TAC[TAUT`( a /\ b) /\ c <=> b /\ a /\ c`; RIGHT_EXISTS_AND_THM] THEN 
DOWN_TAC THEN NHANH (REWRITE_RULE[IN; RIGHT_FORALL_IMP_THM] FINITE_RESTRICT) THEN 
STRIP_TAC THEN SUBGOAL_THEN ` FINITE (SS: real^2 -> bool) ` ASSUME_TAC THENL 
[ASM_MESON_TAC[]; ALL_TAC] THEN 
DOWN_TAC THEN REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM] THEN
PAT_REWRITE_TAC `\x. y /\ x ==> h ` [TAUT` a ==> b <=> a <=> 
b /\ a `] THEN 
NHANH (SET_RULE[]` S = {y | ? N. P y /\ Q N y } ==> S SUBSET P `) THEN 
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN 
REPLICATE_TAC 8 (IMP_TAC THEN STRIP_TAC) THEN NGOAC THEN 
ASM_REWRITE_TAC[] THEN PHA THEN 
DOWN THEN REWRITE_TAC[TAUT`(b /\ a <=> a) <=> a ==> b `] THEN 
ASSUME_TAC2 WHILE_POLAR_LT_IMP_ST THEN 
ABBREV_TAC ` lt x y = ( ( W x /\ W y ) /\ x polar_lt (y:real^2)) `
THEN SUBGOAL_THEN `(! x. ~ lt x (x:real^2) )` ASSUME_TAC THENL 
[FIRST_X_ASSUM ( fun x -> REWRITE_TAC [ GSYM x; 
NO_V0_IMP_NOT_SELF_POLLAR]) THEN REWRITE_TAC[DE_MORGAN_THM]
THEN GEN_TAC THEN ASM_CASES_TAC` (W: real^2 -> bool ) x ` THENL
[DISJ2_TAC THEN ASM MESON_TAC[NO_V0_IMP_NOT_SELF_POLLAR];
ASM_REWRITE_TAC[]];
SUBGOAL_THEN `(!x y z. lt (x:real^2) (y: real^2) /\ lt y z ==> lt x z)` ASSUME_TAC
THEN DOWN] THENL [
FIRST_X_ASSUM (fun x -> REWRITE_TAC[GSYM x ]) THEN 
REPLICATE_TAC 5 STRIP_TAC THEN ASM_REWRITE_TAC[POLAR_LT_TRANS]
THEN DOWN_TAC THEN MESON_TAC[POLAR_LT_TRANS];
REWRITE_TAC[TAUT`(a <=> b /\ a ) <=> a ==> b`] THEN 
REPEAT STRIP_TAC THEN 
UNDISCH_TAC ` ~({y | ?N. y = ITER N f p0 /\
                 (!n. 0 <= n ==> n < N ==> ITER n f p0 polar_lt y) /\
                 y polar_lt p} =
        {})`] THEN REWRITE_TAC[IMP_IMP] THEN DOWN THEN DOWN THEN
FIRST_ASSUM SUBST1_TAC THEN REPEAT STRIP_TAC THEN 
SUBGOAL_THEN `(!x y. (SS:real ^2 -> bool) x /\ SS y /\ ~(x = y) ==> 
lt x y \/ lt y x)` ASSUME_TAC THENL [
USE_FIRST `!x y. ((W:real^2 -> bool) x /\ W y) 
/\ x polar_lt y <=> lt x y` (fun x -> REWRITE_TAC[
GSYM x ]) THEN UNDISCH_TAC` SS SUBSET (W: real^2 -> bool)` THEN 
SET_TAC[NOT_EQ_IMP_TOTAL_ORDER];
SUBGOAL_THEN `(?m. (SS:real^2 -> bool) m /\ 
(!x. SS x ==> lt x m \/ x = m)) ` ASSUME_TAC THENL
[FIRST_X_ASSUM MP_TAC THEN 
UNDISCH_TAC` ! (x:real^2). ~ lt x x ` THEN 
UNDISCH_TAC ` (!(x:real^2) y z. lt x y /\ 
lt y z ==> lt x z) ` THEN 
UNDISCH_TAC `~ ( (SS: real^2 -> bool ) = {})` THEN 
UNDISCH_TAC `FINITE (SS: real^2 -> bool)` THEN 
PHA THEN REWRITE_TAC[EXISTS_MAX_ELEMENT];
REWRITE_TAC[IN] THEN FIRST_X_ASSUM CHOOSE_TAC THEN 
EXISTS_TAC `m: real^2` THEN ASM SET_TAC[]]]);;



let VEC0_BOTH_LT_GT = prove(`
 y = vec 0 ==>  x polar_lt y /\ y polar_lt z `,
REWRITE_TAC[polar_lt] THEN DISCH_TAC THEN 
SUBGOAL_THEN `(! ry ay. ~ (&0 < ry /\ (y:real^2) =
 vector[ ry * cos ay ; ry * sin ay ]))` ( fun x ->
ASM_MESON_TAC[x]) THEN NHANH REAL_LT_IMP_LE THEN 
REPEAT STRIP_TAC THEN ASSUME_TAC2 (SPECL [` ay: real `
;` y: real^2`;` ry: real`] (GEN_ALL NORM_VECTOR2_TRIG))
  THEN DOWN_TAC THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN 
MESON_TAC[REAL_ARITH` ~( &0 < y /\ y = &0 )`]);;



let POLAR_LT_TRANS = prove(` ~( y = vec 0 ) ==>
 x polar_lt y /\ y polar_lt z ==> x polar_lt z `,
MESON_TAC[POLAR_LT_TRANS; VEC0_BOTH_LT_GT]);;



let PROVE_EXISTING_MAX_IN_CYCLIC_FINITE_SET =
prove(` ! (W: real^2 -> bool). FINITE W /\ ~( W = {} ) /\ 
(! x. W x ==> ~( x = vec 0 )) ==>
? m. W m /\ (! x. W x ==> x polar_lt m \/ x = m ) `,
REPEAT STRIP_TAC THEN 
ABBREV_TAC ` lt x y = ( W x /\ W y /\ x polar_lt y ) ` THEN 
SUBGOAL_THEN `! x. ~ lt x (x:real^2) ` ASSUME_TAC THENL [
FIRST_X_ASSUM (fun s -> REWRITE_TAC[GSYM s]) THEN 
GEN_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN 
ASM_CASES_TAC ` (W: real^2 -> bool) (x:real^2)` THENL [
DISJ2_TAC THEN DISJ2_TAC THEN 
ASM_MESON_TAC[NO_V0_IMP_NOT_SELF_POLLAR]; ASM_SIMP_TAC[]];
SUBGOAL_THEN `(! x y z. ( lt: real^2 -> real^2 -> bool) x y
/\ lt y z ==> lt x z) /\ (! x y. W x /\ W y /\ ~ ( x = y )
==> lt x y \/ lt y x ) ` ASSUME_TAC] THENL [
DOWN THEN FIRST_X_ASSUM ( fun x -> REWRITE_TAC[GSYM x])
THEN SIMP_TAC[] THEN 
DISCH_TAC THEN CONJ_TAC THENL [FIRST_X_ASSUM NHANH THEN 
REPEAT STRIP_TAC THEN ASM_MESON_TAC[POLAR_LT_TRANS];
SIMP_TAC[NOT_EQ_IMP_TOTAL_ORDER]];
MP_TAC (ISPECL[`W:real^2 -> bool `;` lt: real^2 -> 
real^2 -> bool `] EXISTS_MAX_ELEMENT) THEN ANTS_TAC THENL
[ASM_REWRITE_TAC[]; USE_FIRST `!x y. (W:real^2 -> bool) x /\ W y /\ 
x polar_lt y <=> lt x y` (fun x -> REWRITE_TAC[ GSYM x]) THEN
MESON_TAC[]]]);;



let PROVE_MIN_ELEMENT_IN_FINITE_CYCLIC_SET =
prove(` ! (W: real^2 -> bool). FINITE W /\ ~( W = {}) /\ 
(! x. W x ==> ~ ( x = vec 0)) ==>
 ? n. W n /\ (! x. W x ==> n polar_lt x \/ n = x ) `,
REPEAT STRIP_TAC THEN 
MP_TAC (BETA_RULE (ISPECL [`W:real^2 -> bool `;` (\x y. W x /\ 
W y /\ y polar_lt x ) `]  EXISTS_MAX_ELEMENT)) THEN ANTS_TAC
THENL [ASM_MESON_TAC[POLAR_LT_TRANS; NO_V0_IMP_NOT_SELF_POLLAR
; NOT_EQ_IMP_TOTAL_ORDER]; MESON_TAC[]]);;







let TOW_NON_VEC0_IMP_NOT_REFL_POLAR_LT = 
prove(` ~((x:real^2) = vec 0 ) /\ ~( y = vec 0 ) ==> 
~( x polar_lt y /\ y polar_lt x ) `,
MESON_TAC[NO_V0_IMP_NOT_SELF_POLLAR; POLAR_LT_TRANS]);;




let EXISTS_STEPS_FOR_FOLLOWING_POINTS = prove(
 ` ! W:real^2 -> bool. (! x. W x ==> ~ ( x = vec 0 )) /\
   FINITE W /\
   W p0 /\ 
   f polar_cycle_on W /\ 
   p0 polar_lt p /\ W p 
==> ? n. ITER n f p0 = p /\ (! nn. nn < n ==> ITER nn f p0
polar_lt p ) `, REPEAT STRIP_TAC THEN 
ABBREV_TAC ` SS = { y| ?N. (y:real^2) = ITER N f p0 /\
       (! n. 0 <= n /\ n < N ==> ITER n f p0 polar_lt y ) /\
      y polar_lt p} ` THEN MP_TAC (SPEC_ALL PROVE_XISTS_MAX_ELEMENT_LT_P)
THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN 
UNDISCH_TAC `mx IN (SS: real^2 -> bool)` THEN 
EXPAND_TAC "SS" THEN REWRITE_TAC[IN_ELIM_THM] THEN 
STRIP_TAC THEN EXISTS_TAC ` N + 1` THEN 
REWRITE_TAC[ARITH_RULE` n < b + 1 <=> n < b \/ n = b `;
MESON[]`(! x. P x \/ x = a ==> Q x ) <=> Q a /\ (! x. 
P x ==> Q x )`] THEN REPLICATE_TAC 3 DOWN THEN PHA THEN 
SIMP_TAC[ARITH_RULE` 0 <= n`] THEN 
ASSUME_TAC2 ( SPEC `p0: real^2 ` ( GEN `p: real ^2 ` 
POLAR_CYCLIC_FUN_IMP_ALL_BELONG)) THEN 
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN SIMP_TAC[] THEN DISCH_TAC
 THEN SUBGOAL_THEN `~ (mx:real^2 = vec 0) ` ASSUME_TAC
THENL [ASM SET_TAC[]; CONJ_TAC] THENL [ALL_TAC ;
ASM_MESON_TAC[POLAR_LT_TRANS]] THEN 
ASM_CASES_TAC ` p polar_lt ( ITER ( N + 1) f p0 ) \/
p = ITER (N + 1) (f:real^2 -> real^2) p0` THEN 
UNDISCH_TAC `f polar_cycle_on W ` THEN REWRITE_TAC[polar_cycle_on]
THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC ` mx:real^2`)
THEN SUBGOAL_THEN ` mx IN (W: real^2 -> bool)` ASSUME_TAC
THENL [ASM_MESON_TAC[];
ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; STRIP_TAC] THENL
[FIRST_X_ASSUM DISJ_CASES_TAC THEN DOWN_TAC THEN 
REWRITE_TAC[GSYM ADD1; ITER] THEN SET_TAC[];
DOWN_TAC THEN REWRITE_TAC[GSYM ADD1; ITER] THEN 
STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN 
SUBGOAL_THEN ` ~((p:real^2) = vec 0 ) ` ASSUME_TAC THENL
[ASM_MESON_TAC[]; SUBGOAL_THEN ` mx polar_lt f mx ` ASSUME_TAC]
THENL [ASM_MESON_TAC[POLAR_LT_TRANS]; 
DOWN_TAC THEN REWRITE_TAC[polar_le] THEN 
SET_TAC[TOW_NON_VEC0_IMP_NOT_REFL_POLAR_LT; 
POLAR_LT_TRANS]]]; ASM_MESON_TAC[];
ANTS_TAC] THENL [FIRST_X_ASSUM ACCEPT_TAC;
DISCH_TAC THEN SE_ALL_TAC THEN 
SUBGOAL_THEN ` ITER (N + 1) (f:real^2 -> real^2) p0 
polar_lt p ` ASSUME_TAC THENL [
SET_TAC[TOW_NON_VEC0_IMP_NOT_REFL_POLAR_LT; 
NOT_EQ_IMP_TOTAL_ORDER; IN]; 
SUBGOAL_THEN ` ITER (N + 1) (f:real^2 -> real^2) p0
IN SS` ASSUME_TAC]] THENL [
SUBGOAL_THEN ` mx polar_lt (f:real^2 -> real^2) mx `
ASSUME_TAC THENL [
FIRST_X_ASSUM DISJ_CASES_TAC THENL [ASM_SIMP_TAC[];
DOWN_TAC] THEN REWRITE_TAC[GSYM ADD1; ITER; polar_le] THEN 
SET_TAC[TOW_NON_VEC0_IMP_NOT_REFL_POLAR_LT];
EXPAND_TAC "SS" THEN REWRITE_TAC[IN_ELIM_THM] THEN 
EXISTS_TAC `N + 1 ` THEN DOWN_TAC THEN REWRITE_TAC[GSYM ADD1; ITER]
THEN STRIP_TAC THEN ASM_REWRITE_TAC[LE_0; LT]] THENL [
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
ASM SET_TAC[POLAR_LT_TRANS]; ASM SET_TAC[POLAR_LT_TRANS]];
SUBGOAL_THEN ` mx polar_lt (f:real^2 -> real^2) mx `
ASSUME_TAC THENL [FIRST_X_ASSUM DISJ_CASES_TAC THENL [ASM_SIMP_TAC[];
DOWN_TAC] THEN REWRITE_TAC[GSYM ADD1; ITER; polar_le] THEN 
SET_TAC[TOW_NON_VEC0_IMP_NOT_REFL_POLAR_LT];
DOWN_TAC THEN REWRITE_TAC[GSYM ADD1; ITER] THEN 
SET_TAC[TOW_NON_VEC0_IMP_NOT_REFL_POLAR_LT]]]);;



let CARD_SING = prove(`! (x:A). CARD {x} = 1 `,
MP_TAC CARD_CLAUSES THEN STRIP_TAC THEN 
GEN_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o SPECL [` x: A `; ` {} : A -> bool `])
THEN SUBGOAL_THEN `FINITE ({} : A -> bool ) ` MP_TAC THENL
[ REWRITE_TAC[FINITE_EMPTY]; FIRST_X_ASSUM NHANH] THEN 
ASM_SIMP_TAC[NOT_IN_EMPTY; ADD1; ADD_CLAUSES]);;





let POLAR_LE_REFL_EQ = prove(` a polar_le b /\ b polar_le a 
<=> a = b \/ a = vec 0 \/ b = vec 0 `, 
REWRITE_TAC[polar_le] THEN 
MESON_TAC[VEC0_BOTH_LT_GT; POLAR_LT_TRANS;
TOW_NON_VEC0_IMP_NOT_REFL_POLAR_LT]);;


let CHANGE ne ol = fun x ->  SPEC ne ( GEN ol x);;


let POLAR_MONOPOLY_IN_FIRST_ITERVAL =
prove(` (!x. W x ==> ~(x = vec 0)) /\
         FINITE W /\
         W p0 /\
         f polar_cycle_on W /\
    (!x. W x ==> p0 polar_le x ) /\
 i < CARD W - 1 ==>
ITER i f p0 polar_lt f (ITER i f p0) `,
ABBREV_TAC ` xx = ITER i f (p0: real^2) ` THEN STRIP_TAC
THEN SUBGOAL_THEN ` (xx: real^2) IN W ` ASSUME_TAC THENL [
ASM_MESON_TAC[POLAR_CYCLIC_FUN_IMP_ALL_BELONG]; 
DOWN THEN USE_FIRST ` f polar_cycle_on W ` MP_TAC] THEN 
REWRITE_TAC[polar_cycle_on] THEN STRIP_TAC THEN 
FIRST_X_ASSUM NHANH THEN STRIP_TAC THEN 
SUBGOAL_THEN ` FINITE {y | ? ii. ii <= i /\ y = ITER ii
f (p0: real^2)} ` ASSUME_TAC THENL [
SPEC_TAC (`i: num`,`i: num `) THEN INDUCT_TAC THENL [
REWRITE_TAC[LE; MESON[]`(?a. a = b /\ P a) <=> P b`; ITER
; SET_RULE[]` {x| x = a} = {a} `] THEN SIMP_TAC[FINITE_RULES];
REWRITE_TAC[ADD1; ARITH_RULE` a <= c + 1 <=> a <= c \/
a = c + 1 `; SET_RULE[]` {y| ? x. ( P x \/ x = a ) /\ y =  Q x } =
Q a INSERT {y | ? x. P x /\ y = Q x } `] THEN 
ASM_SIMP_TAC[FINITE_RULES]];
ABBREV_TAC ` SS = {y | ?ii. ii <= i /\ y = ITER ii f (p0:real^2)}
`] THEN SUBGOAL_THEN ` W SUBSET (SS:real^2 -> bool)` ASSUME_TAC
THENL [REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN 
ASM_CASES_TAC ` p0 = (x:real^2)` THENL [
EXPAND_TAC "x" THEN EXPAND_TAC "SS" THEN REWRITE_TAC[IN_ELIM_THM]
THEN EXISTS_TAC `0` THEN REWRITE_TAC[LE_0; ITER];
ALL_TAC] THEN 
SUBGOAL_THEN`p0 polar_lt x ` ASSUME_TAC THENL [DOWN_TAC
THEN REWRITE_TAC[polar_le] THEN SET_TAC[]; ALL_TAC] THEN 
MP_TAC (SPEC_ALL (CHANGE `x: real^2 ` `p:real^2 ` 
EXISTS_STEPS_FOR_FOLLOWING_POINTS)) THEN ANTS_TAC THENL [
ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM IN] THEN 
ASM_SIMP_TAC[]; STRIP_TAC] THEN
ASM_CASES_TAC ` n <= (i:num) ` THENL [EXPAND_TAC "SS"
THEN EXPAND_TAC "x" THEN REWRITE_TAC[IN_ELIM_THM] THEN 
EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]; DOWN] THEN 
REWRITE_TAC[ARITH_RULE` ~( s <= h ) <=> (h:num) < s `] THEN 
FIRST_ASSUM NHANH THEN 
SUBGOAL_THEN ` x polar_le xx ` ASSUME_TAC THENL [
ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN DOWN THEN
REWRITE_TAC[polar_le] THEN  
ASM SET_TAC[NO_V0_IMP_NOT_SELF_POLLAR;
TOW_NON_VEC0_IMP_NOT_REFL_POLAR_LT]; SUBGOAL_THEN ` CARD (W:real^2 -> bool) <= CARD (SS: real^2
-> bool)` ASSUME_TAC THENL [ASM_MESON_TAC[CARD_SUBSET];
SUBGOAL_THEN ` CARD (SS: real^2 -> bool) <= i + 1 `
ASSUME_TAC]] THENL [UNDISCH_TAC `FINITE (SS:real^2 -> bool)` THEN 
EXPAND_TAC "SS" THEN SPEC_TAC (`i:num`,`i:num`) THEN 
INDUCT_TAC THENL [REWRITE_TAC[LE; SET_RULE[]` {y| ?x. x = 0 /\ y = P x }
= {P 0}`; ITER; CARD_SING; ADD; LE_REFL];
PAT_REWRITE_TAC `\a. b ==> a <= c ` [ADD1; ARITH_RULE ` a <= b + 1
 <=> a <= b \/ a = b + 1 `] THEN PAT_REWRITE_TAC `\x. x ==> h ` [ADD1;
ARITH_RULE ` a <= b + 1 <=> a <= b \/ a = b + 1 `] THEN 
REWRITE_TAC[ADD1; SET_RULE[]` {y| ? x. (P x \/ x = a ) /\ y = Q x } =
Q a INSERT {y| ?x. P x /\ y = Q x } `; FINITE_INSERT] THEN 
FIRST_X_ASSUM NHANH THEN 
NHANH (let [a;b] = CONJUNCTS CARD_CLAUSES in 
ISPEC ` ITER (i' + 1) f (p0: real^2) ` b) THEN 
COND_CASES_TAC THENL [STRIP_TAC THEN ASM_REWRITE_TAC[]
THEN DOWN THEN CONV_TAC ARITH_RULE; STRIP_TAC THEN 
ASM_REWRITE_TAC[] THEN DOWN THEN ARITH_TAC THEN ASM_MESON_TAC[
ARITH_RULE` i < CW - 1 /\ CW <= CS ==> ~( CS <= i + 1) `
]]]; ASM_MESON_TAC[
ARITH_RULE` i < CW - 1 /\ CW <= CS ==> ~( CS <= i + 1) `]]);;




let TRANS_SUC_IMP_INCREASE = prove(`! f. (! x y z. f x y /\ f y z ==> f x z ) /\
(! i. f i ( i + 1 )) ==>
(! i j. i < j ==> f i j ) `,
GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN INDUCT_TAC
THENL [REWRITE_TAC[LT; ARITH_RULE` i < SUC j <=> i < j \/ j = i `];
REWRITE_TAC[ARITH_RULE` i < SUC j <=> i < j \/ i = j `] THEN
ASM_MESON_TAC[ADD1]]);;




let MONOPOLY_IN_FIRST_PERIOD = prove(
` (!x. W x ==> ~(x = vec 0)) /\
         FINITE W /\
         W p0 /\
         f polar_cycle_on W /\
    (!x. W x ==> p0 polar_le x ) 
==> (! i j. i < j /\ j < CARD W ==> 
ITER i f p0 polar_lt ITER j f p0 ) `,
STRIP_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [
REWRITE_TAC[LT]; REWRITE_TAC[LT]] THEN STRIP_TAC THENL
[ASM_REWRITE_TAC[ITER] THEN 
MATCH_MP_TAC POLAR_MONOPOLY_IN_FIRST_ITERVAL THEN 
ASM_REWRITE_TAC[ARITH_RULE` a < b - 1 <=> a + 1 < b `;
GSYM ADD1]; 
UNDISCH_TAC `i < j /\ j < CARD (W:real^2 -> bool) ==> 
ITER i f p0 polar_lt ITER j f p0` THEN ANTS_TAC THENL [
ASM_ARITH_TAC; DISCH_TAC]] THEN MP_TAC (
CHANGE `j:num ` `i:num` POLAR_MONOPOLY_IN_FIRST_ITERVAL)
THEN ANTS_TAC THENL [
ASM_REWRITE_TAC[ARITH_RULE` a < b - 1 <=> SUC a < b`]; 
REWRITE_TAC[GSYM ITER]] THEN 
SUBGOAL_THEN ` ~(ITER j f (p0: real^2) = vec 0 )` ASSUME_TAC
THENL [ASM SET_TAC[IN; POLAR_CYCLIC_FUN_IMP_ALL_BELONG];
ASM_MESON_TAC[POLAR_LT_TRANS]]);;



let FINITE_SEUBSET_OF_NATURAL = prove(`! n. FINITE { f i | i < (n:num) } `,
INDUCT_TAC THENL [REWRITE_TAC[LT; SET_RULE[]` { f i | i | F } = {} `;
FINITE_RULES];
ASM_REWRITE_TAC[ARITH_RULE` i < SUC j <=> i < j \/ i = j `;
SET_RULE[]` {f i| P i \/ i = a } = f a INSERT {f i| P i }`;
FINITE_INSERT]]);;


let STRICTLY_INCREASE_PRESERVING_CARD = 
prove(` ! lt f. (! (x:A) y. lt x y ==> ~( x = y )) /\
(! i (j: num). i < j ==> lt (f i ) ( f j )) ==>
(! n. CARD ({ f i | i < n }) = n ) `,
REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL [
REWRITE_TAC[LT; SET_RULE[]` { f i | i | F } = {} `;
CARD_CLAUSES];
ASM_SIMP_TAC[ARITH_RULE` i < SUC j <=> i < j \/ i = j `;
SET_RULE[]` {f i| P i \/ i = a } = f a INSERT {f i| P i }`;
CARD_CLAUSES; FINITE_SEUBSET_OF_NATURAL] THEN 
SUBGOAL_THEN `~ ((f: num -> A) n IN {f i| i < n }) `
( fun x -> SIMP_TAC[x]) THEN REWRITE_TAC[IN_ELIM_THM] THEN 
ASM_MESON_TAC[]]);;









let XXXXX = prove(`!lt (f: num -> A).
         (!x y. lt x y ==> ~(x = y)) /\
         (!i j. i < j /\ j < N  ==> lt (f i) (f  j))
         ==> (!n. n < N ==> CARD {f i | i < n} = n)`,
REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL [
REWRITE_TAC[LT; EMPTY_GSPEC; SET_RULE[]` { f i| i | F } 
= {} `; CARD_CLAUSES]; REWRITE_TAC[ARITH_RULE` i < SUC v <=> i < v \/ i = v `]]
THEN DISCH_TAC THEN REWRITE_TAC[
SET_RULE[]`{(f:num -> A) i| i < n \/ i = n } = 
f n INSERT {f i | i < n } `] THEN 
SIMP_TAC[FINITE_SEUBSET_OF_NATURAL; CARD_CLAUSES] THEN 
SUBGOAL_THEN ` ~((f:num -> A) n IN { f i | i < n }) `
ASSUME_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN
ASM_MESON_TAC[ARITH_RULE` SUC v < g ==> v < g `];
ASM_REWRITE_TAC[] THEN 
ASM_MESON_TAC[ARITH_RULE` SUC x < y ==> x < y `]]);;




let TDHUFHCYVHYBCC = prove(`  (!x. W x ==> ~(x = vec 0)) /\
     FINITE W /\
     W p0 /\
     f polar_cycle_on W /\
     (!x. W x ==> p0 polar_le x)
==> (! n. n < CARD W ==>
CARD { y | ? i. i < n /\ y = ITER i f p0 } = n ) `,
STRIP_TAC THEN 
REWRITE_TAC[SET_RULE[]` {y | ? i. i < n /\ y = ITER i f p0 
} = {ITER i f p0 | i < n } `] THEN 
MATCH_MP_TAC (BETA_RULE (ISPECL [`CARD (W: real^2 -> bool) `
;`\x y. W x /\ W y /\ x polar_lt y `; `\i. ITER i f (p0:real^2) `] 
(GEN_ALL XXXXX))) THEN 
CONJ_TAC THENL [
ASM_MESON_TAC[POLAR_LT_IMP_NOT_EQ]; REPEAT STRIP_TAC]
THENL [

ASM_REWRITE_TAC[SET_RULE[]` A ( p x ) <=> p x IN A `] THEN 
ASM_MESON_TAC [POLAR_CYCLIC_FUN_IMP_ALL_BELONG];

ASM_REWRITE_TAC[SET_RULE[]` A ( p x ) <=> p x IN A `] THEN 
ASM_MESON_TAC [POLAR_CYCLIC_FUN_IMP_ALL_BELONG];

MP_TAC MONOPOLY_IN_FIRST_PERIOD THEN 
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]]]);;



let POLAR_CYCLIC_FUN_IMP_ALL_BELONG = 
REWRITE_RULE[IN] POLAR_CYCLIC_FUN_IMP_ALL_BELONG;;
    
let CARD_W_AS_ALL_LESS_THAN_PERIODIC = prove(
` (!x. W x ==> ~(x = vec 0)) /\
     FINITE W /\
     W p0 /\
     f polar_cycle_on W /\
     (!x. W x ==> p0 polar_le x)
==> (! n. n = CARD W ==> CARD { y | ? i. i < n /\ y = ITER i f p0 } = n ) `,
SIMP_TAC[] THEN ASM_CASES_TAC ` CARD (W:real^2 -> bool) = 0 `
THENL [ASM_REWRITE_TAC[LT; EMPTY_GSPEC; CARD_CLAUSES];
ASM_SIMP_TAC[ARITH_RULE` ~( a = 0 ) ==> ( b < a <=> b <
a - 1 \/ b = a - 1 )`] THEN REPEAT STRIP_TAC THEN 
REWRITE_TAC[SET_RULE[]` {y | ?i. (P i \/ i = a ) /\ y = Q i}
= Q a INSERT {y | ? i. P i /\ y = Q i }`]] THEN 
SUBGOAL_THEN `FINITE {y | ?i. i < CARD (W:real^2 -> bool)
 - 1 /\ y = ITER i f (p0:real^2)} ` ASSUME_TAC THENL [
REWRITE_TAC[SET_RULE[]` {y | ?i . P i /\ y = Q i } = 
{ Q i | P i } `] THEN 
REWRITE_TAC[FINITE_SEUBSET_OF_NATURAL];
ASM_SIMP_TAC[CARD_CLAUSES] THEN COND_CASES_TAC THENL [
DOWN THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN 
DOWN_TAC THEN 
NHANH (ARITH_RULE `~( CARD W = 0 ) ==>  CARD (W:real^2 -> bool) - 1
< CARD W `) THEN STRIP_TAC THEN 
SUBGOAL_THEN` ITER i f (p0:real^2) polar_lt ITER (CARD (W:
real^2 -> bool) - 1 ) f p0 ` ASSUME_TAC THENL [
ASM_MESON_TAC [MONOPOLY_IN_FIRST_PERIOD]; 
ASM_MESON_TAC[POLAR_LT_IMP_NOT_EQ;
 MONOPOLY_IN_FIRST_PERIOD;
POLAR_CYCLIC_FUN_IMP_ALL_BELONG]]; DOWN_TAC] THEN 
NHANH (ARITH_RULE` ~(x = 0 ) ==> x - 1 < x `) THEN 
STRIP_TAC THEN MP_TAC TDHUFHCYVHYBCC THEN 
ANTS_TAC THENL [ASM_REWRITE_TAC[]; 
DISCH_THEN (MP_TAC o (SPEC ` CARD (W:real^2 -> bool)
- 1 `)) THEN 
ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[] THEN 
DISCH_TAC THEN UNDISCH_TAC `~( CARD (W:real^2 -> bool ) = 0)`
THEN ARITH_TAC]]]);;



let AUTOMAP_IMP_ALL_ITER_IN = 
prove(`W (p: A) /\ (! x. W x ==> f x IN W ) 
==> (! N. ITER N f p IN W ) `,
STRIP_TAC THEN INDUCT_TAC THENL [
ASM_REWRITE_TAC[ITER; IN];
REWRITE_TAC[ITER] THEN ASM SET_TAC[]]);;



let AUTOMAP_IMP_ITER_SET_IS_A_SUBSET = 
prove(`W p /\ (! x. W x ==> f x IN W ) ==>
{y | ?n. y = ITER n f p } SUBSET W `,
STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN 
ASM_MESON_TAC[AUTOMAP_IMP_ALL_ITER_IN]);;





let TOW_NON_VEC0_POLAR_LE_IMP_NOT_LT = 
prove(`~( x = vec 0 ) /\ ~( y = vec 0 ) /\ x polar_le y ==>
~( y polar_lt x ) `, REWRITE_TAC[polar_le] THEN 
MESON_TAC[TOW_NON_VEC0_IMP_NOT_REFL_POLAR_LT;
NOT_EQ_IMP_TOTAL_ORDER;
NO_V0_IMP_NOT_SELF_POLLAR]);;


let CARD_W_IS_THE_PERIODIC = prove(` (!x. W x ==> ~(x = vec 0)) /\
     FINITE W /\
     W p0 /\
     f polar_cycle_on W /\
     (!x. W x ==> p0 polar_le x)
==> ITER (CARD W) f p0 = p0 `,
STRIP_TAC THEN MP_TAC CARD_W_AS_ALL_LESS_THAN_PERIODIC
THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; 
DISCH_THEN (MP_TAC o SPEC `CARD (W:real^2 -> bool)`)] THEN 
REWRITE_TAC[] THEN 


REWRITE_TAC[SET_RULE[]`{y | ?i. i < CARD W /\ y = ITER i f p0} =
{ITER i f p0 | i < CARD W }`] THEN SUBGOAL_THEN ` FINITE {ITER i f (p0:real^2) | 
i < CARD (W:real^2 -> bool)}` ASSUME_TAC THENL [
REWRITE_TAC[FINITE_SEUBSET_OF_NATURAL]; 
ABBREV_TAC ` WW =  {ITER i f (p0:real^2) | i < 
CARD (W:real^2 -> bool ) }`] THEN 
SUBGOAL_THEN ` WW SUBSET (W:real^2 -> bool) ` ASSUME_TAC
THENL [EXPAND_TAC "WW" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN]
THEN ASM_MESON_TAC[POLAR_CYCLIC_FUN_IMP_ALL_BELONG];
DISCH_TAC] THEN SUBGOAL_THEN `WW = (W:real^2 -> bool) ` ASSUME_TAC THENL
[ASM_MESON_TAC[CARD_SUBSET_EQ]; ALL_TAC] THEN 
SUBGOAL_THEN `! (x:real^2). W x ==> x polar_le ITER (CARD
W - 1 ) f p0 ` ASSUME_TAC THENL [


EXPAND_TAC "W" THEN EXPAND_TAC "WW" THEN 
REWRITE_TAC[IN_ELIM_THM] THEN 
ASSUME_TAC2 (ISPEC` W: real^2 -> bool` CARD_EQ_0) THEN 
ASM_CASES_TAC ` ~((W:real^2 -> bool) = {})` THENL [



FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN GEN_TAC THEN 
ASM_REWRITE_TAC[] THEN DOWN THEN 
SIMP_TAC[ARITH_RULE` ~( x = 0 ) ==> ( c < x <=> c < x - 1 
\/ c = x - 1) `] THEN PHA THEN STRIP_TAC THENL [


ASM_REWRITE_TAC[] THEN 
ASSUME_TAC2 (ARITH_RULE` ~(CARD W = 0) ==> 
CARD (W:real^2 -> bool) - 1 < CARD W `) THEN 
ASSUME_TAC2 MONOPOLY_IN_FIRST_PERIOD THEN 
ASM_MESON_TAC[polar_le]; 



ASM_REWRITE_TAC[polar_le]]; 



DOWN THEN DOWN THEN MESON_TAC[LT]];






ASSUME_TAC2 (ISPEC` W: real^2 -> bool` CARD_EQ_0) THEN 
ASSUME_TAC2 (SET_RULE[]`W p0 ==>
 ~((W:real^2 -> bool) = {})`) THEN 
FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN DOWN THEN 
SUBGOAL_THEN `W (ITER (CARD W - 1) f (p0:real^2))` ASSUME_TAC
THENL [ASM_MESON_TAC[POLAR_CYCLIC_FUN_IMP_ALL_BELONG];
NHANH (ARITH_RULE` ~( a = 0 ) ==> a = a - 1 + 1 `)] THEN 
STRIP_TAC THEN SUBGOAL_THEN `ITER (CARD (W:real^2 -> bool)) f (p0:real^2)
= f (ITER ( CARD W - 1 ) f p0 )` ASSUME_TAC THENL [
REWRITE_TAC[GSYM ITER; ADD1] THEN DOWN THEN MESON_TAC[];
ALL_TAC]] THEN DOWN_TAC THEN REWRITE_TAC[polar_cycle_on]
THEN STRIP_TAC THEN 
ABBREV_TAC ` AD = ITER (CARD (W:real^2 -> bool ) - 1)
 f (p0:real^2)` THEN 


SUBGOAL_THEN ` f (AD: real^2) polar_le AD ` ASSUME_TAC
THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];

SUBGOAL_THEN `~( AD polar_lt f AD ) ` ASSUME_TAC THENL [
ASM SET_TAC[TOW_NON_VEC0_POLAR_LE_IMP_NOT_LT];
DOWN_TAC THEN REWRITE_TAC[IN] THEN STRIP_TAC]] THEN 
UNDISCH_TAC `(W:real^2 -> bool) (AD:real^2 )` THEN 
USE_FIRST ` !x. W (x:real^2 )
          ==> x polar_lt f x /\
              (!y. W y ==> ~(x polar_lt y /\ y polar_lt f x)) \/
              (!y. W y ==> f x polar_le y /\ y polar_le x)`
NHANH THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN 
UNDISCH_TAC `(W:real^2 -> bool) p0 ` THEN 
FIRST_X_ASSUM NHANH THEN ASM_MESON_TAC[POLAR_LE_REFL_EQ]);;






let ITER_CARD_W_IDENTIFICATION = prove(`
(!x. W x ==> ~(x = vec 0)) /\
     FINITE W /\
     W p0 /\
     f polar_cycle_on W /\
     (!x. W x ==> p0 polar_le x) 
==> (! x. W x ==> ITER (CARD W) f x = x) `,
STRIP_TAC THEN STRIP_TAC THEN FIRST_ASSUM NHANH THEN 
REWRITE_TAC[polar_le] THEN STRIP_TAC THENL [
MP_TAC (CHANGE `x:real^2 ` `p:real^2 ` (SPEC_ALL 
EXISTS_STEPS_FOR_FOLLOWING_POINTS)) THEN 
ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
EXPAND_TAC "x" THEN REWRITE_TAC[ITER_ADD] THEN 
ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[GSYM ITER_ADD]
THEN MATCH_MP_TAC (MESON[]` a = b ==> P a = P b `) THEN
MATCH_MP_TAC CARD_W_IS_THE_PERIODIC THEN ASM_REWRITE_TAC[];
EXPAND_TAC "x" THEN MATCH_MP_TAC 
CARD_W_IS_THE_PERIODIC THEN ASM_REWRITE_TAC[]]);;




let EXISTS_STEPS_FOR_FOLLOWING_POINTS = 
prove(` (!x. W x ==> ~(x = vec 0)) /\
         FINITE W /\
         W p0 /\
         f polar_cycle_on W /\
         p0 polar_le p /\
         W p
         ==> (?n. ITER n f p0 = p /\
                  (!nn. nn < n ==> ITER nn f p0 polar_lt p))`,
REWRITE_TAC[polar_le] THEN STRIP_TAC THENL [
MP_TAC (SPEC_ALL EXISTS_STEPS_FOR_FOLLOWING_POINTS) THEN 
ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]; 
EXISTS_TAC `0` THEN EXPAND_TAC "p" THEN REWRITE_TAC[ITER; LT]]);;






let EXISTS_STEPS_FOR_FOLLOWING_POINTS =
prove(` (!x. W x ==> ~(x = vec 0)) /\
     FINITE W /\
     W p0 /\
     f polar_cycle_on W /\
     p0 polar_le p /\
     W p
     ==> (?n. n < CARD W /\ 
              ITER n f p0 = p /\ 
              (!nn. nn < n ==> ITER nn f p0 polar_lt p))`,
NHANH EXISTS_STEPS_FOR_FOLLOWING_POINTS THEN 
STRIP_TAC THEN ASM_CASES_TAC ` n < CARD (W:real^2 -> bool) ` THENL
[EXISTS_TAC `n: num ` THEN ASM_REWRITE_TAC[];
UNDISCH_TAC `(W:real^2 -> bool) p ` THEN 
NHANH_PAT `\x. x ==> s ` (SET_RULE[]` S c ==> ~( S = {})`) THEN 
ASSUME_TAC2 (ISPEC `W:real^2 -> bool ` CARD_EQ_0) THEN 
FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN DOWN THEN 
NHANH (ARITH_RULE` ~( a < (b:num)) ==> a = a - b + b `) THEN 
STRIP_TAC THEN STRIP_TAC THEN 
ASSUME_TAC2 (ARITH_RULE` ~( n < CARD (W:real^2 -> bool))
 ==> ~( CARD W = 0 ) ==> n - CARD W < n `) THEN  
DOWN THEN FIRST_X_ASSUM NHANH THEN 
SUBGOAL_THEN `ITER (n - CARD (W: real^2 -> bool)) f p0
= ITER ( n - CARD W + CARD W ) f (p0:real^2) ` ASSUME_TAC]
THENL [ REWRITE_TAC[GSYM ITER_ADD] THEN MP_TAC 
(SPEC_ALL PROVE_MIN_ELEMENT_IN_FINITE_CYCLIC_SET) THEN 
ANTS_TAC THENL [
ASSUME_TAC2 (SET_RULE[]` (W:real^2 -> bool) p ==>
~( W = {} ) `) THEN ASM_REWRITE_TAC[];
STRIP_TAC] THEN MP_TAC (CHANGE `n': real^2 ` `p0:real^2 ` 
ITER_CARD_W_IDENTIFICATION) THEN 
ANTS_TAC THENL [ASM_REWRITE_TAC[polar_le]; DISCH_TAC] THEN 
UNDISCH_TAC ` (W:real^2 -> bool) p0 ` THEN 
FIRST_X_ASSUM NHANH THEN SIMP_TAC[]; 
DOWN THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN 
ASM_MESON_TAC[POLAR_CYCLIC_FUN_IMP_ALL_BELONG;
NO_V0_IMP_NOT_SELF_POLLAR]]);;




let MONO_LE_IN_FIRST_PERIOD = prove(
`(!x. W x ==> ~(x = vec 0)) /\
       FINITE W /\
       W p0 /\
       f polar_cycle_on W /\
       (!x. W x ==> p0 polar_le x)
       ==> (!i j. i <= j /\ j < CARD W 
==> ITER i f p0 polar_le ITER j f p0) `,
REWRITE_TAC[LE_LT; polar_le] THEN REPEAT STRIP_TAC THENL
[DISJ1_TAC THEN DOWN_TAC THEN REWRITE_TAC[GSYM polar_le]
THEN MESON_TAC[MONOPOLY_IN_FIRST_PERIOD; polar_le]; 
DISJ2_TAC THEN ASM_REWRITE_TAC[]]);;






let POLAR_LE_NOT_VEC0_IMP_PL_ANG_LE = 
prove(` x polar_le y /\ ~( x = vec 0 ) /\
~( y = vec 0 ) ==> pl_angle x <= pl_angle y `,
NHANH PL_ANGLE_PROPERTY THEN REWRITE_TAC[polar_le] THEN 
STRIP_TAC THENL [UNDISCH_TAC ` x polar_lt y ` THEN 
REWRITE_TAC[polar_lt; REAL_LE_LT] THEN 
ASM_MESON_TAC[]; ASM_REWRITE_TAC[REAL_LE_REFL]]);;




let TWO_NOT_EQ_VECS_SUM_ARG_DIFF_TWO_PI = prove(
 ` ~( x = vec 0 ) /\ ~ (y = vec 0 ) /\ ~( x = y )==>
arg_diff x y + arg_diff y x = &2 * pi `, 
NHANH_PAT `\x. a /\ b /\ x ==> kk ` NOT_EQ_IMP_TOTAL_ORDER THEN
NGOAC THEN REWRITE_TAC[arg_diff; polar_le] 
THEN (let ttc = ASM_REWRITE_TAC[] THEN 
ASSUME_TAC2 TOW_NON_VEC0_IMP_NOT_REFL_POLAR_LT THEN DOWN
THEN ASM_SIMP_TAC[DE_MORGAN_THM] THEN DISCH_TAC THEN 
CONV_TAC (DEPTH_CONV let_CONV) THEN REAL_ARITH_TAC in 
STRIP_TAC THENL [ttc ;ttc]));;



let ARG_DIFF_SUCCESSIBLE_IN_FIRST_PERIOD = 
prove(`!(W: real^2 -> bool ) xicm. FINITE W /\
     CARD W = n /\
     (!x. W x ==> ~(x = vec 0)) /\
     xicm polar_cycle_on W
     ==> (!p i j.
              W p /\ 0 <= i /\ i <= j /\ j < n
              ==> arg_diff p (ITER i xicm p) +
                  arg_diff (ITER i xicm p) (ITER j xicm p) =
                  arg_diff p (ITER j xicm p))`,
REPEAT STRIP_TAC THEN  
MP_TAC (SPEC_ALL PROVE_MIN_ELEMENT_IN_FINITE_CYCLIC_SET) THEN 
ANTS_TAC THENL [
ASM_MESON_TAC[SET_RULE[]` A x ==> ~( A = {} ) `];
STRIP_TAC] THEN UNDISCH_TAC ` (W:real^2 -> bool) p ` THEN 
FIRST_ASSUM NHANH THEN REWRITE_TAC[GSYM polar_le] THEN STRIP_TAC
THEN MP_TAC (CHANGE `n': real^2 ` `p0: real^2 ` 
(CHANGE `xicm: real^2 -> real^2 ` `f:real^2 -> real^2 `
(SPEC_ALL EXISTS_STEPS_FOR_FOLLOWING_POINTS))) THEN ANTS_TAC
THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN 
ASM_CASES_TAC ` j + n'' < CARD (W:real^2 -> bool) `
THENL [

UNDISCH_TAC ` i <= (j:num) ` THEN 
NHANH (ARITH_RULE` (i:num) <= j ==> i + n'' <= j + n'' `) THEN 
MP_TAC (CHANGE `xicm: real^2 -> real^2 ` `f:real^2 -> real^2 `
(CHANGE `n': real^2 ` `p0: real^2 ` MONO_LE_IN_FIRST_PERIOD)) THEN 
ANTS_TAC THENL [ASM_REWRITE_TAC[polar_le]; 
STRIP_TAC THEN STRIP_TAC] THEN 
UNDISCH_TAC` j + n'' < CARD (W:real^2 -> bool) ` THEN 
DOWN THEN 
PHA THEN 
FIRST_ASSUM NHANH THEN 
NHANH (ARITH_RULE` a <= b /\ b < c ==> a < (c:num) `)  THEN 
STRIP_TAC THEN 
UNDISCH_TAC ` j + n'' < CARD (W:real^2 -> bool) ` THEN 
MP_TAC (ARITH_RULE` n'' <= j + (n'':num) `) THEN 
PHA THEN FIRST_ASSUM NHANH THEN 
STRIP_TAC THEN 
UNDISCH_TAC ` i + n'' < CARD (W:real^2 -> bool) ` THEN 
MP_TAC (ARITH_RULE` n'' <= i + (n'':num) `) THEN 
PHA THEN FIRST_ASSUM NHANH THEN 
DOWN_TAC THEN 
REWRITE_TAC[GSYM ITER_ADD] THEN 
STRIP_TAC THEN 
FIRST_X_ASSUM SUBST_ALL_TAC THEN 
SUBGOAL_THEN ` pl_angle p <= pl_angle (ITER i xicm p) /\
pl_angle p <= pl_angle (ITER j xicm p ) /\
pl_angle (ITER i xicm p) <= pl_angle (ITER j xicm p) ` 
ASSUME_TAC THENL [ASM_MESON_TAC[POLAR_CYCLIC_FUN_IMP_ALL_BELONG;
POLAR_LE_NOT_VEC0_IMP_PL_ANG_LE]; REWRITE_TAC[arg_diff] THEN
ASM_SIMP_TAC[] THEN CONV_TAC (DEPTH_CONV let_CONV) THEN 
ARITH_TAC];





ASM_CASES_TAC` i + n'' < CARD (W:real^2 ->  bool) `] THENL [
ASSUME_TAC2 (ARITH_RULE` ~( j + n'' < CARD (W: real^2 -> bool))
/\ j < n ==> CARD W = n ==> (j + n'') - CARD W < n''`) THEN 
EXPAND_TAC "p" THEN 
REWRITE_TAC[ITER_ADD] THEN 
DOWN_TAC THEN 
NHANH (ARITH_RULE` ~ (a < b )  ==> a - b + b = (a:num)`) THEN 
ABBREV_TAC ` aa = j + (n'': num) ` THEN 
STRIP_TAC THEN 
EXPAND_TAC "aa" THEN 
REWRITE_TAC[GSYM ITER_ADD] THEN 
SUBGOAL_THEN `! x. W x ==> ITER (CARD (W:real^2 -> bool)) xicm x = x ` ASSUME_TAC
THENL [
MATCH_MP_TAC (CHANGE `n':real^2` `p0:real^2 ` ITER_CARD_W_IDENTIFICATION) THEN 
ASM_REWRITE_TAC[polar_le]; 


UNDISCH_TAC ` (W:real^2 -> bool) n' `] THEN 
FIRST_ASSUM NHANH THEN 
SIMP_TAC[] THEN 
REWRITE_TAC[ITER_ADD] THEN 
STRIP_TAC THEN 
ASSUME_TAC2 (ARITH_RULE` i <= j /\ j < n /\ CARD (W:real^2 
-> bool) = n ==> i < CARD W `) THEN 
ASSUME_TAC (ARITH_RULE` n'' <= i + (n'':num) `) THEN 
ASSUME_TAC2 (ARITH_RULE` aa - CARD (W:real^2 -> bool) <
n'' ==> aa - CARD W < i + n'' `) THEN 

(*
POLAR_LE_NOT_VEC0_IMP_PL_ANG_LE;;
 
  |- x polar_le y /\ ~(x = vec 0) /\ ~(y = vec 0)
     ==> pl_angle x <= pl_angle y


POLAR_CYCLIC_FUN_IMP_ALL_BELONG;;

 it : thm = |- W p /\ f polar_cycle_on W ==> (!n. W (ITER n f p))


MONO_LE_IN_FIRST_PERIOD;;

*)
SUBGOAL_THEN` (ITER ( aa - CARD (W:real^2 -> bool)) xicm
(n':real^2) ) polar_lt (ITER n'' xicm n')/\
ITER ( aa - CARD W ) xicm n' polar_lt ITER (i + n'') xicm n'
 ` ASSUME_TAC THENL [
DOWN_TAC THEN REWRITE_TAC[IN; GSYM polar_le] THEN 
ASM_MESON_TAC[MONOPOLY_IN_FIRST_PERIOD]; ALL_TAC] THEN 





SUBGOAL_THEN ` ITER n'' xicm n' polar_le ITER (i + n'')
xicm n'` ASSUME_TAC THENL 
[DOWN_TAC THEN REWRITE_TAC[GSYM polar_le] THEN 
ASM_MESON_TAC[MONO_LE_IN_FIRST_PERIOD]; ALL_TAC] THEN 





SUBGOAL_THEN ` ~(ITER (aa - CARD (W:real^2 -> bool)) xicm
(n':real^2) = vec 0 ) /\
~( ITER n'' xicm n' = vec 0 ) /\
~( ITER (i + n'') xicm n' = vec 0 )` ASSUME_TAC THENL [
ASM_MESON_TAC[POLAR_CYCLIC_FUN_IMP_ALL_BELONG]; ALL_TAC] THEN 

SUBGOAL_THEN ` ~(ITER n'' xicm n' polar_le ITER (aa - CARD (W:real^2 -> bool)) xicm n') /\
~( ITER (i + n'') xicm n' polar_le ITER ( aa - CARD W) xicm n')`
ASSUME_TAC THENL [ASM_MESON_TAC[
TOW_NON_VEC0_POLAR_LE_IMP_NOT_LT]; ALL_TAC] THEN 

ASM_REWRITE_TAC[arg_diff] THEN CONV_TAC (DEPTH_CONV let_CONV)
THEN REAL_ARITH_TAC; ALL_TAC] THEN DOWN THEN DOWN THEN
NHANH (ARITH_RULE` ~( a < (b:num)) ==> a = a - b + b `) THEN 


SUBGOAL_THEN `(! (x:real^2). W x ==> ITER (CARD W) xicm x
= x) ` ASSUME_TAC THENL [

MATCH_MP_TAC (CHANGE `n':real^2 ` `p0: real^2 ` (REWRITE_RULE[polar_le] 
ITER_CARD_W_IDENTIFICATION)) THEN ASM_REWRITE_TAC[];

ABBREV_TAC ` wi = (i + n'') - CARD (W:real^2 -> bool) `] THEN 
ABBREV_TAC ` wj = (j + n'') - CARD (W:real^2 -> bool) ` THEN 
EXPAND_TAC "p" THEN SIMP_TAC[ITER_ADD] THEN 
REWRITE_TAC[GSYM ITER_ADD] THEN ASM_SIMP_TAC[] THEN 
STRIP_TAC THEN STRIP_TAC THEN 
SUBGOAL_THEN ` wi < (n'': num) /\ wj < n'' /\ wi <= wj
/\ wj < CARD (W:real^2 -> bool)` ASSUME_TAC THENL [
ASM_ARITH_TAC; ALL_TAC] THEN 


SUBGOAL_THEN ` (ITER wi xicm n') polar_le (ITER wj xicm n')
/\ ITER wi xicm n' polar_lt ITER n'' xicm n' /\
ITER wj xicm n' polar_lt ITER n'' xicm n' ` ASSUME_TAC THENL [
DOWN_TAC THEN REWRITE_TAC[GSYM polar_le] THEN 
MESON_TAC [MONOPOLY_IN_FIRST_PERIOD;
MONO_LE_IN_FIRST_PERIOD]; ALL_TAC] THEN 

SUBGOAL_THEN ` ~( ITER wi xicm (n':real^2) = vec 0 ) /\
~( ITER wj xicm n' = vec 0 ) /\ ~( ITER n'' xicm n' = vec 0) `
ASSUME_TAC THENL [
ASM_MESON_TAC[POLAR_CYCLIC_FUN_IMP_ALL_BELONG]; ALL_TAC] THEN 

SUBGOAL_THEN ` ~(ITER n'' xicm n' polar_le ITER wi xicm n') /\
     ~( ITER n'' xicm n' polar_le ITER wj xicm n')` ASSUME_TAC
THENL [DOWN THEN DOWN THEN MESON_TAC [
TOW_NON_VEC0_POLAR_LE_IMP_NOT_LT]; ALL_TAC] THEN 


EXPAND_TAC "p" THEN REWRITE_TAC[arg_diff] THEN 
ASM_REWRITE_TAC[] THEN CONV_TAC (DEPTH_CONV let_CONV) THEN 
REAL_ARITH_TAC);;



let TWO_NON_ZERO_VECS_NOT_EQ_EQ_PLT = 
prove(` ~(x = vec 0) /\ ~(y = vec 0) ==> 
(  ~(x = y) <=> x polar_lt y \/ y polar_lt x ) `,
MESON_TAC[POLAR_LT_IMP_NOT_EQ;NOT_EQ_IMP_TOTAL_ORDER]);;



let SUM_OVER_W_EQUAL_AT_ANY_POINT = 
prove(` FINITE W /\
     CARD W = n /\
     (!x. W x ==> ~(x = vec 0)) /\
     xicm polar_cycle_on W /\ W p0 /\
(! x. W x ==> p0 polar_le x )
==> (! p. W p ==>
sum (0.. n - 1 ) (\i. arg_diff ( ITER i xicm p ) (ITER ( i + 1 )
xicm p)) = 
sum (0.. n - 1 ) (\i. arg_diff ( ITER i xicm p0 ) (ITER ( i + 1 )
xicm p0))) `,
REPEAT STRIP_TAC THEN DOWN THEN FIRST_ASSUM NHANH THEN 
STRIP_TAC THEN ASSUME_TAC2 (
CHANGE `xicm: real^2 -> real^2 ` `f:real^2 -> real^2 `
EXISTS_STEPS_FOR_FOLLOWING_POINTS) THEN DOWN THEN STRIP_TAC
THEN ASM_CASES_TAC ` n' = 0 ` THENL [
FIRST_X_ASSUM SUBST_ALL_TAC THEN EXPAND_TAC "p" THEN 
REWRITE_TAC[ITER_ADD; ADD_CLAUSES]; EXPAND_TAC "p"] THEN 
REWRITE_TAC[ITER_ADD; ARITH_RULE` (i + 1) + n' =
(i + n' ) + 1 `] THEN ABBREV_TAC ` ff i = 
arg_diff (ITER i xicm (p0:real^2)) (ITER (i + 1) xicm p0) `
  THEN REWRITE_TAC[GSYM SUM_OFFSET] THEN 
ASSUME_TAC2 (ARITH_RULE` CARD (W:real^2 -> bool) = n /\
n' < CARD W ==> n' <= n - 1 + 1 `) THEN 
ASM_SIMP_TAC[ADD; SUM_ADD_SPLIT] THEN 
ASSUME_TAC2 (ISPEC `W:real^2 -> bool ` CARD_EQ_0) THEN (* 000 *)
ASSUME_TAC2 (SET_RULE[]` (W:real^2 -> bool) p ==>
~( W = {} ) `) THEN FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN 
EXPAND_TAC "n" THEN DOWN THEN UNDISCH_TAC ` ~( n' = 0)` THEN 
PHA THEN NHANH (ARITH_RULE` ~(a = 0) /\ ~( b = 0 ) ==>
b - 1 + 1 = 0 + b /\ b - 1 + a = a - 1 + b `) THEN 
SIMP_TAC[] THEN STRIP_TAC THEN 
REWRITE_TAC[SUM_OFFSET] THEN 
SUBGOAL_THEN `! i. (ff: num -> real) (i + CARD (W:real^2 
-> bool)) = ff i ` ASSUME_TAC THENL [
DOWN_TAC THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN 
SIMP_TAC[] THEN STRIP_TAC THEN 
REWRITE_TAC[ARITH_RULE` (a + b ) + 1 = (a + 1 ) + b `] THEN 
REWRITE_TAC[GSYM ITER_ADD] THEN 
MP_TAC (CHANGE ` xicm: real^2 -> real^2 ` `f: real^2 -> real^2 `
ITER_CARD_W_IDENTIFICATION) THEN 
ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN 
UNDISCH_TAC `(W:real^2 -> bool) p0 ` THEN 
FIRST_X_ASSUM NHANH THEN SIMP_TAC[];
ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN 
MP_TAC (ISPECL[`ff: num -> real `;`0`;`n': num`;` n - 1 `]
SUM_COMBINE_L) THEN 
ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[ETA_AX]]]);;


let SUM_INCREASE_ARG_DIFF = prove(
 ` !(W: real^2 -> bool ) xicm. FINITE W /\
     CARD W = n /\
     (!x. W x ==> ~(x = vec 0)) /\
     xicm polar_cycle_on W
     ==> (!p i j.
              W p /\ 0 <= i /\ i < j /\ j < n
              ==> sum (i .. (j - 1 )) (\i. arg_diff (ITER i xicm p) (ITER (i + 1) xicm p) )
            = arg_diff (ITER i xicm p) (ITER j xicm p)) `,
REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN GEN_TAC THEN 
INDUCT_TAC THENL [REWRITE_TAC[LT]; REWRITE_TAC[LT]] THEN STRIP_TAC
THENL [ASM_REWRITE_TAC[SUC_SUB1; SUM_SING_NUMSEG; ADD1]; 
DOWN THEN NHANH (ARITH_RULE` SUC c < k ==> c < k `)] THEN 
STRIP_TAC THEN UNDISCH_TAC` j < (n:num) ` THEN 
UNDISCH_TAC` i < (j:num)` THEN 
UNDISCH_TAC` 0 <= i ` THEN 
UNDISCH_TAC`(W:real^2 -> bool) p ` THEN 
PHA THEN 
FIRST_ASSUM NHANH THEN 
NHANH (ARITH_RULE`0 <= i /\ i < j /\ j < n ==>
SUC j - 1 = (j - 1) + 1 `) THEN 
SIMP_TAC[] THEN 
NHANH (ARITH_RULE` i < j ==> i <= j - 1 + 1`) THEN
SIMP_TAC[SUM_ADD_SPLIT] THEN 
NHANH (ARITH_RULE` i < j ==> j - 1 + 1 = j `) THEN 
STRIP_TAC THEN 
ASM_REWRITE_TAC[SUM_SING_NUMSEG; ADD1] THEN 
MP_TAC (SPEC_ALL ARG_DIFF_SUCCESSIBLE_IN_FIRST_PERIOD) THEN 
ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN 
DISCH_THEN (MP_TAC o (SPECL [`ITER i xicm (p:real^2)`; ` j - (i: num) `;
` j - i + 1 `])) THEN ANTS_TAC THENL [
CONJ_TAC THENL [ASM_MESON_TAC[POLAR_CYCLIC_FUN_IMP_ALL_BELONG];
ASM_ARITH_TAC]; REWRITE_TAC[ITER_ADD]] THEN 
ASSUME_TAC2 (ARITH_RULE` (i:num) < j ==> j - i + i = j `) THEN 
ASSUME_TAC2 (ARITH_RULE` i < j ==> (j - i + 1) + i = j + 1 `) THEN 
DOWN THEN DOWN THEN SIMP_TAC[]);;




let LEMMA_SUM_ALL_OVER_CYCLIC_SET = prove(`!(W: real^2 -> bool ) xicm. FINITE W /\
     CARD W = n /\
     (!x. W x ==> ~(x = vec 0)) /\
     xicm polar_cycle_on W /\ W p
     ==> ((?p q. W p /\ W q /\ ~(p = q))
     ==> sum (0..n - 1)
         (\i. arg_diff (ITER i xicm p) (ITER (i + 1) xicm p)) =
         &2 * pi)`,
REPEAT GEN_TAC THEN STRIP_TAC THEN 
FIRST_ASSUM NHANH THEN 
STRIP_TAC THEN 
DOWN THEN 
ASM_SIMP_TAC[TWO_NON_ZERO_VECS_NOT_EQ_EQ_PLT] THEN 
REPLICATE_TAC 4 DOWN THEN 
PHA THEN 




SPEC_TAC (`q:real^2`, `q:real^2 `) THEN 
SPEC_TAC (`p':real^2`, `p':real^2 `) THEN 
REWRITE_TAC[MESON[]`(!x. P x ==> Q ) <=> (?x. P x ) ==> Q `;
MESON[]` (? x y. W x /\ ~( x = i ) /\ W y /\
~( y = i ) /\ (x polar_lt y \/ y polar_lt x) ) <=>
(? x y. W x /\ ~( x = i )/\ W y /\ ~( y = i ) /\ x polar_lt y ) `] THEN 
STRIP_TAC THEN 
MP_TAC (SPEC_ALL PROVE_MIN_ELEMENT_IN_FINITE_CYCLIC_SET) THEN 
ANTS_TAC THENL [
ASM_MESON_TAC[SET_RULE[]` A s ==> ~(A = {})`];

STRIP_TAC] THEN 



MP_TAC (CHANGE `n':real^2 ` `p0:real^2 ` 
SUM_OVER_W_EQUAL_AT_ANY_POINT) THEN ANTS_TAC THENL [
ASM_REWRITE_TAC[polar_le]; DISCH_TAC] THEN 


UNDISCH_TAC ` (W:real^2 -> bool) p ` THEN 
FIRST_ASSUM NHANH THEN 
SIMP_TAC[] THEN 
STRIP_TAC THEN 
ASM_CASES_TAC ` n' = (q:real^2) ` THENL [


ASM_MESON_TAC[TOW_NON_VEC0_IMP_NOT_REFL_POLAR_LT;
POLAR_LT_IMP_NOT_EQ]; 

MP_TAC (
CHANGE `q: real^2 ` `p:real^2 ` (
CHANGE `xicm: real^2 -> real^2 ` `f: real^2 -> real^ 2 ` (
CHANGE `n': real^2 ` `p0:real^2 ` EXISTS_STEPS_FOR_FOLLOWING_POINTS)))
   ] THEN 

ANTS_TAC THENL [
REWRITE_TAC[polar_le] THEN 
ASM_MESON_TAC[]; STRIP_TAC] THEN 


ASM_CASES_TAC `n'' = 0 ` THENL [
REPLICATE_TAC 5 DOWN THEN PHA THEN 
MESON_TAC[ITER];

ASSUME_TAC2 (ARITH_RULE`~( n'' = 0) ==> 0 <= n'' - 1 + 1 `)]
    THEN 




ASSUME_TAC2 (ARITH_RULE` CARD (W:real^2 -> bool) = n /\
n'' < CARD W /\ ~(n'' = 0 ) ==> n'' - 1 <= n - 1 `) THEN 
DOWN THEN DOWN THEN PHA THEN 
NHANH (

SPEC `(\i. arg_diff (ITER i xicm n') 
(ITER (i + 1) xicm n'))` (GSYM SUM_COMBINE_R)) THEN 
SIMP_TAC[] THEN 
STRIP_TAC THEN 
MP_TAC (SPEC_ALL SUM_INCREASE_ARG_DIFF) THEN 
ANTS_TAC THENL [
ASM_REWRITE_TAC[];
STRIP_TAC] THEN 


UNDISCH_TAC `n'' < CARD (W:real^2 -> bool) ` THEN 
UNDISCH_TAC `~( n'' = 0 ) ` THEN 
REWRITE_TAC[ ARITH_RULE`~(a = 0) <=> 0 < a `] THEN 
MP_TAC (ARITH_RULE` 0 <= 0 `) THEN 
UNDISCH_TAC `(W:real^2 -> bool) n'` THEN 
PHA THEN 
ASM_REWRITE_TAC[] THEN 
FIRST_ASSUM NHANH THEN 
SIMP_TAC[] THEN 
STRIP_TAC THEN 
ASSUME_TAC2 (
ARITH_RULE`0 < n'' /\ n'' < n ==> n - 1 = n - 1 - 1 + 1 `) THEN 
FIRST_X_ASSUM (fun x -> ONCE_REWRITE_TAC[x]) THEN 
ONCE_REWRITE_TAC[SUM_OFFSET] THEN 

REWRITE_TAC[BETA_THM; GSYM ITER_ADD] THEN 
SUBGOAL_THEN ` (W:real^2 -> bool) (ITER 1 xicm (n':real^2)) ` MP_TAC
THENL [
ASM_SIMP_TAC[POLAR_CYCLIC_FUN_IMP_ALL_BELONG];
DISCH_TAC] THEN 
ASSUME_TAC2 (ARITH_RULE` n'' < n ==> n - 1 < n `) THEN  
DOWN THEN 
ASSUME_TAC2 (ARITH_RULE`0 < n'' /\ n'' < n ==>
n'' - 1 < n - 1 `) THEN 




UNDISCH_TAC `n'' - 1 < n - 1 ` THEN 
ASSUME_TAC2 (ARITH_RULE` 0 < n'' ==> 0 <= n'' - 1 `) THEN 
DOWN THEN 
DOWN THEN 
PHA THEN 
FIRST_ASSUM NHANH THEN 
SIMP_TAC[ITER_ADD] THEN 
STRIP_TAC THEN 
ASSUME_TAC2 (ARITH_RULE` 0 < n'' ==> n'' - 1 + 1 = n''`) THEN 
ASSUME_TAC2 (ARITH_RULE` n'' < n ==> n - 1 + 1 = n `) THEN 
ASM_REWRITE_TAC[ITER] THEN 
UNDISCH_TAC` CARD (W:real^2 -> bool) = n `  THEN 
DISCH_TAC THEN EXPAND_TAC "n" THEN 
MP_TAC (
CHANGE `xicm: real^2 -> real^2 ` `f:real^2 -> real^2 ` (
CHANGE `n': real^2 ` `p0:real^2 `ITER_CARD_W_IDENTIFICATION)
   ) THEN 



ANTS_TAC THENL [
ASM_REWRITE_TAC[polar_le];
DISCH_TAC] THEN 

UNDISCH_TAC` (W:real^2 -> bool) n' ` THEN 
FIRST_ASSUM NHANH THEN 
EXPAND_TAC "n" THEN 
SIMP_TAC[] THEN 
ASM_MESON_TAC[TWO_NOT_EQ_VECS_SUM_ARG_DIFF_TWO_PI]);;






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





let ISRTTNZ = prove(` FINITE W /\
         CARD W = n /\
         (!x. W x ==> ~(x = vec 0)) /\
         xicm polar_cycle_on W /\
         W p /\ (?p q. W p /\ W q /\ ~(p = q))
         ==> sum (0..n - 1)
             (\i. arg_diff (ITER i xicm p) (ITER (i + 1) xicm p)) =
             &2 * pi /\
(!p i j.
              W p /\ 0 <= i /\ i <= j /\ j < n
              ==> arg_diff p (ITER i xicm p) +
                  arg_diff (ITER i xicm p) (ITER j xicm p) =
                  arg_diff p (ITER j xicm p))  `, STRIP_TAC THEN 
MP_TAC (SPEC_ALL ARG_DIFF_SUCCESSIBLE_IN_FIRST_PERIOD) THEN 
ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]] THEN DISCH_TAC
THEN MP_TAC (SPEC_ALL LEMMA_SUM_ALL_OVER_CYCLIC_SET) THEN PHA THEN 
ANTS_TAC THENL [ ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
SIMP_TAC[]]);;
