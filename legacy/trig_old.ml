(* cut from trig.ml.
   Material by J. Rute and T. Hales *)

			
(*** work in progress

  prove
	 (`!u v w. arcV u v w = arcV (vec 0) (v - u) (w - u)`,
	   REWRITE_TAC [CONV_RULE KEP_REAL3_CONV arcV; VECTOR_SUB_RZERO]);;

  let ARCV_BILINEAR_L = prove
	 (`!(u:real^N) v s. ~(u = vec 0) /\ ~(v = vec 0) /\ &0 < s ==> 
	     arcV (vec 0) (s % u) v = arcV (vec 0) u v`,
	  REWRITE_TAC [REAL_ARITH `!x. &0 < x <=> ~(&0 = x) /\ &0 <= x`] THEN
		REWRITE_TAC [GSYM NORM_POS_LT] THEN	REPEAT STRIP_TAC THEN 
		REWRITE
_TAC [CONV_RULE KEP_REAL3_CONV arcV; VECTOR_SUB_RZERO; DOT_LMUL;
		             NORM_MUL; GSYM REAL_MUL_ASSOC] THEN
		SUBGOAL_TAC "norm_pos" `&0 < norm (u:real^N) * norm (v:real^N)`
		 [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC []] THEN 
		SUBGOAL_TAC "norm_nonzero" `~(&0 = norm (u:real^N) * norm (v:real^N))` 
		 [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC] THEN
		SUBGOAL_TAC "stuff" `abs s = s`
		 [ASM_REWRITE_TAC [REAL_ABS_REFL]] THEN 
		ASM_SIMP_TAC [GSYM REAL_DIV_MUL2]);;
	
	let ARCV_SYM = prove
	 (`!(u:real^N) v w. arcV u v w = arcV u w v`,
	 REWRITE_TAC [CONV_RULE KEP_REAL3_CONV arcV; DOT_SYM; REAL_MUL_SYM]);;

  let ARCV_BILINEAR_R = prove
	 (`!(u:real^N) v s. ~(u = vec 0) /\ ~(v = vec 0) /\ &0 < s ==> 
	     arcV (vec 0) u (s % v) = arcV (vec 0) u v`,
		REPEAT STRIP_TAC THEN
		SUBGOAL_TAC "switch" `arcV (vec 0) (u:real^N) (s % v) = arcV (vec 0) (s % v)	u`
		 [REWRITE_TAC [ARCV_SYM]] THEN 
		POP_ASSUM SUBST1_TAC THEN ASM_SIMP_TAC [ARCV_BILINEAR_L; ARCV_SYM]);;

  
  prove
	 (`!u v. ~(u = vec 0) /\ ~(v = vec 0) ==>
	      arcV (vec 0) u v = 
			  arcV (vec 0) ((inv (norm u)) % u) ((inv (norm v)) % v)`,
		REPEAT STRIP_TAC THEN
		SUBGOAL_TAC "u" `&0 < inv (norm (u:real^3))`
		[ REPEAT (POP_ASSUM MP_TAC) THEN 
		  SIMP_TAC [GSYM NORM_POS_LT; REAL_LT_INV] ] THEN
		SUBGOAL_TAC "v" `&0 < inv (norm (v:real^3))`
		[ REPEAT (POP_ASSUM MP_TAC) THEN 
		  SIMP_TAC [GSYM NORM_POS_LT; REAL_LT_INV] ] THEN
		SUBGOAL_TAC "vv" `~(inv (norm v) % (v:real^3) = vec 0)` 
		[ ASM_REWRITE_TAC [VECTOR_MUL_EQ_0] THEN POP_ASSUM MP_TAC THEN 
		  REAL_ARITH_TAC ] THEN
    ASM_SIMP_TAC [ARCV_BILINEAR_L; ARCV_BILINEAR_R]);;

  prove
	 (`!v:real^N. ~(v = vec 0) ==> norm((inv (norm v)) % v) = &1`,
	  REWRITE_TAC [NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; GSYM NORM_POS_LT] THEN
		CONV_TAC REAL_FIELD);;
	
	prove
	 (`!v0 va vb vc. 
	    dihV v0 va vb vc = 
		  dihV (vec 0) (va - v0) (vb - v0) (vc - v0)`,
	  REWRITE_TAC [CONV_RULE KEP_REAL3_CONV dihV; VECTOR_SUB_RZERO]);;

  prove
	 (`!va vb vc s. ~(va = vec 0) /\ ~(vb = vec 0) /\ ~(vb = vec 0) /\ &0 < s ==> 
	     dihV (vec 0) (s % va) vb vc = dihV (vec 0) va vb vc`,
		REWRITE_TAC [REAL_ARITH `!x. &0 < x <=> ~(&0 = x) /\ &0 <= x`] THEN
		REWRITE_TAC [GSYM NORM_POS_LT] THEN	REPEAT STRIP_TAC THEN 
		REWRITE_TAC [CONV_RULE KEP_REAL3_CONV dihV; VECTOR_SUB_RZERO; DOT_LMUL;
		             DOT_RMUL; NORM_MUL; GSYM REAL_MUL_ASSOC; VECTOR_MUL_ASSOC] THEN
		let thm1 = 
			VECTOR_ARITH `!x v. (s * s * x) % (v:real^3) = (s pow 2) % (x % v)` in
		let thm2 =
			VECTOR_ARITH `!x v. (s * x * s) % (v:real^3) = (s pow 2) % (x % v)` in
		REWRITE_TAC [thm1; thm2; GSYM VECTOR_SUB_LDISTRIB]
		);;
	
  let COLLINEAR_TRANSLATE = prove 
	 (`collinear (s:real^N->bool) <=> collinear {v - v0 | v IN s}`,
	  REWRITE_TAC [collinear; IN_ELIM_THM] THEN EQ_TAC THEN STRIP_TAC THEN
		EXISTS_TAC `u :real^N` THEN REPEAT STRIP_TAC THENL 
		[ ASM_SIMP_TAC [VECTOR_ARITH `!u:real^N v w. u - w - (v - w) = u - v`] ;
		  ONCE_REWRITE_TAC [VECTOR_ARITH `x:real^N - y = (x - v0) - (y - v0)`] THEN
		  SUBGOAL_THEN
			  `(?v:real^N. v IN s /\ x - v0 = v - v0) /\
				 (?v. v IN s /\ y - v0 = v - v0)`
	      (fun th -> ASM_SIMP_TAC [th]) THEN 
			STRIP_TAC THENL [EXISTS_TAC `x:real^N`; EXISTS_TAC `y:real^N`] THEN
			ASM_REWRITE_TAC [] ]);;

	let SET_MAP_3 = prove 
	 (`{f x | x IN {a, b, c}} = {f a, f b, f c}`,
	  REWRITE_TAC [EXTENSION; IN_ELIM_THM; 
		             SET_RULE `x IN {a, b, c} <=> (x = a \/ x = b \/ x = c)`] THEN
		MESON_TAC []);;
	
	let COLLINEAR_TRANSLATE_3 = prove 
	 (`collinear {u:real^N, v, w} <=> collinear {u - v0, v - v0, w - v0}`,
	  SUBGOAL_TAC "step1"
		  `collinear {u:real^N, v, w} <=> collinear {x - v0 | x IN {u, v, w}}`
		  [ REWRITE_TAC [GSYM COLLINEAR_TRANSLATE] ] THEN
		SUBGOAL_TAC "step2"
		  `{x - v0 | x:real^N IN {u, v, w}} = {u - v0, v - v0, w - v0}`
			[ REWRITE_TAC [SET_MAP_3] ] THEN
		ASM_REWRITE_TAC [] );;

	let COLLINEAR_ZERO = prove 
	 (`collinear {u:real^N, v, w} <=> collinear {vec 0, v - u, w - u}`,
	  SUBGOAL_TAC "zero"
		  `vec 0 :real^N = u - u`
			[ REWRITE_TAC [VECTOR_SUB_REFL] ] THEN
		ASM_REWRITE_TAC [GSYM COLLINEAR_TRANSLATE_3]);;

  let COLLINEAR_SYM = prove
	 (`collinear {vec 0: real^N, x, y} <=> collinear {vec 0: real^N, y, x}`,
	  AP_TERM_TAC THEN SET_TAC [] );;

  let COLLINEAR_FACT = prove 
	 (`collinear {vec 0: real^N, x, y} <=> 
	   ((y dot y) % x = (x dot y) % y)`,
		ONCE_REWRITE_TAC [COLLINEAR_SYM] THEN EQ_TAC THENL 
		[ REWRITE_TAC [COLLINEAR_LEMMA] THEN STRIP_TAC THEN
		  ASM_REWRITE_TAC [DOT_LZERO; DOT_RZERO; VECTOR_MUL_LZERO; 
		                   VECTOR_MUL_RZERO; VECTOR_MUL_ASSOC; 
											 DOT_LMUL; REAL_MUL_SYM];
			REWRITE_TAC [COLLINEAR_LEMMA;
			             TAUT `A \/ B \/ C <=> ((~A /\ ~B) ==> C)`] THEN 
			REPEAT STRIP_TAC THEN EXISTS_TAC `(x:real^N dot y) / (y dot y)` THEN
			MATCH_MP_TAC 
			  (ISPECL [`y:real^N dot y`;`x:real^N`] VECTOR_MUL_LCANCEL_IMP) THEN
			SUBGOAL_TAC "zero"
			  `~((y:real^N) dot y = &0)` [ ASM_REWRITE_TAC [DOT_EQ_0] ] THEN
			ASM_SIMP_TAC [VECTOR_MUL_ASSOC; REAL_DIV_LMUL] ] );;
	  

  let COLLINEAR_NOT_ZERO = prove 
	 (`~collinear {u:real^N, v, w} ==> ~(vec 0 = v - u) /\ ~(vec 0 = w - u)`,
	  ONCE_REWRITE_TAC [COLLINEAR_ZERO] THEN REWRITE_TAC [COLLINEAR_LEMMA] THEN 
		MESON_TAC [] );;

	let COS_ARCV = prove
	 (`~(vec 0 = u:real^3) /\ ~(vec 0 = v) ==>
	   cos (arcV (vec 0) u v)	= (u dot v) / (norm u * norm v)`,
		REWRITE_TAC [DOT_COS; 
		             MESON [NORM_EQ_0] `!v. vec 0 = v <=> norm v = &0`]	THEN
	  CONV_TAC REAL_FIELD);;

		
	prove
	 (`~(collinear {v0:real^3,va,vc}) /\ ~(collinear {v0,vb,vc}) ==>
    (let gamma = dihV v0 vc va vb in
     let a = arcV v0 vb vc in
     let b = arcV v0 va vc in
     let c = arcV v0 va vb in
       cos(gamma) pow 2 = ((cos(c) - cos(a)*cos(b))/(sin(a)*sin(b))) pow 2)`,			

module Trig : Trigsig = struct

  let trigAxiomProofA a_t = prove(a_t,
      (MP_TAC trig_term) THEN (REWRITE_TAC[trig_term_list]) THEN 
      (DISCH_THEN (fun t-> ASM_REWRITE_TAC[t]))
      )
  let trigAxiomProofB a_t = prove(a_t,
      (MP_TAC trig_term) THEN (REWRITE_TAC[trig_term_list]) THEN 
      (REPEAT STRIP_TAC)
      )

		sin (arcV v0 vb vc) = 
		norm (((vc - v0) dot (vc - v0)) % (va - v0) -
          ((va - v0) dot (vc - v0)) % (vc - v0))
		
		cos (arcV v0 va vb) = 
																												
																																															  
  prove
	 (spherical_loc_t,
	  REWRITE_TAC [COLLINEAR_ZERO ;COLLINEAR_FACT] THEN 
		ONCE_REWRITE_TAC [VECTOR_ARITH `a = b <=> vec 0 = a - b`] THEN 
		REPEAT STRIP_TAC THEN 
		REPEAT (CONV_TAC let_CONV) THEN 
		REWRITE_TAC [CONV_RULE KEP_REAL3_CONV dihV] THEN
		ASM_SIMP_TAC [COS_ARCV ; COLLINEAR_NOT_ZERO]

***)


	(* yet unproven theorems:

module Trig : Trigsig = struct

  let trigAxiomProofA a_t = prove(a_t,
      (MP_TAC trig_term) THEN (REWRITE_TAC[trig_term_list]) THEN 
      (DISCH_THEN (fun t-> ASM_REWRITE_TAC[t]))
      )
  let trigAxiomProofB a_t = prove(a_t,
      (MP_TAC trig_term) THEN (REWRITE_TAC[trig_term_list]) THEN 
      (REPEAT STRIP_TAC)
      )
	
  let  spherical_loc = trigAxiomProofB   spherical_loc_t 
  let  spherical_loc2 = trigAxiomProofB   spherical_loc2_t 
  let  dih_formula = trigAxiomProofB   dih_formula_t 
  let  dih_x_acs = trigAxiomProofB   dih_x_acs_t 
  let  beta_cone = trigAxiomProofB   beta_cone_t 
  let  euler_triangle = trigAxiomProofB   euler_triangle_t 
  let  polar_cycle_rotate = trigAxiomProofB   polar_cycle_rotate_t 
  let  thetaij = trigAxiomProofB   thetaij_t 
  let  thetapq_wind = trigAxiomProofB   thetapq_wind_t 
  let  zenith = trigAxiomProofB   zenith_t 
  let  polar_coord_zenith = trigAxiomProofB   polar_coord_zenith_t 
  let  azim_pair = trigAxiomProofB   azim_pair_t 
  let  azim_cycle_sum = trigAxiomProofB   azim_cycle_sum_t 
  let  dih_azim = trigAxiomProofB   dih_azim_t 
  let  sph_triangle_ineq = trigAxiomProofB   sph_triangle_ineq_t 
  let  sph_triangle_ineq_sum = trigAxiomProofB   sph_triangle_ineq_sum_t 
  let  azim = trigAxiomProofB   azim_t
	*)

(*  let  polar_coords = trigAxiomProofB   polar_coords_t  *)
(*  let  spherical_coord = trigAxiomProofB   spherical_coord_t *) 
(* [deprecated]
  let  aff_insert_sym = trigAxiomProofB   aff_insert_sym_t 
  let  aff_sgn_insert_sym_gt = trigAxiomProofB   aff_sgn_insert_sym_gt_t 
  let  aff_sgn_insert_sym_ge = trigAxiomProofB   aff_sgn_insert_sym_ge_t 
  let  aff_sgn_insert_sym_lt = trigAxiomProofB   aff_sgn_insert_sym_lt_t 
  let  aff_sgn_insert_sym_le = trigAxiomProofB   aff_sgn_insert_sym_le_t 
  let  azim_hyp = trigAxiomProofB   azim_hyp_t 
  let  azim_cycle_hyp = trigAxiomProofB   azim_cycle_hyp_t 
  let  aff = trigAxiomProofA   aff_t
  let  aff_gt = trigAxiomProofB   aff_gt_t
  let  aff_ge = trigAxiomProofB   aff_ge_t
  let  aff_lt = trigAxiomProofB   aff_lt_t
  let  aff_le = trigAxiomProofB   aff_le_t
  let  azim_cycle = trigAxiomProofB   azim_cycle_t
*)

end;;



