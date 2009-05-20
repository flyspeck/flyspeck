(* Formal Spec of Blueprint Chapter  on Trigonometry *)

needs "Multivariate/vectors.ml";;    (* Eventually should load entire   *) 
                                     (* multivariate-complex theory.    *)
needs "Examples/transc.ml";;         (* Then it won't need these. *) 
needs "definitions_kepler.ml";;

prioritize_real();;


(* sin and cos have already been defined in HOL Light.
   Here are several relevant theorems from HOL Light.  *)
sin;;
cos;;
DIFF_SIN;; (* derivative of sin is cos *)
DIFF_COS;; (* derivative of cos is -sin *)
SIN_0;; (* sin(0) = 0 *)
COS_0;; (* cos(0) =1 *)
SIN_CIRCLE;; (* blueprint/lemma:circle *)

SIN_ADD;; (* blueprint/lemma:sin-add *)
COS_ADD;; (* blueprint/lemma:sin-add *)

COS_NEG;; (* blueprint/lemma:cos-neg *)
SIN_NEG;; (* blueprint/lemma:cos-neg *)

SIN_PI2;; (* blueprint/lemma:sin-pi2 *)
COS_SIN;; (* blueprint/lemma:cos-sin *)

tan;; (* blueprint/def:tan *)
TAN_ADD;; (* blueprint/lemma:tan-add *)
TAN_PI4;; (* blueprint/tan-pi4 *)

atn;; (* blueprint/def:arctan *)
acs;; (* blueprint/def:acs *)
asn;; (* blueprint/def:arcsin *)

(* arctan2 function *)
atn2;;  (* definitions_kepler.ml *)

(* This is close to CIRCLE_SINCOS *)

let atn2_spec_t = `!x y. ?r. ((-- pi < atn2(x, y)) /\ (atn2(x,y) <= pi) /\
     (x = r* (cos(atn2(x,y)))) /\ (y = r* (sin (atn2( x, y)))) /\ 
     (&0 <= r))`;;

(* lemma:sin-arccos *)

let sin_acs_t = `!y. (-- &1 <= y /\ y <= &1) ==> (sin (acs(y)) = sqrt(&1 - y pow 2))`;;

(* lemma:arccos-arctan *)

let acs_atn2_t = `!y. (-- &1 <= y /\ y <=  &1) ==> (acs y = pi/(&2) - atn2(sqrt(&1 - y pow 2),y))`;;


(* Jordan/metric_spaces.ml:cauchy_schwartz  cauchy_schwartz *)
(* Jordan/metric_spaces.ml:norm_triangle    triangle inequality *)

(* affine geometry definitions are in definitions_kepler.ml *)

let arcVarc_t = `!u v w:real^3. ~(u=v) /\ ~(u=w) ==> arcV u v w = arclength (dist( u, v)) (dist( u, w)) (dist( v, w))`;;

let law_of_cosines_t = `!a b c. (&0 < a) /\ (&0 < b) /\ (&0 <= c) /\ (c <= a + b) /\ (a <= b + c) /\ (b <= c + a) ==>
   ((c pow 2) = (a pow 2) + (b pow 2) - &2 * a * b * (cos(arclength a b c)))`;;

let law_of_sines_t = `!a b c. (&0 < a) /\ (&0 < b) /\ (&0 <= c) /\ (c <= a + b) /\ (a <= b + c) /\ (b <= c + a) ==>
   (&2 * a * b * sin (arclength a b c) = sqrt(ups_x (a pow 2) (b pow 2) (c pow 2)))`;;

let cross_mag_t = `!u v. norm (cross u v) = (norm u) * (norm v) * sin(arcV (vec 0) u v)`;;

let cross_skew_t = `!u v. (cross u v) = -- (cross v u)`;;

let cross_triple_t = `!u v w.  (cross u v) dot w =  (cross v w) dot u`;;


(* law of cosines *)

let spherical_loc_t = `!v0 va vb vc:real^3.
  ~(collinear {v0,va,vc}) /\ ~(collinear {v0,vb,vc}) ==>
        (
    let gamma = dihV v0 vc va vb in
    let a = arcV v0 vb vc in
    let b = arcV v0 va vc in
    let c = arcV v0 va vb in
      (cos(gamma) = (cos(c) - cos(a)*cos(b))/(sin(a)*sin(b))))`;;

let spherical_loc2_t = `!v0 va vb vc:real^3.
 ~(collinear {v0,va,vc}) /\ ~(collinear {v0,vb,vc}) ==>
        (
    let alpha = dihV v0 va vb vc in
    let beta = dihV v0 vb va vc in
    let gamma = dihV v0 vc vb va in
    let c = arcV v0 va vb in
      (cos(c) = (cos(gamma) + cos(alpha)*cos(beta))/(sin(alpha)*sin(beta))))`;;

let dih_formula_t = `!v0 v1 v2 v3:real^3. 
   ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) ==>
   (
   let (x1,x2,x3,x4,x5,x6) = xlist v0 v1 v2 v3 in
    (dihV v0 v1 v2 v3  = dih_x x1 x2 x3 x4 x5 x6)
   )`;;

let dih_x_acs_t = `!x1 x2 x3 x4 x5 x6.
   (&0 < ups_x x1 x2 x6) /\ (&0 < ups_x x1 x3 x5) /\ (&0 <= delta_x x1 x2 x3 x4 x5 x6) /\ (&0 <= x1) ==>
   dih_x x1 x2 x3 x4 x5 x6 = acs ((delta_x4 x1 x2 x3 x4 x5 x6)/
  ((sqrt (ups_x x1 x2 x6)) * (sqrt (ups_x x1 x3 x5))))`;;

let beta_cone_t = `!v0 v1 v2 v3:real^3.
    ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) /\ 
    (dihV v0 v3 v1 v2 = pi/(&2)) ==>
    (dihV v0 v1 v2 v3 = beta (arcV v0 v1 v3) (arcV v0 v1 v2))`;;

let euler_triangle_t = `!v0 v1 v2 v3:real^3. 
    let p = euler_p v0 v1 v2 v3 in
    let (x1,x2,x3,x4,x5,x6) = xlist v0 v1 v2 v3 in
    let alpha1 = dihV v0 v1 v2 v3 in
    let alpha2 = dihV v0 v2 v3 v1 in
    let alpha3 = dihV v0 v3 v1 v2 in
    let d = delta_x x1 x2 x3 x4 x5 x6 in
    ((&0 < d) ==>
      (alpha1 + alpha2 + alpha3 - pi = pi - &2 * atn2(sqrt(d), (&2 * p))))`;;

let polar_coords_t = `!x y. (x = (radius x y)*(cos(polar_angle x y))) /\
     (y = (radius x y)*(sin(polar_angle x y)))`;;

let polar_cycle_rotate_t = `!V psi u f.
       (!x y. f (x,y) = (x*cos psi + y*sin psi, -- x*sin psi + y*cos psi)) /\
       FINITE V  /\ V u ==>
       (polar_cycle (IMAGE f V) (f u) =  f (polar_cycle V u))`;;

let thetaij_t = `!theta1 theta2 k12 k21 theta12 theta21.
     (&0 <= theta1) /\ (theta1 < &2 * pi) /\ (&0 <= theta2) /\ (theta2 < &2 * pi) /\
     (theta12 = theta2 - theta1 + &2 * pi * (&k12)) /\
     (theta21 = theta1 - theta2 + &2 * pi * (&k21)) /\
     (&0 <= theta12) /\ (theta12 < &2 * pi) /\
     (&0 <= theta21) /\ (theta21 < &2 * pi) ==>
     ((theta12+theta21) = (if (theta1=theta2) then (&0) else (&2 * pi)))`;;


let thetapq_wind_t = `!W n thetapq kpq. 
    (!x y. (W (x,y) ==> (~(x= &0) /\ ~(y = &0)))) /\
    (W HAS_SIZE n) /\
    (!u v. W u /\ W v ==> 
       ((thetapq u v = polar_angle (FST v) (SND v) -  polar_angle (FST u) (SND u) + &2 * pi * kpq u v) /\  (&0 <= thetapq u v) /\ (thetapq u v < &2 * pi)))
    ==>
    ((!u i j. (W u /\ (0 <= i) /\ (i <= j) /\ (j < n)) ==>
        thetapq u (iter i (polar_cycle W) u) + thetapq (iter i (polar_cycle W) u) (iter j (polar_cycle W) u) = thetapq u (iter j (polar_cycle W) u)) /\
    ((!u v.  (W u /\ W v) ==> (polar_angle (FST u) (SND u) = polar_angle (FST v) (SND v))) \/
     (!u. (W u)  ==> (sum(0,n) (\i. thetapq (iter i (polar_cycle W) u) (iter (SUC i) (polar_cycle W) u))  = &2 * pi)) ))`;;

let zenith_t = `!u v w:real^3.  ~(u=v) /\ ~(w = v)  ==>
   (?u' r phi e3.
        (phi = arcV v u w) /\ (r = dist( u, v)) /\ ((dist( w, v)) % e3 = (w-v)) /\
  ( u' dot e3 = &0) /\ (u = v + u' + (r*cos(phi)) % e3))`;;

let spherical_coord_t = `!u v w u' e1 e2 e3 r phi theta.
        ~(collinear {v,w,u}) /\ ~(collinear {v,w,u'}) /\
       orthonormal e1 e2 e3 /\ ((dist( v, w)) % e3 = (v-w)) /\
  (aff_gt {v,w} {u} e1) /\ (e2 = cross e3 e1) /\
  (r = dist( v, u')) /\ (phi = arcV v u' w) /\ (theta = azim v w u u') ==>
  (u' = u + (r*cos(theta)*sin(phi)) % e1 + (r*sin(theta)*sin(phi)) % e2 
      + (r * cos(phi)) % e3)`;;

let polar_coord_zenith_t = `!u v w u' n.
  ~(collinear {u,v,w}) /\ (aff {u,v,w} u') /\ ~(u' = v) /\
  (n = cross (w - v) (u - v)) ==>
   (arcV v (v + n) u' = pi/ (&2))`;;

let azim_pair_t = `!v w w1 w2.
    let a1 = azim v w w1 w2 in
    let a2 = azim v w w2 w1 in
    (cyclic_set {w1,w2} v w) ==> 
      (a1 + a2 = (if (a1 = &0) then (&0) else (&2 * pi)))`;;

let azim_cycle_sum_t = `!W v w n. 
   (cyclic_set W v w) /\
   (W HAS_SIZE n) ==>
   (!p i j. (W p /\ (0 <= i) /\ (i <= j) /\ (j < n)) ==> 
       ((!q.  W q ==> (azim v w p q = &0) ) \/
       (sum(0,n) (\i. azim v w (iter i (azim_cycle W v w) p) (iter (SUC i) (azim_cycle W v w) p)) = &2 * pi   )))`;;

let dih_azim_t = `!v w v1 v2. 
   ~(collinear {v,w,v1}) /\ ~(collinear {v,w,v2}) ==>
  (cos(azim v w v1 v2) = cos(dihV v w v1 v2))`;;

let sph_triangle_ineq_t = `!p u v w:real^3.
   ~(collinear {p,u,w}) /\ ~(collinear {p,u,v}) /\ ~(collinear {p,v,w}) ==>
  (arcV p u w <= arcV p u v + arcV p v w)`;;

let sph_triangle_ineq_sum_t = `!p:real^3 u r.
   (!i. (i < r) ==> ~(collinear {p,u i, u (SUC i)})) /\
   ~(collinear {p,u 0, u r}) ==>
   (arcV p (u 0) (u r) <= sum(0,r) (\i. arcV p (u i) (u (SUC i))))`;;

(* obligations created by definition by specification, to make them useable. *)

(* [deprecated]
let aff_insert_sym_t = `aff_insert_sym`;;
let aff_sgn_insert_sym_gt_t = `aff_sgn_insert_sym (\t. &0 < t)`;;
let aff_sgn_insert_sym_ge_t = `aff_sgn_insert_sym (\t. &0 <= t)`;;
let aff_sgn_insert_sym_lt_t = `aff_sgn_insert_sym (\t. t < &0)`;;
let aff_sgn_insert_sym_le_t = `aff_sgn_insert_sym (\t. t <= &0)`;;
*)

let azim_hyp_t = `azim_hyp`;;
let azim_cycle_hyp_t = `azim_cycle_hyp`;;

(* definitions without obligations *)

(* [deprecated]
let aff_t = `(aff {} = {}) /\
         (!v S.
              FINITE S
              ==> aff (v INSERT S) =
                  (if v IN S then aff S else aff_insert v (aff S)))`;;

let aff_gt_t = `!S1.
          (aff_gt S1 {} = aff S1) /\
             (!v S.
                  FINITE S
                  ==> aff_gt S1 (v INSERT S) =
                      (if v IN S
                       then aff_gt S1 S
                       else aff_sgn_insert (\t. &0 < t) v (aff_gt S1 S)))`;;

let aff_ge_t = `!S1.
          (aff_ge S1 {} = aff S1) /\
             (!v S.
                  FINITE S
                  ==> aff_ge S1 (v INSERT S) =
                      (if v IN S
                       then aff_ge S1 S
                       else aff_sgn_insert (\t. &0 <= t) v (aff_ge S1 S)))`;;

let aff_lt_t = `!S1.
          (aff_lt S1 {} = aff S1) /\
             (!v S.
                  FINITE S
                  ==> aff_lt S1 (v INSERT S) =
                      (if v IN S
                       then aff_lt S1 S
                       else aff_sgn_insert (\t. t < &0) v (aff_lt S1 S)))`;;

let aff_le_t = `!S1.
          (aff_le S1 {} = aff S1) /\
             (!v S.
                  FINITE S
                  ==> aff_le S1 (v INSERT S) =
                      (if v IN S
                       then aff_le S1 S
                       else aff_sgn_insert (\t. t <= &0) v (aff_le S1 S)))`;;
*)

let azim_t = `!v w w1 w2 e1 e2 e3.
         ?psi h1 h2 r1 r2.
                 ~collinear {v, w, w1} /\
                 ~collinear {v, w, w2} /\
                 orthonormal e1 e2 e3 /\
                 (dist( w, v) % e3 = w - v)
             ==> &0 <= azim v w w1 w2 /\
                 azim v w w1 w2 < &2 * pi /\
                 &0 < r1 /\
                 &0 < r2 /\
                 w1 =
                 (r1 * cos psi) % e1 + (r1 * sin psi) % e2 + h1 % (w - v) /\
                 (w2 =
                 (r2 * cos (psi + azim v w w1 w2)) % e1 +
                 (r2 * sin (psi + azim v w w1 w2)) % e2 +
                 h2 % (w - v))`;;

let azim_cycle_t = `!W proj v w e1 e2 e3 p.
             W p /\
             cyclic_set W v w /\
             (dist( v, w) % e3 = w - v) /\
             orthonormal e1 e2 e3 /\
             (!u x y.
                  proj u = x,y <=> (?h. u = v + x % e1 + y % e2 + h % e3))
         ==> (proj (azim_cycle W v w p) = polar_cycle (IMAGE proj W) (proj p))`;;


(* signature for trig theorems.
   This is the list of theorems that should be provided by
   an implementation of the blueprint on trig.
   The signature can be extended, but care needs to made
   in removing anything, because it may create incompatibilities
   with other pieces of code. *)

(* In every case, there is a term giving the precise theorem to
   be proved *)


module type Trigsig = sig
  val atn2_spec : thm (* atn2_spec_t  *)
  val sin_acs : thm (* sin_acs_t *)
  val acs_atn2: thm  (* acs_atn2_t *)
  val arcVarc : thm (*  arcVarc_t *)
  val law_of_cosines : thm (*  law_of_cosines_t *)
  val law_of_sines : thm (*  law_of_sines_t *)
  val cross_mag : thm (*  cross_mag_t *)
  val cross_skew : thm (*  cross_skew_t *)
  val cross_triple : thm (*  cross_triple_t *)
  val spherical_loc : thm (*  spherical_loc_t *)
  val spherical_loc2 : thm (*  spherical_loc2_t *)
  val dih_formula : thm (*  dih_formula_t *)
  val dih_x_acs : thm (*  dih_x_acs_t *)
  val beta_cone : thm (*  beta_cone_t *)
  val euler_triangle : thm (*  euler_triangle_t *)
  val polar_coords : thm (*  polar_coords_t *)
  val polar_cycle_rotate : thm (*  polar_cycle_rotate_t *)
  val thetaij : thm (*  thetaij_t *)
  val thetapq_wind : thm (*  thetapq_wind_t *)
  val zenith : thm (*  zenith_t *)
  val spherical_coord : thm (*  spherical_coord_t *)
  val polar_coord_zenith : thm (*  polar_coord_zenith_t *)
  val azim_pair : thm (*  azim_pair_t *)
  val azim_cycle_sum : thm (*  azim_cycle_sum_t *)
  val dih_azim : thm (*  dih_azim_t *)
  val sph_triangle_ineq : thm (*  sph_triangle_ineq_t *)
  val sph_triangle_ineq_sum : thm (*  sph_triangle_ineq_sum_t *)
(* [deprecated]
  val aff_insert_sym : thm (*  aff_insert_sym_t *)  
  val aff_sgn_insert_sym_gt : thm (*  aff_sgn_insert_sym_gt_t *)
  val aff_sgn_insert_sym_ge : thm (*  aff_sgn_insert_sym_ge_t *)
  val aff_sgn_insert_sym_lt : thm (*  aff_sgn_insert_sym_lt_t *)
  val aff_sgn_insert_sym_le : thm (*  aff_sgn_insert_sym_le_t *)
*)
  val azim_hyp : thm (*  azim_hyp_t *)
  val azim_cycle_hyp : thm (*  azim_cycle_hyp_t *)
(* [deprecated]
  val aff : thm (* aff_t *)
  val aff_gt : thm (*  aff_gt_t   *)
  val aff_ge : thm (*  aff_ge_t   *)
  val aff_lt : thm (*  aff_lt_t   *)
  val aff_le : thm (*  aff_le_t   *)
*)
  val azim : thm (*  azim_t   *)
  val azim_cycle : thm (*  azim_cycle_t   *)
end;;

(* Here is a single axiom that permits a quick implementation of the
   module with the given signature.
   The axiom can be used so that the proofs in different chapters can
   proceed independently.  *)

let trig_axiom_list = new_definition (mk_eq (`trig_axiom:bool`, (list_mk_conj
   [
 atn2_spec_t  ;
 sin_acs_t ;
 acs_atn2_t ;
  arcVarc_t ;
  law_of_cosines_t ;
  law_of_sines_t ;
  cross_mag_t ;
  cross_skew_t ;
  cross_triple_t ;
  spherical_loc_t ;
  spherical_loc2_t ;
  dih_formula_t ;
  dih_x_acs_t ;
  beta_cone_t ;
  euler_triangle_t ;
  polar_coords_t ;
  polar_cycle_rotate_t ;
  thetaij_t ;
  thetapq_wind_t ;
  zenith_t ;
  spherical_coord_t ;
  polar_coord_zenith_t ;
  azim_pair_t ;
  azim_cycle_sum_t ;
  dih_azim_t ;
  sph_triangle_ineq_t ;
  sph_triangle_ineq_sum_t ;
(* [deprecated]
  aff_insert_sym_t ;
  aff_sgn_insert_sym_gt_t ;
  aff_sgn_insert_sym_ge_t ;
  aff_sgn_insert_sym_lt_t ;
  aff_sgn_insert_sym_le_t ;
*)
  azim_hyp_t ;
  azim_cycle_hyp_t ;
(* [deprecated]
  aff_t;
  aff_gt_t;
  aff_ge_t;
  aff_lt_t;
  aff_le_t;
*)
  azim_t;
  azim_cycle_t;
   ])));;

(* partial implementation of  Trigsig *)

let trig_axiom = new_axiom `trig_axiom`;; 

module Trig : Trigsig = struct

  let trigAxiomProofA a_t = prove(a_t,
      (MP_TAC trig_axiom) THEN (REWRITE_TAC[trig_axiom_list]) THEN 
      (DISCH_THEN (fun t-> ASM_REWRITE_TAC[t]))
      )
  let trigAxiomProofB a_t = prove(a_t,
      (MP_TAC trig_axiom) THEN (REWRITE_TAC[trig_axiom_list]) THEN 
      (REPEAT STRIP_TAC)
      )
  
  (* ---------------------------------------------------------------------- *)
  (* Useful theorems about real numbers.                                    *)
  (* ---------------------------------------------------------------------- *)
  
  let REAL_LT_MUL_3 = prove
   (`!x y z. &0 < x /\ &0 < y /\ &0 < z ==> &0 < x * y * z`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC []);;

  let SQRT_MUL_L = prove
   (`!x y. &0 <= x /\ &0 <= y ==> x * sqrt y = sqrt(x pow 2 * y)`,
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [REAL_LE_POW_2; SQRT_MUL; POW_2_SQRT]);;

  let SQRT_MUL_R = prove
   (`!x y. &0 <= x /\ &0 <= y ==> sqrt x * y = sqrt(x * y pow 2)`,
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [REAL_LE_POW_2; SQRT_MUL; POW_2_SQRT]);;

  (* ABS_SQUARE_LE_1 is in HOL-Light Multivariate/transc.ml.  *)
  (* Proof by John Harrison. *)

  let ABS_SQUARE_LE_1 = prove
   (`!x. x pow 2 <= &1 <=> abs(x) <= &1`,
    ONCE_REWRITE_TAC[GSYM REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_LT_SQUARE_ABS; GSYM REAL_NOT_LT] THEN REAL_ARITH_TAC);;

  
  (* ---------------------------------------------------------------------- *)
  (* Basic trig results not included in Examples/transc.ml                  *)
  (* ---------------------------------------------------------------------- *)
  
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
  
  (* Next two proofs similar to TAN_PERIODIC_NPI in *)
  (* Examples/transc.ml by John Harrison *)
  
  let SIN_PERIODIC_N2PI = prove
   (`!x n. sin(x + &n * (&2 * pi)) = sin(x)`,
    GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    ASM_REWRITE_TAC[REAL_ADD_ASSOC; SIN_PERIODIC]);;
  
  let COS_PERIODIC_N2PI = prove
   (`!x n. cos(x + &n * (&2 * pi)) = cos(x)`,
    GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    ASM_REWRITE_TAC[REAL_ADD_ASSOC; COS_PERIODIC]);;

  let TWOPI_POS = prove (`&0 < &2 * pi`, MP_TAC PI_POS THEN REAL_ARITH_TAC);;
  
  let CIRCLE_SINCOS_PI_LEMMA = prove
   (`!x y. (x pow 2 + y pow 2 = &1) ==> 
       ?t. (--pi <= t /\ t <= pi) /\ ((x = cos(t)) /\ (y = sin(t)))`,
    REPEAT STRIP_TAC THEN IMP_RES_THEN STRIP_ASSUME_TAC CIRCLE_SINCOS THEN
    STRIP_ASSUME_TAC (REWRITE_RULE [TWOPI_POS] 
    (SPECL [`--pi`;`&2 * pi`;`t:real`] arith_lemma)) THEN EXISTS_TAC `y':real` THEN 
    STRIP_TAC THENL
    [ POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
      REAL_ARITH_TAC ;
      ASM_REWRITE_TAC [COS_PERIODIC_N2PI; SIN_PERIODIC_N2PI] ;
      POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
      REAL_ARITH_TAC ;
      ASM_REWRITE_TAC [COS_PERIODIC_N2PI; SIN_PERIODIC_N2PI] ]);;
    
  let CIRCLE_SINCOS_PI = prove
   (`!x y. (x pow 2 + y pow 2 = &1) ==> 
       ?t. (--pi < t /\ t <= pi) /\ ((x = cos(t)) /\ (y = sin(t)))`,
    REPEAT STRIP_TAC THEN IMP_RES_THEN STRIP_ASSUME_TAC CIRCLE_SINCOS_PI_LEMMA 
    THEN FIND_ASSUM (DISJ_CASES_TAC o (REWRITE_RULE [REAL_LE_LT])) `--pi <= t`
    THENL
    [ EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC [];
      EXISTS_TAC `pi:real` THEN POP_ASSUM (ASSUME_TAC o GSYM) THEN
      ASM_REWRITE_TAC [SIN_NEG; COS_NEG; SIN_PI] THEN MP_TAC PI_POS THEN
      REAL_ARITH_TAC ]);; 
  
  let SIN_NEGPOS_PI = prove 
   (`!x. (--pi < x /\ x <= pi) ==>
         (sin x < &0 <=> --pi < x /\ x < &0) /\
         (sin x = &0 <=> (x = &0 \/ x = pi)) /\
         (&0 < sin x <=> &0 < x /\ x < pi)`,
    STRIP_TAC THEN STRIP_TAC THEN SUBGOAL_THEN
      `if (sin x < &0) then (sin x < &0 <=> --pi < x /\ x < &0) else
       if (sin x = &0) then (sin x = &0 <=> (x = &0 \/ x = pi)) else
       (&0 < sin x <=> &0 < x /\ x < pi)` MP_TAC THENL
    [ SUBGOAL_TAC "a" `--pi < x /\ x < &0 ==> sin x < &0`
      [ MP_TAC (REWRITE_RULE [SIN_NEG] (SPEC `--x:real` SIN_POS_PI)) THEN
        REAL_ARITH_TAC ] THEN
      SUBGOAL_TAC "b" `x = &0 ==> sin x = &0`
      [ STRIP_TAC THEN ASM_REWRITE_TAC [SIN_0] ] THEN
      SUBGOAL_TAC "c" `x = pi ==> sin x = &0`
      [ STRIP_TAC THEN ASM_REWRITE_TAC [SIN_PI] ] THEN
      LABEL_TAC "d" (SPEC `x:real` SIN_POS_PI) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
      REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC ]);;

  let COS_NEGPOS_PI = prove
   (`!x. (--pi < x /\ x <= pi) ==>
         (cos x < &0 <=> (--pi < x /\ x < --(pi / &2)) \/ 
                         (pi / &2 < x /\ x <= pi)) /\
         (cos x = &0 <=> (x = --(pi / &2) \/ x = pi / &2)) /\
         (&0 < cos x <=> --(pi / &2) < x /\ x < pi / &2)`,
    STRIP_TAC THEN STRIP_TAC THEN SUBGOAL_THEN
      `if (cos x < &0) then (cos x < &0 <=> (--pi < x /\ x < --(pi / &2)) \/ 
                            (pi / &2 < x /\ x <= pi)) else
       if (cos x = &0) then 
       (cos x = &0 <=> (x = --(pi / &2) \/ x = pi / &2)) else
       (&0 < cos x <=> --(pi / &2) < x /\ x < pi / &2)` MP_TAC THENL
    [ SUBGOAL_TAC "a" `--pi < x /\ x < --(pi / &2) ==> cos x < &0`
      [ MP_TAC (REWRITE_RULE [COS_PERIODIC_PI] 
               (SPEC `x + pi:real` COS_POS_PI2)) THEN
        REAL_ARITH_TAC ] THEN
      SUBGOAL_TAC "b" `pi / &2 < x /\ x <= pi ==> cos x < &0`
      [ MP_TAC (REWRITE_RULE [SIN_NEG; GSYM COS_SIN] 
               (SPEC `--(pi / &2 - x)` SIN_POS_PI2)) THEN
        SUBGOAL_TAC "b1" `x = pi ==> cos x < &0` 
        [ STRIP_TAC THEN ASM_REWRITE_TAC [COS_PI; REAL_ARITH `&0 < &1`] THEN
          REAL_ARITH_TAC ] THEN
        POP_ASSUM MP_TAC THEN REAL_ARITH_TAC ] THEN
      SUBGOAL_TAC "c" `x = --(pi / &2) ==> cos x = &0`
      [ STRIP_TAC THEN ASM_REWRITE_TAC [COS_NEG; COS_PI2] ] THEN
      SUBGOAL_TAC "d" `x = pi / &2 ==> cos x = &0`
      [ STRIP_TAC THEN ASM_REWRITE_TAC [COS_PI2] ] THEN
      LABEL_TAC "e" (SPEC `x:real` COS_POS_PI) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
      REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC ]);;
  
  (* PI_POS_LE is in Multivariate/transc.ml. Proof by John Harrison *)
  
  let PI_POS_LE = prove
   (`&0 <= pi`,
    REWRITE_TAC[REAL_LE_LT; PI_POS]);;
    
  (* Note that if you ever switch to Multivariate/transc that ACS_COS is    *)
  (* COS_ACS, but ACS_1 and ACS_NEG1 already exist in Multivariate/transc.  *)
  (* Proofs same as or adapted from John Harision's.                        *)
  
  let ACS_1 = prove
   (`acs(&1) = &0`,
    REWRITE_TAC [GSYM COS_0] THEN 
    ASM_SIMP_TAC [REAL_ARITH `&0 <= &0`; PI_POS_LE; COS_ACS]);;
    
  let ACS_NEG_1 = prove
   (`acs(-- &1) = pi`,    
    REWRITE_TAC [GSYM COS_PI] THEN 
    ASM_SIMP_TAC [REAL_ARITH `pi <= pi`; PI_POS_LE; COS_ACS]);;

  (* lemma:sin_acs *)
  
  (* SQRT_UNIQUE is in HOL-Light Multivariate/transc.ml.  *)
  (* Proof adapted from John Harrison's. *)
  
  let SQRT_UNIQUE = prove
   (`!x y. &0 <= y /\ (y pow 2 = x) ==> (sqrt(x) = y)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[sqrt_def] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_POW_2] THEN
    REWRITE_TAC[REAL_ARITH `(x * x = y * y) <=> ((x + y) * (x - y) = &0)`] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;
  
  (* Note that if you ever switch to Multivariate/transc that ACS_COS is     *)
  (* COS_ACS...but then SIN_ASC already exists in Multivariate/transc!       *)
    
  let sin_acs = prove
   (sin_acs_t,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(GSYM SQRT_UNIQUE) THEN
    ASM_SIMP_TAC[ACS_BOUNDS; SIN_POS_PI_LE; REAL_EQ_SUB_RADD] THEN
    ASM_MESON_TAC[ACS_COS; SIN_CIRCLE]);;

  (* ACS_ATN is in Multivariate/transc.ml *)
  (* Proof by John Harrison. *)
  
  let ACS_ATN = prove
   (`!x. -- &1 < x /\ x < &1 ==> 
         acs(x) = pi / &2 - atn(x / sqrt(&1 - x pow 2))`,
    STRIP_TAC THEN STRIP_TAC THEN ABBREV_TAC `y = acs(x)` THEN 
    ABBREV_TAC `z = atn(x / sqrt(&1 - x pow 2))` THEN 
    SUBGOAL_TAC "y_bounds" `--(pi / &2) < pi / &2 - y /\ pi / &2 - y < pi / &2`
    [ EXPAND_TAC "y" THEN MP_TAC (SPEC `x:real` ACS_BOUNDS_LT) THEN 
      ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC ] THEN
    SUBGOAL_TAC "z_bounds" `--(pi / &2) < z /\ z < pi / &2`
    [ EXPAND_TAC "z" THEN REWRITE_TAC [ATN_BOUNDS] ] THEN
    SUBGOAL_THEN `atn(tan(pi / &2 - y)) = atn(tan(z))` 
                 (fun th -> MP_TAC th THEN ASM_SIMP_TAC [TAN_ATN] THEN
                            REAL_ARITH_TAC) THEN
    AP_TERM_TAC THEN SUBGOAL_TAC "tan" `inv (tan y) =(cos y) / (sin y)`
    [ REWRITE_TAC [tan] THEN POP_ASSUM MP_TAC THEN 
      CONV_TAC REAL_FIELD ] THEN
    ASM_REWRITE_TAC [TAN_COT] THEN EXPAND_TAC "y" THEN EXPAND_TAC "z" THEN
    REWRITE_TAC [ATN_TAN] THEN POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_TAC "x_LE" `--(&1) <= x /\ x <= &1`
    [ POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC ] THEN
    ASM_SIMP_TAC [ACS_COS; sin_acs]);;
  
  (* ----------------------------------------------------------------------- *)
  (* Theory of atan_2 function. See definitions_kepler.ml for the definiton. *)
  (* ----------------------------------------------------------------------- *)
  
  (* lemma:atn2_spec *)
   
  let dist_lemma = prove
   (`!x y. ~(x = &0) \/ ~(y = &0) ==> 
      (x / sqrt(x pow 2 + y pow 2)) pow 2 +
      (y / sqrt(x pow 2 + y pow 2)) pow 2 = &1 /\
      &0 < sqrt(x pow 2 + y pow 2)`,
    STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
    SUBGOAL_TAC "sum_pos" `&0 < x pow 2 + y pow 2 /\ &0 <= x pow 2 + y pow 2`
    [ MP_TAC (SPEC `x:real` REAL_LE_POW_2) THEN 
      MP_TAC (SPEC `y:real` REAL_LE_POW_2) THEN
      IMP_RES_THEN MP_TAC (SPECL [`x:real`; `2`] REAL_POW_NZ) THEN 
      IMP_RES_THEN MP_TAC (SPECL [`y:real`; `2`] REAL_POW_NZ) THEN 
      REAL_ARITH_TAC ] THEN
    POP_ASSUM MP_TAC THEN STRIP_TAC THEN 
    ASM_SIMP_TAC [REAL_POW_DIV; SQRT_POW_2; SQRT_POS_LT] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    CONV_TAC REAL_FIELD);;
  
  let ATAN2_EXISTS = prove 
   (`!x y. ?t. (--pi < t /\ t <= pi) /\
         x = sqrt(x pow 2 + y pow 2) * cos t /\
         y = sqrt(x pow 2 + y pow 2) * sin t`,
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x = &0) /\ (y = &0)` THENL
    [ ASM_REWRITE_TAC [(SPEC `2` REAL_POW_ZERO)] THEN 
      NUM_REDUCE_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
      REWRITE_TAC [SQRT_0] THEN EXISTS_TAC `pi` THEN MP_TAC PI_POS THEN
      REAL_ARITH_TAC ;
      IMP_RES_THEN STRIP_ASSUME_TAC 
      (REWRITE_RULE [TAUT `(~A \/ ~B) <=> ~(A /\ B)`] dist_lemma) THEN
      IMP_RES_THEN STRIP_ASSUME_TAC CIRCLE_SINCOS_PI THEN 
      POP_ASSUM (MP_TAC o GSYM) THEN POP_ASSUM (MP_TAC o GSYM) THEN
      STRIP_TAC THEN STRIP_TAC THEN EXISTS_TAC `t:real` THEN 
      ASM_REWRITE_TAC [] THEN
      POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN 
      POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
      POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD ]);;
  
  (* The official Kepler definition (atn2) is different, but it was easier  *)
  (* to start with this one an prove it is equivalent.                      *)
  
  let ATAN2_TEMP_DEF = new_definition
    `atan2_temp (x,y) = if (x = &0 /\ y = &0) 
                        then pi 
                        else @t. (--pi < t /\ t <= pi) /\
                                 x = sqrt(x pow 2 + y pow 2) * cos t /\
                                 y = sqrt(x pow 2 + y pow 2) * sin t`;;
                     
  let ATAN2_TEMP = prove
   (`!x y. (--pi < atan2_temp (x,y) /\ atan2_temp (x,y) <= pi) /\
           x = sqrt(x pow 2 + y pow 2) * cos (atan2_temp (x,y)) /\
           y = sqrt(x pow 2 + y pow 2) * sin (atan2_temp (x,y))`,
    STRIP_TAC THEN STRIP_TAC THEN REWRITE_TAC [ATAN2_TEMP_DEF] THEN
    COND_CASES_TAC THENL
    [ ASM_REWRITE_TAC [(SPEC `2` REAL_POW_ZERO)] THEN 
      NUM_REDUCE_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
      REWRITE_TAC [SQRT_0] THEN MP_TAC PI_POS THEN
      REAL_ARITH_TAC ; 
      REWRITE_TAC [(SELECT_RULE (SPECL [`x:real`;`y:real`] ATAN2_EXISTS))]]);;

  let ATAN2_TEMP_SPEC = prove
   (`!x y. ?r. ((-- pi < atan2_temp(x, y)) /\ (atan2_temp(x,y) <= pi) /\
       (x = r* (cos(atan2_temp(x,y)))) /\ (y = r* (sin (atan2_temp( x, y)))) /\ 
       (&0 <= r))`,
    STRIP_TAC THEN STRIP_TAC THEN EXISTS_TAC `sqrt(x pow 2 + y pow 2)` THEN
    REWRITE_TAC [ATAN2_TEMP] THEN SUBGOAL_TAC "sum_pos" `&0 <= x pow 2 + y pow 2`
    [ MP_TAC (SPEC `x:real` REAL_LE_POW_2) THEN 
      MP_TAC (SPEC `y:real` REAL_LE_POW_2) THEN
      IMP_RES_THEN MP_TAC (SPECL [`x:real`; `2`] REAL_POW_NZ) THEN 
      IMP_RES_THEN MP_TAC (SPECL [`y:real`; `2`] REAL_POW_NZ) THEN 
      REAL_ARITH_TAC ] THEN
    MP_TAC (SPEC `x pow 2 + y pow 2` SQRT_POS_LE) THEN POP_ASSUM MP_TAC THEN
    REAL_ARITH_TAC);;
      
  let ATAN2_TEMP_BREAKDOWN = prove
   (`!x y. (&0 < x ==> atan2_temp(x,y) = atn(y / x)) /\
           (&0 < y ==> atan2_temp(x,y) = pi / &2 - atn(x / y)) /\
           (y < &0 ==> atan2_temp(x,y) = --(pi / &2) - atn(x / y)) /\
           (y = &0 /\ x <= &0 ==> atan2_temp(x,y) = pi)`,
    REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
    [ STRIP_ASSUME_TAC (SPECL [`x:real`;`y:real`] ATAN2_TEMP) THEN
      ABBREV_TAC `t = atan2_temp (x,y)` THEN 
      ABBREV_TAC `r = sqrt (x pow 2 + y pow 2)` THEN STRIP_TAC THEN
      SUBGOAL_TAC "r_pos" `&0 < r` 
      [ EXPAND_TAC "r" THEN MP_TAC (SPECL [`x:real`;`y:real`] dist_lemma) THEN
        POP_ASSUM MP_TAC THEN REAL_ARITH_TAC] THEN
      SUBGOAL_TAC "tan" `(r * sin t) / (r * cos t) = tan t`
      [ REWRITE_TAC [tan] THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD ] THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (GSYM TAN_ATN) THEN 
      POP_ASSUM (K ALL_TAC) THEN 
      POP_ASSUM (fun th -> POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
      ASM_SIMP_TAC [GSYM COS_NEGPOS_PI; REAL_LT_LMUL_0] THEN REAL_ARITH_TAC ;

      STRIP_ASSUME_TAC (SPECL [`x:real`;`y:real`] ATAN2_TEMP) THEN
      ABBREV_TAC `t = atan2_temp (x,y)` THEN 
      ABBREV_TAC `r = sqrt (x pow 2 + y pow 2)` THEN STRIP_TAC THEN
      SUBGOAL_TAC "r_pos" `&0 < r` 
      [ EXPAND_TAC "r" THEN MP_TAC (SPECL [`x:real`;`y:real`] dist_lemma) THEN
        POP_ASSUM MP_TAC THEN REAL_ARITH_TAC] THEN
      SUBGOAL_TAC "tan" `(r * cos t) / (r * sin t) = inv (tan t)`
      [ REWRITE_TAC [tan] THEN POP_ASSUM MP_TAC THEN 
        CONV_TAC REAL_FIELD ] THEN
      ASM_REWRITE_TAC [GSYM TAN_COT] THEN
      SUBGOAL_THEN `pi / &2 - t = atn (tan (pi / &2 - t))` 
                   (fun th -> REWRITE_TAC [GSYM th] THEN REAL_ARITH_TAC) THEN
      MATCH_MP_TAC (GSYM TAN_ATN) THEN 
      SUBGOAL_THEN `&0 < t /\ t < pi` 
                   (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
      POP_ASSUM (K ALL_TAC) THEN 
      POP_ASSUM (fun th -> POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
      ASM_SIMP_TAC [GSYM SIN_NEGPOS_PI; REAL_LT_LMUL_0] THEN REAL_ARITH_TAC ;
    
      STRIP_ASSUME_TAC (SPECL [`x:real`;`y:real`] ATAN2_TEMP) THEN
      ABBREV_TAC `t = atan2_temp (x,y)` THEN 
      ABBREV_TAC `r = sqrt (x pow 2 + y pow 2)` THEN STRIP_TAC THEN
      SUBGOAL_TAC "r_pos" `&0 < r` 
      [ EXPAND_TAC "r" THEN MP_TAC (SPECL [`x:real`;`y:real`] dist_lemma) THEN
        POP_ASSUM MP_TAC THEN REAL_ARITH_TAC] THEN
      SUBGOAL_TAC "tan" `(r * cos t) / (r * sin t) = --inv (tan (--t))`
      [ REWRITE_TAC [TAN_NEG; REAL_INV_NEG] THEN 
        REWRITE_TAC [tan; REAL_NEG_NEG] THEN 
        POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD ] THEN
      ASM_REWRITE_TAC [GSYM TAN_COT; ATN_NEG] THEN
      SUBGOAL_THEN `pi / &2 + t = atn (tan (pi / &2 + t))` 
        (fun th -> REWRITE_TAC [REAL_ARITH `pi / &2 - --t = pi / &2 + t`;GSYM th] 
                   THEN REAL_ARITH_TAC) THEN
      MATCH_MP_TAC (GSYM TAN_ATN) THEN 
      SUBGOAL_THEN `--pi < t /\ t < &0` 
                   (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
      POP_ASSUM (K ALL_TAC) THEN
      POP_ASSUM (fun th -> POP_ASSUM (MP_TAC o (REWRITE_RULE [GSYM REAL_NEG_GT0]))
                           THEN ASSUME_TAC th) THEN
      ASM_SIMP_TAC [GSYM SIN_NEGPOS_PI; REAL_LT_LMUL_0; REAL_NEG_RMUL] THEN 
      REAL_ARITH_TAC ;
    
      ASM_CASES_TAC `x = &0` THENL
    [ STRIP_TAC THEN ASM_REWRITE_TAC [ATAN2_TEMP_DEF];
      ALL_TAC] THEN
    STRIP_ASSUME_TAC (SPECL [`x:real`;`y:real`] ATAN2_TEMP) THEN
    ABBREV_TAC `t = atan2_temp (x,y)` THEN 
    ABBREV_TAC `r = sqrt (x pow 2 + y pow 2)` THEN STRIP_TAC THEN
    SUBGOAL_TAC "r_pos" `&0 < r` 
    [ EXPAND_TAC "r" THEN MP_TAC (SPECL [`x:real`;`y:real`] dist_lemma) THEN
      POP_ASSUM MP_TAC THEN FIND_ASSUM MP_TAC `~(x = &0)` THEN 
      REAL_ARITH_TAC ] THEN
    SUBGOAL_TAC "sin_cos" `sin t = &0 /\ cos t < &0 ==> t = pi`
    [ ASM_SIMP_TAC [SIN_NEGPOS_PI; COS_NEGPOS_PI] THEN MP_TAC PI_POS THEN
      REAL_ARITH_TAC ] THEN
    POP_ASSUM MATCH_MP_TAC THEN 
    SUBGOAL_TAC "x_pos" `&0 < --x` 
    [ FIND_ASSUM MP_TAC `x <= &0` THEN FIND_ASSUM MP_TAC `~(x = &0)` THEN
      REAL_ARITH_TAC ] THEN
    POP_ASSUM MP_TAC THEN   
    POP_ASSUM (fun th -> POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC THEN 
                         ASSUME_TAC th) THEN
    ASM_SIMP_TAC [REAL_LT_LMUL_0; REAL_NEG_RMUL] THEN POP_ASSUM MP_TAC THEN
    CONV_TAC REAL_FIELD]);;
    
  let ATAN2_TEMP_ALT = prove
   (`!x y. atan2_temp (x,y) = 
     if ( abs y < x ) then atn(y / x) else
     (if (&0 < y) then ((pi / &2) - atn(x / y)) else
     (if (y < &0) then (-- (pi/ &2) - atn (x / y)) else (  pi )))`,
    STRIP_TAC THEN STRIP_TAC THEN COND_CASES_TAC THENL 
    [ SUBGOAL_THEN `&0 < x` 
                  (fun th -> SIMP_TAC [th; ATAN2_TEMP_BREAKDOWN]) THEN
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
      COND_CASES_TAC THENL
      [ SUBGOAL_THEN `&0 < y` 
                     (fun th -> SIMP_TAC [th; ATAN2_TEMP_BREAKDOWN]) THEN
        POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
        COND_CASES_TAC THENL
        [ SUBGOAL_THEN `y < &0` 
                      (fun th -> SIMP_TAC [th; ATAN2_TEMP_BREAKDOWN]) THEN
          POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
          SUBGOAL_THEN `y = &0` 
            (fun th -> POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
                       ASSUME_TAC th) THENL
          [ POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC ;
            SUBGOAL_THEN `x <= &0` 
                        (fun th -> ASM_SIMP_TAC [th; ATAN2_TEMP_BREAKDOWN]) THEN
            POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC ]]]]);;  
  
  (* Show that the working def and the official def are equivalent. *)
  
  let ATAN_TEMP_ATN2 = prove
   (`atn2 = atan2_temp`,
    REWRITE_TAC [FORALL_PAIR_THM; FUN_EQ_THM; atn2; ATAN2_TEMP_ALT]);;

  (* These three and the definition should suffice as the basic *)
  (* specifications for atn2. No more need for atan2_temp.*)
  
  let atn2_spec = prove
   (atn2_spec_t,
    REWRITE_TAC [ATAN_TEMP_ATN2; ATAN2_TEMP_SPEC]);; 
  
  let ATN2_BREAKDOWN = prove
   (`!x y. (&0 < x ==> atn2 (x,y) = atn(y / x)) /\
           (&0 < y ==> atn2 (x,y) = pi / &2 - atn(x / y)) /\
           (y < &0 ==> atn2 (x,y) = --(pi / &2) - atn(x / y)) /\
           (y = &0 /\ x <= &0 ==> atn2(x,y) = pi)`,
    REWRITE_TAC [ATAN_TEMP_ATN2; ATAN2_TEMP_BREAKDOWN]);;
    
  let ATN2_CIRCLE = prove
   (`!x y. (--pi < atan2_temp (x,y) /\ atan2_temp (x,y) <= pi) /\
           x = sqrt(x pow 2 + y pow 2) * cos (atan2_temp (x,y)) /\
           y = sqrt(x pow 2 + y pow 2) * sin (atan2_temp (x,y))`,
    REWRITE_TAC [ATAN_TEMP_ATN2; ATAN2_TEMP]);;

  (* Useful properties of atn2. *)
  
  let ATN2_0_1 = prove
   (`atn2 (&0, &1) = pi / &2`,
    ASSUME_TAC (REAL_ARITH `&0 < &1`) THEN 
    ASM_SIMP_TAC [ATN2_BREAKDOWN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [ATN_0] THEN REAL_ARITH_TAC);;
    
  let ATN2_0_NEG_1 = prove
   (`atn2 (&0, --(&1)) = --(pi / &2)`,
    ASSUME_TAC (REAL_ARITH `--(&1) < &0`) THEN 
    ASM_SIMP_TAC [ATN2_BREAKDOWN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [ATN_0] THEN REAL_ARITH_TAC);;
  
  let ATN2_LMUL_EQ = prove
   (`!a x y. &0 < a ==> atn2(a * x, a * y) = atn2 (x, y)`,
    REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC 
      (REAL_ARITH `&0 < x \/ &0 < y \/ y < &0 \/ (y = &0 /\ x <= &0)`) THENL
    [ SUBGOAL_TAC "pos_x" `&0 < a * x` 
      [ let th = SPECL [`a:real`;`&0`;`x:real`] REAL_LT_LMUL_EQ in
        let th2 = REWRITE_RULE [REAL_MUL_RZERO] th in
        ASM_SIMP_TAC [th2] ] ;
      SUBGOAL_TAC "pos_y" `&0 < a * y` 
      [ let th = SPECL [`a:real`;`&0`;`y:real`] REAL_LT_LMUL_EQ in
        let th2 = REWRITE_RULE [REAL_MUL_RZERO] th in
        ASM_SIMP_TAC [th2] ] ;
       SUBGOAL_TAC "neg_y" `a * y < &0` 
      [ let th = SPECL [`a:real`;`y:real`;`&0`] REAL_LT_LMUL_EQ in
        let th2 = REWRITE_RULE [REAL_MUL_RZERO] th in
        ASM_SIMP_TAC [th2] ] ;
      SUBGOAL_TAC "other" `a * y = &0 /\ a * x <= &0`
      [ ASM_REWRITE_TAC [REAL_MUL_RZERO] THEN
        let th = SPECL [`x:real`;`&0`;`a:real`] REAL_LE_LMUL_EQ in
        let th2 = REWRITE_RULE [REAL_MUL_RZERO] th in
        ASM_SIMP_TAC [th2] ] ] THEN
    let th1 = SPECL [`x:real`;`y:real`] ATN2_BREAKDOWN in
    let th2 = SPECL [`a * x:real`;`a * y:real`] ATN2_BREAKDOWN in
    let th3 = REAL_ARITH `!x. (x < &0 \/ &0 < x) ==> ~(&0 = x)` in
    ASM_SIMP_TAC [th1; th2; th3; GSYM (SPEC `a:real` REAL_DIV_MUL2)] );;
  
  let ATN2_RNEG = prove
   (`!x y. (~(y = &0) \/ &0 < x) ==> atn2(x,--y) = --(atn2(x,y))`,
    STRIP_TAC THEN STRIP_TAC THEN STRIP_ASSUME_TAC 
      (REAL_ARITH `&0 < x \/ &0 < y \/ y < &0 \/ (y = &0 /\ x <= &0)`) THENL
    [ ASM_REWRITE_TAC [] ;
      ASM_SIMP_TAC [REAL_LT_IMP_NE] THEN SUBGOAL_TAC "neg" `--y < &0`
       [ ASM_REWRITE_TAC [REAL_NEG_LT0] ] ;
      ASM_SIMP_TAC [REAL_LT_IMP_NE] THEN SUBGOAL_TAC "pos" `&0 < --y`
       [ ASM_REWRITE_TAC [REAL_NEG_GT0] ] ;
      ASM_REWRITE_TAC [real_lt] ] THEN
    let th1 = SPECL [`x:real`;`y:real`] ATN2_BREAKDOWN in
    let th2 = SPECL [`x:real`;`--y:real`] ATN2_BREAKDOWN in
    let th3 = REAL_ARITH `(--x)/y = --(x/y)` in
    let th4 = REAL_FIELD `(y < &0 \/ &0 < y) ==>  x / (--y) = --(x/y)` in
    ASM_SIMP_TAC [th1; th2; th3; th4; ATN_NEG] THEN REAL_ARITH_TAC);;

  (* lemma:acs_atn2 *)   
  
  let acs_atn2 = prove
   (acs_atn2_t,
    STRIP_TAC THEN ASM_CASES_TAC `y = &1 \/ y = --(&1)` THENL
    [ POP_ASSUM DISJ_CASES_TAC THENL
      [ ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
        REWRITE_TAC [ACS_1; SQRT_0; ATN2_0_1] THEN REAL_ARITH_TAC ;
        ASM_REWRITE_TAC [] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
        REWRITE_TAC [ACS_NEG_1; SQRT_0; ATN2_0_NEG_1] THEN REAL_ARITH_TAC ] ;
      STRIP_TAC THEN 
      SUBGOAL_TAC "sqrt" `&0 < sqrt (&1 - y pow 2)`
      [ MATCH_MP_TAC SQRT_POS_LT THEN
        SUBGOAL_THEN `&0 <= y pow 2 /\ y pow 2 < &1`
                     (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
        REWRITE_TAC [REAL_LE_SQUARE_POW; REAL_ARITH `a < &1 <=> a < &1 pow 2`;
                     GSYM REAL_LT_SQUARE_ABS ] THEN 
        REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC ] THEN
       ASM_SIMP_TAC [ATN2_BREAKDOWN] THEN MATCH_MP_TAC ACS_ATN THEN
       REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC ]);;
  
  (* ----------------------------------------------------------------------- *)
  (* Theory of triangles (without vectors). Includes laws of cosines/sines.  *)
  (* ----------------------------------------------------------------------- *)
  
  let UPS_X_SQUARES = prove
   (`!a b c. ups_x (a * a) (b * b) (c * c) =
           &16 * ((a + b + c) / &2) * 
           (((a + b + c) / &2) - a) * 
           (((a + b + c) / &2) - b) * 
           (((a + b + c) / &2) - c)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC [ups_x] THEN REAL_ARITH_TAC);;

  (* Theorems assuming a, b, c are lengths of a triangle (c not 0). *)

  let TRI_UPS_X_POS = prove
   (`!a b c. (&0 < a) /\ (&0 < b) /\ (&0 <= c) /\ (c <= a + b) /\ (a <= b + c) /\ (b <= c + a) ==>
     &0 <= ups_x (a * a) (b * b) (c * c)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC [UPS_X_SQUARES] THEN
    REPEAT (MATCH_MP_TAC REAL_LE_MUL THEN STRIP_TAC) THENL
    [ REAL_ARITH_TAC ;
      REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC ;
      SUBGOAL_THEN `&2 * a <= a + b + c` 
                   (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC ;
      SUBGOAL_THEN `&2 * b <= a + b + c` 
                   (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC ;
      SUBGOAL_THEN `&2 * c <= a + b + c` 
                   (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC ]);;
  
  let TRI_SQUARES_BOUNDS = prove
   (`!a b c. (&0 < a) /\ (&0 < b) /\ (&0 <= c) /\ (c <= a + b) /\ (a <= b + c) /\ (b <= c + a) ==>
     --(&1) <= ((a * a) + (b * b) - (c * c)) / (&2 * a * b) /\
     ((a * a) + (b * b) - (c * c)) / (&2 * a * b) <= &1`,
    REPEAT STRIP_TAC THEN 
    SUBGOAL_TAC "2ab_pos" `&0 < &2 * a * b` 
    [ ASM_SIMP_TAC [REAL_LT_MUL_3; REAL_ARITH `&0 < &2`] ] THENL
    [ SUBGOAL_TAC "abc_square" `c*c <= (a + b) * (a + b)`
      [ MATCH_MP_TAC (REWRITE_RULE [IMP_IMP] REAL_LE_MUL2) THEN 
        REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC ] THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ] THEN REMOVE_THEN "abc_square" MP_TAC THEN
      REAL_ARITH_TAC ;
      SUBGOAL_TAC "abc_square" `(a - b) * (a - b) <= c*c`
      [ DISJ_CASES_TAC (REAL_ARITH `a <= b \/ b <= a`) THENL
        [ SUBST1_TAC (REAL_ARITH `(a-b)*(a-b)=(b-a)*(b-a)`); ALL_TAC ] THEN
        MATCH_MP_TAC (REWRITE_RULE [IMP_IMP] REAL_LE_MUL2) THEN 
        REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC ] THEN
      ASM_SIMP_TAC [REAL_LE_LDIV_EQ] THEN REMOVE_THEN "abc_square" MP_TAC THEN
      REAL_ARITH_TAC ]);;

  let ATN2_ARCLENGTH = prove
   (`!a b c. (&0 < a) /\ (&0 < b) /\ (&0 <= c) /\ (c <= a + b) /\ (a <= b + c) /\ (b <= c + a) ==>
     arclength a b c = pi / &2 - atn2(sqrt(ups_x (a*a) (b*b) (c*c)), (a*a) + (b*b) - (c*c))`,
    REPEAT STRIP_TAC THEN 
    let th = REAL_ARITH `c * c - a * a - b * b = --(a * a + b * b - c * c)` in
    REWRITE_TAC [arclength; th; ATN2_RNEG] THEN
    SUBGOAL_THEN `~(a * a + b * b - c * c = &0) \/
                 &0 < sqrt(ups_x (a*a) (b*b) (c*c))` 
                (fun th -> ASM_SIMP_TAC [th; ATN2_RNEG] THEN 
                           REAL_ARITH_TAC) THEN
    REWRITE_TAC [TAUT `(~A \/ B) <=> (A ==> B)`] THEN STRIP_TAC THEN
    SUBGOAL_TAC "c_ab" `c*c = a*a + b*b` 
    [ POP_ASSUM MP_TAC THEN REAL_ARITH_TAC ] THEN 
    REMOVE_THEN "c_ab" (fun th -> REWRITE_TAC [ups_x; th]) THEN 
    MATCH_MP_TAC SQRT_POS_LT THEN 
    CONV_TAC (DEPTH_BINOP_CONV `(<)` REAL_POLY_CONV) THEN
    MATCH_MP_TAC REAL_LT_MUL_3 THEN STRIP_TAC THENL
    [ REAL_ARITH_TAC ;
      ASM_SIMP_TAC [REAL_POW_LT] ]);;

  let TRI_LEMMA = prove
   (`!a b c. (&0 < a) /\ (&0 < b) /\ (&0 <= c) /\ (c <= a + b) /\ (a <= b + c) /\ (b <= c + a) ==>
     (&2 * a * b) * (a * a + b * b - c * c) / (&2 * a * b) =
     a * a + b * b - c * c`,
    REPEAT STRIP_TAC THEN 
    SUBGOAL_TAC "2ab_pos" `&0 < &2 * a * b`
    [ ASM_SIMP_TAC [REAL_LT_MUL_3; REAL_ARITH `&0 < &2`] ] THEN
    SUBGOAL_TAC "2ab_not0" `~(&2 * a * b = &0)` 
    [ POP_ASSUM MP_TAC THEN REAL_ARITH_TAC ] THEN
    ASM_SIMP_TAC [REAL_DIV_LMUL]);;

  let TRI_UPS_X_SQUARES = prove
   (`!a b c. (&0 < a) /\ (&0 < b) /\ (&0 <= c) /\ (c <= a + b) /\ (a <= b + c) /\ (b <= c + a) ==>
     ups_x (a * a) (b * b) (c * c) =
     (&2 * a * b) pow 2 * (&1 - ((a * a + b * b - c * c) / (&2 * a * b)) pow 2)`,
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [ups_x; REAL_SUB_LDISTRIB; GSYM REAL_POW_MUL; TRI_LEMMA] THEN
    REAL_ARITH_TAC);;

  let TRI_UPS_X_SQRT = prove
   (`!a b c. (&0 < a) /\ (&0 < b) /\ (&0 <= c) /\ (c <= a + b) /\ (a <= b + c) /\ (b <= c + a) ==>
     sqrt(ups_x (a * a) (b * b) (c * c)) =
     (&2 * a * b) * sqrt(&1 - ((a * a + b * b - c * c) / (&2 * a * b)) pow 2)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_TAC "2ab_pos" `&0 < &2 * a * b`
    [ ASM_SIMP_TAC [REAL_LT_MUL_3; REAL_ARITH `&0 < &2`] ] THEN
    SUBGOAL_TAC "other_pos" `&0 <= &1 - ((a * a + b * b - c * c) / (&2 * a * b)) pow 2`
    [ SUBGOAL_THEN `((a * a + b * b - c * c) / (&2 * a * b)) pow 2 <= &1`
        (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
    ASM_SIMP_TAC [ABS_SQUARE_LE_1; REAL_ABS_BOUNDS; TRI_SQUARES_BOUNDS] ] THEN
    ASM_SIMP_TAC [SQRT_MUL_L; REAL_LT_IMP_LE; TRI_UPS_X_SQUARES] );;

  let ACS_ARCLENGTH = prove
   (`!a b c. (&0 < a) /\ (&0 < b) /\ (&0 <= c) /\ (c <= a + b) /\ (a <= b + c) /\ (b <= c + a) ==>
     arclength a b c = acs (((a * a) + (b * b) - (c * c)) / (&2 * a * b))`,
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [ATN2_ARCLENGTH; TRI_SQUARES_BOUNDS; acs_atn2] THEN
    SUBGOAL_TAC "2ab_pos" `&0 < &2 * a * b`
    [ ASM_SIMP_TAC [REAL_LT_MUL_3; REAL_ARITH `&0 < &2`] ] THEN
    SUBGOAL_THEN 
      `(sqrt (ups_x (a * a) (b * b) (c * c)), a * a + b * b - c * c) =
       ((&2 * a * b) * sqrt (&1 - ((a * a + b * b - c * c) / (&2 * a * b)) pow 2),
        (&2 * a * b) * ((a * a + b * b - c * c) / (&2 * a * b)))`
      (fun th -> ASM_SIMP_TAC [ATN2_LMUL_EQ; th]) THEN 
    ASM_SIMP_TAC [TRI_UPS_X_SQRT; TRI_LEMMA]);;

  let law_of_cosines = prove    
   (law_of_cosines_t,
    REPEAT STRIP_TAC THEN 
    REWRITE_TAC [REAL_ARITH `&2 * a * b * x = (&2 * a * b) * x`] THEN
    ASM_SIMP_TAC [ACS_ARCLENGTH; TRI_SQUARES_BOUNDS; ACS_COS; TRI_LEMMA] THEN 
    REAL_ARITH_TAC);;

  let law_of_sines =  prove
   (law_of_sines_t,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [REAL_ARITH `&2 * a * b * x = (&2 * a * b) * x`;
                 REAL_ARITH `x pow 2 = x * x` ] THEN
    ASM_SIMP_TAC [ACS_ARCLENGTH; TRI_SQUARES_BOUNDS; sin_acs; TRI_UPS_X_SQRT]);;

  (* ----------------------------------------------------------------------- *)
	(* Conversion tool for defintions of form:                                 *)
	(*   `let (a,b,c) = triple_of_real3 v in P[a,b,c]`                         *)
	(* Converts it to                                                          *)
	(*   `P[v$1,v$2,v$3]                                                       *)
	(* Also handles etc.                                      *)
	(* ----------------------------------------------------------------------- *)
	
	let KEP_REAL3_CONV = REDEPTH_CONV (CHANGED_CONV 
		(REWRITE_CONV [ mk_vec3; real3_of_triple; 
		               triple_of_real3] THENC
		 TRY_CONV (let_CONV)));;

  (* ----------------------------------------------------------------------- *)
  (* Cross product properties.                                               *)
  (* ----------------------------------------------------------------------- *)

(* work in progress *)

  let DIST_TRIANGLE_DETAILS = prove
	 (`~(u = v) /\ ~(u = w) <=>
	   &0 < dist(u,v) /\ &0 < dist(u,w) /\
     &0 <= dist(v,w) /\
     dist(v,w) <= dist(u,v) + dist(u,w) /\
     dist(u,v) <= dist(u,w) + dist(v,w) /\
     dist(u,w) <= dist(v,w) + dist(u,v)`,
		NORM_ARITH_TAC);;

  let arcVarc = prove
	 (arcVarc_t,
	  SIMP_TAC [DIST_TRIANGLE_DETAILS;  arcV; ACS_ARCLENGTH] THEN
		REPEAT STRIP_TAC THEN AP_TERM_TAC THEN 
		REWRITE_TAC [DOT_NORM_NEG; dist] THEN 
		let tha = NORM_ARITH `norm (v - u) = norm (u - v)` in
		let thb = NORM_ARITH `norm (w - u) = norm (u - w)` in
		let thc = NORM_ARITH `norm (v - u - (w - u)) = norm (v - w)` in
		REWRITE_TAC [tha; thb; thc] THEN CONV_TAC REAL_FIELD);;

let DIST_LAW_OF_COS = prove
	 (`(dist(v:real^3,w)) pow 2 = (dist(u,v)) pow 2 + (dist(u,w)) pow 2 - 
		                     &2 * (dist(u,v)) * (dist(u,w)) * cos (arcV u v w)`,
    ASM_CASES_TAC `~(u = v:real^3) /\ ~(u = w)` THEN POP_ASSUM MP_TAC THENL
		[ ASM_SIMP_TAC [arcVarc] THEN 
		  REWRITE_TAC [law_of_cosines; DIST_TRIANGLE_DETAILS];
		  REWRITE_TAC [TAUT `~(~A /\ ~B) <=> (A \/ B)`] THEN STRIP_TAC THEN 
			ASM_REWRITE_TAC [DIST_REFL; DIST_SYM] THEN REAL_ARITH_TAC]);;

  let DIST_L_ZERO = prove
	 (`!v. dist(vec 0, v) = norm v`,
    NORM_ARITH_TAC);;
	
  (* I would like to change this to real^N but that means changing arcV to real^N *)

  let DOT_COS = prove 
	 (`u:real^3 dot v = (norm u) * (norm v) * cos (arcV (vec 0) u v)`,
    MP_TAC (INST [`vec 0:real^3`,`u:real^3`; 
		              `u:real^3`,`v:real^3`; 
								  `v:real^3`,`w:real^3`] DIST_LAW_OF_COS) THEN  
		SUBGOAL_THEN 
		  `dist(u:real^3,v) pow 2 = 
		   dist(vec 0, v) pow 2 + dist(vec 0, u) pow 2 - &2 * u dot v` 
			(fun th -> REWRITE_TAC [th; DIST_L_ZERO] THEN REAL_ARITH_TAC) THEN
		REWRITE_TAC [NORM_POW_2; dist; DOT_RSUB; DOT_LSUB; 
		             DOT_SYM; DOT_LZERO; DOT_RZERO] THEN
    REAL_ARITH_TAC);;

  (* DIMINDEX_3, FORALL_3, SUM_3, DOT_3, VECTOR_3, FORALL_VECTOR_3          *)
	(* are all very useful.  Any time you see a theorem you need with         *)
	(* 1 <= i /\ i <= dimindex(:3), first use INST_TYPE and then rewrite      *)
	(* with DIMINDEX_3 and FORALL_3 or see if it's in the list below.         *)
	
  let CART_EQ_3 = prove
   (`!x y. (x:A^3) = y <=> x$1 = y$1 /\ x$2 = y$2 /\ x$3 = y$3`,
	  REWRITE_TAC [CART_EQ; DIMINDEX_3; FORALL_3]);;
	
	let LAMBDA_BETA_3 = prove
   (`((lambda) g:A^3) $1 = g 1 /\
	   ((lambda) g:A^3) $2 = g 2 /\
		 ((lambda) g:A^3) $3 = g 3`,
    let th = REWRITE_RULE [DIMINDEX_3; FORALL_3] 
		                      (INST_TYPE [`:3`,`:B`] LAMBDA_BETA) in
		REWRITE_TAC [th]);;

  let VEC_COMPONENT_3 = prove
   (`!k. (vec k :real^3)$1 = &k /\ 
	       (vec k :real^3)$2 = &k /\ 
		     (vec k :real^3)$3 = &k`,
    let th = REWRITE_RULE [DIMINDEX_3; FORALL_3] 
		                      (INST_TYPE [`:3`,`:N`] VEC_COMPONENT) in
		REWRITE_TAC [th]);;

  let VECTOR_ADD_COMPONENT_3 = prove
   (`!x:real^3 y. (x + y)$1 = x$1 + y$1 /\
	                (x + y)$2 = x$2 + y$2 /\
									(x + y)$3 = x$3 + y$3`,
		let th = REWRITE_RULE [DIMINDEX_3; FORALL_3] 
		                      (INST_TYPE [`:3`,`:N`] VECTOR_ADD_COMPONENT) in
		REWRITE_TAC [th]);;

  let VECTOR_SUB_COMPONENT_3 = prove
   (`!x:real^3 y. (x - y)$1 = x$1 - y$1 /\
	                (x - y)$2 = x$2 - y$2 /\
									(x - y)$3 = x$3 - y$3`,
		let th = REWRITE_RULE [DIMINDEX_3; FORALL_3] 
		                      (INST_TYPE [`:3`,`:N`] VECTOR_SUB_COMPONENT) in
		REWRITE_TAC [th]);;

  let VECTOR_NEG_COMPONENT_3 = prove
   (`!x:real^3. (--x)$1 = --(x$1) /\
	              (--x)$2 = --(x$2) /\
								(--x)$3 = --(x$3)`,
    let th = REWRITE_RULE [DIMINDEX_3; FORALL_3] 
		                      (INST_TYPE [`:3`,`:N`] VECTOR_NEG_COMPONENT) in
		REWRITE_TAC [th]);;

  let VECTOR_MUL_COMPONENT_3 = prove
   (`!c x:real^3. (c % x)$1 = c * x$1 /\
	                (c % x)$2 = c * x$2 /\
									(c % x)$3 = c * x$3`,
    let th = REWRITE_RULE [DIMINDEX_3; FORALL_3] 
		                      (INST_TYPE [`:3`,`:N`] VECTOR_MUL_COMPONENT) in
		REWRITE_TAC [th]);;

 (* COND_COMPONENT_3 - no need, COND_COMPONENT works fine. *)

  let BASIS_3 = prove
   (`(basis 1:real^3)$1 = &1 /\ (basis 1:real^3)$2 = &0 /\ (basis 1:real^3)$3 = &0 /\
	   (basis 2:real^3)$1 = &0 /\ (basis 2:real^3)$2 = &1 /\ (basis 2:real^3)$3 = &0 /\
	   (basis 3:real^3)$1 = &0 /\ (basis 3:real^3)$2 = &0 /\ (basis 3:real^3)$3 = &1`,
	  REWRITE_TAC [basis; 
	               REWRITE_RULE [DIMINDEX_3; FORALL_3] 
							                (INST_TYPE [`:3`,`:B`] LAMBDA_BETA)] THEN
	  ARITH_TAC);;

  let COMPONENTS_3 = prove
	 (`!v. v:real^3 = v$1 % basis 1 + v$2 % basis 2 + v$3 % basis 3`,
    REWRITE_TAC [CART_EQ_3; VECTOR_ADD_COMPONENT_3; 
		             VECTOR_MUL_COMPONENT_3; BASIS_3] THEN REAL_ARITH_TAC);;

  let VECTOR_COMPONENTS_3 = prove
	 (`!a b c. vector [a;b;c]:real^3 = a % basis 1 + b % basis 2 + c % basis 3`,
	  let th = REWRITE_RULE [VECTOR_3] 
		                      (ISPEC `vector [a;b;c]:real^3` COMPONENTS_3) in
    REWRITE_TAC [th]);;
	
	let CROSS_COMPONENTS = prove
	 (`!u v. (cross u v)$1 = u$2 * v$3 - v$2 * u$3 /\
	         (cross u v)$2 = u$3 * v$1 - v$3 * u$1 /\
					 (cross u v)$3 = u$1 * v$2 - v$1 * u$2`,
		REWRITE_TAC [CONV_RULE KEP_REAL3_CONV cross; VECTOR_3]);;
					
	let cross_def = prove
	 (`!u v. cross u v = vector [u$2 * v$3 - v$2 * u$3; 
	                           u$3 * v$1 - v$3 * u$1; 
														 u$1 * v$2 - v$1 * u$2]`,
    REWRITE_TAC [CONV_RULE KEP_REAL3_CONV cross]);;

  let cross_skew = prove
	 (cross_skew_t,
	  REWRITE_TAC [CART_EQ_3; CROSS_COMPONENTS; VECTOR_NEG_COMPONENT_3] THEN 
		REAL_ARITH_TAC);;
	  
  let cross_triple = prove
	 (cross_triple_t,
	  REWRITE_TAC [ DOT_3; CROSS_COMPONENTS] THEN REAL_ARITH_TAC);;
  
	let NORM_CAUCHY_SCHWARZ_FRAC = prove
	 (`!(u:real^N) v. ~(u = vec 0) /\ ~(v = vec 0) ==>
	         -- &1 <= (u dot v) / (norm u * norm v) /\
	         (u dot v) / (norm u * norm v) <= &1`,
		REPEAT STRIP_TAC THEN
		SUBGOAL_TAC "norm_pos" `&0 < norm (u:real^N) * norm (v:real^N)`
		[ POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN 
		  SIMP_TAC [GSYM NORM_POS_LT; IMP_IMP; REAL_LT_MUL] ] THEN
		MP_TAC (SPECL [`u:real^N`;`v:real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN
		ASM_SIMP_TAC [REAL_ABS_BOUNDS; REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
		REAL_ARITH_TAC);;
	
	let CROSS_LZERO = prove
	 (`!x. cross (vec 0) x = vec 0`,
	   REWRITE_TAC [CART_EQ_3; CROSS_COMPONENTS; VEC_COMPONENT_3] THEN 
	   REAL_ARITH_TAC);;

	let CROSS_RZERO = prove
	 (`!x. cross x (vec 0) = vec 0`,
	   REWRITE_TAC [CART_EQ_3; CROSS_COMPONENTS; VEC_COMPONENT_3] THEN 
	   REAL_ARITH_TAC);;
 
  let CROSS_SQUARED = prove
	 (`!u v. (cross u v) dot (cross u v) = 
		       (ups_x (u dot u) (v dot v) ((u - v) dot (u - v))) / &4`,
	  REWRITE_TAC [DOT_3; CROSS_COMPONENTS; ups_x; VECTOR_SUB_COMPONENT_3] THEN
	  REAL_ARITH_TAC);;
 
  let DIST_UPS_X_POS = prove
   (`~(u = v) /\ ~(u = w) ==>
	   &0 <= ups_x (dist(u,v) pow 2) (dist(u,w) pow 2) (dist(v,w) pow 2)`,
		REWRITE_TAC [DIST_TRIANGLE_DETAILS; TRI_UPS_X_POS; REAL_POW_2]);;
  
	let SQRT_DIV_R = prove
	 (`&0 <= x /\ &0 <= y ==> sqrt (x) / y = sqrt (x/ (y pow 2)) /\ &0 <= x/(y pow 2)`,
		SIMP_TAC [SQRT_DIV; REAL_LE_POW_2; POW_2_SQRT; REAL_LE_DIV]);;
	
  let NORM_CROSS = prove
	 (`!u v. ~(vec 0 = u) /\ ~(vec 0 = v) ==>
	           norm (cross u v) = 
		         sqrt (ups_x ((norm u) pow 2) 
					               ((norm v) pow 2) 
								  			 ((dist(u,v)) pow 2)) / &2`,
		REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN MP_TAC DIST_UPS_X_POS THEN
		REWRITE_TAC [DIST_L_ZERO] THEN 
		SIMP_TAC[SQRT_DIV_R; REAL_ARITH `&0 <= &2`; REAL_ARITH `&2 pow 2 = &4`] THEN 
		DISCH_TAC THEN MATCH_MP_TAC (GSYM SQRT_UNIQUE) THEN 
		REWRITE_TAC [dist; NORM_POW_2; CROSS_SQUARED] THEN NORM_ARITH_TAC);;
				
	let VECTOR_LAW_OF_SINES = prove			
	 (`~(vec 0 = u:real^3) /\ ~(vec 0 = v) ==>
	   &2 * (norm u) * (norm v) * sin (arcV (vec 0) u v) =
              sqrt (ups_x (norm u pow 2) (norm v pow 2) (dist (u,v) pow 2))`,
		 SIMP_TAC [arcVarc; DIST_TRIANGLE_DETAILS; law_of_sines; DIST_L_ZERO]);; 	
						
	let cross_mag = prove
	 (cross_mag_t,
	  REPEAT STRIP_TAC THEN 
		REWRITE_TAC [arcVarc; VECTOR_SUB_RZERO] THEN
		ASM_CASES_TAC `(u:real^3) = vec 0 \/ (v:real^3) = vec 0` THENL
		[ POP_ASSUM STRIP_ASSUME_TAC THEN 
		  ASM_REWRITE_TAC [CROSS_LZERO; CROSS_RZERO; NORM_0] THEN REAL_ARITH_TAC ;
			POP_ASSUM MP_TAC THEN 
			REWRITE_TAC [DE_MORGAN_THM; MESON [] `a = vec 0 <=> vec 0 = a`] THEN 
			SIMP_TAC [NORM_CROSS; GSYM VECTOR_LAW_OF_SINES] THEN REAL_ARITH_TAC ]);;
			
(*** work in progress

  prove
	 (`!u v w. arcV u v w = arcV (vec 0) (v - u) (w - u)`,
	   REWRITE_TAC [CONV_RULE KEP_REAL3_CONV arcV; VECTOR_SUB_RZERO]);;

  let ARCV_BILINEAR_L = prove
	 (`!(u:real^N) v s. ~(u = vec 0) /\ ~(v = vec 0) /\ &0 < s ==> 
	     arcV (vec 0) (s % u) v = arcV (vec 0) u v`,
	  REWRITE_TAC [REAL_ARITH `!x. &0 < x <=> ~(&0 = x) /\ &0 <= x`] THEN
		REWRITE_TAC [GSYM NORM_POS_LT] THEN	REPEAT STRIP_TAC THEN 
		REWRITE_TAC [CONV_RULE KEP_REAL3_CONV arcV; VECTOR_SUB_RZERO; DOT_LMUL;
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
			
	(* yet unproven theorems: *)
	
  let  spherical_loc = trigAxiomProofB   spherical_loc_t 
  let  spherical_loc2 = trigAxiomProofB   spherical_loc2_t 
  let  dih_formula = trigAxiomProofB   dih_formula_t 
  let  dih_x_acs = trigAxiomProofB   dih_x_acs_t 
  let  beta_cone = trigAxiomProofB   beta_cone_t 
  let  euler_triangle = trigAxiomProofB   euler_triangle_t 
  let  polar_coords = trigAxiomProofB   polar_coords_t 
  let  polar_cycle_rotate = trigAxiomProofB   polar_cycle_rotate_t 
  let  thetaij = trigAxiomProofB   thetaij_t 
  let  thetapq_wind = trigAxiomProofB   thetapq_wind_t 
  let  zenith = trigAxiomProofB   zenith_t 
  let  spherical_coord = trigAxiomProofB   spherical_coord_t 
  let  polar_coord_zenith = trigAxiomProofB   polar_coord_zenith_t 
  let  azim_pair = trigAxiomProofB   azim_pair_t 
  let  azim_cycle_sum = trigAxiomProofB   azim_cycle_sum_t 
  let  dih_azim = trigAxiomProofB   dih_azim_t 
  let  sph_triangle_ineq = trigAxiomProofB   sph_triangle_ineq_t 
  let  sph_triangle_ineq_sum = trigAxiomProofB   sph_triangle_ineq_sum_t 
(* [deprecated]
  let  aff_insert_sym = trigAxiomProofB   aff_insert_sym_t 
  let  aff_sgn_insert_sym_gt = trigAxiomProofB   aff_sgn_insert_sym_gt_t 
  let  aff_sgn_insert_sym_ge = trigAxiomProofB   aff_sgn_insert_sym_ge_t 
  let  aff_sgn_insert_sym_lt = trigAxiomProofB   aff_sgn_insert_sym_lt_t 
  let  aff_sgn_insert_sym_le = trigAxiomProofB   aff_sgn_insert_sym_le_t 
*)
  let  azim_hyp = trigAxiomProofB   azim_hyp_t 
  let  azim_cycle_hyp = trigAxiomProofB   azim_cycle_hyp_t 
(* [deprecated]
  let  aff = trigAxiomProofA   aff_t
  let  aff_gt = trigAxiomProofB   aff_gt_t
  let  aff_ge = trigAxiomProofB   aff_ge_t
  let  aff_lt = trigAxiomProofB   aff_lt_t
  let  aff_le = trigAxiomProofB   aff_le_t
*)
  let  azim = trigAxiomProofB   azim_t
  let  azim_cycle = trigAxiomProofB   azim_cycle_t
end;;

open Trig;;
