(* Formal Spec of Blueprint Chapter  on Trigonometry *)

needs "Examples/transc.ml";;
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
     (x = r* (cos(atn2(x,y)))) /\ (y = r* (cos (atn2( x, y)))) /\ 
     (r >= &0))`;;

(* lemma:sin-arccos *)

let sin_acs_t = `!y. (-- &1 <= y /\ y <= &1) ==> (cos (acs(y)) = sqrt(&1 - y pow 2))`;;

(* lemma:arccos-arctan *)

let acs_atn2_t = `!y. (-- &1 <= y /\ y <=  &1) ==> (acs y = pi/(&2) - atn2(sqrt(&1 - y pow 2),y))`;;


(* Jordan/metric_spaces.ml:cauchy_schwartz  cauchy_schwartz *)
(* Jordan/metric_spaces.ml:norm_triangle    triangle inequality *)

(* affine geometry definitions are in definitions_kepler.ml *)

let arcVarc_t = `!u v w. ~(u=v) /\ ~(u=w) ==> arcV u v w = arclength (d3 u v) (d3 u w) (d3 v w)`;;

let law_of_cosines_t = `!a b c. (a > &0) /\ (b > &0) /\ (c >= &0) /\ (a + b >= c) /\ (b + c >= a) /\ (c + a >= b) ==> 
   ((c pow 2) = (a pow 2) + (b pow 2) - &2 * a * b * (cos(arclength a b c)))`;;

let law_of_sines_t = `!a b c. (a> &0) /\ (b> &0) /\ (c >= &0) /\ (a + b >= c) /\ (b + c >= a) /\ (c + a >= b) ==> (&2 * a * b * sin (arclength a b c) = sqrt(ups_x (a pow 2) (b pow 2) (c pow 2)))`;;

let cross_mag_t = `!u v. norm3 (cross u v) = (norm3 u) * (norm3 v) * sin(arcV orig3 u v)`;;

let cross_skew_t = `!u v. (cross u v) = -- (cross v u)`;;

let cross_triple_t = `!u v w. dot3 (cross u v) w = dot3 (cross v w) u`;;


(* law of cosines *)

let spherical_loc_t = `!v0 va vb vc.
  ~(collinear {v0,va,vc}) /\ ~(collinear {v0,vb,vc}) ==>
        (
	  let gamma = dihV v0 vc va vb in
	  let a = arcV v0 vb vc in
	  let b = arcV v0 va vc in
	  let c = arcV v0 va vb in
	    (cos(gamma) = (cos(c) - cos(a)*cos(b))/(sin(a)*sin(b))))`;;

let spherical_loc2_t = `!v0 va vb vc.
 ~(collinear {v0,va,vc}) /\ ~(collinear {v0,vb,vc}) ==>
        (
	  let alpha = dihV v0 va vb vc in
	  let beta = dihV v0 vb va vc in
	  let gamma = dihV v0 vc vb va in
	  let c = arcV v0 va vb in
	    (cos(c) = (cos(gamma) + cos(alpha)*cos(beta))/(sin(alpha)*sin(beta))))`;;

let dih_formula_t = `!v0 v1 v2 v3. 
   ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) ==>
   (
   let (x1,x2,x3,x4,x5,x6) = xlist v0 v1 v2 v3 in
    (dihV v0 v1 v2 v3  = dih_x x1 x2 x3 x4 x5 x6)
   )`;;

let dih_x_acs_t = `!x1 x2 x3 x4 x5 x6.
   (ups_x x1 x2 x6 > &0) /\ (ups_x x1 x3 x5 > &0) /\ (delta_x x1 x2 x3 x4 x5 x6 >= &0) /\ (x1 >= &0) ==>
   dih_x x1 x2 x3 x4 x5 x6 = acs ((delta_x4 x1 x2 x3 x4 x5 x6)/
	((sqrt (ups_x x1 x2 x6)) * (sqrt (ups_x x1 x3 x5))))`;;

let beta_cone_t = `!v0 v1 v2 v3.
    ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) /\ 
    (dihV v0 v3 v1 v2 = pi/(&2)) ==>
    (dihV v0 v1 v2 v3 = beta (arcV v0 v1 v3) (arcV v0 v1 v2))`;;

let euler_triangle_t = `!v0 v1 v2 v3. 
    let p = euler_p v0 v1 v2 v3 in
    let (x1,x2,x3,x4,x5,x6) = xlist v0 v1 v2 v3 in
    let alpha1 = dihV v0 v1 v2 v3 in
    let alpha2 = dihV v0 v2 v3 v1 in
    let alpha3 = dihV v0 v3 v1 v2 in
    let d = delta_x x1 x2 x3 x4 x5 x6 in
    ((d > &0) ==>
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

let zenith_t = `!u v w.  ~(u=v) /\ ~(w = v)  ==>
   (?u' r phi e3.
        (phi = arcV v u w) /\ (r = d3 u v) /\ ((d3 w v) *# e3 = (w-v)) /\
	(dot3 u' e3 = &0) /\ (u = v + u' + (r*cos(phi)) *# e3))`;;

let spherical_coord_t = `!u v w u' e1 e2 e3 r phi theta.
        ~(collinear {v,w,u}) /\ ~(collinear {v,w,u'}) /\
       orthonormal e1 e2 e3 /\ ((d3 v w) *# e3 = (v-w)) /\
	(aff_gt {v,w} {u} e1) /\ (e2 = cross e3 e1) /\
	(r = d3 v u') /\ (phi = arcV v u' w) /\ (theta = azim v w u u') ==>
	(u' = u + (r*cos(theta)*sin(phi)) *# e1 + (r*sin(theta)*sin(phi)) *# e2 
	    + (r * cos(phi)) *# e3)`;;

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
       (sum(0,n) (\i. azim v w (iter i (azim_cycle W) p) (iter (SUC i) (azim_cycle W) p)) = &2 * pi   )))`;;

let dih_azim_t = `!v w v1 v2. 
   ~(collinear {v,w,v1}) /\ ~(collinear {v,w,v2}) ==>
  (cos(azim v w v1 v2) = cos(dihV v w v1 v2))`;;

let sph_triangle_ineq_t = `!p u v w.
   ~(collinear {p,u,w}) /\ ~(collinear {p,u,v}) /\ ~(collinear {p,v,w}) ==>
  (arcV p u w <= arcV p u v + arcV p v w)`;;

let sph_triangle_ineq_sum_t = `!p u r.
   (!i. (i < r) ==> ~(collinear {p,u i, u (SUC i)})) /\
   ~(collinear {p,u 0, u r}) ==>
   (arcV p (u 0) (u r) <= sum(0,r) (\i. arcV p (u i) (u (SUC i))))`;;

(* obligations created by definition by specification, to make them useable. *)

let aff_insert_sym_t = `aff_insert_sym`;;
let aff_sgn_insert_sym_gt_t = `aff_sgn_insert_sym (\t. t > &0)`;;
let aff_sgn_insert_sym_ge_t = `aff_sgn_insert_sym (\t. t >= &0)`;;
let aff_sgn_insert_sym_lt_t = `aff_sgn_insert_sym (\t. t < &0)`;;
let aff_sgn_insert_sym_le_t = `aff_sgn_insert_sym (\t. t <= &0)`;;

let azim_hyp_t = `azim_hyp`;;
let azim_cycle_hyp_t = `azim_cycle_hyp`;;

(* definitions without obligations *)

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
                       else aff_sgn_insert (\t. t > &0) v (aff_gt S1 S)))`;;

let aff_ge_t = `!S1.
          (aff_ge S1 {} = aff S1) /\
             (!v S.
                  FINITE S
                  ==> aff_ge S1 (v INSERT S) =
                      (if v IN S
                       then aff_ge S1 S
                       else aff_sgn_insert (\t. t >= &0) v (aff_ge S1 S)))`;;

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

let azim_t = `!v w w1 w2 e1 e2 e3.
         ?psi h1 h2 r1 r2.
                 ~collinear {v, w, w1} /\
                 ~collinear {v, w, w2} /\
                 orthonormal e1 e2 e3 /\
                 (d3 w v *# e3 = w - v)
             ==> &0 <= azim v w w1 w2 /\
                 azim v w w1 w2 < &2 * pi /\
                 &0 < r1 /\
                 &0 < r2 /\
                 w1 =
                 (r1 * cos psi) *# e1 + (r1 * sin psi) *# e2 + h1 *# (w - v) /\
                 (w2 =
                 (r2 * cos (psi + azim v w w1 w2)) *# e1 +
                 (r2 * sin (psi + azim v w w1 w2)) *# e2 +
                 h2 *# (w - v))`;;

let azim_cycle_t = `!W proj v w e1 e2 e3 p.
             W p /\
             cyclic_set W v w /\
             (d3 v w *# e3 = w - v) /\
             orthonormal e1 e2 e3 /\
             (!u x y.
                  proj u = x,y <=> (?h. u = v + x *# e1 + y *# e2 + h *# e3))
         ==> (proj (azim_cycle W p) = polar_cycle (IMAGE proj W) (proj p))`;;


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
  val aff_insert_sym : thm (*  aff_insert_sym_t *)
  val aff_sgn_insert_sym_gt : thm (*  aff_sgn_insert_sym_gt_t *)
  val aff_sgn_insert_sym_ge : thm (*  aff_sgn_insert_sym_ge_t *)
  val aff_sgn_insert_sym_lt : thm (*  aff_sgn_insert_sym_lt_t *)
  val aff_sgn_insert_sym_le : thm (*  aff_sgn_insert_sym_le_t *)
  val azim_hyp : thm (*  azim_hyp_t *)
  val azim_cycle_hyp : thm (*  azim_cycle_hyp_t *)
  val aff : thm (* aff_t *)
  val aff_gt : thm (*  aff_gt_t   *)
  val aff_ge : thm (*  aff_ge_t   *)
  val aff_lt : thm (*  aff_lt_t   *)
  val aff_le : thm (*  aff_le_t   *)
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
  aff_insert_sym_t ;
  aff_sgn_insert_sym_gt_t ;
  aff_sgn_insert_sym_ge_t ;
  aff_sgn_insert_sym_lt_t ;
  aff_sgn_insert_sym_le_t ;
  azim_hyp_t ;
  azim_cycle_hyp_t ;
  aff_t;
  aff_gt_t;
  aff_ge_t;
  aff_lt_t;
  aff_le_t;
  azim_t;
  azim_cycle_t;
   ])));;

(* axiomatic implementation of  Trigsig *)

(* 

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
  let atn2_spec = trigAxiomProofB atn2_spec_t
  let sin_acs = trigAxiomProofB sin_acs_t
  let acs_atn2 = trigAxiomProofB  acs_atn2_t 
  let  arcVarc = trigAxiomProofB   arcVarc_t 
  let  law_of_cosines = trigAxiomProofB   law_of_cosines_t 
  let  law_of_sines = trigAxiomProofB   law_of_sines_t 
  let  cross_mag = trigAxiomProofB   cross_mag_t 
  let  cross_skew = trigAxiomProofB cross_skew_t
  let  cross_triple = trigAxiomProofB   cross_triple_t 
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
  let  azim = trigAxiomProofB   azim_t
  let  azim_cycle = trigAxiomProofB   azim_cycle_t
end;;

open Trig;;

*)
