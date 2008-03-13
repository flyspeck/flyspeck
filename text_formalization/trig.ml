(* Blueprint Chapter  on trig *)

(* sin and cos have already been defined in HOL Light *)

needs "Examples/trans.ml";;
needs "Examples/transc.ml";;

(*
needs "Examples/polylog.ml";;

needs "Jordan/tactics_refine.ml";;
needs "Jordan/lib_ext.ml";;
needs "Jordan/tactics_fix.ml";;
needs "Jordan/parse_ext_override_interface.ml";;
needs "Jordan/tactics_ext.ml";;
needs "Jordan/num_ext_gcd.ml";;
needs "Jordan/num_ext_nabs.ml";;
needs "Jordan/real_ext_geom_series.ml";;
needs "Jordan/num_calc_simp.ml";;
needs "Jordan/real_ext.ml";;
needs "Jordan/float.ml";;
needs "Jordan/tactics_ext2.ml";;
needs "Jordan/misc_defs_and_lemmas.ml";;
needs "Jordan/metric_spaces.ml";;
*)

needs "definitions_kepler.ml";;

prioritize_real();;

sin;;
cos;;
DIFF_SIN;; (* derivative of sin is cos *)
DIFF_COS;; (* derivative of cos is sin *)
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

let law_of_cosines_t = `!a b c. ~(a= &0) /\ ~(b=&0) /\ (a + b >= c) /\ (b + c >= a) /\ (c + a >= b) ==> 
   ((c pow 2) = (a pow 2) + (b pow 2) - &2 * a * b * (cos(arclength a b c)))`;;

let law_of_sines_t = `!a b c. ~(a= &0) /\ ~(b=&0) /\ (a + b >= c) /\ (b + c >= a) /\ (c + a >= b) ==> (&2 * a * b * sin (arclength a b c) = sqrt(ups_x (a pow 2) (b pow 2) (c pow 2)))`;;

let cross_mag_t = `!u v. norm3 (cross u v) = (norm3 u) * (norm3 v) * sin(arcV orig3 u v)`;;

let cross_skew_t = `!u v. (cross u v) = -- (cross v u)`;;

let cross_triple_t = `!u v w. dot3 (cross u v) w = dot3 (cross v w) u`;;

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
	    (cos(c) = (cos(gamma) + cos(alpha)*cos(beta))/(sin(a)*sin(b))))`;;

let dih_formula_t = `!v0 v1 v2 v3. 
   ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) ==>
   (
   let (x1,x2,x3,x4,x5,x6) = xlist v0 v1 v2 v3 in
    (dihV v0 v1 v2 v3  = dih_x x1 x2 x3 x4 x5 x6)
   )`;;

let dih_x_acs_t = `!x1 x2 x3 x4 x5 x6.
   (ups x1 x2 x6 > &0) /\ (ups x1 x3 x5 > &0) /\ (delta_x x1 x2 x3 x4 x5 x6 >= &0) /\ (x1 >= &0) ==>
   dih_x x1 x2 x3 x4 x5 x6 = acs ((delta_x4 x1 x2 x3 x4 x5 x6)/
	((sqrt (ups x1 x2 x6)) * (sqrt (ups x1 x3 x5))))`;;

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

let polar_cycle_rotate_t = `!V psi u.
       let f (x,y) = (x*cos psi + y*sin psi, -- x*sin psi + y*cos psi) in
       FINITE V  /\ V u ==>
       (polar_cycle (IMAGE f V) (f u) =  f (polar_cycle V u))`;;

let thetaij_t = `!theta1 theta2 k12 k21 theta12 theta21.
     (&0 <= theta1) /\ (theta1 < &2 * pi) /\ (&0 <= theta2) /\ (theta2 < &2 * pi) /\
     (theta12 = theta2 - theta1 + &2 * pi * (&k12)) /\
     (theta21 = theta1 - theta2 + &2 * pi * (&k21)) /\
     (&0 <= theta12) /\ (theta12 < &2 * pi) /\
     (&0 <= theta21) /\ (theta21 < &2 * pi) ==>
     ((theta12+theta21) = (if (theta1=theta2) then (&0) else (&2 * pi)))`;;

