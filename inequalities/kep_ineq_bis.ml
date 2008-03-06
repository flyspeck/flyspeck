(* Added inequalities 2008 *)


(* Let's start with Ferguson's thesis. *)


(* LOC: DCG 2006, V, page 197. Calc 17.4.1.1. *)

(* verification uses dimension reduction *)
let I_7728905995=
  all_forall `ineq
   [((#4.0),x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    ((#4.0),x6,square_2t0)
   ]
   ( (gamma_x x1 x2 x3 x4 x5 x6 < pp_a1 *  dih_x x1 x2 x3 x4 x5 x6 - pp_a2) \/
   (gamma_x x1 x2 x3 x4 x5 x6 < -- (#0.52) *  pt))`;;


(* LOC: DCG 2006, V, page 197. Calc 17.4.1.2. *)

(* verification uses dimension reduction *)
let I_8421744162=
  all_forall `ineq
   [((#4.0),x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    ((#4.0),x6,square_2t0)
   ]
   ( (gamma_x x1 x2 x3 x4 x5 x6 < pp_a1 *  dih_x x1 x2 x3 x4 x5 x6 + (#3.48 *  pt) - (#2.0 * pi * pp_a1) + (#4.0 * pp_a2)) \/
   (gamma_x x1 x2 x3 x4 x5 x6 < -- (#0.52) *  pt) \/
   (dih_x x1 x2 x3 x4 x5 x6 < pp_d0))`;;

(* LOC: DCG 2006, V, page 197. Calc 17.4.1.3. *)

(* verification uses dimension reduction *)
let I_2045090718=
   all_forall `ineq
   [((#4.0),x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    ((#4.0),x6,square_2t0)
   ]
   ( (gamma_x x1 x2 x3 x4 x5 x6 + pp_m * sol_x x1 x2 x3 x4 x5 x6 +
     pp_a * (dih_x x1 x2 x3 x4 x5 x6 - #2.0 * pi / #5.0) < pp_bc) \/
       (gamma_x x1 x2 x3 x4 x5 x6 < -- (#0.52) *  pt) \/
   (dih_x x1 x2 x3 x4 x5 x6 > pp_d0))`;;


(* LOC: DCG 2006, V, page 198. Calc 17.4.2.1. *)

(* verification uses dimension reduction.  See note on Calc 17.4.2.2 
   *)

let I_9046001781=
all_forall `ineq
   [((#4.0),x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    (square_2t0,x6,(#8.0))
   ]
   ( (gamma_x x1 x2 x3 x4 x5 x6 + pp_m * sol_x x1 x2 x3 x4 x5 x6  < pp_bc / (#2.0)) \/
       (eta_x x1 x2  x6 >  sqrt2) \/
       (eta_x x4 x5  x6 >  sqrt2) \/
   (gamma_x x1 x2 x3 x4 x5 x6 < -- (#1.04)*  pt))`;;

(* LOC: DCG 2006, V, page 198. Calc 17.4.2.2. *)
(* I am not including this inequality because I don't see that it is needed.
   Ferguson gives a special boundary case of the inequality 9046001781 here, because
   he sees the dimension reduction as not applying in a boundary case.  It seems
   to me that dimension reduction in the previous ineq is entirely justified. *)




(* LOC: DCG 2006, V, page 198. Calc 17.4.2.3. *)
(* LOC: DCG 2006, V, page 199. Calc 17.4.2.4. *)
(* LOC: DCG 2006, V, page 199. Calc 17.4.2.5. *)
(* LOC: DCG 2006, V, page 199. Calc 17.4.2.6. *)

(* Ferguson separates the following two interval calculations into four cases,
depending on things like derivative information,
dimension reduction, a separate calculation in a small
neighborhood of the tight corner at (2,2,2,2,2,Sqrt[8]), etc. 
I am combining them here.  Ferguson's discussion may be needed in their formal
verification. *)

let I_4075001492=
all_forall `ineq
   [((#4.0),x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    (square_2t0,x6,(#8.0))
   ]
   ( (vor_analytic_x x1 x2 x3 x4 x5 x6 + pp_m * sol_x x1 x2 x3 x4 x5 x6  < pp_bc / (#2.0)) \/
       (eta_x x1 x2  x6 < sqrt2) \/
   (vor_analytic_x x1 x2 x3 x4 x5 x6 < -- (#1.04)*  pt))`;;

let I_8777240900=
all_forall `ineq
   [((#4.0),x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    (square_2t0,x6,(#8.0))
   ]
   ( (vor_analytic_x x1 x2 x3 x4 x5 x6 + pp_m * sol_x x1 x2 x3 x4 x5 x6  < pp_bc / (#2.0)) \/
       (eta_x x4 x5  x6 < sqrt2) \/
   (vor_analytic_x x1 x2 x3 x4 x5 x6 < -- (#1.04)*  pt))`;;





(* LOC: DCG 2006, V, page 199. Calc 17.4.3.1. *)
(* upright quarters in an octahedron *)

let I_4780480978=
all_forall `ineq
   [(square_2t0,x1,(#8.0));
    (square (#2.2),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    ((#4.0),x6,square_2t0)
   ]
   ( (octavor_analytic_x x1 x2 x3 x4 x5 x6 < -- (#0.52) *  pt) \/
     (eta_x x1 x2 x6 < sqrt2))`;;


let I_1520829511=
all_forall `ineq
   [(square_2t0,x1,(#8.0));
    (square (#2.2),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    ((#4.0),x6,square_2t0)
   ]
   ( (octavor_analytic_x x1 x2 x3 x4 x5 x6 < -- (#0.52) *  pt) \/
     (eta_x x1 x3 x5 < sqrt2))`;;

let I_6529801070=
all_forall `ineq
   [(square_2t0,x1,(#8.0));
    (square (#2.2),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    ((#4.0),x6,square_2t0)
   ]
   (gamma_x x1 x2 x3 x4 x5 x6 < -- (#0.52) *  pt)`;;


(* LOC: DCG 2006, V, page 199. Calc 17.4.3.2. *)

let I_2301260168=
all_forall `ineq
   [(square_2t0,x1,square (#2.716));
    ((#4.0),x2,square (#2.2));
    ((#4.0),x3,square (#2.2));
    ((#4.0),x4,square (#2.2));
    ((#4.0),x5,square (#2.2));
    ((#4.0),x6,square (#2.2))
   ]
   ((gamma_x x1 x2 x3 x4 x5 x6 + pp_c * dih_x x1 x2 x3 x4 x5 x6 < pp_d) \/
    (gamma_x x1 x2 x3 x4 x5 x6 < -- (#1.04) * pt))`;;

(* LOC: DCG 2006, V, page 200. Calc 17.4.3.3. *)

let I_9580162379=
all_forall `ineq
   [(square (#2.716),x1,(#8.0));
    ((#4.0),x2,square (#2.2));
    ((#4.0),x3,square (#2.2));
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square (#2.2));
    ((#4.0),x6,square (#2.2))
   ]
   ((gamma_x x1 x2 x3 x4 x5 x6 + pp_m * sol_x x1 x2 x3 x4 x5 x6 
       + (#0.14) * dih_x x1 x2 x3 x4 x5 x6  < pp_b /  (#4.0) + (#0.14)* pi/  (#2.0)) \/
    (gamma_x x1 x2 x3 x4 x5 x6 < -- (#1.04) * pt) \/
           (eta_x x1 x2  x6 >  sqrt2) \/
       (eta_x x1 x3  x5 >  sqrt2))`;;


(* LOC: DCG 2006, V, page 200. Calc 17.4.3.4. *)

let I_2785497175=
all_forall `ineq
   [(square (#2.716),x1,square (#2.81));
    ((#4.0),x2,square (#2.2));
    ((#4.0),x3,square (#2.2));
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square (#2.2));
    ((#4.0),x6,square (#2.2))
   ]
   ((octavor_analytic_x x1 x2 x3 x4 x5 x6 + pp_m * sol_x x1 x2 x3 x4 x5 x6 
       + (#0.14) * dih_x x1 x2 x3 x4 x5 x6  < pp_b /  (#4.0) + (#0.14)* pi/  (#2.0)) \/
    (octavor_analytic_x x1 x2 x3 x4 x5 x6 < -- (#1.04) * pt) \/
           (eta_x x1 x2  x6 >  sqrt2))`;;

(* LOC: DCG 2006, V, page 200. Calc 17.4.3.5. *)

let I_5112922270=
all_forall `ineq
   [(square (#2.81),x1,(#8.0));
    ((#4.0),x2,square (#2.2));
    ((#4.0),x3,square (#2.2));
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square (#2.2));
    ((#4.0),x6,square (#2.2))
   ]
   ((gamma_x x1 x2 x3 x4 x5 x6 + pp_m * sol_x x1 x2 x3 x4 x5 x6 
       + (#0.054) * dih_x x1 x2 x3 x4 x5 x6  + (#0.00455) * (x1- (#8.0)) < 
          pp_b /  (#4.0) + (#0.054)* pi/  (#2.0)) \/
    (gamma_x x1 x2 x3 x4 x5 x6 < -- (#1.04) * pt) \/
           (eta_x x1 x2  x6 >  sqrt2) \/
       (eta_x x1 x3  x5 >  sqrt2))`;;


(* LOC: DCG 2006, V, page 200. Calc 17.4.3.6. *)

let I_8586415208=
all_forall `ineq
   [(square (#2.81),x1,(#8.0));
    ((#4.0),x2,square (#2.2));
    ((#4.0),x3,square (#2.2));
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square (#2.2));
    ((#4.0),x6,square (#2.2))
   ]
   ((octavor_analytic_x x1 x2 x3 x4 x5 x6 + pp_m * sol_x x1 x2 x3 x4 x5 x6 
       + (#0.054) * dih_x x1 x2 x3 x4 x5 x6  -  (#0.00455) * (x1- (#8.0)) < 
          pp_b /  (#4.0) + (#0.054)* pi/  (#2.0)) \/
    (octavor_analytic_x x1 x2 x3 x4 x5 x6 < -- (#1.04) * pt) \/
       (eta_x x1 x2  x6 >  sqrt2))`;;


(* LOC: DCG 2006, V, page 201. Calc 17.4.4.1. *)
(* pure Voronoi quad clusters, sigma is sqrt-2 truncated Voronoi *)
(* acute case *)

let I_1017762470=
all_forall `ineq
   [((#4.0),x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    (square (#2.84),x6,(#16.0))
   ]
   ((vort_x  x1 x2 x3 x4 x5 x6 sqrt2 + pp_m * sol_x x1 x2 x3 x4 x5 x6 
         < pp_b /  (#2.0)) \/
    (sol_x x1 x2 x3 x4 x5 x6 < pp_solt0) \/
    (x1 + x2 < x6) \/
       (vort_x x1 x2 x3 x4 x5 x6 sqrt2 < -- (#1.04) *  pt))`;;


(* LOC: DCG 2006, V, page 201. Calc 17.4.4.... *)
(* See note in DCG errata.  We need to check that each half is nonpositive for the proof
   of Lemma DCG 16.7, page 182. *)

let I_5127197465=
all_forall `ineq
   [((#4.0),x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    ((#8.0),x6,(#16.0))
   ]
   ((vort_x  x1 x2 x3 x4 x5 x6 sqrt2 < (#0.0)) \/
    (x1 + x2 < x6))`;;


(* LOC: DCG 2006, V, page 201. Calc 17.4.4.2. *)
(* LOC: DCG 2006, V, page 201. Calc 17.4.4.3. *)
(* pure Voronoi quad clusters, sigma is sqrt-2 truncated Voronoi *)
(* acute case *)
(* This is separated into 2 cases in Ferguson. *)

let I_2314721799=
all_forall `ineq
   [((#4.0),x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    ((#8.0),x6,square (#2.84))
   ]
   ((vort_x  x1 x2 x3 x4 x5 x6 sqrt2 + pp_m * sol_x x1 x2 x3 x4 x5 x6 
         < pp_b /  (#2.0)) \/
    (sol_x x1 x2 x3 x4 x5 x6 < pp_solt0) \/
    (x1 + x2 < x6) \/
       (vort_x x1 x2 x3 x4 x5 x6 sqrt2 < -- (#1.04) *  pt))`;;


(* LOC: DCG 2006, V, page 201. Calc 17.4.4.4. *)
(* pure Voronoi quad clusters, sigma is sqrt-2 truncated Voronoi *)
(* obtuse case *)


let I_6318537815=
all_forall `ineq
   [((square ((#4.0)/(#2.51))),x,square_2t0);
    ((#8.0),ds,((#2.0)* square_2t0))
   ]
   ((vort_x  (#4.0) (#4.0) (#4.0) x x ds sqrt2 + pp_m * sol_x (#4.0) (#4.0) (#4.0) x x ds
         < pp_b /  (#2.0)) \/
      (vort_x (#4.0) (#4.0) (#4.0) x x ds sqrt2 < -- (#0.52) *  pt) \/
    (sol_x (#4.0) (#4.0) (#4.0) x x ds  < pp_solt0) \/
    ((#2.0) * x < ds))`;;

(* LOC: DCG 2006, V, page 201. Calc 17.4.4.5. *)
(* pure Voronoi quad clusters, sigma is sqrt-2 truncated Voronoi *)
(* obtuse case *)


let I_6737436637=
all_forall `ineq
   [((square ((#4.0)/(#2.51))),x1,square_2t0);
    ((square ((#4.0)/(#2.51))),x2,square_2t0)
   ]
   ((vort_x  (#4.0) (#4.0) (#4.0) x1 x1 (#8.0) sqrt2  + vort_x  (#4.0) (#4.0) (#4.0) x2 x2 (#8.0) sqrt2
       + pp_m * (sol_x (#4.0) (#4.0) (#4.0) x1 x1 (#8.0) + sol_x (#4.0) (#4.0) (#4.0) x2 x2 (#8.0))
         < pp_b) \/
      (vort_x (#4.0) (#4.0) (#4.0) x1 x1 (#8.0) sqrt2 + vort_x (#4.0) (#4.0) (#4.0) x2 x2 (#8.0) sqrt2  < -- (#1.04) *  pt) \/
    (sol_x (#4.0) (#4.0) (#4.0) x1 x1 (#8.0) + sol_x (#4.0) (#4.0) (#4.0) x2 x2 (#8.0)  < (#2.0) *  pp_solt0))`;;


(* LOC: DCG 2006, V, page 201. Calc 17.4.5.1.  DCG, V, page 174, Theorem 16.1. *)
(* This 91-term polynomial is used to justify dimension reduction for vol_analytic_x. *)
(* Ferguson states two cases, but the second case covers the first as well. *)

let I_2298281931=
all_forall `ineq
   [
   ((#4.0),x1,square_2t0);
   ((#4.0),x2,square_2t0);
   ((#4.0),x3,square_2t0);
   ((#4.0),x4,square_2t0);
   ((#4.0),x5,square_2t0);
   ((#4.0),x6,(#8.0))
   ]
   (((x1 pow 5)*x4 - (&2)*(x1 pow 4)*x2*x4 + (x1 pow 3)*(x2 pow 2)*x4 - (&2)*(x1 pow 4)*x3*x4 + 
   (&4)*(x1 pow 3)*x2*x3*x4 - (&2)*(x1 pow 2)*(x2 pow 2)*x3*x4 + (x1 pow 3)*(x3 pow 2)*x4 - 
   (&2)*(x1 pow 2)*x2*(x3 pow 2)*x4 + x1*(x2 pow 2)*(x3 pow 2)*x4 - (x1 pow 4)*x2*x5 + 
   (&2)*(x1 pow 3)*(x2 pow 2)*x5 - (x1 pow 2)*(x2 pow 3)*x5 + (x1 pow 4)*x3*x5 - 
   (x1 pow 3)*x2*x3*x5 - (x1 pow 2)*(x2 pow 2)*x3*x5 + x1*(x2 pow 3)*x3*x5 - 
   (x1 pow 3)*(x3 pow 2)*x5 + (&2)*(x1 pow 2)*x2*(x3 pow 2)*x5 - 
   x1*(x2 pow 2)*(x3 pow 2)*x5 - (&2)*(x1 pow 4)*x4*x5 + (&4)*(x1 pow 3)*x2*x4*x5 - 
   (&2)*(x1 pow 2)*(x2 pow 2)*x4*x5 + (&2)*(x1 pow 3)*x2*(x5 pow 2) - 
   (&4)*(x1 pow 2)*(x2 pow 2)*(x5 pow 2) + (&2)*x1*(x2 pow 3)*(x5 pow 2) - 
   (x1 pow 3)*x3*(x5 pow 2) + (&3)*(x1 pow 2)*x2*x3*(x5 pow 2) - 
   (&3)*x1*(x2 pow 2)*x3*(x5 pow 2) + (x2 pow 3)*x3*(x5 pow 2) + (x1 pow 3)*x4*(x5 pow 2) - 
   (&2)*(x1 pow 2)*x2*x4*(x5 pow 2) + x1*(x2 pow 2)*x4*(x5 pow 2) - 
   (x1 pow 2)*x2*(x5 pow 3) + (&2)*x1*(x2 pow 2)*(x5 pow 3) - (x2 pow 3)*(x5 pow 3) + 
   (x1 pow 4)*x2*x6 - (x1 pow 3)*(x2 pow 2)*x6 - (x1 pow 4)*x3*x6 - (x1 pow 3)*x2*x3*x6 + 
   (&2)*(x1 pow 2)*(x2 pow 2)*x3*x6 + (&2)*(x1 pow 3)*(x3 pow 2)*x6 - 
   (x1 pow 2)*x2*(x3 pow 2)*x6 - x1*(x2 pow 2)*(x3 pow 2)*x6 - (x1 pow 2)*(x3 pow 3)*x6 + 
   x1*x2*(x3 pow 3)*x6 - (&2)*(x1 pow 4)*x4*x6 + (&4)*(x1 pow 3)*x3*x4*x6 - 
   (&2)*(x1 pow 2)*(x3 pow 2)*x4*x6 - (x1 pow 3)*x2*x5*x6 + (&3)*(x1 pow 2)*(x2 pow 2)*x5*x6 - 
   (x1 pow 3)*x3*x5*x6 - (&4)*(x1 pow 2)*x2*x3*x5*x6 + x1*(x2 pow 2)*x3*x5*x6 + 
   (&3)*(x1 pow 2)*(x3 pow 2)*x5*x6 + x1*x2*(x3 pow 2)*x5*x6 - 
   (&2)*(x2 pow 2)*(x3 pow 2)*x5*x6 + (&4)*(x1 pow 3)*x4*x5*x6 - (&4)*x1*x2*x3*x4*x5*x6 - 
   (x1 pow 2)*x2*(x5 pow 2)*x6 - (&3)*x1*(x2 pow 2)*(x5 pow 2)*x6 + 
   (&2)*(x1 pow 2)*x3*(x5 pow 2)*x6 + x1*x2*x3*(x5 pow 2)*x6 + (x2 pow 2)*x3*(x5 pow 2)*x6 - 
   (&2)*(x1 pow 2)*x4*(x5 pow 2)*x6 + x1*x2*(x5 pow 3)*x6 + (x2 pow 2)*(x5 pow 3)*x6 - 
   (x1 pow 3)*x2*(x6 pow 2) + (&2)*(x1 pow 3)*x3*(x6 pow 2) + 
   (&3)*(x1 pow 2)*x2*x3*(x6 pow 2) - (&4)*(x1 pow 2)*(x3 pow 2)*(x6 pow 2) - 
   (&3)*x1*x2*(x3 pow 2)*(x6 pow 2) + (&2)*x1*(x3 pow 3)*(x6 pow 2) + 
   x2*(x3 pow 3)*(x6 pow 2) + (x1 pow 3)*x4*(x6 pow 2) - (&2)*(x1 pow 2)*x3*x4*(x6 pow 2) + 
   x1*(x3 pow 2)*x4*(x6 pow 2) + (&2)*(x1 pow 2)*x2*x5*(x6 pow 2) - 
   (x1 pow 2)*x3*x5*(x6 pow 2) + x1*x2*x3*x5*(x6 pow 2) - (&3)*x1*(x3 pow 2)*x5*(x6 pow 2) + 
   x2*(x3 pow 2)*x5*(x6 pow 2) - (&2)*(x1 pow 2)*x4*x5*(x6 pow 2) - 
   x1*x2*(x5 pow 2)*(x6 pow 2) - x1*x3*(x5 pow 2)*(x6 pow 2) - 
   (&2)*x2*x3*(x5 pow 2)*(x6 pow 2) + x1*x4*(x5 pow 2)*(x6 pow 2) - 
   (x1 pow 2)*x3*(x6 pow 3) + (&2)*x1*(x3 pow 2)*(x6 pow 3) - (x3 pow 3)*(x6 pow 3) + 
   x1*x3*x5*(x6 pow 3) + (x3 pow 2)*x5*(x6 pow 3)) < (#0.0))`;;


(* End of Sphere Packings V, DCG, Ferguson's thesis *)









