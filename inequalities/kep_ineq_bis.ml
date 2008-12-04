(* Added inequalities 2008 *)








(* LOC: New proof of -1.04 bound [lemma:1.04] BLUEPRINT.
*)

(* if any top edge is 2.43 or more, then < -1.04 pt *)


let I_8227268739_GEN=
   `(\ a1 a2 a3 a4. (ineq
[
((#8.0), x, (square (#4.0)))]
   (vor_0_x a4 a1 a2 (#4.0) x (square (#2.43))  +
    vor_0_x a2 a3 a4 (#4.0) x (#4.0) < -- (#1.04) * pt) \/
    delta_x a4 a1 a2 (#4.0) x (square (#2.43))  < (#0.0) \/
    delta_x a2 a3 a4 (#4.0) x (#4.0) < (#0.0) \/
  (cross_diag_x a1 a2 a4 x (square (#2.43)) (#4.0) a3 (#4.0) (#4.0) < sqrt8)))`;;

let rec binexpand i j = 
 if (j <= 0) then []
           else [ (i mod 2)] @ (binexpand  (i / 2) (j-1));;

let mk_8227268739 i=
  all_forall (list_mk_comb( I_8227268739_GEN,
  map (fun j->if (j=0) then `#4.0` else `square (#2.3)`) (binexpand i 4)));;

let [I_8227268739_0;I_8227268739_1;I_8227268739_2;I_8227268739_3;
     I_8227268739_4;I_8227268739_5;I_8227268739_6;I_8227268739_7;
     I_8227268739_8;I_8227268739_9;I_8227268739_10;I_8227268739_11;
     I_8227268739_12;I_8227268739_13;I_8227268739_14;I_8227268739_15]=
 map mk_8227268739 (0 -- 15);;

(* if a diagonal hits sqrt8 : *)

let I_8227268739_16=
all_forall `ineq
   [((#4.0),x1,(square (#2.3)));
    ((#4.0),x2,(square (#2.3)));
    ((#4.0),x3,(square (#2.3)));
    ((#8.0),x4,(#8.0));
    ((square (#2.43)),x5,(square (#2.43)));
    ((#4.0),x6,(#4.0))
   ]
   (vor_0_x  x1 x2 x3 x4 x5 x6  < -- (#1.04) * pt - (#0.009))`;;


let I_8227268739_17=
all_forall `ineq
   [((#4.0),x1,(square (#2.3)));
    ((#4.0),x2,(square (#2.3)));
    ((#4.0),x3,(square (#2.3)));
    ((#8.0),x4,(#8.0));
    ((square (#2.43)),x5,(square (#2.43)));
    ((#4.0),x6,(#4.0))
   ]
   (vor_0_x  x1 x2 x3 x4 x5 x6  < -- (#1.04) * pt - (#0.009))`;;

(* 6337649845 deleted, March 21, 2008 *)



(* Next one is a consequence of others and deformation.  Don't prove separately. *)

let I_8227268739_99=
all_forall `ineq
  [( (#4.0),x0, square_2t0);
   ( (#4.0),x1, square_2t0);
   ( (#4.0),x2, square_2t0);
   ( (#8.0),x3, (#8.0));
   ( (square (#2.43)),x4, square_2t0);
   ( (#4.0),x4, square_2t0);
   ( (#4.0),x5, square_2t0);
   ( (#4.0),x6, square_2t0);
   ( (#4.0),x7, square_2t0)
  ]
  ( -- (vor_0_x x0 x1 x2 x3 x4 x5)
    - vor_0_x x1 x2 x6 x7 x8 x3 - (#1.04)* pt  > (#0.0))`;;



let I_1852976279=
all_forall `ineq
  [( two_t0,y0, (#8.0));
   ( (#2.0),y1, two_t0);
   ( (#2.0),y2, two_t0);
   ( sqrt8,y3, sqrt8);
   ( (#2.0),y4, two_t0);
   ( (#2.0),y5, two_t0)
  ]
  ( -- (kappa y0 y1 y2 y3 y4 y5) - (#0.019) > (#0.0))`;;



let I_8587053087=
all_forall `ineq
  [( two_t0,x0, sqrt8);
   ( (#2.0),x1, two_t0);
   ( (#2.0),x2, two_t0);
   ( (#2.0),x3, two_t0);
   ( (#2.0),x4, two_t0)
  ]
  ( -- (kappa_dih_y y0 y1 y2 y3 y4 (#2.9)) - (#0.019) > (#0.0))`;;



let I_9401027298=
all_forall `ineq
  [( square_2t0,x0, (#8.0));
   ( (#4.0),x1, square_2t0);
   ( (#4.0),x2, square_2t0);
   ( (#4.0),x3, (square (#2.43)));
   ( (#4.0),x4, (square (#3.17)));
   ( (#4.0),x5, (square (#3.17)))
  ]
  ( -- (dih_x x0 x1 x2 x3 x4 x5) + (#2.0672) > (#0.0))`;;



let I_8713619400=
all_forall `ineq
  [( square_2t0,x0, (#8.0));
   ( (#4.0),x1, square_2t0);
   ( (#4.0),x2, square_2t0);
   ( (#4.0),x3, (#4.0));
   ( (square (#3.17)),x4, (square (#3.8)));
   ( (#4.0),x5, (square (#3.17)))
  ]
  ( -- (dih_x x0 x1 x2 x3 x4 x5)  + (#1.0743) > (#0.0))`;;



let I_5815318817=
all_forall `ineq
  [( square_2t0,x0, (#8.0));
   ( (#4.0),x1, square_2t0);
   ( (#4.0),x2, square_2t0);
   ( (#4.0),x3, (#4.0));
   ( (square (#3.17)),x4, (square (#3.8)));
   ( (square (#3.17)),x5, (square (#3.8)))
  ]
  ( -- (dih_x x0 x1 x2 x3 x4 x5) + (#2.0672)  > (#0.0))`;;



let I_5817445944=
all_forall `ineq
  [( square_2t0,x0, (#8.0));
   ( (#4.0),x1, square_2t0);
   ( (#4.0),x2, square_2t0);
   ( (#4.0),x3, square_2t0);
   ( square_2t0,x4, (square (#3.17)));
   ( square_2t0,x5, (square (#3.17)))
  ]
  ( -- (vor_0_x x0 x1 x2 x3 x4 x5) - (#0.05) > (#0.0))`;;



let I_5781533845=
all_forall `ineq
  [( square_2t0,x0, (#8.0));
   ( (#4.0),x1, square_2t0);
   ( (#4.0),x2, square_2t0);
   ( (#4.0),x3, square_2t0);
   ( (#4.0),x4, square_2t0);
   ( square_2t0,x5, (square (#3.17)))
  ]
  ( -- (vor_0_x x0 x1 x2 x3 x4 x5) + (#0.005) > (#0.0))`;;



let I_3006850743=
all_forall `ineq
  [( square_2t0,x0, (#8.0));
   ( (#4.0),x1, square_2t0);
   ( (#4.0),x2, square_2t0);
   ( (#4.0),x3, square_2t0);
   ( (#4.0),x4, (#4.0));
   ( square_2t0,x5, square_2t0)
  ]
  ( -- (vor_0_x x0 x1 x2 x3 x4 x5)  > (#0.0))`;;



let I_3915426488=
all_forall `ineq
  [( square_2t0,x0, (#8.0));
   ( (#4.0),x1, square_2t0);
   ( (#4.0),x2, square_2t0);
   ( (#4.0),x3, square_2t0);
   ( (#4.0),x4, square_2t0);
   ( square_2t0,x5, square_2t0);
   ( (#4.0),x6, square_2t0);
   ( (#4.0),x7, square_2t0);
   ( (#4.0),x8, square_2t0)
  ]
  (( -- (vor_0_x x0 x1 x2 x3 x4 x5 )
    - vor_0_x x0 x1 x8 x6 x7 x5 - (#0.039) > (#0.0)) \/
  ( -- dih_x x0 x1 x2 x3 x4 x5 
    -dih_x x0 x1 x8 x6 x7 x5+ (#2.9) > (#0.0)))`;;



let I_7031224851=
all_forall `ineq
  [( square_2t0,x0, (#8.0));
   ( (#4.0),x1, square_2t0);
   ( (#4.0),x2, square_2t0);
   ( (#4.0),x3, square_2t0);
   ( (#4.0),x4, square_2t0);
   ( square_2t0,x5, square_2t0);
   ( (#4.0),x6, square_2t0);
   ( (#4.0),x7, square_2t0);
   ( (#4.0),x8, square_2t0)
  ]
  (( -- (vor_0_x x0 x1 x2 x3 x4 x5 )
    -vor_0_x x0 x1 x8 x6 x7 x5 - (#0.035) > (#0.0)) \/
   ( sqrt8 - crossdiag_x x0 x1 x2 x3 x4 x5 x6 x7 x8   > (#0.0)))`;;


(*  gamma branch. *)

let I_2172978729_1=
all_forall `ineq
  [( square_2t0,x0, (#8.0));
   ( (#4.0),x1, square_2t0);
   ( (#4.0),x2, square_2t0);
   ( (#4.0),x3, square_2t0);
   ( (#4.0),x4, square_2t0);
   ( (#4.0),x5, square_2t0)
  ]
  (( -- (nu_x x0 x1 x2 x3 x4 x5) - (#0.0036) > (#0.0)) \/
  (pi  - (#2.9) / (#2.0) - dih_x x0 x1 x2 x3 x4 x5 > (#0.0) ))`;;


(* vor branch. *)

let I_2172978729_2=
all_forall `ineq
  [( square_2t0,x0, (#8.0));
   ( (#4.0),x1, square_2t0);
   ( (#4.0),x2, square_2t0);
   ( (#4.0),x3, square_2t0);
   ( (#4.0),x4, square_2t0);
   ( (#4.0),x5, square_2t0)
  ]
  (( -- (nu_x x0 x1 x2 x3 x4 x5) - (#0.0036) > (#0.0)) \/
   (pi  - (#2.9) / (#2.0) - dih_x x0 x1 x2 x3 x4 x5 > (#0.0) ) \/
   (sqrt2 - eta_x x0 x1 x5 > (#0.0) ))`;;



let I_1480860075=
all_forall `ineq
  [( square_2t0,x0, (#8.0));
   ( square_2t0,x1, square_2t0);
   ( (#4.0),x2, square_2t0);
   ( (#4.0),x3, (#4.0));
   ( (#4.0),x4, square_2t0);
   ( square_2t0,x5, (square (#3.17)))
  ]
  ( -- (vor_0_x x0 x1 x2 x3 x4 x5) - (#0.02) > (#0.0))`;;



let I_6479729349=
all_forall `ineq
  [( square_2t0,x0, (#8.0));
   ( (#4.0),x1, (#4.0));
   ( (#4.0),x2, square_2t0);
   ( (#4.0),x3, (#4.0));
   ( (#4.0),x4, square_2t0);
   ( square_2t0,x5, (square (#3.17)))
  ]
  ( -- (dih_x x0 x1 x2 x3 x4 x5) + pi / (#2.0) > (#0.0))`;;



let I_1741049647=
all_forall `ineq
  [( square_2t0,x0, (#8.0));
   ( (#4.0),x1, square_2t0);
   ( (#4.0),x2, square_2t0);
   ( square_2t0,x3, (square (#3.17)));
   ( (#4.0),x4, square_2t0);
   ( (#4.0),x5, square_2t0)
  ]
  (( sqrt8 - crossdiag_x x1 x0 (#4.0) x3 (#4.0) x5 x2 (#4.0) x4  > (#0.0)) \/
   ( -- (vor_0_x x0 x1 (#4.0) (#4.0) x3 x5)
    -vor_0_x x0 x2 (#4.0) (#4.0) x3 x4 
    -kappa (sqrt x0) (sqrt x1) (sqrt x2) sqrt8 (sqrt x4) (sqrt x5) - (#1.04)*pt > (#0.0) ))`;;


(* 
Inequalities added October 30, 2008 for use in "A Revision of the Kepler Conjecture" biconnected argument.
*)

(* LOC: DCG 2006, V, page 201. Calc 17.4.4.... *)
(* See note in DCG errata.  We need to check that each half is nonpositive for the proof
   of Lemma DCG 16.7, page 182. 


CCC fixed x1 x2 bounds
Bound: 0.152942962259

Point: [6.30009985876, 6.30009985876, 4.00000006053, 4.00000007573, 4.00000007573, 12.6001995643]

*)

let I_5127197465=
all_forall `ineq
   [((#4.0),x1,(square (#2.3)));
    ((#4.0),x2,(square (#2.3)));
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    ((#8.0),x6,(#16.0))
   ]
   ((vort_x  x1 x2 x3 x4 x5 x6 sqrt2 <= (#0.0)) \/
    (x1 + x2 < x6))`;;

(* add inequality that vor_0 of quad cluster is < -1.04 pt if any vertex ht > 2.3.  By dimension reduction (DCG Lemma 13.1, Lemma 12.10) 
it reduces to the following cases.  
This also gives vort_x ... sqrt2 < -1.04 pt. *)


(* lemma:three-edge *)
(* verified by S. McLaughlin Nov 3, 2008 *)
(* biconnected section *)
let I_2799256461=
all_forall `ineq
   [((#4.0),x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,(#4.0));
    (square (#2.91),x5,square (#3.2));
    (square (#2.91),x6,square (#3.2));
   ]
   (dih_x  x1 x2 x3 x4 x5 x6  > (#0.7))`;;

(* lemma:three-edge *)
(* verified by S. McLaughlin Nov 3, 2008 *)
(* biconnected section *)
let I_5470795818=
all_forall `ineq
   [((#4.0),x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,(#4.0));
    ((#4.0),x5,square_2t0);
    ((#4.0),x6,square_2t0);
   ]
   (dih_x  x1 x2 x3 x4 x5 x6  < (#1.4))`;;

(* Revision, lemma:double-cross *)
(* changed 11/25/2008 *)
(* biconnected section *)
let I_7431506800=
all_forall `ineq
   [((#4.0),x1,(square (#2.23)));
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,(#4.0));
    (square(#3.2),x5,square(#3.2));
    (square_2t0,x6,square_2t0); 
   ]
   (dih_x  x1 x2 x3 x4 x5 x6  > (#0.5))`;; 

(* Revision, lemma:double-cross *)
(* changed 11/25/2008 *)
(* biconnected section *)
let I_5568465464 =
all_forall `ineq
   [((#4.0),x1,(square (#2.23)));
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    (square_2t0,x4,square_2t0); 
    (square(#3.2),x5,square(#3.2));
    ((#4.0),x6,square_2t0);
   ]
   (dih_x  x1 x2 x3 x4 x5 x6  > (#0.5))`;; 

(* Revision, lemma:double-cross *)
(* verified by S. McLaughlin Nov 3, 2008 *)
(* biconnected section *)
let I_4741571261 =
all_forall `ineq
   [((#4.0),x1,(square (#2.23)));
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,(#4.0)); 
    (square(#3.2),x5,square(#3.2));
    (square(#3.2),x6,square(#3.2));
   ]
   (dih_x  x1 x2 x3 x4 x5 x6  > (#0.8))`;; 

(* Revision, lemma:double-cross *)
(* revised 11/25/2008 *)
(* biconnected section *)

let I_6915275259 =
all_forall `ineq
   [((#4.0),x1,(square (#2.23)));
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,(#4.0)); 
    ((#4.0),x5,square_2t0);
    ((#4.0),x6,square_2t0);
   ]
   (dih_x  x1 x2 x3 x4 x5 x6  < (#1.3))`;; 

(* 
LOC: Blueprint, Lemma:1.04.
This was never verified with interval arithmetic.
*)


let I_7710172071_GEN=
   `(\ a1 a2 a3 a4. (ineq
[
((#8.0), x, (square (#4.0)))]
   (vor_0_x a4 a1 a2 (#4.0) x (#4.0)  +
    vor_0_x a2 a3 a4 (#4.0) x (#4.0) < -- (#1.04) * pt) \/
    delta_x a4 a1 a2 (#4.0) x (#4.0)  < (#0.0) \/
    delta_x a2 a3 a4 (#4.0) x (#4.0) < (#0.0) \/
  (cross_diag_x a1 a2 a4 x (#4.0) (#4.0) a3 (#4.0) (#4.0) < sqrt8)))`;;

(* wlog a2 <= a4 *)

let I_7710172071_1=
  all_forall (list_mk_comb( I_302085207_GEN,
  [`(square (#2.3))`;`#4.0`;`#4.0`;`#4.0`]));;

(* 
CCC false. fixed square

Bound: 0.47653139353

Point: [8.00000008497]

 *)

let I_7710172071_2=
  all_forall (list_mk_comb( I_302085207_GEN,
  [`(square (#2.3))`;`#4.0`;`#4.0`;`square_2t0`]));;

(* 
CCC false. fixed square

Bound: 0.472007641148

Point: [8.18163440844]
*) 
let I_7710172071_3=
  all_forall (list_mk_comb( I_302085207_GEN,
  [`(square (#2.3))`;`#4.0`;`square_2t0`;`#4.0`]));;


(* 
CCC false. fixed square

Bound: 1.20170306839

Point: [8.00000019731]
*) 

let I_7710172071_4=
  all_forall (list_mk_comb( I_302085207_GEN,
  [`(square (#2.3))`;`#4.0`;`square_2t0`;`square_2t0`]));;

let I_7710172071_5=
  all_forall (list_mk_comb( I_302085207_GEN,
  [`(square (#2.3))`;`square_2t0`;`#4.0`;`square_2t0`]));;

let I_7710172071_6=
  all_forall (list_mk_comb( I_302085207_GEN,
  [`(square (#2.3))`;`square_2t0`;`square_2t0`;`square_2t0`]));;


let I_7710172071_7= 
  all_forall (list_mk_comb( I_302085207_GEN,
  [`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));; 

(* CCC false. fixed square *) 
let I_7710172071_8= 
  all_forall (list_mk_comb( I_302085207_GEN,
  [`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));; 

(* CCC false. fixed square *) 
let I_7710172071_9= 
  all_forall (list_mk_comb( I_302085207_GEN,
  [`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));; 

(* CCC false. fixed square *) 
let I_7710172071_10= 
  all_forall (list_mk_comb( I_302085207_GEN,
  [`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));; 

let I_7710172071_11= 
  all_forall (list_mk_comb( I_302085207_GEN,
  [`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));; 

let I_7710172071_12= 
  all_forall (list_mk_comb( I_302085207_GEN,
  [`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));; 


(* cases when the diagonal hits sqrt8 *)

 let I_7710172071_13= 
 all_forall `ineq 
    [(square (#2.3),x1,square_2t0); 
     ((#4.0),x2,square_2t0); 
     ((#4.0),x3,square_2t0); 
     ((#8.0),x4,(#8.0)); 
     ((#4.0),x5,square_2t0); 
     ((#4.0),x6,square_2t0) 
    ] 
    ((vor_0_x  x1 x2 x3 x4 x5 x6 < -- (#1.04) *pt - (#0.009)))`;; 



 let I_7710172071_14= 
 all_forall `ineq 
    [ 
     ((#4.0),x1,square_2t0); 
      (square (#2.3),x2,square_2t0); 
     ((#4.0),x3,square_2t0); 
     ((#8.0),x4,(#8.0)); 
     ((#4.0),x5,square_2t0); 
     ((#4.0),x6,square_2t0) 
    ] 
    ((vor_0_x  x1 x2 x3 x4 x5 x6  < -- (#0.52) *pt))`;; 






