(* Added inequalities 2008 *)


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
   ((vort_x  x1 x2 x3 x4 x5 x6 sqrt2 < (#0.0)) \/
    (x1 + x2 < x6))`;;

(* add inequality that vor_0 of quad cluster is < -1.04 pt if any vertex ht > 2.3.  By dimension reduction (DCG Lemma 13.1, Lemma 12.10) 
it reduces to the following cases.  
This also gives vort_x ... sqrt2 < -1.04 pt. *)


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



(* EXPUNGE 3-CROWDED. 
LOC: DCG errata : 
http://flyspeck.googlecode.com/svn/trunk/dcg_errata/dcg_errata.tex
(svn 338)
Added March7,2008.

CCC false
Bound: 0.064541497335

Point: [6.30010733228, 6.30007582978, 5.35475339765, 4.00000309308, 6.30007582977, 5.35475339763]

3/10/2008, changed. octavor_analytic_x to octavor0_x

CCC octavor_0_x is not defined.  I feel like we're programming
in assembly language...

 *)

 let I_9467217686= 
 all_forall `ineq 
    [(square_2t0,x1,(#8.0)); 
     ((#4.0),x2,square_2t0); 
     ((#4.0),x3,square_2t0); 
     ((#4.0),x4,square_2t0); 
     ((#4.0),x5,square_2t0); 
     ((#4.0),x6,square_2t0) 
    ] 
    ((gamma_x  x1 x2 x3 x4 x5 x6 < octavor0_x x1 x2 x3 x4 x5 x6 + 
         (#0.5)*(dih_x x1 x2 x3 x4 x5 x6) - (#0.54125)) \/ 
     (eta_x x1 x2 x6 > sqrt2) \/ (eta_x x1 x3 x5 > sqrt2))`;; 

(* EXPUNGE UPRIGHT DIAG OVER FLAT QUARTER
LOC: DCG errata : 
http://flyspeck.googlecode.com/svn/trunk/dcg_errata/dcg_errata.tex
(svn 338)
Added March7,2008.
It is a consequence of I_2333917810, I_8220246614.
 *)
(* use monotonicity on upper end of y4.  Used for y4 out to 3.2. *)

let I_1427782443=
all_forall `ineq
   [((#2.51),y1,(#2.0)* sqrt2);
    ((#2.0),y2,(#2.51));
    ((#2.0),y3,(#2.51));
    ((#2.91),y4,(#2.91));
    ((#2.0),y5,(#2.51));
    ((#2.0),y6,(#2.51))
   ]
   ((kappa y1 y2 y3 y4 y5 y6 < -- (#0.0201)))`;;

(* (l42)
LOC: DCG errata : 
http://flyspeck.googlecode.com/svn/trunk/dcg_errata/dcg_errata.tex
(svn 338)
Added March7,2008.
 *)

(* use monotonicity on upper end of y4 *)
let I_8220246614=
all_forall `ineq
   [((#2.51),y1,(#2.57));
    ((#2.0),y2,(#2.51));
    ((#2.0),y3,(#2.51));
    ((#2.91),y4,(#2.91)); 
    ((#2.0),y5,(#2.51));
    ((#2.0),y6,(#2.51))
   ]
   ((kappa y1 y2 y3 y4 y5 y6 < -- (#0.022)))`;;

(* (L42)
LOC: DCG errata : 
http://flyspeck.googlecode.com/svn/trunk/dcg_errata/dcg_errata.tex
(svn 338)
Added March7,2008.
 *)

(* use monotonicity on upper end of y4 *)

(* 
XXX false


Bound: 2.88750850026E~4

Point: [2.57000013158, 2.00000021362, 2.50999916311, 2.91, 2.5099991631, 2.00000023519]

*) 
let I_2333917810=
all_forall `ineq
   [((#2.57),y1,(#2.0)*sqrt2);
    ((#2.0),y2,(#2.51));
    ((#2.0),y3,(#2.51));
    ((#2.91),y4,(#2.91)); 
    ((#2.0),y5,(#2.51));
    ((#2.0),y6,(#2.51))
   ]
   ((kappa y1 y2 y3 y4 y5 y6 < -- (#0.03)))`;;


(* L41e257
LOC: DCG errata : 
http://flyspeck.googlecode.com/svn/trunk/dcg_errata/dcg_errata.tex
(svn 338)
Added March7,2008.
 *)

(* use monotonicity on upper end of y4 *)
let I_6863978831=
all_forall `ineq
   [((#2.51),y1,(#2.57));
    ((#2.0),y2,(#2.51));
    ((#2.0),y3,(#2.51));
    ((#2.0),y4,(#2.51)); 
    ((#2.51),y5,(#2.51));
    ((#2.0),y6,(#2.51))
   ]
   ((kappa y1 y2 y3 y4 y5 y6 < (-- (#2.0)*xi_gamma) + (#0.029)))`;;


(* L41e257
LOC: DCG errata : 
http://flyspeck.googlecode.com/svn/trunk/dcg_errata/dcg_errata.tex
(svn 338)
Added March7,2008.

CCC Fixed (#2.51) --> (square (#2.51))
Bound: 0.223878304374

Point: [6.30010754072, 6.30009424726, 4.00000591053, 4, 4.00000591051, 6.3001]

 *)

let I_6410186704=
all_forall `ineq
   [(square_2t0,x1,square (#2.57));
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,(#4.0));
    ((#4.0),x5,square_2t0);
    (square_2t0,x6,square_2t0)
   ]
   ((dih_x  x1 x2 x3 x4 x5 x6  > 
    dih_x (square_2t0) (square_2t0) x3 x4 x5 (square_2t0) - (#0.0084)))`;;


(* 
CCC fixed (#2.51) -> square_2t0
Bound: 0.194552580073

Point: [6.30011135252, 6.30009239209, 4.00000677596, 3.2, 4.00000677583, 6.3001]

XXX false

Bound: 0.0044085164046

Point: [6.30010017942, 4.00000040706, 6.30009980299, 3.2, 4.00000045964, 6.3001]

*) 

let I_3008133607=
all_forall `ineq
   [(square_2t0,x1,square (#2.57));
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#3.2),x4,(#3.2));
    ((#4.0),x5,square_2t0);
    (square_2t0,x6,square_2t0)
   ]
   ((dih_x  x1 x2 x3 x4 x5 x6  > 
    dih_x (square_2t0) (square_2t0) x3 x4 x5 (square_2t0) - (#0.0084)))`;;

let I_5617427593=
all_forall `ineq
   [(square_2t0,x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    ((#4.0),x5,square_2t0);
    ((#4.0),x6,square_2t0)
   ]
   ((dih_x  x1 square_2t0 x3 (#4.0) x5 square_2t0  +
     dih_x  x1 x2 square_2t0 (square (#3.2)) square_2t0 x6 > (#3.0)) \/ 
    (delta_x x1 x2 x3 x4 x5 x6 < (#0.0)))`;;


(* type C.
LOC: DCG errata : 
http://flyspeck.googlecode.com/svn/trunk/dcg_errata/dcg_errata.tex
(svn 338)
Added March7,2008.
 *)

let I_2377396571=
all_forall `ineq
   [((#4.0),x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square_2t0);
    (square (#3.2),x4,square (#3.2));
    (square (#2.91),x5,square (#3.2));
    (square (#2.91),x6,square (#3.2))
   ]
   (dih_x  x1 x2 x3 x4 x5 x6  > (#1.2))`;;

let I_3656545285=
all_forall `ineq
   [((#4.0),x1,square_2t0);
    (square_2t0,x2,square (#2.57));
    (square_2t0,x3,square (#2.57));
    ((#4.0),x4,(#4.0));
    ((#4.0),x5,square_2t0);
    ((#4.0),x6,square_2t0)
   ]
   (dih_x  x1 x2 x3 x4 x5 x6  < (#1.2))`;;


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
