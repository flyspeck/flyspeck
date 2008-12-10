(* 

These are inequalities that have been withdrawn for various reasons
from kep_inequalities.ml.  The main reason is that some of them are false.
If a new version of the inequalities are introduced, they should carry
a new 9-digit identification number.  The numbers of the following
inequalities should be retired.

We keep these inequalities around for reference, because some were
part of the 1998 proof. Others are here just to keep a record of what happened to them.  
It may still be necessary to refer to them
sometimes.

*)

(* interval verification in partK.cc *)
(* LOC: 2002 k.c page 48
17.17 Group_17 *)

(* XXX false: 

Bound: 0.0336078908192
Point: [6.30009999999, 3.99999999999, 3.99999999999, 4.20260782962, 7.67289999999, 7.67289999999]

The interval arithmetic code in partK.cc was incorrectly
copied from a different inequality.  Thus, this appears to
be a genuine counterexample.  Reported in dcg_errata.
TCH 1/31/2008.

*)

let I_900212351=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((square (#2.7)), x5, (square (#2.77)));
     ((square (#2.7)), x6, (square (#2.77)))
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  ( (#1.798) +.  ( (--. (#0.1)) *.
        ( (sqrt x1) +.  (sqrt x2) +.  (sqrt x3))) +.  ( (--. (#0.19))
        *.  (sqrt x4)) +.  ( (--. (#0.17)) *.  ( (sqrt x5) +.  (sqrt
        x6)))))`;;



(* XXX Appears this is false.  
  Check point (4,10.4329)
*)
(* This inequality agrees with what is written in SPVI-2002-Group25,p.52.
   This does not agree with what appears in partK.cc, which has
   right-hand-side = 0.05925 - 0.14 (y5 - sqrt8).
   If we take the interval code to be the authority, we need to change
   the sign of 0.14 to -0.14.

   This inequality only gets used in the proof of SPVI-2002-Prop~17.2,page52.
 *)
(* interval verification in partK.cc *)

(* 
XXX false

Bound: 0.112123545317

Point: [3.99999999999, 10.4328999999]

*)

let I_775220784=
   all_forall `ineq 
    [((#4.0), x3, square_2t0);
     ((#8.0), x5, (square (#3.23)))
    ]
    ( (tau_0_x (#4.0) (#4.0) x3 (#4.0) x5 (#4.0)) >.  
  ( (#0.05925) +.  (  (#0.14) *.  ( (sqrt x5) +.  (  (--. (#2.0)) *.  (sqrt (#2.0)))))))`;;



(* interval verification in partK.cc
 
LOC: 2002 k.c page 60
Group_18.16

*)
(*
XXX false.  This seems false.  The constant term in partK.cc is wrong.
dcg_errata note added. 1/31/2008.

Bound: 0.0109646865132

Point: [4, 3.99999999999, 3.99999999999, 3.99999999999, 10.2399999999, 6.30009999999]
*)
let I_292827481=
  all_forall `ineq
  [((#4.0), x1, (#4.0) );
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, (#4.0) );
     ((#4.0), x4, (#4.0) );
     ((#8.0)  , x5, square (#3.2));
     (square_2t0  , x6, square_2t0)
  ]
  (vor_0_x x1 x2 x3 x4 x5 x6 <. --(#0.084) - ((sqrt x5 - sqrt8)*(#0.1))  )
  `;;




(*
The proof that vor_0_analytic < -1.04 pt from DCG Lemma 10.14 has been
redone.  I am deprecating the inequalities for that proof, even though
they are all still correct.  *)


(*
LOC: 2002 Form, Appendix 1, page 19
 2002_Calc_4.1.1
 DCG Lemma 10.14, mixed quad -1.04 bound 
*)
let J_69785808=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     (square_2t0, x2, (square (#2.7)));
     (square_2t0, x3, (square (#2.7)));
    
        ((#4.0), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        ( (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  
     (  (--. (#1.04)) *.  pt)) \/ 
        ( (eta_x x2 x3 x4) >.  (sqrt (#2.0))))`;;


(*
LOC: 2002 Form, Appendix 1, page 19
 2002_Calc_4.1.1
 DCG Lemma 10.14, mixed quad -1.04 bound 
*)
let J_104677697=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     (square_2t0, x2, (square (#2.7)));
     (square_2t0, x3, (square (#2.7)));
    
        ((#4.0), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (square (#2.7)))
    ]
    (
        ( (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  (  (--. (#1.04)) *.  pt)) \/ 
        ( (eta_x x2 x3 x4) >.  (sqrt (#2.0))) \/ 
        ( (eta_x x1 x2 x6) >.  (sqrt (#2.0))))`;;







(*
LOC: 2002 Form, Appendix 1, page 19
 2002_Calc_4.1.2
 DCG Lemma 10.14, the -1.04 bound.

WWW KX is wildly unstable as x2 and x3 approach 8.  Are you sure
about these?
*)
let J_586706757=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     (square_2t0, x2, (#8.0));
     (square_2t0, x3, (#8.0));
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        ( (KX x1 x2 x3 x4 x5 x6) <.  (  (--. (#1.04)) *.  pt)) \/ 
        ( (eta_x x2 x3 x4) <.  (sqrt (#2.0))))`;;



(*
LOC: 2002 Form, Appendix 1, page 19
 2002_Calc_4.1.2
 DCG Lemma 10.14, mixed quad -1.04 bound 
*)
let J_87690094=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     (square_2t0, x2, (#8.0));
     (square_2t0, x3, (#8.0));
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (square (#2.7)))
    ]
    (
        ( (KX x1 x2 x3 x4 x5 x6) <.  (  (--. (#1.04)) *.  pt)) \/ 
        ( (eta_x x2 x3 x4) <.  (sqrt (#2.0))) \/ 
        ( (eta_x x1 x2 x6) >.  (sqrt (#2.0))))`;;



(*
LOC: 2002 Form, Appendix 1, page 19
 2002_Formulation_4.1.3
 DCG Lemma 10.14, mixed quad -1.04 bound 
*)
let J_185703487=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (square (#2.7)));
    
        (square_2t0, x4, (square (#2.7)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        ( (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  (  (--. (#0.52)) *.  pt)) \/ 
        ( (eta_x x2 x3 x4) >.  (sqrt (#2.0))))`;;


(*
LOC: 2002 Form, Appendix 1, page 19
 2002_Formulation_4.1.4
 DCG Lemma 10.14, mixed quad -1.04 bound 
*)
let J_441195992=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (#8.0));
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, (square (#2.2)));
     ((#4.0), x6, square_2t0)
    ]
    (
        ( (KX x1 x2 x3 x4 x5 x6) <.  (  (--. (#0.52)) *.  pt)) \/ 
        ( (eta_x x2 x3 x4) <.  (sqrt (#2.0))))`;;


(*
LOC: 2002 Form, Appendix 1, page 19
 2002_Formulation_4.1.5
 DCG Lemma 10.14, mixed quad -1.04 bound 
*)
let J_848147403=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (#8.0));
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        ( (KX x1 x2 x3 x4 x5 x6) <.  (  (--. (#0.31)) *.  pt)) \/ 
        ( (eta_x x2 x3 x4) <.  (sqrt (#2.0))))`;;


(*
LOC: 2002 Form, Appendix 1, page 20
 2002_Formulation_4.1.6
 DCG Lemma 10.14, mixed quad -1.04 bound 
*)
let J_969320489=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((square (#2.2)), x6, square_2t0)
    ]
    ( (mu_flat_x x1 x2 x3 x4 x5 x6) <.  (  (--. (#0.21)) *.  pt))`;;


(*
LOC: 2002 Form, Appendix 1, page 20
 2002_Formulation_4.1.6
 DCG Lemma 10.14, mixed quad -1.04 bound 
*)
let J_975496332=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((square (#2.2)), x6, square_2t0)
    ]
    ( (nu_x x1 x2 x3 x4 x5 x6) <.  (  (--. (#0.21)) *.  pt))`;;


(*
LOC: 2002 Form, Appendix 1, page 20
 2002_Formulation_4.1.7
 DCG Lemma 10.14, mixed quad -1.04 bound 
*)
let J_766771911=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((square (#2.2)), x5, square_2t0);
     ((square (#2.2)), x6, square_2t0)
    ]
    ( (mu_upright_x x1 x2 x3 x4 x5 x6) <.  (  (--. (#0.42)) *.  pt))`;;



(* 


A number of inequalities were provisionally added in Dec 2007 to deal with the
deformation (biconnectedness problem) on page 131 of DCG.  This argument was rewritten
in October 2008 for the paper "A Revision of the Proof of the Kepler Conjecture."
These provisional inequalities are now deprecated.

They will be labeled "BICONNECTED-131".  These were deprecated on Nov 2, 2008.

*)

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

BICONNECTED-131

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
BICONNECTED-131
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
BICONNECTED-131
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
BICONNECTED-131
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
BICONNECTED-131
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
BICONNECTED-131
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
BICONNECTED-131

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

(* BICONNECTED-131 *)

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
BICONNECTED-131
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

(* BICONNECTED-131 *)

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


(* deleted from kep_ineq_bis.ml on 11/27/08 because it is false.
   The proof of the lemma that used it has been completely rewritten. 
   This was originally for the 2008 "Revision of the Kepler Conjecture"
   by Hales et al. Sec. Biconnected Graphs. *)
(* Revision, lemma:double-edge *)
(* XX FALSE *)
(* biconnected section *)
let I_8167927350=
all_forall `ineq
   [
   ((square (#2.39)),x1,square_2t0);
   (#4.0 ,x2,square(#2.15));
   (#4.0,x3,square(#2.15));
   (#4.0,x5,square(#2.15));
   (#4.0,x6,square(#2.15));
   ]
  (dih_x x1 x2 (square_2t0) (#4.0) (#4.0) x6 +
   dih_x x1 square_2t0 square_2t0 (#4.0) (#4.0) (square (#2.7)) +
   dih_x x1 square_2t0 x3 (#4.0) x5 (square (#2.7)) > pi)`;;

(* deleted from kep_ineq_bis.ml on 11/27/08 because is was used in connection
   with the false inequality 8167927350 .
   The proof of the lemma that used it has been completely rewritten. 
   This was originally for the 2008 "Revision of the Kepler Conjecture"
   by Hales et al. Sec. Biconnected Graphs. *)
(* Revision, lemma:double-edge *)
(* verified by S. McLaughlin Nov 3, 2008 *)
(* biconnected section *)
let I_6040218010=
all_forall `ineq
   [((square (#2.36)),x1,square_2t0);
    ((#4.0),x2,square_2t0);
    ((#4.0),x3,square (#2.16));
    (square (#2.7),x4, square (#2.7));
    ((#4.0),x5,(square (#2.17)));
    ((#4.0),x6,(#4.0));
   ]
   (dih_x  x1 x2 x3 x4 x5 x6  > pi / (#2.0) )`;;



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



(* Revision errata SPV p 182, Lemma 16.7--16.9 *)
(* complement to SPV page 183, Lemma 16.9 *)
(* deprecated 12/9/2008 *)
let I_7220423821=
all_forall `ineq
   [((#4.0),x1,(square (#2.1)));
    ((#4.0),x2,(square (#2.1)));
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,(#4.0));
    ((#8.0),x6,(#8.82))
   ]
   ((vort_x  x1 x2 x3 x4 x5 x6 sqrt2 + pp_m* solid_x x1 x2 x3 x4 x5 x6 - pp_b/(#2.0) < (#0.0)) \/ (vort_x x1 x2 x3 x4 x5 x6 sqrt2 > -- (pt * (#1.04))))`;;

(* Revision errata SPV p 182, Lemma 16.7--16.9 *)
(* dim reduction on x3 *)
(* deprecated 12/9/2008 *)
let I_7188502846=
all_forall `ineq
   [((#4.0),x1,(square (#2.1)));
    ((#4.0),x2,(square (#2.1)));
    ((#4.0),x3,(#4.0));
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    ((#8.0),x6,(#8.82))
   ]
   ((vort_x  x1 x2 x3 x4 x5 x6 sqrt2 + pp_m* solid_x x1 x2 x3 x4 x5 x6 - pp_b/(#2.0) < (#0.0)) \/ (vort_x x1 x2 x3 x4 x5 x6 sqrt2 > -- (pt * (#1.04))))`;;

(* variant of 5127197465 in a small corner f the tight spot *)
(* deprecated 12/9/08 *)
let I_1017723951=
(* 8.82 = (2.1 Sqrt[2])^2, for triangle acuteness condition *)
all_forall `ineq
   [((#4.0),x1,(square (#2.1)));
    ((#4.0),x2,(square (#2.1)));
    ((#4.0),x3,square_2t0);
    ((#4.0),x4,square_2t0);
    ((#4.0),x5,square_2t0);
    ((#8.0),x6,(#8.82))
   ]
   (vort_x  x1 x2 x3 x4 x5 x6 sqrt2 + (#0.05)*(x1 + x2 - x6) <= (#0.0))`;;

