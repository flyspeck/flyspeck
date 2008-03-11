(* 

These are inequalities that have been withdrawn for various reasons
from kep_inequalities.ml.  The main reason is that some of them are false.
If a new version of the inequalities are introduced, they should carry
a new 9-digit identification number.  The numbers of the following
inequalities should be retired.

We keep these inequalities around for reference, because they were
part of the 1998 proof.  Hence it is still necessary to refer to them
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


