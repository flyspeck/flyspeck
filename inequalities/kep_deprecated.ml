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

(* interval verification by Ferguson, source/section_a46_1c.c *)
(* There are counterexamples to various cases, listed below *)

let I_207203174_GEN=
   `(\ a1 a2 a3 a4 a5. 
 (ineq
[
((#8.0),b5,(square (#3.2)));
((square(#3.2)), x, (square_4t0));
((square(#3.2)), x', (square_4t0))
]
   (((tau_0_x a3 a2 a1 (#4.0)  x (#4.0)) +.
    (tau_0_x a3 a1 a5 b5 x' x) +.
      (tau_0_x a3 a5 a4 (#4.0) (#4.0) x') 
    >. (#0.54525))
   \/
  (delta_x a3 a2 a1 (#4.0)  x (#4.0) <. (#0.0)) \/
  (delta_x a3 a1 a5 b5 x' x <. (#0.0)) \/
  (delta_x a3 a5 a4 (#4.0) (#4.0) x' <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_207203174_1=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_2=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
(* WWW infeasible *)
let I_207203174_3=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_4=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_207203174_5=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
(* XXX false 
   False at {ay1,ay2,ay3,ay4,ay5}={2,2,2.51,2,2.51}; 
   by5=Sqrt[8]; {y,yp}={3.2,3.9086};
   Note that Solve[Delta[2, 2.51, 2.51, y, 2, 2] == 0, y] gives a zero
   near y = 3.90866.
   tauVc drops rapidly as x' increases in the range [3.9,3.9086].
   It is still true by a considerable margin at yp=3.9.
  
   The verification code is there in source/section_a46_1c.c, but I haven't
   located the bug.

   Reported in dcg_errata.tex 1/31/2008, TCH.
*)
let I_207203174_6=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_207203174_7=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_8=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
(* WWW infeasible *)
let I_207203174_9=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
(* WWW infeasible *)
let I_207203174_10=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
(* WWW infeasible *)
let I_207203174_11=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
(* WWW infeasible *)
let I_207203174_12=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_207203174_13=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_14=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_207203174_15=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_16=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_207203174_17=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_18=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
(* WWW infeasible *)
let I_207203174_19=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_20=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
(* XXX false.  Comments before I_207203174_6 *)
let I_207203174_21=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
(* XXX false.  Comments before I_207203174_6 *)
let I_207203174_22=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_207203174_23=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_24=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_207203174_25=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_26=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
(* WWW infeasible *)
let I_207203174_27=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_28=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_207203174_29=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_30=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_207203174_31=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_32=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;


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




