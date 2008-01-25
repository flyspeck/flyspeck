


(*
 Inequalities for the proof of the Kepler Conjecture
 Jan 15, 2003
 HOL-light format.
 Converted from kep_inequalities.ml CVS:1.4,
 using "modify()" in "kep_inequalities_convert.ml"

 Eventually this file will become the final authority about
 the various inequalities.  For now, there are still typos,
 so that 2002-version of Kepler Conjecture and the
 interval arithmetic C++ files have higher authority.
*)

(*
 Acknowledgement:  I would like to thank Carole Bunting for
 typing many of these inequalities in a machine readable form.
*)


(*

Errata:

Please report any errors that are found.  This includes typos (such
as a typo in the 9-digit identifier for the inequality), missing inequalities, 
false inequalities, incompatibilities
between the stated inequality and the interval arithmetic verification,
and incompatibilities between the stated inequality and how the inequality
is used in the proof of the Keper Conjecture.


Tue Feb 24 09:30:41 EST 2004: 
(* interval verification in partK.cc *)
I'm suspicious of I_354217730.
The sqrt2 looks odd and it doesn't fit with the interval arithmetic code.
(* interval verification in partK.cc *)
Note that similar inequalities such as I_938003786 use sqrt8 
instead of sqrt2.

Nov 8, 2007: Fixed the x1 bound on calc 815492935 and
729988292 (SPIV-2002 Sec. A2-A3).  It should be (square_2t0,x1,(#8.0))

Dec 16, 2007: Fixed the direction of inequalities in 690626704_*

*)

(* Files for 1998 interval verification:
partK.cc = http://www.math.pitt.edu/~thales/kepler98/interval/partK.cc
  533270809 appears in partK.cc but not below.
  353116995 appears in partK.cc but not below.
part3.cc = http://www.math.pitt.edu/~thales/kepler98/interval/PART3/part3.c
part3a.cc
part3more.c

*)



(* Search for LOC: to find the location of inequalities
 in preprint.

 The order of the inequalities is from last paper to first:
 Kepler Conjecture: k.c.
 IV.
 III.
 II. (a couple that are needed)
 I. (one? inequality)
 Form.
*)

(* CONSTANT LIST:

BIT0*
BIT1*
COND*
CONS*
D31
D32
D33
D41
D42
D51
DECIMAL*
KX
LET*
LET_END*
NUMERAL*
Z32
Z33
Z41
Z42
_0*
acs*
anc
arclength
beta
chi_x
cos*
cross_diag_x
crown
delta_x
deriv
deriv2
dih2_x
dih3_x
dihR
dih_x
doct
eta_x
gamma_x
ineq
kappa
mu_flat_x
mu_flipped_x
mu_upright_x
nu_gamma_x
nu_x
octa_x
octavor0_x
octavor_analytic_x
overlap_f
pi*
pi_prime_sigma
pi_prime_tau
pt
quo_x
rad2_x
s5
sigma1_qrtet_x
sigma32_qrtet_x
sigma_qrtet_x
sigmahat_x
sol_x
sqrt*
sqrt2
sqrt8
square
square_2t0
square_4t0
t0
t5
tauA_x
tauC0_x
tauVt_x
tau_0_x
tau_analytic_x
tau_sigma_x
tauhat_x
tauhatpi_x
taumu_flat_x
taunu_x
two_t0
u_x
v0x
v1x
vorA_x
vorC0_x
vorC_x
vor_0_x
vor_0_x_flipped
vor_analytic_x
vor_analytic_x_flipped
vort_x
xi'_gamma
xiV



*)

(*
 GENERAL NOTES:
*)

(*
 1. FERGUSON
*)

(*
 Many of the original interval arithmetic verifications
 were completed by Sam Ferguson.  The original 1998 proof 
 (available at the arXiv)
 contains details about which inequalities were verified by him.
*)

(*
 2. EQUALITY
*)

(*
In general, to the greatest extent possible, we express each
inequality as a strict inequality on a compact domain.  There are,
however, a few inequalities that are not strict, such as the bound
of $1\,\pt$ on the score of a quasi_regular tetrahedron or the
bound of $0.0$ on the score of a quad cluster.  (These particular
sharp bounds appear in the proof of the local optimality of the
face_centered cubic and hexagonal close packings.)
*)

(*
 The most significant are the bounds
$\sigma\le\pt$ on quasi_regular tetrahedra and $\sigma\le0$ on
quad_clusters. The fact that these are attained for the regular cases
with edge lengths(#2.0) and diagonal $2\sqrt{2.0}$ on the quad_cluster 
and for
no other cases gives the bound $\pi/\sqrt{18.0}$ on density and the local
optimality of the fcc and hcp packings.
*)

(*
Another place where we have allowed equality to be obtained is
with $\tau_0\ge0$ for quasi_regular simplices.
*)

(*
There are also a few less significant cases where an inequality is
sharp. For example,
    $$\tau_0(2t_0,2,2,x,2,2)\ge0,\quad\vor_0(2t_0,2,2,x,2,2)\le0$$
for special simplices satisfying  $x\in[2\sqrt{2.0},3.2]$.  Also, equality
occurs in Lemma~\ref{lemma:pass_makes_quarter} and
Lemma~\ref{lemma:neg_orient_quad}.
*)

(*
Equality is attained in \calc{} iff $S$ is a regular_tetrahedron
of edge_length $2.0$.  Equality is attained in \calc{346093004},
\calc{40003553}, and \calc{522528841} \calc{892806084} iff the
simplex has five edges of length $2.0$ and one edge of length
$\sqrt8$.
*)

(*
Search for SKIP to find sections skipped.
Search for LOC: to find preprint locations.
*)



(*
LOC: 2002 k.c page 42.
17.1  Group_1
*)

(* interval verification in partK.cc *)
let I_572068135=
   all_forall `ineq 
    [((square (#2.3)), x1, (#6.3001));
     ((#4.0), x2, (#6.3001));
     ((#4.0), x3, (#6.3001));
     ((#4.0), x4, (#6.3001));
     ((#4.0), x5, (#6.3001));
     ((#4.0), x6, (#6.3001))
    ]
    (
            (
                ( (tau_sigma_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >. 
                (--. (#0.3442))) \/ 
            ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.51)))`;;




(* interval verification in partK.cc *)
let I_723700608=
   all_forall `ineq 
    [((square (#2.3)), x1, (#6.3001));
     ((#4.0), x2, (#6.3001));
     ((#4.0), x3, (#6.3001));
     ((#4.0), x4, (#6.3001));
     ((#4.0), x5, (#6.3001));
     ((#8.0), x6, (square (#3.02)))
    ]
    (
            (
                ( (tau_0_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >. 
                (--. (#0.1787))) \/ 
            ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.26)) \/ 
            ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.63)))`;;




(* interval verification in partK.cc *)
let I_560470084=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((square (#2.3)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (tauhat_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih2_x x1 x2 x3 x4 x5 x6))) >. 
                (--. (#0.2137)))`;;



(* interval verification in partK.cc *)
let I_535502975=
   all_forall `ineq 
    [((square (#2.3)), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, (square (#3.02)));
     (square_2t0, x6, (square (#3.02)))
    ]
    (
            (
                ( (tau_0_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >. 
                (--. (#0.1371))) \/ 
            ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.14)) \/ 
            ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.51)))`;;



(*
  
LOC: 2002 k.c page 42
17.2  Group_2
*)



(* let I_821707685= *)
(*    all_forall `ineq  *)
(*     [((#4.0), x1, (#6.3001)); *)
(*      ((#4.0), x2, (square (#2.168))); *)
(*      ((#4.0), x3, (square (#2.168))); *)
(*      ((#4.0), x4, (#6.3001)); *)
(*      ((#4.0), x5, (#6.3001)); *)
(*      (square_2t0, x6, (square ( ( *. ) (#2.0) (#2.51)))) *)
(*     ] *)
(*     ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.63))`;; *)

(* Added delta_x > 0, Jan 2008 *)
(* interval verification by Ferguson *)
let I_821707685=
   all_forall `ineq 
    [((#4.0), x1, (#6.3001));
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, (#6.3001));
     ((#4.0), x5, (#6.3001));
     (square_2t0, x6, (square ( ( *. ) (#2.0) (#2.51))))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.63) \/ 
      (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;

(* interval verification by Ferguson *)
let I_115383627=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     (square_2t0, x6, (square ( ( *. ) (#2.0) (#2.51))))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.51) \/
      (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0)) `;;
(* interval verification by Ferguson *)
let I_576221766=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#8.0), x4, (#8.0));
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (square ( ( *. ) (#2.0) (#2.51))))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.93) \/
      (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;


(* interval verification by Ferguson *)
let I_122081309=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#8.0), x4, (#8.0));
     (square_2t0, x5, square_2t0);
     (square_2t0, x6, (square ( ( *. ) (#2.0) (#2.51))))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.77) \/
      (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;


(* interval verification by Ferguson *)
(* XXX false 
bug = {4.63819949615, 4.66049671047, 4.09692910296, 5.04974164466, 4.613058661, 24.6625187406}
this point is undefined in tau_0
*)
let I_644534985=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (square ( ( *. ) (#2.0) (#2.51))))
    ]
    (
         (
           ( (tau_0_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (--. (#0.2391))) \/ 
           ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.2)) \/
           (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;


(* interval verification by Ferguson *)
let I_467530297=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     (square_2t0, x6, (square ( ( *. ) (#2.0) (#2.51))))
    ]
    (
         (
           ( (tau_0_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (--. (#0.1376))) \/ 
           ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.2)) \/
           (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;


(* interval verification by Ferguson *)
let I_603910880=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (square ( ( *. ) (#2.0) (#2.51))))
    ]
    (
         (
            ( (tau_0_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (--. (#0.266))) \/ 
           ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.2)) \/
           (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;

(* interval verification by Ferguson *)
let I_135427691=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     (square_2t0, x4, (#8.0));
     (square_2t0, x5, square_2t0);
     (square_2t0, x6, (square ( ( *. ) (#2.0) (#2.51))))
    ]
    (
         (
            ( (tau_0_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (--. (#0.12))) \/ 
           ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.2)) \/
           (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;

(* interval verification by Ferguson *)
let I_60314528=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, (#4.0));
     (square_2t0, x5, square_2t0);
     (square_2t0, x6, square_4t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.16) \/
        (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;



(* interval verification by Ferguson *)
let I_312132053=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, (square (#3.488)));
     (square_2t0, x6, square_2t0)
    ]
    (
      ( (tau_0_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (--. (#0.1453)))`;;




(*
 
LOC: 2002 k.c page 42
17.3 Group_3
*)

let I_751442360=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih2_x x1 x2 x3 x4 x5 x6) >.  (#0.74))`;;




let I_893059266=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, (square (#3.488)));
     ((#4.0), x6, square_2t0)
    ]
    (
          (
            ( ((tau_0_x x1 x2 x3 x4 x5 x6) ) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >. 
            (--. (#0.2391))) \/ 
            ( (delta_x x5 (#4.0) (#4.0) (#8.0) square_2t0 x6) <.  (#0.0)))`;;




let I_690646028=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, (square ( ( *. ) (#2.0) (#2.51))));
     ((#4.0), x6, square_2t0)
    ]
    ( ( (dih_x x1 x2 x3 x4 x5 x6) +.  (  (#0.5) *.  ( (#2.402) -.  (sqrt x4)))) <.  (  pi /  (#2.0)))`;;



(*
 
LOC: 2002 k.c page 42
17.4 Group_4
*)


(* interval verification in partK.cc *)
let I_161665083=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#3.2)), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.78)) \/ 
            ( ( (sqrt x2) +.  (sqrt x3)) >.  (#4.6)))`;;




(*
 
LOC: 2002 k.c page 42-43
17.5 Group_5
*)



(* interval verification in partK.cc *)
let I_867513567_1=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (dih2_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.35) *.  (sqrt x2)) +.  (  (--. (#0.15)) *. 
            (sqrt x1)) +.  (  (--. (#0.15)) *.  (sqrt x3)) +.  (  (#0.7022) *.  (sqrt x5)) +.  (  (--. (#0.17)) *. 
            (sqrt x4))) >.  (--. (#0.0123)))`;;





let I_867513567_2=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (dih2_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.13)) *.  (sqrt x2)) +.  (  (#0.631) *. 
            (sqrt x1)) +.  (  (#0.31) *.  (sqrt x3)) +.  (  (--. (#0.58)) *.  (sqrt x5)) +.  (  (#0.413) *. 
            (sqrt x4)) +.  (  (#0.025) *.  (sqrt x6))) >.  (#2.63363))`;;



let I_867513567_3=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.714) *.  (sqrt x1)) +.  (  (--. (#0.221)) *. 
            (sqrt x2)) +.  (  (--. (#0.221)) *.  (sqrt x3)) +.  (  (#0.92) *.  (sqrt x4)) +.  (  (--. (#0.221)) *. 
            (sqrt x5)) +.  (  (--. (#0.221)) *.  (sqrt x6))) >.  (#0.3482))`;;




let I_867513567_4=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (dih_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.315)) *.  (sqrt x1)) +.  (  (#0.3972) *. 
            (sqrt x2)) +.  (  (#0.3972) *.  (sqrt x3)) +.  (  (--. (#0.715)) *.  (sqrt x4)) +.  (  (#0.3972) *. 
            (sqrt x5)) +.  (  (#0.3972) *.  (sqrt x6))) >.  (#2.37095))`;;


(* interval verification by Ferguson *)
let I_867513567_5=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (sol_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.187)) *.  (sqrt x1)) +.  (  (--. (#0.187)) *. 
            (sqrt x2)) +.  (  (--. (#0.187)) *.  (sqrt x3)) +.  (  (#0.1185) *.  (sqrt x4)) +.  (  (#0.479) *. 
            (sqrt x5)) +.  (  (#0.479) *.  (sqrt x6))) >.  (#0.437235))`;;


(* interval verification by Ferguson *)
let I_867513567_6=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (sol_x x1 x2 x3 x4 x5 x6) +.  (  (#0.488) *.  (sqrt x1)) +.  (  (#0.488) *. 
            (sqrt x2)) +.  (  (#0.488) *.  (sqrt x3)) +.  (  (--. (#0.334)) *.  (sqrt x5)) +.  (  (--. (#0.334)) *. 
            (sqrt x6))) >.  (#2.244))`;;



let I_867513567_7=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (sigmahat_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.145)) *.  (sqrt x1)) +.  (  (--. (#0.081)) *. 
            (sqrt x2)) +.  (  (--. (#0.081)) *.  (sqrt x3)) +.  (  (--. (#0.133)) *.  (sqrt x5)) +.  (  (--. (#0.133)) *. 
            (sqrt x6))) >.  (--. (#1.17401)))`;;



(* XXX This is false at 
   point: [4, 4, 4, 6.75999999999, 4, 4]
   value: 0.00366265861696
   in the vor_analytic part of the max_real
*)
let I_867513567_8=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (sigmahat_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.12)) *.  (sqrt x1)) +.  (  (--. (#0.081)) *. 
            (sqrt x2)) +.  (  (--. (#0.081)) *.  (sqrt x3)) +.  (  (--. (#0.113)) *.  (sqrt x5)) +.  (  (--. (#0.113)) *. 
            (sqrt x6)) +.  (  (#0.029) *.  (sqrt x4))) >.  (--. (#0.94903)))`;;



let I_867513567_9=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (sigmahat_x x1 x2 x3 x4 x5 x6) +.  (  (#0.153) *.  (sqrt x4)) +.  (  (#0.153) *. 
            (sqrt x5)) +.  (  (#0.153) *.  (sqrt x6))) <.  (#1.05382))`;;




(* XXX This is false at 
   point: [4, 4, 4, 6.75999999999, 5.23872683413, 5.23872688303]
   value: .0005
   in the vor_0_x part of the max_real
*)

let I_867513567_10=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (sigmahat_x x1 x2 x3 x4 x5 x6) +.  (  (#0.419351) *.  (sol_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.19) *. 
            (sqrt x1)) +.  (  (#0.19) *.  (sqrt x2)) +.  (  (#0.19) *.  (sqrt x3))) <.  (#1.449))`;;


let I_867513567_11=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (sigmahat_x x1 x2 x3 x4 x5 x6) +.  (  (#0.419351) *.  (sol_x x1 x2 x3 x4 x5 x6))) <. 
              ( (--. (#0.01465)) +.  (  (#0.0436) *.  (sqrt x5)) +.  (  (#0.436) *.  (sqrt x6)) +.  (  (#0.079431) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



(* XXX This is false (twice) at 
   point: [4, 4, 4, 6.75999999999, 4, 4]
   value: about 0.0006
   in the vor_analytic part of the max_real
   AND the vor_0_x part
*)

let I_867513567_12=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigmahat_x x1 x2 x3 x4 x5 x6) <.  (#0.0114))`;;


(* XXX This is false (twice) at 
   point: [4, 4, 4, 6.75999999999, 4, 4]
   value: about 0.001
   in the vor_analytic part of the max_real
   AND the vor_0_x part
*)

let I_867513567_13=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (tauhat_x x1 x2 x3 x4 x5 x6) >.  (  (#1.019) *.  pt))`;;


(*
 
LOC: 2002 k.c page 43
17.6 Group_6
*)


(* let I_498839271_1= *)
(*    all_forall `ineq  *)
(*     [(square_2t0, x1, (#8.0)); *)
(*      ((#4.0), x2, square_2t0); *)
(*      ((#4.0), x3, square_2t0); *)
(*      ((#4.0), x4, square_2t0); *)
(*      ((#4.0), x5, square_2t0); *)
(*      ((#4.0), x6, square_2t0) *)
(*     ] *)
(*     ( (sqrt x1) >.  (#2.51))`;; *)




(* let I_498839271_2= *)
(*    all_forall `ineq  *)
(*     [(square_2t0, x1, (#8.0)); *)
(*      ((#4.0), x2, square_2t0); *)
(*      ((#4.0), x3, square_2t0); *)
(*      ((#4.0), x4, square_2t0); *)
(*      ((#4.0), x5, square_2t0); *)
(*      ((#4.0), x6, square_2t0) *)
(*     ] *)
(*     ( (sqrt x1) <=.  (  (#2.0) *.  (sqrt (#2.0))))`;; *)



(* interval verification in partK.cc *)
let I_498839271_3=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (dih_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.636)) *.  (sqrt x1)) +.  (  (#0.462) *.  (sqrt x2)) +.  (  (#0.462) *.  (sqrt x3)) +. 
                (  (--. (#0.82)) *.  (sqrt x4)) +.  (  (#0.462) *.  (sqrt x5)) +.  (  (#0.462) *.  (sqrt x6))) >=.  (#1.82419))`;;


(* interval verification in partK.cc *)
let I_498839271_4=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.55) *.  (sqrt x1)) +.  (  (--. (#0.214)) *.  (sqrt x2)) +.  (  (--. (#0.214)) *.  (sqrt x3)) +. 
                (  (#1.24) *.  (sqrt x4)) +.  (  (--. (#0.214)) *.  (sqrt x5)) +.  (  (--. (#0.214)) *.  (sqrt x6))) >.  (#0.75281))`;;

(* interval verification in partK.cc *)
let I_498839271_5=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (dih2_x x1 x2 x3 x4 x5 x6) +.  (  (#0.4) *.  (sqrt x1)) +.  (  (--. (#0.15)) *.  (sqrt x2)) +.  (  (#0.09) *.  (sqrt x3)) +. 
                (  (#0.631) *.  (sqrt x4)) +.  (  (--. (#0.57)) *.  (sqrt x5)) +.  (  (#0.23) *.  (sqrt x6))) >.  (#2.5481))`;;


(* interval verification in partK.cc *)
let I_498839271_6=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (( --. ) (dih2_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.454)) *.  (sqrt x1)) +.  (  (#0.34) *.  (sqrt x2)) +.  (  (#1.54) *.  (sqrt x3)) +. 
                (  (--. (#0.346)) *.  (sqrt x4)) +.  (  (#0.805) *.  (sqrt x5))) >.  (--. (#0.3429)))`;;


(* interval verification in partK.cc *)
let I_498839271_7=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (dih3_x x1 x2 x3 x4 x5 x6) +.  (  (#0.4) *.  (sqrt x1)) +.  (  (--. (#0.15)) *.  (sqrt x3)) +.  (  (#0.09) *.  (sqrt x2)) +. 
                (  (#0.631) *.  (sqrt x4)) +.  (  (--. (#0.57)) *.  (sqrt x6)) +.  (  (#0.23) *.  (sqrt x5))) >.  (#2.5481))`;;




(* Seems to be wrong : check at 
   (8, 4.77946715116, 4.0, 6.30009999999, 6.30009999999, 4)
  STM changed from 0.364 
  1/20/2008.  This seems to fix the problem.  The
  left hand side evaluates to -0.342688 > -0.3429.
*)
(* interval verification in partK.cc *)
let I_498839271_8=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
      ( (( --. ) (dih3_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.454)) *.  (sqrt x1)) +.  (  (#0.34) *.  (sqrt x3)) +.  (  (#0.154) *.  (sqrt x2)) +. 
          (  (--. (#0.346)) *.  (sqrt x4)) +.  (  (#0.805) *.  (sqrt x6))) >.  (--. (#0.3429)))`;;


(* interval verification in partK.cc *)
let I_498839271_9=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (sol_x x1 x2 x3 x4 x5 x6) +.  (  (#0.065) *.  (sqrt x2)) +.  (  (#0.065) *.  (sqrt x3)) +.  (  (#0.061) *.  (sqrt x4)) +. 
                (  (--. (#0.115)) *.  (sqrt x5)) +.  (  (--. (#0.115)) *.  (sqrt x6))) >.  (#0.2618))`;;


(* interval verification in partK.cc *)
let I_498839271_10=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (( --. ) (sol_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.293)) *.  (sqrt x1)) +.  (  (--. (#0.03)) *.  (sqrt x2)) +.  (  (--. (#0.03)) *.  (sqrt x3)) +. 
                (  (#0.12) *.  (sqrt x4)) +.  (  (#0.325) *.  (sqrt x5)) +.  (  (#0.325) *.  (sqrt x6))) >.  (#0.2514))`;;


(* interval verification in partK.cc *)
let I_498839271_11=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (( --. ) (nu_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.0538)) *.  (sqrt x2)) +.  (  (--. (#0.0538)) *.  (sqrt x3)) +. 
                (  (--. (#0.083)) *.  (sqrt x4)) +.  (  (--. (#0.0538)) *.  (sqrt x5)) +.  (  (--. (#0.0538)) *.  (sqrt x6))) >.  (--. (#0.5995)))`;;

(* interval verification in partK.cc *)
let I_498839271_12=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (nu_x x1 x2 x3 x4 x5 x6) >=.  (#0.0))`;;


(* interval verification in partK.cc *)
let I_498839271_13=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (taunu_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.5945)) *.  pt)) >.  (#0.0))`;;



(* Duplicate inequality.  This is the same as 413688580 *)
(*
let J_549774315_1=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (nu_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#4.10113)) *.  (dih_x x1 x2 x3 x4 x5 x6))) <.  (--. (#4.3223)))`;;
*)


(* Duplicate inequality.  This is the same as 805296510 *)
(*
let J_549774315_2=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (nu_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.80449)) *.  (dih_x x1 x2 x3 x4 x5 x6))) <.  (--. (#0.9871)))`;;
*)

(* Duplicate inequality.  This is the same as 136610219 *)
(*
let J_549774315_3=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (nu_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.70186)) *.  (dih_x x1 x2 x3 x4 x5 x6))) <.  (--. (#0.8756)))`;;
*)

(* Duplicate inequality.  This is the same as 379204810 *)
(*
let J_549774315_4=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (nu_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.24573)) *.  (dih_x x1 x2 x3 x4 x5 x6))) <.  (--. (#0.3404)))`;;
*)

(* Duplicate inequality.  This is the same as 878731435 *)
(*
let J_549774315_5=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (nu_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.00154)) *.  (dih_x x1 x2 x3 x4 x5 x6))) <.  (--. (#0.0024)))`;;
*)

(* Duplicate inequality.  This is the same as 891740103 *)
(*
let J_549774315_6=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (nu_x x1 x2 x3 x4 x5 x6) +.  (  (#0.07611) *.  (dih_x x1 x2 x3 x4 x5 x6))) <.  (#0.1196))`;;
*)

(* Duplicate inequality.  This is the same as 334002329 *)
(*
let J_574435320_1=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (taunu_x x1 x2 x3 x4 x5 x6) +.  (  (#4.16523) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (#4.42873))`;;
*)

(* Duplicate inequality.  This is the same as 883139937 *)
(*
let J_574435320_2=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (taunu_x x1 x2 x3 x4 x5 x6) +.  (  (#0.78701) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (#1.01104))`;;
*)

(* Duplicate inequality.  This is the same as 507989176 *)
(*
let J_574435320_3=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (taunu_x x1 x2 x3 x4 x5 x6) +.  (  (#0.77627) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (#0.99937))`;;
*)

(* Duplicate inequality.  This is the same as 244435805 *)
(*
let J_574435320_4=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (taunu_x x1 x2 x3 x4 x5 x6) +.  (  (#0.21916) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (#0.34877))`;;
*)

(* Duplicate inequality.  This is the same as 930176500 *)
(*
let J_574435320_5=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (taunu_x x1 x2 x3 x4 x5 x6) +.  (  (#0.05107) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (#0.11434))`;;
*)

(* Duplicate inequality.  This is the same as 815681339 *)
(*
let J_574435320_6=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (taunu_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.07106)) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (--. (#0.07749)))`;;
*)


(*
 
LOC: 2002 k.c page 44
17.7 Group_7
*)


(* interval verification in partK.cc *)
let I_319046543_1=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sqrt x1) <.  (#2.696))`;;




let I_319046543_2=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                    ( (dih_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.49)) *.  (sqrt x1)) +.  (  (#0.44) *.  (sqrt x2)) +.  (  (#0.44) *.  (sqrt x3)) +. 
                    (  (--. (#0.82)) *.  (sqrt x4)) +.  (  (#0.44) *.  (sqrt x5)) +.  (  (#0.44) *.  (sqrt x6))) >.  (#2.0421))`;;



let I_319046543_3=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                    ( (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.495) *.  (sqrt x1)) +.  (  (--. (#0.214)) *.  (sqrt x2)) +.  (  (--. (#0.214)) *.  (sqrt x3)) +. 
                    (  (#1.05) *.  (sqrt x4)) +.  (  (--. (#0.214)) *.  (sqrt x5)) +.  (  (--. (#0.214)) *.  (sqrt x6))) >.  (#0.2282))`;;



let I_319046543_4=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                    ( (dih2_x x1 x2 x3 x4 x5 x6) +.  (  (#0.38) *.  (sqrt x1)) +.  (  (--. (#0.15)) *.  (sqrt x2)) +.  (  (#0.09) *.  (sqrt x3)) +. 
                    (  (#0.54) *.  (sqrt x4)) +.  (  (--. (#0.57)) *.  (sqrt x5)) +.  (  (#0.24) *.  (sqrt x6))) >.  (#2.3398))`;;



let I_319046543_5=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                    ( (( --. ) (dih2_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.375)) *.  (sqrt x1)) +.  (  (#0.33) *.  (sqrt x2)) +.  (  (#0.11) *.  (sqrt x3)) +. 
                    (  (--. (#0.36)) *.  (sqrt x4)) +.  (  (#0.72) *.  (sqrt x5)) +.  (  (#0.034) *.  (sqrt x6))) >.  (--. (#0.36135)))`;;


let I_319046543_6=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                    ( (sol_x x1 x2 x3 x4 x5 x6) +.  (  (#0.42) *.  (sqrt x1)) +.  (  (#0.165) *.  (sqrt x2)) +.  (  (#0.165) *.  (sqrt x3)) +. 
                    (  (--. (#0.06)) *.  (sqrt x4)) +.  (  (--. (#0.135)) *.  (sqrt x5)) +.  (  (--. (#0.135)) *.  (sqrt x6))) >.  (#1.479))`;;


let I_319046543_7=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                    ( (( --. ) (sol_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.265)) *.  (sqrt x1)) +.  (  (--. (#0.06)) *.  (sqrt x2)) +.  (  (--. (#0.06)) *.  (sqrt x3)) +. 
                    (  (#0.124) *.  (sqrt x4)) +.  (  (#0.296) *.  (sqrt x5)) +.  (  (#0.296) *.  (sqrt x6))) >.  (#0.0997))`;;



let I_319046543_8=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                    ( (( --. ) (nu_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.112) *.  (sqrt x1)) +.  (  (--. (#0.142)) *.  (sqrt x2)) +.  (  (--. (#0.142)) *.  (sqrt x3)) +. 
                    (  (--. (#0.16)) *.  (sqrt x4)) +.  (  (--. (#0.074)) *.  (sqrt x5)) +.  (  (--. (#0.074)) *.  (sqrt x6))) >.  (--. (#0.9029)))`;;



let I_319046543_9=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                    ( (nu_x x1 x2 x3 x4 x5 x6) +.  (  (#0.07611) *.  (dih_x x1 x2 x3 x4 x5 x6))) <.  (#0.11))`;;




let I_319046543_10=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ((
                    ( (nu_gamma_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.015)) *.  (sqrt x1)) +.  (  (--. (#0.16)) *.  ( (sqrt x2) +.  (sqrt x3) +.  (sqrt x4))) +. 
                    (  (--. (#0.0738)) *.  ( (sqrt x5) +.  (sqrt x6))) ) >.  (--. (#1.29285))) \/ (sqrt2 <. (eta_x x1 x2 x6) ))`;;




let I_319046543_11=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                    ( (taunu_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.07106)) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (--. (#0.06429)))`;;




let I_319046543_12=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (taunu_x x1 x2 x3 x4 x5 x6) >.  (#0.0414))`;;



(*
 LOC: 2002 k.c page 44
 Remark (#17.1)

 From text: 

In connection with the Inequality (I_319046543_3), we
occasionally use the stronger constant $0.2345$ instead of
$0.2282$.  To justify this constant, we have checked using
interval arithmetic that the bound $0.2345$ holds if $y_1\le2.68$
or $y_4\le2.475$. Further interval calculations show that the
anchored simplices can be erased if they share an upright diagonal
with such a quarter.

*)


let I_319046543_13=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.495) *.  (sqrt x1)) +.  (  (--. (#0.214)) *.  (sqrt x2)) +.  (  (--. (#0.214)) *.  (sqrt x3)) +. 
            (  (#1.05) *.  (sqrt x4)) +.  (  (--. (#0.214)) *.  (sqrt x5)) +.  (  (--. (#0.214)) *.  (sqrt x6))) >.  (#0.2345)) \/ 
        ( (sqrt x1) >.  (#2.68)))`;;




let I_319046543_14=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.495) *.  (sqrt x1)) +.  (  (--. (#0.214)) *.  (sqrt x2)) +.  (  (--. (#0.214)) *.  (sqrt x3)) +. 
            (  (#1.05) *.  (sqrt x4)) +.  (  (--. (#0.214)) *.  (sqrt x5)) +.  (  (--. (#0.214)) *.  (sqrt x6))) >.  (#0.2345)) \/ 
        ( (sqrt x4) >.  (#2.475)))`;;





(*
 
LOC: 2002 k.c page 44--45
17.8 Group_8
*)

(*
 The following comment about Group_8 is copied from 
 KC_2002_17.8_page44_group8.
*)

(*
 We give lower and upper bounds on  dihedral angles.  The domains that we
 list are not disjoint. In general we consider an edge as belonging to
 the most restrictive domain that the information of the following charts
 permit us to conclude that it lies in.
*)



(* interval verification by Ferguson *)
let I_853728973_1=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.153))`;;




(* interval verification by Ferguson *)
let I_853728973_2=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#2.28))`;;





(* interval verification by Ferguson *)
let I_853728973_3=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.32))`;;




(* interval verification by Ferguson *)
let I_853728973_4=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (  (#2.0) *.  pi))`;;




(* interval verification by Ferguson *)
let I_853728973_5=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#0.633))`;;




(* interval verification by Ferguson *)
let I_853728973_6=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (square (#3.02)))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.624))`;;





(* interval verification by Ferguson *)
let I_853728973_7=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.033))`;;




(* interval verification by Ferguson *)
let I_853728973_8=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.929))`;;





(* interval verification by Ferguson *)
let I_853728973_9=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, square_4t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.033))`;;




(* interval verification by Ferguson *)
let I_853728973_10=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, square_4t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (  (#2.0) *.  pi))`;;




(* interval verification by Ferguson *)
let I_853728973_11=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.259))`;;




(* interval verification by Ferguson *)
let I_853728973_12=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (  (#2.0) *.  pi))`;;





(* interval verification by Ferguson *)
let I_853728973_13=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#0.817))`;;




(* interval verification by Ferguson *)
let I_853728973_14=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, (square (#3.02)));
     (square_2t0, x6, (square (#3.02)))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.507))`;;




(* interval verification by Ferguson *)
let I_853728973_15=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.07))`;;




(* interval verification by Ferguson *)
let I_853728973_16=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.761))`;;




(* interval verification by Ferguson *)
let I_853728973_17=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, square_4t0);
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.07))`;;




(* interval verification by Ferguson *)
let I_853728973_18=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, square_4t0);
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (  (#2.0) *.  pi))`;;




(* interval verification by Ferguson *)
let I_853728973_19=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.23))`;;




(* interval verification by Ferguson *)
let I_853728973_20=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (  (#2.0) *.  pi))`;;




(* interval verification by Ferguson *)
let I_853728973_21=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#0.956))`;;



(* interval verification by Ferguson *)
let I_853728973_22=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#2.184))`;;




(* interval verification by Ferguson *)
let I_853728973_23=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.23))`;;




(* interval verification by Ferguson *)
let I_853728973_24=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  pi)`;;



(* interval verification by Ferguson *)
let I_853728973_25=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.23))`;;




(* interval verification by Ferguson *)
let I_853728973_26=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  pi)`;;



(* interval verification by Ferguson *)
let I_853728973_27=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.416))`;;




(* interval verification by Ferguson *)
let I_853728973_28=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  pi)`;;




(* interval verification by Ferguson *)
let I_853728973_29=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (#8.0));
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#0.633))`;;




(* interval verification by Ferguson *)
let I_853728973_30=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (#8.0));
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.624))`;;




(* interval verification by Ferguson *)
let I_853728973_31=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (#8.0));
     (square_2t0, x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.033))`;;




(* interval verification by Ferguson *)
let I_853728973_32=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (#8.0));
     (square_2t0, x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (  (#2.0) *.  pi))`;;





(* interval verification by Ferguson *)
let I_853728973_33=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (#8.0));
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#0.0))`;;




(* interval verification by Ferguson *)
let I_853728973_34=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (#8.0));
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.381))`;;



(* interval verification by Ferguson *)
let I_853728973_35=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (#8.0));
     (square_2t0, x4, square_2t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#0.777))`;;




(* interval verification by Ferguson *)
let I_853728973_36=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (#8.0));
     (square_2t0, x4, square_2t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (  (#2.0) *.  pi))`;;


(*
 
LOC: 2002 k.c page 45--46
17.9 Group_9
*)



(* interval verification by Ferguson *)
let I_529738375_1=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (  (dih_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.372)) *.  (sqrt x1)) +.  (  (#0.465) *.  (sqrt x2)) +.  (  (#0.465) *.  (sqrt x3)) +. 
            (  (#0.465) *.  (sqrt x5)) +.  (  (#0.465) *.  (sqrt x6))) >.   (#4.885))`;;




(* interval verification by Ferguson *)
let I_529738375_2=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    (
            (  (  (#0.291) *.  (sqrt x1)) +.  (  (--. (#0.393)) *.  (sqrt x2)) +.  (  (--. (#0.586)) *.  (sqrt x3)) +.  (  (#0.79) *.  (sqrt x4)) +. 
            (  (--. (#0.321)) *.  (sqrt x5)) +.  (  (--. (#0.397)) *.  (sqrt x6)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) ) <.   (--. (#2.47277)))`;;


(* interval verification by Ferguson *)
let I_529738375_3=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, square_4t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    (
            (  (  (#0.291) *.  (sqrt x1)) +.  (  (--. (#0.393)) *.  (sqrt x2)) +.  (  (--. (#0.586)) *.  (sqrt x3)) +. 
            (  (--. (#0.321)) *.  (sqrt x5)) +.  (  (--. (#0.397)) *.  (sqrt x6)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) ) <.   (--. (#4.45567)))`;;



(* interval verification by Ferguson *)
let I_529738375_4=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    (
            (  (  (#0.291) *.  (sqrt x1)) +.  (  (--. (#0.393)) *.  (sqrt x2)) +.  (  (--. (#0.586)) *.  (sqrt x3)) +. 
            (  (--. (#0.321)) *.  (sqrt x5)) +.  (  (--. (#0.397)) *.  (sqrt x6)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) ) <.   (--. (#4.71107)))`;;



(* interval verification by Ferguson *)
let I_529738375_5=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    (
            (  (--.  (#0.214) *.  (sqrt x1)) +.  (  ( (#0.4)) *.  (sqrt x2)) +.  (  ( (#0.58)) *.  (sqrt x3)) +. 
            (  ( (#0.155)) *.  (sqrt x5)) +.  (  ( (#0.395)) *.  (sqrt x6)) +.   (dih_x x1 x2 x3 x4 x5 x6) ) >.   (#4.52345))`;;



(* interval verification in partK.cc *)
let I_529738375_6=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    ( (tauA_x x1 x2 x3 x4 x5 x6) >.  D32)`;;


(* interval verification in partK.cc *)
let I_529738375_7=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    ( (vorA_x x1 x2 x3 x4 x5 x6) <.  Z32)`;;




(* interval verification by Ferguson *)
let I_529738375_8=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    (
            (  (( --. ) (sol_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.492)) *.  (sqrt x1)) +.  (  (--. (#0.492)) *.  (sqrt x2)) +.  (  (--. (#0.492)) *.  (sqrt x3)) +. 
            (  (#0.43) *.  (sqrt x4)) +.  (  (#0.038) *.  (sqrt x5)) +.  (  (#0.038) *.  (sqrt x6)) ) <.   (--. (#2.71884)))`;;



(* interval verification in partK.cc *)
let I_529738375_9=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    (
            (  (( --. ) (vorA_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.058)) *.  (sqrt x1)) +.  (  (--. (#0.105)) *.  (sqrt x2)) +.  (  (--. (#0.105)) *.  (sqrt x3)) +. 
            (  (--. (#0.115)) *.  (sqrt x4)) +.  (  (#0.062) *.  (sqrt x5)) +.  (  (--. (#0.062)) *.  (sqrt x6)) ) >.   (--. (#1.02014)))`;;



(* interval verification in partK.cc *)
let I_529738375_10=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    (
            (  (vor_0_x x1 x2 x3 x4 x5 x6) +.  (  (#0.419351) *.  (sol_x x1 x2 x3 x4 x5 x6)) ) <.   (#0.3085))`;;



(* interval verification by Ferguson *)
let I_529738375_11=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    (
            (  (  (#0.115) *.  (sqrt x1)) +.  (  (--. (#0.452)) *.  (sqrt x2)) +.  (  (--. (#0.452)) *.  (sqrt x3)) +. 
            (  (#0.613) *.  (sqrt x4)) +.  (  (--. (#0.15)) *.  (sqrt x5)) +.  (  (--. (#0.15)) *.  (sqrt x6)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) ) <.   (--. (#2.177)))`;;



(* interval verification by Ferguson *)
let I_529738375_12=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    (
            (  (  (#0.115) *.  (sqrt x1)) +.  (  (--. (#0.452)) *.  (sqrt x2)) +.  (  (--. (#0.452)) *.  (sqrt x3)) +. 
            (  (#0.618) *.  (sqrt x4)) +.  (  (--. (#0.15)) *.  (sqrt x5)) +.  (  (--. (#0.15)) *.  (sqrt x6)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) ) <.   (--. (#2.17382)))`;;



(* interval verification in partK.cc *)
let I_529738375_13=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    (  (vor_0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.121)))`;;




(* interval verification in partK.cc *)
let I_529738375_14=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    (  ((tau_0_x x1 x2 x3 x4 x5 x6)) >.  (#0.21301))`;;


(* interval verification by Ferguson *)
let I_529738375_15=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, square_4t0);
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    (
            (  (  (#0.115) *.  (sqrt x1)) +.  (  (--. (#0.452)) *.  (sqrt x2)) +.  (  (--. (#0.452)) *.  (sqrt x3)) +. 
            (  (--. (#0.15)) *.  (sqrt x5)) +.  (  (--. (#0.15)) *.  (sqrt x6)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) ) <.   (--. (#3.725)))`;;




(* interval verification by Ferguson *)
let I_529738375_16=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    (
            (  (  (#0.115) *.  (sqrt x1)) +.  (  (--. (#0.452)) *.  (sqrt x2)) +.  (  (--. (#0.452)) *.  (sqrt x3)) +. 
            (  (--. (#0.15)) *.  (sqrt x5)) +.  (  (--. (#0.15)) *.  (sqrt x6)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) ) <.   (--. (#3.927)))`;;



(*
 
LOC: 2002 k.c page 46
17.10 Group_10
*)


let I_456320257_1=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vorC_x x1 x2 x3 x4 x5 x6) <.  (#0.0))`;;




let I_456320257_2=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (  (  (#0.47) *.  (sqrt x1)) +.  (  (--. (#0.522)) *.  (sqrt x2)) +.  (  (--. (#0.522)) *.  (sqrt x3)) +.  (  (#0.812) *.  (sqrt x4)) +. 
            (  (--. (#0.522)) *.  (sqrt x5)) +.  (  (--. (#0.522)) *.  (sqrt x6)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) ) <.   (--. (#2.82988)))`;;




let I_456320257_3=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (  (  (#0.47) *.  (sqrt x1)) +.  (  (--. (#0.522)) *.  (sqrt x2)) +.  (  (--. (#0.522)) *.  (sqrt x3)) +. 
            (  (--. (#0.522)) *.  (sqrt x5)) +.  (  (--. (#0.522)) *.  (sqrt x6)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) ) <.   (--. (#4.8681)))`;;




let I_456320257_4=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (  (  (#0.47) *.  (sqrt x1)) +.  (  (--. (#0.522)) *.  (sqrt x2)) +.  (  (--. (#0.522)) *.  (sqrt x3)) +. 
            (  (--. (#0.522)) *.  (sqrt x5)) +.  (  (--. (#0.522)) *.  (sqrt x6)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) ) <.   (--. (#5.1623)))`;;




(*
 
LOC: 2002 k.c page 47
17.11 Group_11
*)



let I_664959245_1=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (#8.0));
     (square_2t0, x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (  (  (--. (#0.4)) *.  (sqrt x3)) +.  (  (#0.15) *.  (sqrt x1)) +.  (  (--. (#0.09)) *.  (sqrt x2)) +. 
            (  (--. (#0.631)) *.  (sqrt x6)) +.  (  (--. (#0.23)) *.  (sqrt x5)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) ) <.   (--. (#3.9788)))`;;



let I_664959245_2=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (#8.0));
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    (
            (  (  (#0.289) *.  (sqrt x1)) +.  (  (--. (#0.148)) *.  (sqrt x2)) +.  (  (--. (#1.36)) *.  (sqrt x3)) +. 
            (  (#0.688) *.  (sqrt x4)) +.  (  (--. (#0.148)) *.  (sqrt x5)) +.  (  (--. (#1.36)) *.  (sqrt x6)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) ) <.   (--. (#6.3282)))`;;




let I_664959245_3=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     (square_2t0, x3, (#8.0));
     (square_2t0, x4, (square (( +. ) (#2.51) (sqrt (#8.0)))));
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (#8.0))
    ]
    (
            (  (  (#0.289) *.  (sqrt x1)) +.  (  (--. (#0.148)) *.  (sqrt x2)) +.  (  (--. (#0.723)) *.  (sqrt x3)) +. 
            (  (--. (#0.148)) *.  (sqrt x5)) +.  (  (--. (#0.723)) *.  (sqrt x6)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) ) <.   (--. (#4.85746)))`;;




(*
 
LOC: 2002 k.c page 47
17.12 Group_12
*)


(* interval verification in partK.cc *)
let I_704795925_1=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
    (  (nu_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.055)))`;;



let I_704795925_2=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
    (  (taunu_x x1 x2 x3 x4 x5 x6) >.  (#0.092))`;;





(* interval verification in partK.cc *)
let I_332919646_1=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (sigmahat_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.039)))`;;


(* XXX This is false at 
   point: [4, 6.3001, 4, 6.756, 4, 4]
   value: about 0.001
   vor_0_x part
*)

let I_332919646_2=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (tauhat_x x1 x2 x3 x4 x5 x6) >.  (#0.094))`;;





(* interval verification in partK.cc *)
let I_335795137_1=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
    (  (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.197)))`;;



let I_335795137_2=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
    (  (taunu_x x1 x2 x3 x4 x5 x6) >.  (#0.239))`;;





(* interval verification by Ferguson *)
(* interval verification by Ferguson *)
let I_605071818_1=
   all_forall `ineq 
    [((square (#2.45)), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    (  (vor_0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.089)))`;;



let I_605071818_2=
   all_forall `ineq 
    [((square (#2.45)), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    (  (tau_0_x x1 x2 x3 x4 x5 x6) >.  (#0.154))`;;



(* interval verification by Ferguson *)
let I_642806938_1=
   all_forall `ineq 
    [((square (#2.45)), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        (square_2t0, x5, (#8.0));
     ((#4.0), x6, square_2t0)
    ]
    (  (vor_0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.089)))`;;



let I_642806938_2=
   all_forall `ineq 
    [((square (#2.45)), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        (square_2t0, x5, (#8.0));
     ((#4.0), x6, square_2t0)
    ]
    (  (tau_0_x x1 x2 x3 x4 x5 x6) >.  (#0.154))`;;


(*
 
LOC: 2002 k.c page 47
17.13 Group_13
*)


(* interval verification in partK.cc *)
let I_104506452=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (  (octavor_analytic_x x1 x2 x3 x4 x5 x6) <.  ( (octavor0_x x1 x2 x3 x4 x5 x6) +.  (--. (#0.017)))) \/ 
            (  (eta_x x1 x2 x6) <.  (sqrt (#2.0))))`;;




(* interval verification in partK.cc *)
let I_601083647=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#9.0), x4, (#9.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.678)) \/ 
            (  ( (sqrt x2) +.  (sqrt x3) +.  (sqrt x5) +.  (sqrt x6)) >.  (#8.77)))`;;


(*
 
LOC: 2002 k.c page 47
17.14 Group_14
*)



(* interval verification in partK.cc *)
let I_543730647=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (square (#2.6)));
    
        ((#4.0), x5, (square (#2.138)));
     ((#4.0), x6, square_2t0)
    ]
    (  (gamma_x x1 x2 x3 x4 x5 x6) <.  ( (#0.3138) +.  (  (--. (#0.157)) *.  (sqrt x5))))`;;




(* interval verification in partK.cc *)
let I_163030624=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((square (#2.121)), x2, (square (#2.145)));
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((square (#2.22)), x5, (square (#2.238)));
     ((#4.0), x6, square_2t0)
    ]
    (  (gamma_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.06)))`;;




(* 
Earlier version was false at (4.0,4.0,4.0,4.0,5.5225,5.5225).
Bug fixed 1/19/2008 : lower bound on x4 was a typo. It should be square_2t0.
*)
(* interval verification in partK.cc *)
let I_181462710=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.2)));
     ((#4.0), x2, (square (#2.2)));
     ((#4.0), x3, (square (#2.2)));
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, (square (#2.35)));
     ((#4.0), x6, (square (#2.35)))
    ]
    (  (gamma_x x1 x2 x3 x4 x5 x6) <. 
            ( (#0.000001) +.  (#1.4) +.  ( (--. (#0.1)) *.  (sqrt x1))
            +.  ( (--. (#0.15)) *.  ( (sqrt x2) +.  (sqrt x3) +.
            (sqrt x5) +.  (sqrt x6)))))`;;




(*
 
LOC: 2002 k.c page 48
17.15 Group_15
*)

(* interval verification in partK.cc *)
let I_463544803=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     ((square (#2.7)), x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  (vor_0_x x1 x2 x3 x4 x5 x6))`;;




(* interval verification in partK.cc *)
let I_399326202=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (square (#2.72)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (  (vor_0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.064))) \/ 
            (  (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;



(* interval verification in partK.cc *)
let I_569240360=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#2.7)), x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (vor_0_x x1 x2 x3 x4 x5 x6) <. 
            ( (#1.0612) +.  (  (--. (#0.08)) *.  ( (sqrt x1) +.  (sqrt x2) +.  (sqrt x3))) +.  (  (--. (#0.142)) *.  ( (sqrt x5) +.  (sqrt x6)))))`;;




(* False at 
SphereIn[5]:= VorVc @@ Sqrt [{4,4,4,6.7081,6.1009,4.41}]
SphereOut[5]= -0.0625133.
1/19/2008.  Added the missing eta456 constraint to eliminate counterexample.
*)
(* interval verification in partK.cc *)
let I_252231882=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#2.59)), x4, (square (#2.64)));
     ((square (#2.47)), x5, square_2t0);
     ((square (#2.1)), x6, (square (#3.51)))
    ]
    ((  (vor_0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.0713))) \/
    ( (eta_x x4 x5 x6) <. (sqrt (#2.0))))`;;



let I_472436131=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.13)));
     ((#4.0), x2, (square (#2.13)));
     ((#4.0), x3, (square (#2.13)));
     ((square (#2.7)), x4, (square (#2.74)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (  (vor_0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.06))) \/ 
            (  (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;




(* interval verification in partK.cc *)
let I_913534858=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (square (#2.747)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (  (vor_0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.058))) \/ 
            (  (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;




(* interval verification in partK.cc *)
let I_850226792=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (square (#2.77)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (  (vor_0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.0498))) \/ 
            (  (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;



(*
 
LOC: 2002 k.c page 48
17.16 Group_16
*)



(* 
Was false at (4,4,4,8,6.3001,6.3001)
Fixed by inserting the missing circumradius condition on 1/19/2008.
Also, the lower bound on x4 was changed to 7.29 from square_2t0 
to bring it into agreement with the interval calculation in partK.cc
*)
(* interval verification in partK.cc *)

(* changed (square_2t0, x4, (#8.0)); *)

let I_594246986=
  all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     ((square (#7.29), x4, (#8.0))); 
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (( ( (( --. ) (gamma_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.145)) *.  (sqrt x1)) +.  (  (--. (#0.08)) *.  ( (sqrt x2) +.  (sqrt x3))) +. 
           (  (--. (#0.133)) *.  ( (sqrt x5) +.  (sqrt x6)))) >.   (--. (#1.146))) \/ (  (eta_x x4 x5 x6) >.  (sqrt (#2.0))))`;;



(* interval verification in partK.cc *)

(* XXX This is false at 
   point: [4, 4, 4, 6.3001, 5.29, 5.29]
   value: about 0.0001
*)

let I_381970727=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, (square (#2.3)));
     ((#4.0), x6, (square (#2.3)))
    ]
    ( ( (( --. ) (gamma_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.145)) *.  (sqrt x1)) +.  (  (--. (#0.081)) *.  ( (sqrt x2) +.  (sqrt x3))) +. 
            (  (--. (#0.16)) *.  ( (sqrt x5) +.  (sqrt x6)))) >.   (--. (#1.255)))`;;




(* interval verification in partK.cc *)
let I_951798877=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, (square (#2.3)));
     ((#4.0), x6, (square (#2.3)))
    ]
    ( ( (( --. ) (gamma_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.03)) *.  (sqrt x1)) +.  (  (--. (#0.03)) *.  ( (sqrt x2) +.  (sqrt x3))) +. 
            (  (--. (#0.094)) *.  ( (sqrt x5) +.  (sqrt x6)))) >.   (--. (#0.5361)))`;;




(* interval verification in partK.cc *)
let I_923397705=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( ( (( --. ) (gamma_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.03)) *.  (sqrt x1)) +.  (  (--. (#0.03)) *.  ( (sqrt x2) +.  (sqrt x3))) +. 
            (  (--. (#0.16)) *.  ( (sqrt x5) +.  (sqrt x6)))) >.  ( (--. (#0.82)) +.  (--. (#0.000001)))) \/ 
            ( ( (sqrt x5) +.  (sqrt x6)) >.  (#4.3)))`;;




(* interval verification in partK.cc *)
let I_312481617=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     (square_2t0, x4, (#8.0));
    
        ((square (#2.35)), x5, square_4t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (gamma_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.053)))`;;



(* interval verification in partK.cc *)
let I_292760488=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     (square_2t0, x4, (#8.0));
    
        ((square (#2.25)), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (gamma_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.041)))`;;




(* interval verification in partK.cc *)
let I_155008179=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( ( (gamma_x x1 x2 x3 x4 x5 x6) +.  (  (#0.419351) *.  (sol_x x1 x2 x3 x4 x5 x6))) <. 
            ( (  (#0.079431) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.0436) *.  ( (sqrt x5) +.  (sqrt x6))) +.  (--. (#0.0294)))) \/ 
            (  (eta_x x4 x5 x6) >.  (sqrt (#2.0))))`;;



(* interval verification in partK.cc *)
let I_819450002=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.13)));
     ((#4.0), x2, (square (#2.13)));
     ((#4.0), x3, (square (#2.13)));
     (square_2t0, x4, (square (#2.67)));
    
        ((#4.0), x5, (square (#2.1)));
     ((square (#2.27)), x6, (square (#2.43)))
    ]
    ( (gamma_x x1 x2 x3 x4 x5 x6) <.  ( (#1.1457) +.  (  (--. (#0.1)) *.  ( (sqrt x1) +.  (sqrt x2) +.  (sqrt x3))) +. 
            (  (--. (#0.17)) *.  (sqrt x5)) +.  (  (--. (#0.11)) *.  (sqrt x6))))`;;




(* interval verification in partK.cc *)
let I_495568072=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     (square_2t0, x4, (square (#2.7)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( ( (  (#1.69) *.  (sqrt x4)) +.  (sqrt x5) +.  (sqrt x6)) >.  (#9.0659)) \/ 
            (  (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;



(* interval verification in partK.cc *)
let I_838887715=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     (square_2t0, x4, (square (#2.77)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( ( (  (#1.69) *.  (sqrt x4)) +.  (sqrt x5) +.  (sqrt x6)) >.  (#9.044)) \/ 
            (  (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;




(* interval verification in partK.cc *)
let I_794413343=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     (square_2t0, x4, (square (#2.72)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( ( (sqrt x5) +.  (sqrt x6)) >.  (#4.4)) \/ 
            (  (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;



(*
 
LOC: 2002 k.c page 48
17.17 Group_17
*)



(* interval verification in partK.cc *)
let I_378020227=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, (square (#2.77)));
     (square_2t0, x6, (square (#2.77)))
    ]
    (  ( (( --. ) (vor_analytic_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.058)) *.  (sqrt x1)) +.  (  (--. (#0.08)) *.  (sqrt x2)) +.  (  (--. (#0.08)) *.  (sqrt x3)) +. 
            (  (--. (#0.16)) *.  (sqrt x4)) +.  (  (--. (#0.21)) *.  ( (sqrt x5) +.  (sqrt x6))) ) >.  (--. (#1.7531)))`;;



(* 
Changed x5 from 4..(2t)^2
*)
(* interval verification in partK.cc *)
let I_256893386=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, #8.0);
     ((square (#2.77)), x6, (#8.0))
    ]
    (
            (  ( (( --. ) (vor_0_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.058)) *.  (sqrt x1)) +.  (  (--. (#0.1)) *.  (sqrt x2)) +.  (  (--. (#0.1)) *.  (sqrt x3)) +. 
            (  (--. (#0.165)) *.  (sqrt x4)) +.  (  (--. (#0.115)) *.  (sqrt x6)) +.  (  (--. (#0.12)) *.  (sqrt x5)) ) >.  (--. (#1.38875))) \/ 
            ( (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;




(* interval verification in partK.cc *)
let I_749955642=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        (square_2t0, x5, (square (#2.77)));
     (square_2t0, x6, (square (#2.77)))
    ]
    (
            (  ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) >.  (#7.206)) \/ 
            ( (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;



(* interval verification in partK.cc *)
let I_653849975=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.14)));
     ((#4.0), x2, (square (#2.14)));
     ((#4.0), x3, (square (#2.14)));
     ((#4.0), x4, square_2t0);
    
        (square_2t0, x5, (square (#2.77)));
     (square_2t0, x6, (square (#2.77)))
    ]
    (
            (  ( (( --. ) (vor_0_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.058)) *.  (sqrt x1)) +.  (  (--. (#0.05)) *.  (sqrt x2)) +.  (  (--. (#0.05)) *.  (sqrt x3)) +. 
            (  (--. (#0.16)) *.  (sqrt x4)) +.  (  (--. (#0.13)) *.  (sqrt x6)) +.  (  (--. (#0.13)) *.  (sqrt x5)) ) >.  (--. (#1.24547))) \/ 
            ( (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;





(* interval verification in partK.cc *)
let I_480930831=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((square (#2.77)), x5, (#8.0));
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.077)))`;;



(* interval verification in partK.cc *)
let I_271703736=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (square (#2.77)));
     (square_2t0, x5, (square (#2.77)));
     ((#4.0), x6, square_2t0)
    ]
    ( ( (vor_analytic_x x1 x2 x3 x4 x5 x6) +.  (  (#0.419351) *.  (sol_x x1 x2 x3 x4 x5 x6))) <.  (#0.289))`;;

(* interval verification in partK.cc *)
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

(*
 
LOC: 2002 k.c page 49
17.18 Group_18
*)




(* interval verification in partK.cc *)
let I_455329491=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (square (#2.6961)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  (  (--. (#0.078)) /  (#2.0)))`;;




(* interval verification in partK.cc *)
let I_857241493=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        (square_2t0, x5, (square (#2.6961)));
     (square_2t0, x6, (square (#2.6961)))
    ]
    (
            ( (vort_x x1 x2 x3 x4 x5 x6 (sqrt (#2.0))) <.  (--. (#0.078))) \/ 
            ( (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;




(*
 
LOC: 2002 k.c page 49
17.19 Group_19
*)


(*

2002 text:

The interval calculations here show that the set of separated
vertices (\ref{definition:admissible:excess}) can be generalized
to include   opposite vertices of a quadrilateral unless the edge
between those vertices forms a flat quarter.   Consider a vertex
of type $(3,1,1)$ with $a(3)=1.4\,\pt$.  By the arguments in the
text, we may assume that the dihedral angles of the exceptional
regions at those vertices are at least $1.32$ (see
\cite[3.11.4]{part4}). Also, the three quasi-regular tetrahedra at
the vertex squander at least $1.5\,\pt$ by a linear programming
bound, if the angle of the quad cluster is at least $1.55$.  Thus,
we assume that the dihedral angles at opposite vertices of the
quad cluster are at most $1.55$.   A linear program also gives
$\tau+0.316\dih>0.3864$ for a quasi-regular tetrahedron.

If we give bounds of the form
$\tau_x +0.316\dih> b$, for the part of the quad cluster around a
vertex, where $\tau_x$ is the appropriate squander function, then
we obtain
    $$\sum\tau_x > -0.316(2\pi-1.32) + b + 3 (0.3864)$$
for a lower bound on what is squandered.  If the two opposite
vertices give at least  $2(1.4)\,\pt + 0.1317$, then the inclusion
of  two opposite vertices in the separated set of vertices is
justified.  (Recall that $t_4=0.1317$.)  The following
inequalities give the desired result.

*)



(* interval verification in partK.cc *)
let I_912536613=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( ( (taumu_flat_x x1 x2 x3 x4 x5 x6) +.  (  (#0.316) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (#0.5765)) \/ 
            ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.55)))`;;



(* interval verification in partK.cc *)
let I_640248153=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( ( (tau_0_x x1 x2 x3 x4 x5 x6) +.  (  (#0.316) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (#0.5765)) \/ 
            ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.55)))`;;




(* interval verification in partK.cc *)
let I_594902677=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (taunu_x x1 x2 x3 x4 x5 x6) +.  (  (#0.316) *.  (dih2_x x1 x2 x3 x4 x5 x6))) >.  (#0.2778))`;;


(* XXX Note I moved the huge non-interval-arithmetic inequalitites
   to kep_inequalities2.ml *)

(*
 
LOC: 2002 k.c page 50
17.23 Group_23
*)


(* interval verification in partK.cc *)
let I_365179082_1=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vorC_x x1 x2 x3 x4 x5 x6) <.  (#0.0))`;;




let I_365179082_2=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vorC_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.05)))`;;




let I_365179082_3=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (vorC_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.119))) \/ 
                ( (eta_x x1 x2 x6) <.  (sqrt (#2.0))))`;;


(*
 
LOC: 2002 k.c page 50-51
17.24 Group_24
*)

(* 

From 2002 text:

    \begin{eqnarray}
        \sigma_R(D) <
            \begin{cases}
                0,& y_1\in[2t_0,2\sqrt2],\\
                -0.043, & y_1\in[2t_0,2.696],\\
            \end{cases}
    %\label{sec:4.5.6}
    \label{eqn:group24}
    \end{eqnarray}
 for quad regions $R$ constructed from  an anchored
simplex $S$ and adjacent special simplex $S'$. Assume that
$y_4(S)=y_4(S')\in[2\sqrt2,3.2]$, and that the other edges have
lengths in $[2,2t_0]$. The bound $0$ is found in \cite[Lemma
3.13]{formulation}. The bound $-0.043$ is obtained from
deformations, reducing the inequality to the following interval
calculations.

(* interval verification by Ferguson *)
\refno{368244553\dag}

(* interval verification by Ferguson *)
\refno{820900672\dag}

(* interval verification by Ferguson *)
\refno{961078136\dag}


Under certain conditions, Inequality \ref {eqn:group24} can be
improved.
...
(The last of these was verified by S. Ferguson.) \refno{424186517}

These combine to give
$$
\vor_0(S)+\vor_0(S') < \begin{cases}  -0.091,&\text{ or }\\
        -0.106,&
        \end{cases}
$$
for the combination of special simplex and anchored simplex under
the stated conditions.

*)


let I_368244553=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     (square_2t0, x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  (  (--. (#0.043)) /  (#2.0)))`;;

let I_820900672=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (vor_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))) <.  (--. (#0.043))) \/ 
                ( (cross_diag_x x1 x2 x3 x4 x5 x6 (#4.0) (#4.0) (#4.0)) <.  two_t0))`;;

let I_961078136=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (vor_0_x square_2t0 x2 x3 x4 (#4.0) (#4.0))) <.  (--. (#0.043))) \/ 
                ( (cross_diag_x x1 x2 x3 x4 x5 x6 square_2t0 (#4.0) (#4.0)) <.  two_t0))`;;

(* Fixed bad bounds on first variable on 1/19/2008  *)
(* interval verification in part4.cc:424186517+1 *)
let I_424186517_1=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.12)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.033))) \/ 
                ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.8)))`;;

(* interval verification in part4.cc:424186517+2 *)
let I_424186517_2=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.058))) \/ 
                ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.5)))`;;

(* interval code in part4.cc:424186517+3 not used *)
(* interval verification by Ferguson *)
let I_424186517_3=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
                ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.073))) \/ 
                ( (eta_x x1 x2 x6) <.  (sqrt (#2.0))))`;;



(*
 
LOC: 2002 k.c page 51
17.25 Group_25 (pentagons)
*)

(*

From 2002 text:

There are a few inequalities that arise for pentagonal regions.

\begin{proposition} If the pentagonal region has no flat quarters
and no upright quarters, the subregion $F$ is a pentagon. It
satisfies
    $$
    \begin{array}{lll}
     \vor_0 &< -0.128,\\
    \tau_0 &> 0.36925.
    \end{array}
    %\label{eqn:4.7.2}
    $$
\end{proposition}


\begin{proof}  The proof is by deformations and interval calculations. If
a deformation produces a new flat quarter, then the result follows
from \cite[$\A_{13}$]{part4} and Inequality \ref {app:hexquad}. So
we may assume that all diagonals remain at least $2\sqrt2$. If all
diagonals remain at least 3.2, the result follows from the
tcc-bound on the pentagon \cite[Section 5.5]{part4}.  Thus, we
assume that some diagonal is at most $3.2$. We deform the cluster
into the form
    $$(a_1,2,a_2,2,a_3,2,a_4,2,a_5,2),\quad |v_i|=a_i\in\{2,2t_0\}.$$
Assume that $|v_1-v_3|\le3.2$.  If $\max(a_1,a_3)=2t_0$, the
result follows from \cite[$\A_{13}$]{part4} and
Section~\ref{app:hexquad}, Equations \ref{eqn:hexquadsig} and
\ref{eqn:hexquadtau}.

Assume $a_1=a_3=2$. There is a diagonal of the quadrilateral of
length at most $3.23$ because
    $$\Delta(3.23^2,4,4,3.23^2,4,3.2^2)<0.$$
  The result now follows from the following interval arithmetic
  calculations.

(These inequalities are closely related to
\cite[$\A_{21}$]{part4}.)

*)

(* interval verification by Ferguson *)
let I_587781327=
   all_forall `ineq 
    [((#8.0), x4, (square (#3.2)));
     ((#8.0), x4', (square (#3.23)))
    ]
    ( ( (vor_0_x (#4.0) (#4.0) (#4.0) x4 (#4.0) (#4.0)) +.  
   (vor_0_x (#4.0) (#4.0) (#4.0) x4' (#4.0) (#4.0)) +.  
  (vor_0_x (#4.0) (#4.0) (#4.0) x4 x4' (#4.0))) <.  (--. (#0.128)))`;;



(* interval verification by Ferguson *)
let I_807067544=
   all_forall `ineq 
    [((#8.0), x4, (square (#3.2)));
     ((#8.0), x4', (square (#3.23)))
    ]
    ( ( (tau_0_x (#4.0) (#4.0) (#4.0) x4 (#4.0) (#4.0)) +.  
  (tau_0_x (#4.0) (#4.0) (#4.0) x4' (#4.0) (#4.0)) +.  
  (tau_0_x (#4.0) (#4.0) (#4.0) x4 x4' (#4.0))) >.  (#0.36925))`;;




(* interval verification (commented out) in partK.cc *)
(* interval verification by Ferguson *)
let I_986970370=
   all_forall `ineq 
    [((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.06)))
    ]
    ( (tau_0_x (#4.0) (#4.0) x3 x4 (#4.0) (#4.0)) <.  
  (tau_0_x square_2t0 (#4.0) x3 x4 (#4.0) (#4.0)))`;;




(* interval verification (commented out) in partK.cc *)
(* interval verification by Ferguson *)
let I_677910379=
   all_forall `ineq 
    [((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.06)))
    ]
    ( (vor_0_x (#4.0) (#4.0) x3 x4 (#4.0) (#4.0)) >.  
  (vor_0_x square_2t0 (#4.0) x3 x4 (#4.0) (#4.0)))`;;





(* interval verification in partK.cc *)
let I_276168273=
   all_forall `ineq 
    [((#4.0), x3, square_2t0);
     ((square (#3.06)), x5, (square (#3.23)));
     ((square (#3.06)), x6, (square (#3.23)))
    ]
    ( (vor_0_x (#4.0) (#4.0) x3 (#4.0) x5 x6) <.  (--. (#0.128)))`;;



(* interval verification in partK.cc *)
let I_411203982=
   all_forall `ineq 
    [((square (#3.06)), x5, (square (#3.23)));
     ((square (#3.06)), x6, (square (#3.23)))
    ]
    ( (tau_0_x (#4.0) (#4.0) (#4.0) (#4.0) x5 x6) >.  (#0.36925))`;;




(* interval verification in partK.cc *)
let I_860823724=
   all_forall `ineq 
    [((square (#3.06)), x5, (square (#3.23)));
     ((square (#3.06)), x6, (square (#3.23)))
    ]
    ( (tau_0_x (#4.0) (#4.0) square_2t0 (#4.0) x5 x6) >.  (#0.31))`;;




let I_353116955=
   all_forall `ineq 
    [((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x5, (square (#3.23)));
    
        ((square (#3.06)), x6, (square (#3.23)))
    ]
    ( (vor_0_x (#4.0) x2 x3 (#4.0) x5 x6) <.  
   ( (--. (#0.137)) +.  (  (--. (#0.14)) *.  ( (sqrt x5) +.  
       (  (--. (#2.0)) *.  (sqrt (#2.0)))))))`;;



(* interval verification in partK.cc *)
let I_943315982=
   all_forall `ineq 
    [((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x5, (square (#3.23)));
    
        ((square (#3.105)), x6, (square (#3.23)))
    ]
    ( (tau_0_x (#4.0) x2 x3 (#4.0) x5 x6) >.  
    ( (#0.31) +.  (  (#0.14) *.  ( (sqrt x5) +.  
        (  (--. (#2.0)) *.  (sqrt (#2.0)))))))`;;




(* interval verification in partK.cc *)
let I_941799628=
   all_forall `ineq 
    [((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x5, (square (#3.23)));
    
        ((square (#3.06)), x6, (square (#3.105)))
    ]
    ( (tau_0_x (#4.0) x2 x3 (#4.0) x5 x6) >.  
      ( (#0.31) +.  (  (#0.14) *.  ( (sqrt x5) +.  (  (--. (#2.0)) *.  (sqrt (#2.0))))) +. 
        (  (#0.19) *.  ( (--. (#3.105)) +.  (sqrt x6)))))`;;



(* interval verification in partK.cc *)
let I_674284283=
   all_forall `ineq 
    [((#4.0), x3, square_2t0);
     ((#8.0), x5, (square (#3.23)))
    ]
    ( (vor_0_x (#4.0) (#4.0) x3 (#4.0) x5 (#4.0)) <.  
  ( (#0.009) +.  (  (#0.14) *.  ( (sqrt x5) +.  (  (--. (#2.0)) *.  (sqrt (#2.0)))))))`;;



 
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
let I_775220784=
   all_forall `ineq 
    [((#4.0), x3, square_2t0);
     ((#8.0), x5, (square (#3.23)))
    ]
    ( (tau_0_x (#4.0) (#4.0) x3 (#4.0) x5 (#4.0)) >.  
  ( (#0.05925) +.  (  (#0.14) *.  ( (sqrt x5) +.  (  (--. (#2.0)) *.  (sqrt (#2.0)))))))`;;



(* interval verification in partK.cc *)
let I_286076305=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#8.0), x4, (square (#3.23)))
    ]
    ( (tau_0_x x1 x2 square_2t0 x4 (#4.0) (#4.0)) >.  (#0.05925))`;;



(* interval verification in partK.cc *)
let I_589319960=
   all_forall `ineq 
    [((square (#3.06)), x4, (square (#3.105)))
    ]
    ( (tau_0_x square_2t0 (#4.0) (#4.0) x4 (#4.0) (#4.0)) >.  
  (  (--. (#0.19)) *.  ( (sqrt x4) +.  (--. (#3.105)))))`;;


(*
 
LOC: 2002 k.c page 52
17.26 Group_26
*)

(*

From 2002 text:

Let $Q$ be a quadrilateral region with parameters
    $$(a_1,2t_0,a_2,2,a_3,2,a_4,2t_0),\quad a_i\in\{2,2t_0\}.$$
Assume that $|v_2-v_4|\in[2\sqrt2,3.2]$,
    $|v_1-v_3|\in[3.2,3.46]$. Note that
$$\Delta(4,4,8,2t_0^2,2t_0^2,3.46^2)<0.$$

Sat Feb 21 12:47:03 EST 2004: Are we making an implicit convexity
assumption by phrasing the inequality this way?


*)

(* interval verification by Ferguson *)
let I_302085207_GEN= 
   `\ a1 a2 a3 a4. (ineq
   [
   ((#8.0),x4,(square (#3.2)))
   ]
   ((vor_0_x a1 a2 a4 x4 (square_2t0) (square_2t0) +
    (vor_0_x a3 a2 a4 x4 (#4.0) (#4.0)) <. (--. (#0.168))) \/
    ((cross_diag_x a1 a2 a4 x4 (square_2t0) (square_2t0) a3 (#4.0) (#4.0)) <. (#3.2)) \/
    ((cross_diag_x a1 a2 a4 x4 (square_2t0) (square_2t0) a3 (#4.0) (#4.0)) >. (#3.46))))`;;

(* interval verification by Ferguson *)
let I_302085207_1= 
  all_forall (list_mk_comb( I_302085207_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_302085207_2= 
  all_forall (list_mk_comb( I_302085207_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_302085207_3= 
  all_forall (list_mk_comb( I_302085207_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_302085207_4= 
  all_forall (list_mk_comb( I_302085207_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_302085207_5= 
  all_forall (list_mk_comb( I_302085207_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));; 

(* XXX 
  This seems unfeasible due to cross_diag constraints
*)
(* interval verification by Ferguson *)
let I_302085207_6= 
  all_forall (list_mk_comb( I_302085207_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_302085207_7= 
  all_forall (list_mk_comb( I_302085207_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_302085207_8= 
  all_forall (list_mk_comb( I_302085207_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_302085207_9= 
  all_forall (list_mk_comb( I_302085207_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_302085207_10= 
  all_forall (list_mk_comb( I_302085207_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_302085207_11= 
  all_forall (list_mk_comb( I_302085207_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_302085207_12= 
  all_forall (list_mk_comb( I_302085207_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_302085207_13= 
  all_forall (list_mk_comb( I_302085207_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_302085207_14= 
  all_forall (list_mk_comb( I_302085207_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_302085207_15= 
  all_forall (list_mk_comb( I_302085207_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_302085207_16= 
  all_forall (list_mk_comb( I_302085207_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_411491283_GEN= 
   `\ a1 a2 a3 a4. (ineq
   [
   ((#8.0),x4,(square (#3.2)))
   ]
   ((tau_0_x a1 a2 a4 x4 (square_2t0) (square_2t0) +
    (tau_0_x a3 a2 a4 x4 (#4.0) (#4.0)) >. ( (#0.352))) \/
    ((cross_diag_x a1 a2 a4 x4 (square_2t0) (square_2t0) a3 (#4.0) (#4.0)) <. (#3.2)) \/
    ((cross_diag_x a1 a2 a4 x4 (square_2t0) (square_2t0) a3 (#4.0) (#4.0)) >. (#3.46))))`;;

(* interval verification by Ferguson *)
let I_411491283_1= 
  all_forall (list_mk_comb( I_411491283_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_411491283_2= 
  all_forall (list_mk_comb( I_411491283_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_411491283_3= 
  all_forall (list_mk_comb( I_411491283_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_411491283_4= 
  all_forall (list_mk_comb( I_411491283_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_411491283_5= 
  all_forall (list_mk_comb( I_411491283_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));; 

(* 
XXX Seems infeasible due to cross_diag_x constraints
*)
(* interval verification by Ferguson *)
let I_411491283_6= 
  all_forall (list_mk_comb( I_411491283_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_411491283_7= 
  all_forall (list_mk_comb( I_411491283_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_411491283_8= 
  all_forall (list_mk_comb( I_411491283_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_411491283_9= 
  all_forall (list_mk_comb( I_411491283_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_411491283_10= 
  all_forall (list_mk_comb( I_411491283_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_411491283_11= 
  all_forall (list_mk_comb( I_411491283_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_411491283_12= 
  all_forall (list_mk_comb( I_411491283_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_411491283_13= 
  all_forall (list_mk_comb( I_411491283_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_411491283_14= 
  all_forall (list_mk_comb( I_411491283_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));; 

(* interval verification by Ferguson *)
let I_411491283_15= 
  all_forall (list_mk_comb( I_411491283_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));; 

(* interval verification by Ferguson *)
let I_411491283_16= 
  all_forall (list_mk_comb( I_411491283_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));; 




(*
 
LOC: 2002 k.c page 52
17.27 Group_27
*)

(* 2002 text:

Consider a pentagonal region. If the pentagonal region has one
flat quarter and no upright quarters, there is a quadrilateral
region $F$.  It satisfies
    $$
    \begin{array}{lll}
    \vor_0 &< -0.075,\\
    \tau_0 &> 0.176.
    \end{array}
    $$
    \oldlabel{4.6.4}
Break the cluster into two simplices $S=S(y_1,\ldots,y_6)$,
$S'=S(y'_1,y_2,y_3,y_4,y'_5,y'_6)$, by drawing a diagonal of
length $y_4$. Assume that the edge $y'_5\in[2t_0,2\sqrt2]$.  Let
$y_4'$ be the length of the diagonal that crosses $y_4$.
    $$
    \begin{array}{lll}
    \vor_0 &< 2.1327-0.1 y_1 -0.15 y_2 -0.08 y_3 -0.15 y_5\\
            &\qquad -0.15 y_6 - 0.1 y'_1 - 0.17 y'_5 -0.16 y'_6,\\
        &\quad\text{if }\dih(S)<1.9,\ \dih(S')<2.0,\ y_1\in[2,2.2],\
            y_4\ge2\sqrt2,\\
    \vor_0 & < 2.02644 - 0.1 y_1 -0.14 (y_2+y_3)-0.15 (y_5+y_6)
            -0.1 y'_1 - 0.12 (y_5'+y_6'), \\
        &\quad\text{if }y_1\in[2,2.08],\quad y_4\le3.\\
    \vor_0 &+0.419351 \sol < 0.4542 + 0.0238 (y_5+y_6+y_6'),\\
        &\quad\text{if }\ y_4,y_4'\ge2\sqrt2.\\
    %\tag  A.4.7.1
    \end{array}
    $$
    \oldlabel{A.4.7.1}
The inequalities above are verified in smaller pieces:


*)


(* interval verification in partK.cc *)
let I_131574415=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.2)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (vor_0_x x1 x2 x3 x4 x5 x6) <. 
               ( (#1.01) +.  (  (--. (#0.1)) *.  (sqrt x1)) +.  (  (--. (#0.05)) *.  (sqrt x2)) +.  (  (--. (#0.05)) *.  (sqrt x3)) +. 
               (  (--. (#0.15)) *.  (sqrt x5)) +.  (  (--. (#0.15)) *.  (sqrt x6)))) \/ 
            ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.9)))`;;



(* interval verification in partK.cc *)
let I_929773933=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
    
        (square_2t0, x5, (#8.0));
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (vor_0_x x1 x2 x3 x4 x5 x6) <. 
               ( (#1.1227) +.  (  (--. (#0.1)) *.  (sqrt x1)) +.  (  (--. (#0.1)) *.  (sqrt x2)) +.  (  (--. (#0.03)) *.  (sqrt x3)) +. 
               (  (--. (#0.17)) *.  (sqrt x5)) +.  (  (--. (#0.16)) *.  (sqrt x6)))) \/ 
            ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.0)) \/ 
            ( ( (sqrt x2) +.  (sqrt x3)) >.  (#4.67)))`;;



(* interval verification in partK.cc *)
let I_223261160=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.08)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (#9.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <. 
               ( (#1.0159) +.  (  (--. (#0.1)) *.  (sqrt x1)) +.  (  (--. (#0.08)) *.  ( (sqrt x2) +.  (sqrt x3))) +. 
               (  (#0.04) *.  (sqrt x4)) +.  (  (--. (#0.15)) *.  ( (sqrt x5) +.  (sqrt x6)))))`;;



(* interval verification in partK.cc *)
let I_135018647=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (#9.0));
    
        (square_2t0, x5, (#8.0));
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <. 
               ( (#1.01054) +.  (  (--. (#0.1)) *.  (sqrt x1)) +.  (  (--. (#0.06)) *.  ( (sqrt x2) +.  (sqrt x3))) +. 
               (  (--. (#0.04)) *.  (sqrt x4)) +.  (  (--. (#0.12)) *.  ( (sqrt x5) +.  (sqrt x6)))))`;;




(* interval verification in partK.cc *)
let I_559676877=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0);
     ((#4.0), x1', square_2t0);
     (square_2t0, x5', (#8.0));
    
        ((#4.0), x6', square_2t0)
    ]
    (
            ( ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (vor_0_x x1' x2 x3 x4 x5' x6') +. 
               (  (#0.419351) *.  ( (sol_x x1 x2 x3 x4 x5 x6) +.  (sol_x x1' x2 x3 x4 x5' x6')))) <. 
               ( (#0.4542) +.  (  (#0.0238) *.  ( (sqrt x5) +.  (sqrt x6) +.  (sqrt x6'))))) \/ 
            ( (cross_diag_x x1 x2 x3 x4 x5 x6 x1' x5' x6') <.  (  (#2.0) *.  (sqrt (#2.0)))))`;;



(*
 
LOC: 2002 k.c page 52--53
17.28 Group_28
*)

(* interval verification by Ferguson *)
let I_615073260=
  all_forall 
  `
let x6B = x5A in
let x2B = x3A in
let x6C = x5B in
let x2C = x3B in
let x6D = x5C in
let x2D = x3C in
let x6E = x5D in
let x2E = x3D in
let x6A = x5E in
let x2A = x3E in
   (ineq
   [((#4.0), x1, square_2t0);
    ((#4.0), x2A, square_2t0);
    ((#4.0), x3A, square_2t0);
    ((#4.0), x4A, square_2t0);
    ((#4.0), x5A, square_2t0);
    ((#4.0), x6A, square_2t0);
    ((#4.0), x2B, square_2t0);
    ((#4.0), x3B, square_2t0);
    ((#4.0), x4B, square_2t0);
    ((#4.0), x5B, square_2t0);
    ((#4.0), x6B, square_2t0);
    ((#4.0), x2C, square_2t0);
    ((#4.0), x3C, square_2t0);
    ((#4.0), x4C, square_2t0); 
    ((#4.0), x5C, square_2t0);
    ((#4.0), x6C, square_2t0);
    ((#4.0), x2D, square_2t0);
    ((#4.0), x3D, square_2t0);
    ((#4.0), x4D, square_2t0);
    ((#4.0), x5D, square_2t0);
    ((#4.0), x6D, square_2t0);
    ((#4.0), x2E, square_2t0);
    ((#4.0), x3E, square_2t0);
    ((square_2t0), x4E, (square_4t0)); // (* NB *) 
    ((#4.0), x5E, square_2t0);
    ((#4.0), x6E, square_2t0)]
      ((sqrt x2A) + (sqrt x2B) + (sqrt x2C) + (sqrt x2D) + (sqrt x2E) +
       (sqrt x6A) + (sqrt x6B) + (sqrt x6C) + (sqrt x6D) + (sqrt x6E) >. (#20.42)))`;;

(* interval verification by Ferguson *)
let I_844430737=
  all_forall 
  `
let x6B = x5A in
let x2B = x3A in
let x6C = x5B in
let x2C = x3B in
let x6D = x5C in
let x2D = x3C in
let x6E = x5D in
let x2E = x3D in
let x6A = x5E in
let x2A = x3E in
   (ineq
   [((#4.0), x1, square_2t0);
    ((#4.0), x2A, square_2t0);
    ((#4.0), x3A, square_2t0);
    ((#4.0), x4A, square_2t0);
    ((#4.0), x5A, square_2t0);
    ((#4.0), x6A, square_2t0);
    ((#4.0), x2B, square_2t0);
    ((#4.0), x3B, square_2t0);
    ((#4.0), x4B, square_2t0);
    ((#4.0), x5B, square_2t0);
    ((#4.0), x6B, square_2t0);
    ((#4.0), x2C, square_2t0);
    ((#4.0), x3C, square_2t0);
    ((#4.0), x4C, square_2t0); 
    ((#4.0), x5C, square_2t0);
    ((#4.0), x6C, square_2t0);
    ((#4.0), x2D, square_2t0);
    ((#4.0), x3D, square_2t0);
    ((#4.0), x4D, square_2t0);
    ((#4.0), x5D, square_2t0);
    ((#4.0), x6D, square_2t0);
    ((#4.0), x2E, square_2t0);
    ((#4.0), x3E, square_2t0);
    ((#8.0), x4E, (square_4t0)); // (* NB *) 
    ((#4.0), x5E, square_2t0);
    ((#4.0), x6E, square_2t0)]
      ((sqrt x2A) + (sqrt x2B) + (sqrt x2C) + (sqrt x2D) + (sqrt x2E) +
       (sqrt x6A) + (sqrt x6B) + (sqrt x6C) + (sqrt x6D) + (sqrt x6E) >. (#20.76)))`;;



(*
 
LOC: 2002 k.c page 53
17.29 Group_29
*)

(* 

2002 text:

    $$
    \vor_0 < -0.136\quad\text{and }\tau_0 > 0.224,
    %\tag   A.4.12.4
    $$
    \oldlabel{A.4.12.4}
for a combination of anchored simplex $S$ and special simplex
$S'$, with $y_1(S)\in[2.696,2\sqrt2]$,
$y_2(S),y_6(S)\in[2.45,2t_0]$, $y_4(S)\in[2\sqrt2,3.2]$, and with
cross-diagonal at least $2t_0$. This inequality can be verified by
proving the following inequalities in lower dimension. In the
first four $y_1\in[2.696,2\sqrt2]$, $y_2,y_6\in[2.45,2t_0]$,
$y_4\in[2\sqrt2,3.2]$, and $y_4'\ge2t_0$ (the cross-diagonal).


*)


(* interval verification by Ferguson *)
let I_967376139=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
    (
            ( ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (vor_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))) <.  (--. (#0.136))) \/ 
            ( (cross_diag_x x1 x2 x3 x4 x5 x6 (#4.0) (#4.0) (#4.0) ) <.  two_t0))`;;




(* interval verification by Ferguson *)
let I_666869244=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
    (
            ( ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (vor_0_x square_2t0 x2 x3 x4 (#4.0) (#4.0))) <.  (--. (#0.136))) \/ 
            ( (cross_diag_x x1 x2 x3 x4 x5 x6 square_2t0 (#4.0) (#4.0) ) <.  two_t0))`;;




(* interval verification by Ferguson *)
let I_268066802=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
    (
     ( ( (tau_0_x x1 x2 x3 x4 x5 x6) +.  
    (tau_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))) >.  (#0.224)) \/ 
    ( (cross_diag_x x1 x2 x3 x4 x5 x6 (#4.0) (#4.0) (#4.0) ) <.  two_t0))`;;




(* interval verification by Ferguson *)
let I_508108214=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
    (
            ( ( (tau_0_x x1 x2 x3 x4 x5 x6) +.  
   (tau_0_x square_2t0 x2 x3 x4 (#4.0) (#4.0))) >.  (#0.224)) \/ 
            ( (cross_diag_x x1 x2 x3 x4 x5 x6 square_2t0 (#4.0) (#4.0) ) <.  two_t0))`;;




(* interval verification by Ferguson *)
let I_322505397=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        (square_2t0, x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.125)))`;;



(* interval verification by Ferguson *)
let I_736616321=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  (#0.011))`;;




(* interval verification by Ferguson *)
let I_689417023=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        (square_2t0, x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
    ( (tau_0_x x1 x2 x3 x4 x5 x6) >.  (#0.17))`;;



(* interval verification by Ferguson *)
let I_748466752=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (tau_0_x x1 x2 x3 x4 x5 x6) >.  (#0.054))`;;


(*
 
LOC: 2002 k.c page 53
17.30 Group_30
*)

(*

2002 text:

$$\vor_0 < -0.24\text{ and }\tau_0 > 0.346,
    %\tag  {A.4.12.5}
    $$
    \oldlabel{A.4.12.5}
for an anchored simplex $S$ and simplex $S'$ with edge parameters
$(3,2)$ in a hexagonal cluster, with $y_2(S)=y_2(S')$,
$y_3(S)=y_3(S')$, $y_4(S)=y_4(S')$, $y_1(S)\in[2.696,2\sqrt2]$,
$y_4(S)\in[2\sqrt2,3.2]$, $y_2(S),y_6(S)\in[2.45,2t_0]$, and
$$\max(y_5(S'),y_6(S'))\in[2t_0,2\sqrt2],\quad
\min(y_5(S'),y_6(S'))\in[2,2t_0].$$ This breaks into separate
interval calculations for $S$ and $S'$.

This inequality  results from the following four inequalities:

(* interval verification by Ferguson *)
$\vor_0(S) < -0.126$ and $\tau_0(S) > 0.16$ \refno{369386367\dag}

$\vor_0(S') < -0.114$ and $\tau_0(S') >0.186$ (There are two cases
for each, depending on which of $y_5,y_6$ is longer.)
(* interval verification by Ferguson *)
\refno{724943459\dag}

Sun Feb 22 07:47:31 EST 2004: I assume S' is a special below.

*)


let I_369386367_1=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
  (vor_0_x x1 x2 x3 x4 x5 x6 <. (--. (#0.126)))
  `;;

let I_369386367_2=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
  (tau_0_x x1 x2 x3 x4 x5 x6 >. (#0.16))
  `;;

let I_724943459_1=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((square_2t0), x6, (#8.0))
    ]
  (vor_0_x x1 x2 x3 x4 x5 x6 <. (--. (#0.114)))
  `;;

let I_724943459_2=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
     ((square_2t0), x5, (#8.0));
     ((#4.0), x6, square_2t0)
    ]
  (vor_0_x x1 x2 x3 x4 x5 x6 <. (--. (#0.114)))
  `;;

let I_724943459_3=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((square_2t0), x6, (#8.0))
    ]
  (tau_0_x x1 x2 x3 x4 x5 x6 >. (#0.186))
  `;;

let I_724943459_4=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
     ((square_2t0), x5, (#8.0));
     ((#4.0), x6, square_2t0)
    ]
  (tau_0_x x1 x2 x3 x4 x5 x6 >. (#0.186))
  `;;


(*
LOC: 2002 k.c page 53
17.31 Group_31
*)

(* interval verification by Ferguson *)
let I_836331201_1=
 all_forall `ineq
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((square(#2.45)), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     (square_2t0, x5, (#8.0));
     ((#4.0), x6, square_2t0);
     ((#4.0), x7, square_2t0);
     ((#4.0), x8, square_2t0);
     ((#4.0), x9, square_2t0)]
   (((vor_0_x x1 x2 x3 x4 x5 x6) +
    (vor_0_x x7 x2 x3 x4 x8 x9) <. (-- (#0.149)))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 x7 x8 x9 <. (sqrt8)))`;;

let I_836331201_2=
 all_forall `ineq
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((square(#2.45)), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     (square_2t0, x5, (#8.0));
     ((#4.0), x6, square_2t0);
     ((#4.0), x7, square_2t0);
     ((#4.0), x8, square_2t0);
     ((#4.0), x9, square_2t0)]
   (((tau_0_x x1 x2 x3 x4 x5 x6) +
    (tau_0_x x7 x2 x3 x4 x8 x9) >. (#0.281))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 x7 x8 x9 <. (sqrt8)))`;;


(*
 
LOC: 2002 k.c page 54
17.32 Group_32
*)

(* 2002 text:

    $$\vor_0 < -0.254\quad\text{and }\tau_0 > 0.42625,
    %\tag  {A.4.12.9}
    $$
    %\oldlabel{A.4.12.9}
for a combination of anchored simplex $S$ and quadrilateral
cluster $Q$.  It is assumed that $y_1(S)\in[2.696,2\sqrt2]$,
$y_2(S),y_6(S)\in[2.45,2t_0]$. The adjacent quadrilateral
subcluster is assumed to have both diagonals $\ge2\sqrt2$, and
parameters
$$(a_1,b_1,a_2,b_2,a_3,b_3,a_4,b_4),$$
with $b_4\in[2\sqrt2,3.2]$. The verification of this inequality
reduces to separate inequalities for the anchored simplex and
quadrilateral subcluster. For the anchored simplex we use the
bounds $\vor_0(S')<-0.126$, $\tau_0(S')>0.16$ that have already
been established above.  We then show that the quad cluster
satisfies

(* interval verification by Ferguson *)
$\vor_0 < -0.128$ and $\tau_0 > 0.26625$. \refno{327474205\dag}

(* interval verification in partK.cc *)
For this, use deformations to reduce either to the case where the
diagonal is $2\sqrt2$, or to the case where $b_1=b_2=b_3=2$,
$a_2,a_3\in\{2,2t_0\}$.  When the diagonal is $2\sqrt2$, the flat
quarter can be scored by \cite[$\A_{13}$]{part4}:
    $(\vor_0<0.009,\tau_0>0.05925)$.
(There are two cases depending on which direction the diagonal of
length $2\sqrt2$ runs.)



*)


let I_327474205_1=
 all_forall `
let x2 = (#4.0) in
let x7 = (#4.0) in
let x8 = (#4.0) in
let x9 = (#4.0) in
  (ineq
    [     
     ((square(#2.45)), x1, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#8.0), x5, (square (#3.2)));
     ((#4.0), x6, square_2t0)]
   (((vor_0_x x1 x2 x3 x4 x5 x6) +
    (vor_0_x x7 x2 x3 x4 x8 x9) <. (-- (#0.128)))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 x7 x8 x9 <. (sqrt8))))`;;

let I_327474205_2=
 all_forall `
let x2 = (square_2t0) in
let x7 = (#4.0) in
let x8 = (#4.0) in
let x9 = (#4.0) in
  (ineq
    [     
     ((square(#2.45)), x1, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#8.0), x5, (square (#3.2)));
     ((#4.0), x6, square_2t0)]
   (((vor_0_x x1 x2 x3 x4 x5 x6) +
    (vor_0_x x7 x2 x3 x4 x8 x9) <. (-- (#0.128)))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 x7 x8 x9 <. (sqrt8))))`;;

let I_327474205_3=
 all_forall `
let x2 = (square_2t0) in
let x7 = (square_2t0) in
let x8 = (#4.0) in
let x9 = (#4.0) in
  (ineq
    [     
     ((square(#2.45)), x1, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#8.0), x5, (square (#3.2)));
     ((#4.0), x6, square_2t0)]
   (((vor_0_x x1 x2 x3 x4 x5 x6) +
    (vor_0_x x7 x2 x3 x4 x8 x9) <. (-- (#0.128)))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 x7 x8 x9
       <. (sqrt8))))`;;

let I_327474205_4=
 all_forall `
let x2 = (#4.0) in
let x7 = (square_2t0) in
let x8 = (#4.0) in
let x9 = (#4.0) in
  (ineq
    [     
     ((square(#2.45)), x1, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#8.0), x5, (square (#3.2)));
     ((#4.0), x6, square_2t0)]
   (((vor_0_x x1 x2 x3 x4 x5 x6) +
    (vor_0_x x7 x2 x3 x4 x8 x9) <. (-- (#0.128)))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 x7 x8 x9
       <. (sqrt8))))`;;

let I_327474205_5=
 all_forall `ineq
    [     
     ((square(#2.45)), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x5, (square (#3.2)));
     ((#4.0), x6, square_2t0)]
   ((vor_0_x x1 x2 x3 (#8.0) x5 x6) <. (-- (#0.128)) - (#0.009))`;;

let I_327474205_6=
 all_forall `ineq
    [     
     ((square(#2.45)), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#8.0), x5, (square (#3.2)))]
   ((vor_0_x x1 x2 x3 x4 x5 (#8.0)) <. (-- (#0.128)) - (#0.009))`;;



let I_327474205_1=
 all_forall `
let x2 = (#4.0) in
let x7 = (#4.0) in
let x8 = (#4.0) in
let x9 = (#4.0) in
  (ineq
    [     
     ((square(#2.45)), x1, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#8.0), x5, (square (#3.2)));
     ((#4.0), x6, square_2t0)]
   (((tau_0_x x1 x2 x3 x4 x5 x6) +
    (tau_0_x x7 x2 x3 x4 x8 x9) >. (#0.26625))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 x7 x8 x9
       <. (sqrt8))))`;;

let I_327474205_2=
 all_forall `
let x2 = (square_2t0) in
let x7 = (#4.0) in
let x8 = (#4.0) in
let x9 = (#4.0) in
  (ineq
    [     
     ((square(#2.45)), x1, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#8.0), x5, (square (#3.2)));
     ((#4.0), x6, square_2t0)]
   (((tau_0_x x1 x2 x3 x4 x5 x6) +
    (tau_0_x x7 x2 x3 x4 x8 x9) >. (#0.26625))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 x7 x8 x9
       <. (sqrt8))))`;;

let I_327474205_3=
 all_forall `
let x2 = (square_2t0) in
let x7 = (square_2t0) in
let x8 = (#4.0) in
let x9 = (#4.0) in
  (ineq
    [     
     ((square(#2.45)), x1, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#8.0), x5, (square (#3.2)));
     ((#4.0), x6, square_2t0)]
   (((tau_0_x x1 x2 x3 x4 x5 x6) +
    (tau_0_x x7 x2 x3 x4 x8 x9) >. (#0.26625))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 x7 x8 x9
       <. (sqrt8))))`;;

let I_327474205_4=
 all_forall `
let x2 = (#4.0) in
let x7 = (square_2t0) in
let x8 = (#4.0) in
let x9 = (#4.0) in
  (ineq
    [     
     ((square(#2.45)), x1, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, square_4t0);
     ((#8.0), x5, (square (#3.2)));
     ((#4.0), x6, square_2t0)]
   (((tau_0_x x1 x2 x3 x4 x5 x6) +
    (tau_0_x x7 x2 x3 x4 x8 x9) >. (#0.26625))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 x7 x8 x9
       <. (sqrt8))))`;;

let I_327474205_5=
 all_forall `ineq
    [     
     ((square(#2.45)), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x5, (square (#3.2)));
     ((#4.0), x6, square_2t0)]
   ((tau_0_x x1 x2 x3 (#8.0) x5 x6) >. (#0.26625) - (#0.05925))`;;

let I_327474205_6=
 all_forall `ineq
    [     
     ((square(#2.45)), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#8.0), x5, (square (#3.2)))]
   ((tau_0_x x1 x2 x3 x4 x5 (#8.0)) >. (#0.26625) - (#0.05925))`;;


(*
LOC: 2002 k.c page 55--
18. Appendix  Hexagonal Inequalities
*)

(*
LOC: 2002 k.c page 55--56
SKIP 18.1.  This has been moved to the main part of the
text.  It is more mathematical argument than interval arithmetic.
*)

(*
LOC: 2002 k.c page 56--59
SKIP first part of 18.2.
This is a mathematical proof.  It has been moved into the main
body of text.
*)

(*
LOC: 2002 k.c page 56--59
Last part of 18.2.
*)


(* interval verification by Ferguson *)
let I_725257062=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#3.2)), x4, (square (#3.2)));
    
        ((#8.0), x5, (square (#3.2)));
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#0.212)) +.  (--. (#0.0461)) +.  (#0.137)))`;;



(* interval verification by Ferguson *)
let I_977272202=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#3.2)), x4, (square (#3.2)));
    
        ((#8.0), x5, (square (#3.2)));
     ((#4.0), x6, square_2t0)
    ]
    ( (tau_0_x x1 x2 x3 x4 x5 x6) >.  ( (#0.54525) +.  (--. (#0.0)) +.  (--. (#0.31))))`;;



(*
LOC: 2002 k.c page 59
Group_18.3
*)

(*

let CKC_377409251= (* 18.3 : app:p1b *)
let CKC_586214007= (* 18.4 : app:p1c *)
let CKC_89384104= (* 18.5 : app:p1d *)
let CKC_859726639= (* kc group 18.6 : app:p1e  *)
let CKC_673399623= (* kc group 18.7 : app:p2a  *)
let CKC_297256991= (* kc group 18.8 : app:p2b *)
let CKC_861511432= (* kc group 18.9 : app:p2c *)
let CKC_746445726= (* kc group 18.10 : app:p2d *)
let CKC_897046482= (* kc group 18.11 : app:p2e *)
let CKC_928952883= (* kc group 18.12 : app:p2f *)
let CKC_673800906= (* kc group 18.13 : app:p2g *)
let CKC_315678695= (* kc group 18.14 : app:p3  *)
let CKC_468742136= (* kc group 18.15 : app:p8 *)
let CKC_938091791= (* kc group 18.16 : app:p11 *)

*)

(* interval verification by Ferguson *)
let I_583626763_GEN=
   `(\ a2 a3 a4. 
 (ineq
[
((square(#3.2)), x, (#16.0));
((square(#3.2)), x', square_4t0)
]
   (((vor_0_x (#4.0) a2 a3 (#4.0) x (#4.0))+.
    (vor_0_x (#4.0) a3 a4 (#4.0) x' x) +.
      (vor_0_x (#4.0) a4 (#4.0) (#4.0) (#8.0) x') + (#0.0461)
    <. (--(#0.212)))
   \/
  (delta_x (#4.0) a2 a3 (#4.0) x (#4.0) <. (#0.0)) \/
  (delta_x (#4.0) a3 a4 (#4.0) x' x  <. (#0.0)) \/
  (delta_x (#4.0) a4 (#4.0) (#4.0) (#8.0) x'<. (#0.0)))))`;;

(* XXX false *)
(* interval verification by Ferguson *)
let I_583626763_1= 
  all_forall 
  (list_mk_comb(I_583626763_GEN,[`#4.0`;`#4.0`;`#4.0`]));;

(* XXX false *)
(* interval verification by Ferguson *)
let I_583626763_2= 
  all_forall 
  (list_mk_comb(I_583626763_GEN,[`#4.0`;`#4.0`;`square_2t0`]));;

(* XXX false *)
(* interval verification by Ferguson *)
let I_583626763_3= 
  all_forall 
  (list_mk_comb(I_583626763_GEN,[`#4.0`;`square_2t0`;`#4.0`]));;

(* XXX false *)
(* interval verification by Ferguson *)
let I_583626763_4= 
  all_forall 
  (list_mk_comb(I_583626763_GEN,[`#4.0`;`square_2t0`;`square_2t0`]));;

(* XXX Infeasible *)
(* interval verification by Ferguson *)
let I_583626763_5= 
  all_forall 
  (list_mk_comb(I_583626763_GEN,[`square_2t0`;`#4.0`;`#4.0`]));;

(* XXX Infeasible *)
(* interval verification by Ferguson *)
let I_583626763_6= 
  all_forall 
  (list_mk_comb(I_583626763_GEN,[`square_2t0`;`#4.0`;`square_2t0`]));;

(* XXX false *)
(* interval verification by Ferguson *)
let I_583626763_7= 
  all_forall 
  (list_mk_comb(I_583626763_GEN,[`square_2t0`;`square_2t0`;`#4.0`]));;

(* XXX false *)
(* interval verification by Ferguson *)
let I_583626763_8= 
  all_forall 
  (list_mk_comb(I_583626763_GEN,[`square_2t0`;`square_2t0`;`square_2t0`]));;


(* XXX all false or infeasible *)
(* interval verification by Ferguson *)
let I_390951718_GEN=
   `(\ a2 a3 a4. 
 (ineq
[
((square(#3.2)), x, (#16.0));
((square(#3.2)), x', square_4t0)
]
   (((tau_0_x (#4.0) a2 a3 (#4.0) x (#4.0))+.
    (tau_0_x (#4.0) a3 a4 (#4.0) x' x) +.
      (tau_0_x (#4.0) a4 (#4.0) (#4.0) (#8.0) x') 
    >. (#0.54525))
   \/
  (delta_x (#4.0) a2 a3 (#4.0) x (#4.0) <. (#0.0)) \/
  (delta_x (#4.0) a3 a4 (#4.0) x' x  <. (#0.0)) \/
  (delta_x (#4.0) a4 (#4.0) (#4.0) (#8.0) x'<. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_390951718_1= 
  all_forall 
  (list_mk_comb(I_390951718_GEN,[`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_390951718_2= 
  all_forall 
  (list_mk_comb(I_390951718_GEN,[`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_390951718_3= 
  all_forall 
  (list_mk_comb(I_390951718_GEN,[`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_390951718_4= 
  all_forall 
  (list_mk_comb(I_390951718_GEN,[`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_390951718_5= 
  all_forall 
  (list_mk_comb(I_390951718_GEN,[`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_390951718_6= 
  all_forall 
  (list_mk_comb(I_390951718_GEN,[`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_390951718_7= 
  all_forall 
  (list_mk_comb(I_390951718_GEN,[`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_390951718_8= 
  all_forall 
  (list_mk_comb(I_390951718_GEN,[`square_2t0`;`square_2t0`;`square_2t0`]));;

let CKC_377409251= (* 18.3 *)
  list_mk_conj
  [I_390951718_8; I_390951718_7; I_390951718_6; I_390951718_5; 
   I_390951718_4; I_390951718_3; I_390951718_2; I_390951718_1; 
   I_583626763_8; I_583626763_7; I_583626763_6; I_583626763_5; 
   I_583626763_4; I_583626763_3; I_583626763_2; I_583626763_1;   ];;

(*
LOC: 2002 k.c page 59
Group_18.4
*)

(* interval verification by Ferguson *)
let I_621852152_GEN=
   `(\ a1 a2 a3 a4 a5. 
 (ineq
[
((#8.0),b5,(square (#3.2)));
((square(#3.2)), x, (square_4t0));
((square(#3.2)), x', (square_4t0))
]
   (((vor_0_x a3 a2 a1 (#4.0)  x (#4.0)) +.
    (vor_0_x a3 a1 a5 b5 x' x) +.
      (vor_0_x a3 a5 a4 (#4.0) (#4.0) x') 
   + (#0.0461) <. (--(#0.212)))
   \/
  (delta_x a3 a2 a1 (#4.0)  x (#4.0) <. (#0.0)) \/
  (delta_x a3 a1 a5 b5 x' x <. (#0.0)) \/
  (delta_x a3 a5 a4 (#4.0) (#4.0) x' <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_621852152_1=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_2=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* XXX infeasible *)
(* interval verification by Ferguson *)
let I_621852152_3=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_4=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_621852152_5=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_6=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_621852152_7=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_8=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* XXX infeasible *)
(* interval verification by Ferguson *)
let I_621852152_9=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* XXX infeasible *)
(* interval verification by Ferguson *)
let I_621852152_10=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* XXX infeasible *)
(* interval verification by Ferguson *)
let I_621852152_11=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* XXX infeasible *)
(* interval verification by Ferguson *)
let I_621852152_12=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_621852152_13=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_14=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_621852152_15=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_16=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_621852152_17=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_18=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* XXX infeasible *)
(* interval verification by Ferguson *)
let I_621852152_19=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_20=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_621852152_21=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_22=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_621852152_23=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_24=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_621852152_25=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_26=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* XXX infeasible *)
(* interval verification by Ferguson *)
let I_621852152_27=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_28=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_621852152_29=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_30=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_621852152_31=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_621852152_32=
  all_forall 
  (list_mk_comb(I_621852152_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
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
let I_207203174_9=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_10=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_207203174_11=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
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
let I_207203174_19=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_207203174_20=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_207203174_21=
  all_forall 
  (list_mk_comb(I_207203174_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
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


let CKC_586214007= (* 18.4 *)
  list_mk_conj[
  I_207203174_32;I_207203174_31;I_207203174_30;I_207203174_29;
  I_207203174_28;I_207203174_27;I_207203174_26;I_207203174_25;
  I_207203174_24;I_207203174_23;I_207203174_22;I_207203174_21;
  I_207203174_20;I_207203174_19;I_207203174_18;I_207203174_17;
  I_207203174_16;I_207203174_15;I_207203174_14;I_207203174_13;
  I_207203174_12;I_207203174_11;I_207203174_10;I_207203174_9;
  I_207203174_8;I_207203174_7;I_207203174_6;I_207203174_5;
  I_207203174_4;I_207203174_3;I_207203174_2;I_207203174_1;
  I_621852152_32;I_621852152_31;I_621852152_30;I_621852152_29;
  I_621852152_28;I_621852152_27;I_621852152_26;I_621852152_25;
  I_621852152_24;I_621852152_23;I_621852152_22;I_621852152_21;
  I_621852152_20;I_621852152_19;I_621852152_18;I_621852152_17;
  I_621852152_16;I_621852152_15;I_621852152_14;I_621852152_13;
  I_621852152_12;I_621852152_11;I_621852152_10;I_621852152_9;
  I_621852152_8;I_621852152_7;I_621852152_6;I_621852152_5;
  I_621852152_4;I_621852152_3;I_621852152_2;I_621852152_1;  ];;


(*
LOC: 2002 k.c page 59
Group_18.5
*)


(* interval verification by Ferguson *)
let I_368258024_GEN=
   `(\ a1 a2 a3 a4 a5 a6. 
 (ineq
[
((#8.0) , xd3, (square(#3.2)));
((square(#3.2)), xd4 , square_4t0);
((#8.0) , xd5,(square(#3.2)))
]
   (((vor_0_x a1 a2 a3 (#4.0) xd3  (#4.0)) +.
    (vor_0_x a1 a3 a4 (#4.0) xd4 xd3) +.
      (vor_0_x a1 a4 a5 (#4.0) xd5 xd4) +. 
      (vor_0_x a1 a5 a6 (#4.0) (#4.0) xd5) 
   <. (--(#0.212)))
   \/
  (cross_diag_x a3 a1 a4    xd4 (#4.0) xd3   a5 (#4.0) xd5 
        >. (sqrt(#8.0))) \/
  (delta_x a1 a2 a3 (#4.0) xd3  (#4.0) <. (#0.0)) \/
  (delta_x a1 a3 a4 (#4.0) xd4 xd3 <. (#0.0)) \/
  (delta_x a1 a4 a5 (#4.0) xd5 xd4 <. (#0.0)) \/
  (delta_x a1 a5 a6 (#4.0) (#4.0) xd5 <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_368258024_1=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_2=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_3=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_4=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_5=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_6=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_7=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_8=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
let I_368258024_9=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_10=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_11=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_12=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_13=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_14=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_15=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_16=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_17=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_18=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_19=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_20=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_21=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_22=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_23=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_24=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_25=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_26=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_27=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_28=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_29=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_30=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_31=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_32=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_33=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_34=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_35=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_36=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_37=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_38=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_39=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_40=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
let I_368258024_41=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_42=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_43=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_44=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_45=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_46=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_47=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_48=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_49=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_50=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_51=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_52=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_53=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_54=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_55=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_56=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_57=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_58=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_59=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_60=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_61=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_62=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_368258024_63=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_368258024_64=
  all_forall 
  (list_mk_comb(I_368258024_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
let I_564618342_GEN=
   `(\ a1 a2 a3 a4 a5 a6. 
 (ineq
[
((#8.0) , xd3, (square(#3.2)));
((square(#3.2)), xd4 , square_4t0);
((#8.0) , xd5,(square(#3.2)))
]
   (((tau_0_x a1 a2 a3 (#4.0) xd3  (#4.0)) +.
    (tau_0_x a1 a3 a4 (#4.0) xd4 xd3) +.
      (tau_0_x a1 a4 a5 (#4.0) xd5 xd4) +. 
      (tau_0_x a1 a5 a6 (#4.0) (#4.0) xd5) 
   >. (#0.54525))
   \/
  (cross_diag_x a3 a1 a4    xd4 (#4.0) xd3   a5 (#4.0) xd5 
        >. (sqrt(#8.0))) \/
  (delta_x a1 a2 a3 (#4.0) xd3  (#4.0) <. (#0.0)) \/
  (delta_x a1 a3 a4 (#4.0) xd4 xd3 <. (#0.0)) \/
  (delta_x a1 a4 a5 (#4.0) xd5 xd4 <. (#0.0)) \/
  (delta_x a1 a5 a6 (#4.0) (#4.0) xd5 <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_564618342_1=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_2=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_3=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_4=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_5=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_6=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_7=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_8=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
let I_564618342_9=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_10=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_11=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_12=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_13=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_14=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_15=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_16=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_17=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_18=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_19=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_20=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_21=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_22=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_23=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_24=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_25=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_26=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_27=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_28=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_29=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_30=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_31=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_32=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_33=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_34=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_35=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_36=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_37=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_38=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_39=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_40=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
let I_564618342_41=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_42=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_43=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_44=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_45=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_46=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_47=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_48=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_49=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_50=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_51=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_52=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_53=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_54=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_55=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_56=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_57=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_58=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_59=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_60=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_61=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_62=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_564618342_63=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_564618342_64=
  all_forall 
  (list_mk_comb(I_564618342_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

let CKC_89384104= (* 18.5 *)
 list_mk_conj[
  I_564618342_64;I_564618342_63;I_564618342_62;I_564618342_61;
  I_564618342_60;I_564618342_59;I_564618342_58;I_564618342_57;
  I_564618342_56;I_564618342_55;I_564618342_54;I_564618342_53;
  I_564618342_52;I_564618342_51;I_564618342_50;I_564618342_49;
  I_564618342_48;I_564618342_47;I_564618342_46;I_564618342_45;
  I_564618342_44;I_564618342_43;I_564618342_42;I_564618342_41;
  I_564618342_40;I_564618342_39;I_564618342_38;I_564618342_37;
  I_564618342_36;I_564618342_35;I_564618342_34;I_564618342_33;
  I_564618342_32;I_564618342_31;I_564618342_30;I_564618342_29;I_564618342_28;I_564618342_27;
  I_564618342_26;I_564618342_25;I_564618342_24;I_564618342_23;I_564618342_22;I_564618342_21;
  I_564618342_20;I_564618342_19;I_564618342_18;I_564618342_17;I_564618342_16;I_564618342_15;
  I_564618342_14;I_564618342_13;I_564618342_12;I_564618342_11;I_564618342_10;I_564618342_9;
  I_564618342_8;I_564618342_7;I_564618342_6;I_564618342_5;I_564618342_4;I_564618342_3;I_564618342_2;I_564618342_1;
  I_368258024_64;I_368258024_63;I_368258024_62;I_368258024_61;I_368258024_60;I_368258024_59;
  I_368258024_58;I_368258024_57;I_368258024_56;I_368258024_55;I_368258024_54;I_368258024_53;
  I_368258024_52;I_368258024_51;I_368258024_50;I_368258024_49;I_368258024_48;I_368258024_47;I_368258024_46;
  I_368258024_45;I_368258024_44;I_368258024_43;I_368258024_42;I_368258024_41;I_368258024_40;I_368258024_39;
  I_368258024_38;I_368258024_37;I_368258024_36;I_368258024_35;I_368258024_34;I_368258024_33;I_368258024_32;
  I_368258024_31;I_368258024_30;I_368258024_29;I_368258024_28;I_368258024_27;I_368258024_26;I_368258024_25;
  I_368258024_24;I_368258024_23;I_368258024_22;I_368258024_21;I_368258024_20;I_368258024_19;I_368258024_18;
  I_368258024_17;I_368258024_16;I_368258024_15;I_368258024_14;I_368258024_13;I_368258024_12;I_368258024_11;
  I_368258024_10;I_368258024_9;I_368258024_8;I_368258024_7;I_368258024_6;I_368258024_5;I_368258024_4;
  I_368258024_3;I_368258024_2;I_368258024_1;  ];;


(*
LOC: 2002 k.c page 59
Group_18.6
*)


(* interval verification by Ferguson *)
let I_498774382_GEN= 
   `(\ a1 a2 a3 a4 a5 a6. 
 (ineq
[
((#8.0) , x, (square(#3.2)));
((#8.0) , x'', (square(#3.2)));
((square(#3.2)), x' , (square(#3.78)))
]
   (((vor_0_x a1 a2 a6 x (#4.0) (#4.0) ) +
    (vor_0_x a2 a6 a5 (#4.0) x' x) +
      (vor_0_x a2 a3 a5 x'' x' (#4.0) ) +
      (vor_0_x a3 a4 a5 (#4.0) x'' (#4.0) ) 
   <. (--(#0.212)))
   \/
  (cross_diag_x a3 a2 a5 x' x'' (#4.0) a6 (#4.0) x
        >. (square(#3.2))) \/
  (delta_x a1 a2 a6 x (#4.0) (#4.0) <. (#0.0)) \/
  (delta_x a2 a6 a5 (#4.0) x' x <. (#0.0)) \/
  (delta_x a2 a3 a5 x'' x' (#4.0) <. (#0.0)) \/
  (delta_x a3 a4 a5 (#4.0) x'' (#4.0) <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_498774382_1=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_2=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_3=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_4=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_5=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_6=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_7=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_8=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
let I_498774382_9=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_10=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_11=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_12=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_13=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_14=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_15=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_16=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_17=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_18=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_19=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_20=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_21=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_22=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_23=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_24=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_25=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_26=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_27=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_28=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_29=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_30=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_31=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_32=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_33=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_34=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_35=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_36=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_37=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_38=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_39=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_40=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
let I_498774382_41=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_42=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_43=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_44=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_45=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_46=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_47=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_48=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_49=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_50=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_51=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_52=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_53=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_54=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_55=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_56=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_57=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_58=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_59=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_60=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_61=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_62=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_498774382_63=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_498774382_64=
  all_forall 
  (list_mk_comb(I_498774382_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
let I_544865225_GEN= 
   `(\ a1 a2 a3 a4 a5 a6. 
 (ineq
[
((#8.0) , x, (square(#3.2)));
((#8.0) , x'', (square(#3.2)));
((square(#3.2)), x' , (square(#3.78)))
]
   (((tau_0_x a1 a2 a6 x (#4.0) (#4.0) ) +
    (tau_0_x a2 a6 a5 (#4.0) x' x) +
      (tau_0_x a2 a3 a5 x'' x' (#4.0) ) +
      (tau_0_x a3 a4 a5 (#4.0) x'' (#4.0) ) 
   >. (#0.54525))
   \/
  (cross_diag_x a3 a2 a5 x' x'' (#4.0) a6 (#4.0) x
        >. (square(#3.2))) \/
  (delta_x a1 a2 a6 x (#4.0) (#4.0) <. (#0.0)) \/
  (delta_x a2 a6 a5 (#4.0) x' x <. (#0.0)) \/
  (delta_x a2 a3 a5 x'' x' (#4.0) <. (#0.0)) \/
  (delta_x a3 a4 a5 (#4.0) x'' (#4.0) <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_544865225_1=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_2=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_3=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_4=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_5=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_6=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_7=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_8=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
let I_544865225_9=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_10=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_11=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_12=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_13=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_14=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_15=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_16=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_17=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_18=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_19=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_20=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_21=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_22=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_23=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_24=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_25=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_26=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_27=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_28=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_29=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_30=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_31=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_32=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_33=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_34=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_35=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_36=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_37=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_38=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_39=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_40=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
let I_544865225_41=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_42=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_43=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_44=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_45=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_46=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_47=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_48=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_49=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_50=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_51=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_52=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_53=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_54=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_55=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_56=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_57=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_58=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_59=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_60=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_61=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_62=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_544865225_63=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_544865225_64=
  all_forall 
  (list_mk_comb(I_544865225_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

let CKC_859726639= list_mk_conj 
  [I_544865225_64;I_544865225_63;I_544865225_62;I_544865225_61;I_544865225_60;I_544865225_59;
   I_544865225_58;I_544865225_57;I_544865225_56;I_544865225_55;I_544865225_54;I_544865225_53;
   I_544865225_52;I_544865225_51;I_544865225_50;I_544865225_49;I_544865225_48;I_544865225_47;
   I_544865225_46;I_544865225_45;I_544865225_44;I_544865225_43;I_544865225_42;I_544865225_41;
   I_544865225_40;I_544865225_39;I_544865225_38;I_544865225_37;I_544865225_36;I_544865225_35;
   I_544865225_34;I_544865225_33;I_544865225_32;I_544865225_31;I_544865225_30;I_544865225_29;
   I_544865225_28;I_544865225_27;I_544865225_26;I_544865225_25;I_544865225_24;I_544865225_23;
   I_544865225_22;I_544865225_21;I_544865225_20;I_544865225_19;I_544865225_18;I_544865225_17;
   I_544865225_16;I_544865225_15;I_544865225_14;I_544865225_13;I_544865225_12;I_544865225_11;
   I_544865225_10;I_544865225_9;I_544865225_8;I_544865225_7;I_544865225_6;I_544865225_5;I_544865225_4;
   I_544865225_3;I_544865225_2;I_544865225_1; I_498774382_64;I_498774382_63;I_498774382_62;I_498774382_61;
   I_498774382_60;I_498774382_59;I_498774382_58;I_498774382_57;I_498774382_56;I_498774382_55;I_498774382_54;
   I_498774382_53;I_498774382_52;I_498774382_51;I_498774382_50;I_498774382_49;I_498774382_48;I_498774382_47;
   I_498774382_46;I_498774382_45;I_498774382_44;I_498774382_43;I_498774382_42;I_498774382_41;I_498774382_40;
   I_498774382_39;I_498774382_38;I_498774382_37;I_498774382_36;I_498774382_35;I_498774382_34;I_498774382_33;
   I_498774382_32;I_498774382_31;I_498774382_30;I_498774382_29;I_498774382_28;I_498774382_27;I_498774382_26;
   I_498774382_25;I_498774382_24;I_498774382_23;I_498774382_22;I_498774382_21;I_498774382_20;I_498774382_19;
   I_498774382_18;I_498774382_17;I_498774382_16;I_498774382_15;I_498774382_14;I_498774382_13;I_498774382_12;
   I_498774382_11;I_498774382_10;I_498774382_9;I_498774382_8;I_498774382_7;I_498774382_6;I_498774382_5;
   I_498774382_4;I_498774382_3;I_498774382_2;I_498774382_1; ];; (* kc group 18.6  *)


(*
LOC: 2002 k.c page 59
Group_18.7
*)


(* interval verification by Ferguson *)
let I_234734606=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0) , x4, (#8.0));
     ((#8.0), x5, (square(#3.2)));
     ((square_2t0), x6, (#8.0))
    ]
    (
        (  (vor_0_x x1 x2 x3 x4 x5 x6 ) <. (--(#0.221))-(&.2)*(#0.009)))` ;;


(* interval verification by Ferguson *)
let I_791682321=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0) , x4, (#8.0));
     ((#8.0), x5, (square(#3.2)));
     ((square_2t0), x6, (#8.0))
    ]
    (
        (  (tau_0_x x1 x2 x3 x4 x5 x6 ) <. (#0.486)-(&.2)*(#0.05925)))`;;

let CKC_673399623= list_mk_conj [I_791682321;I_234734606;  ];; (* kc group 18.7  *)

(*
LOC: 2002 k.c page 59
 Group_18.8
*)

(* interval verification by Ferguson *)
let I_995351614_GEN= 
   `(\ a2 a3 a4 . 
 (ineq
[
((#4.0) , a1, square_2t0);
((#8.0) , x, (square(#3.2)));
((#8.0) , b1, (square(#3.2)))
]
   ((((vor_0_x a1 a2 a4 x square_2t0 b1) +
    (vor_0_x a3 a2 a4 x (#4.0) (#4.0) )
   <. (--(#0.221))-(#0.009)))
   \/
  (cross_diag_x a1 a2 a4 x square_2t0 b1 a3 (#4.0) (#4.0) 
        <. (square(#3.2))) \/
  (delta_x a1 a2 a4 x square_2t0 b1 <. (#0.0)) \/
  (delta_x a3 a2 a4 x (#4.0) (#4.0) <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_995351614_1=
  all_forall 
  (list_mk_comb(I_995351614_GEN,[`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_995351614_2=
  all_forall 
  (list_mk_comb(I_995351614_GEN,[`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_995351614_3=
  all_forall 
  (list_mk_comb(I_995351614_GEN,[`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_995351614_4=
  all_forall 
  (list_mk_comb(I_995351614_GEN,[`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_995351614_5=
  all_forall 
  (list_mk_comb(I_995351614_GEN,[`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_995351614_6=
  all_forall 
  (list_mk_comb(I_995351614_GEN,[`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_995351614_7=
  all_forall 
  (list_mk_comb(I_995351614_GEN,[`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_995351614_8=
  all_forall 
  (list_mk_comb(I_995351614_GEN,[`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
let I_321843503_GEN= 
   `(\ a2 a3 a4 . 
 (ineq
[
((#4.0) , a1, square_2t0);
((#8.0) , x, (square(#3.2)));
((#8.0) , b1, (square(#3.2)))
]
   ((((tau_0_x a1 a2 a4 x square_2t0 b1) +
    (tau_0_x a3 a2 a4 x (#4.0) (#4.0) )
   >. (#0.486)-(#0.0595)))
   \/
  (cross_diag_x a1 a2 a4 x square_2t0 b1 a3 (#4.0) (#4.0) 
        <. (square(#3.2))) \/
  (delta_x a1 a2 a4 x square_2t0 b1 <. (#0.0)) \/
  (delta_x a3 a2 a4 x (#4.0) (#4.0) <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_321843503_1=
  all_forall 
  (list_mk_comb(I_321843503_GEN,[`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_321843503_2=
  all_forall 
  (list_mk_comb(I_321843503_GEN,[`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_321843503_3=
  all_forall 
  (list_mk_comb(I_321843503_GEN,[`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_321843503_4=
  all_forall 
  (list_mk_comb(I_321843503_GEN,[`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_321843503_5=
  all_forall 
  (list_mk_comb(I_321843503_GEN,[`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_321843503_6=
  all_forall 
  (list_mk_comb(I_321843503_GEN,[`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_321843503_7=
  all_forall 
  (list_mk_comb(I_321843503_GEN,[`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_321843503_8=
  all_forall 
  (list_mk_comb(I_321843503_GEN,[`square_2t0`;`square_2t0`;`square_2t0`]));;

let CKC_297256991= list_mk_conj [I_321843503_8;I_321843503_7;I_321843503_6;I_321843503_5;
  I_321843503_4;I_321843503_3;I_321843503_2;I_321843503_1; I_995351614_8;
  I_995351614_7;I_995351614_6;I_995351614_5;I_995351614_4;I_995351614_3;
  I_995351614_2;I_995351614_1; ];; (* kc group 18.8  *)

(*
LOC: 2002 k.c page 59--60
Group_18.9
*)

(* interval verification by Ferguson *)
let I_354217730=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0) , x4, (#4.0));
     ((#8.0), x5, (square(#3.2)));
     ((square(#3.2)), x6, (square(#3.47)))
    ]
    (
        (  (vor_0_x x1 x2 x3 x4 x5 x6 ) <. (--(#0.19))-((sqrt x5)-(sqrt2))*(#0.14)))`;;


(* interval verification in partK.cc, possibly also in Ferguson *)
let I_595674181=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0) , x4, (#4.0));
     ((#8.0), x5, (square(#3.2)));
     ((square(#3.2)), x6, (square(#3.23)))
    ]
    (
        (  (tau_0_x x1 x2 x3 x4 x5 x6 ) >. (#0.281)))`;;


(* interval verification by Ferguson *)
let I_547486831=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0) , x4, (#4.0));
     (square_2t0, x5, square_2t0);
     ((square(#3.2)), x6, (square(#3.2)))
    ]
    (
        (  (vor_0_x x1 x2 x3 x4 x5 x6 ) <. (--(#0.11))))`;;

(* interval verification by Ferguson *)
let I_683897354=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0) , x4, (#4.0));
     (square_2t0, x5, square_2t0);
     ((square(#3.2)), x6, (square(#3.2)))
    ]
    (
        (  (tau_0_x x1 x2 x3 x4 x5 x6 ) >. ((#0.205))))`;;

(* interval verification by Ferguson *)
let I_938003786=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0) , x4, (#4.0));
     ((#8.0) , x5, (square(#3.2)));
     ((#4.0) , x6, (#4.0) )
    ]
    (
        (  (vor_0_x x1 x2 x3 x4 x5 x6 ) <. ((#0.009)-((sqrt x5)-(sqrt8))*(#0.14))))`;;

let CKC_861511432= list_mk_conj[I_938003786;I_683897354;I_547486831;
  I_595674181;I_354217730;  ];; (* kc group 18.9  *)

(*
LOC: 2002 k.c page 60
 Group_18.10
*)


(* interval verification by Ferguson *)
let I_109046923_GEN= 
   `(\ a1 a2 a3 a4 . 
 (ineq
[
((square ( # 3.2)) , x, (square_4t0))
]
   (((vor_0_x a1 a2 a4 x square_2t0 (#4.0) )+
    (vor_0_x a3 a2 a4 x (#4.0) (#8.0) ) 
   <. (--(#0.221))-(#0.0461))
   \/
  (cross_diag_x a1 a2 a4 x square_2t0 (#4.0) a3 (#4.0) (#8.0) 
        >. (square(#3.2))) \/
  (delta_x a1 a2 a4 x square_2t0 (#4.0) <. (#0.0)) \/
  (delta_x a3 a2 a4 x (#4.0) (#8.0) <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_109046923_1=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_109046923_2=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_109046923_3=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_109046923_4=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_109046923_5=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_109046923_6=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_109046923_7=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_109046923_8=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_109046923_9=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_109046923_10=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_109046923_11=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_109046923_12=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_109046923_13=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_109046923_14=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_109046923_15=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_109046923_16=
  all_forall 
  (list_mk_comb(I_109046923_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;



(* interval verification by Ferguson *)
let I_642590101_GEN= 
   `(\ a1 a2 a3 a4 . 
 (ineq
[
((square ( # 3.2)) , x, (square_4t0))
]
   (((tau_0_x a1 a2 a4 x square_2t0 (#4.0) )+
    (tau_0_x a3 a2 a4 x (#4.0) (#8.0) ) 
   >. (#0.486))
   \/
  (cross_diag_x a1 a2 a4 x square_2t0 (#4.0) a3 (#4.0) (#8.0) 
        >. (square(#3.2))) \/
  (delta_x a1 a2 a4 x square_2t0 (#4.0) <. (#0.0)) \/
  (delta_x a3 a2 a4 x (#4.0) (#8.0) <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_642590101_1=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`#4.0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_642590101_2=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`#4.0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_642590101_3=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`#4.0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_642590101_4=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`#4.0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_642590101_5=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`#4.0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_642590101_6=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`#4.0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_642590101_7=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_642590101_8=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`#4.0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_642590101_9=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`square_2t0`;`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_642590101_10=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`square_2t0`;`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_642590101_11=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_642590101_12=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`square_2t0`;`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_642590101_13=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_642590101_14=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_642590101_15=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_642590101_16=
  all_forall 
  (list_mk_comb(I_642590101_GEN,[`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`]));;

let CKC_746445726= list_mk_conj[
  I_642590101_16;I_642590101_15;I_642590101_14;I_642590101_13;I_642590101_12;
  I_642590101_11;I_642590101_10;I_642590101_9;I_642590101_8;I_642590101_7;
  I_642590101_6;I_642590101_5;I_642590101_4;I_642590101_3;I_642590101_2;
  I_642590101_1; I_109046923_16;I_109046923_15;I_109046923_14;I_109046923_13;
  I_109046923_12;I_109046923_11;I_109046923_10;I_109046923_9;I_109046923_8;
  I_109046923_7;I_109046923_6;I_109046923_5;I_109046923_4;I_109046923_3;
  I_109046923_2;I_109046923_1;  ];; (* kc group 18.10  *)

(*
LOC: 2002 k.c page 60
Group_18.11
*)

(* XXX 
Error:  for much of this group a3 is not in scope here!
*)
(* interval verification by Ferguson *)
let I_160800042_GEN= 
   `(\ a2 a4 . 
 (ineq
[
((#8.0)  , x, (square(#3.2)));
((#8.0)  , x', (square(#3.2)))
]
   (((vor_0_x a2 a3 a1 x (#4.0) (#4.0))+
     (vor_0_x a1 a3 a5 x' square_2t0 x)+
    (vor_0_x a5 a3 a4 (#4.0) (#4.0) x')
   <. (--(#0.221)))
   \/
  (delta_x a2 a3 a1 x (#4.0) (#4.0) <. (#0.0)) \/
  (delta_x a1 a3 a5 x' square_2t0 x <. (#0.0)) \/
  (delta_x a5 a3 a4 (#4.0) (#4.0) x' <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_160800042_1=
  all_forall 
  (list_mk_comb(I_160800042_GEN,[`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_160800042_2=
  all_forall 
  (list_mk_comb(I_160800042_GEN,[`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_160800042_3=
  all_forall 
  (list_mk_comb(I_160800042_GEN,[`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_160800042_4=
  all_forall 
  (list_mk_comb(I_160800042_GEN,[`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_690272881_GEN= 
   `(\ a2 a4 . 
 (ineq
[
((#8.0)  , x, (square(#3.2)));
((#8.0)  , x', (square(#3.2)))
]
   (((tau_0_x a2 a3 a1 x (#4.0) (#4.0))+
     (tau_0_x a1 a3 a5 x' square_2t0 x)+
    (tau_0_x a5 a3 a4 (#4.0) (#4.0) x')
   >. (#0.486))
   \/
  (delta_x a2 a3 a1 x (#4.0) (#4.0) <. (#0.0)) \/
  (delta_x a1 a3 a5 x' square_2t0 x <. (#0.0)) \/
  (delta_x a5 a3 a4 (#4.0) (#4.0) x' <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_690272881_1=
  all_forall 
  (list_mk_comb(I_690272881_GEN,[`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_690272881_2=
  all_forall 
  (list_mk_comb(I_690272881_GEN,[`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_690272881_3=
  all_forall 
  (list_mk_comb(I_690272881_GEN,[`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_690272881_4=
  all_forall 
  (list_mk_comb(I_690272881_GEN,[`square_2t0`;`square_2t0`]));;

let CKC_897046482= list_mk_conj[
  I_690272881_4;I_690272881_3;I_690272881_2;I_690272881_1
  ; I_160800042_4;I_160800042_3;I_160800042_2;I_160800042_1;  ];; (* kc group 18.11  *)


(*
LOC: 2002 k.c page 60
Group_18.12
*)



(* interval verification by Ferguson *)
let I_713930036_GEN= 
   `(\ a1 a5 . 
 (ineq
[
((square(#3.2)),x,square_4t0);
((square(#3.2)),x',square_4t0)
     ]
   (((vor_0_x (#4.0) (#4.0) a1 x (#4.0) (#4.0))+
     (vor_0_x a1 (#4.0) a5 x' square_2t0 x)+
    (vor_0_x a5 (#4.0) (#4.0) (#4.0) (#4.0) x')
   <. (--(#0.221)))
   \/
  ((dih_x (#4.0) a5 (#4.0) (#4.0) (#4.0) x') +
   (dih_x (#4.0) a5 a1 square_2t0 x x') +
   (dih_x (#4.0) (#4.0) a1 (#4.0) x (#4.0) ) < acs(--(&.53)/(&.75))) \/
  (delta_x (#4.0) (#4.0) a1 x (#4.0) (#4.0) <. (#0.0)) \/
  (delta_x a1 (#4.0) a5 x' square_2t0 x <. (#0.0)) \/
  (delta_x a5 (#4.0) (#4.0) (#4.0) (#4.0) x' <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_713930036_1=
  all_forall 
  (list_mk_comb(I_713930036_GEN,[`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_713930036_2=
  all_forall 
  (list_mk_comb(I_713930036_GEN,[`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_713930036_3=
  all_forall 
  (list_mk_comb(I_713930036_GEN,[`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_713930036_4=
  all_forall 
  (list_mk_comb(I_713930036_GEN,[`square_2t0`;`square_2t0`]));;



(* interval verification by Ferguson *)
let I_724922588_GEN= 
   `(\ a1 a5 . 
 (ineq
[
((square(#3.2)),x,square_4t0);
((square(#3.2)),x',square_4t0)
     ]
   (((tau_0_x (#4.0) (#4.0) a1 x (#4.0) (#4.0))+
     (tau_0_x a1 (#4.0) a5 x' square_2t0 x)+
    (tau_0_x a5 (#4.0) (#4.0) (#4.0) (#4.0) x')
   >. (#0.221))
   \/
  ((dih_x (#4.0) a5 (#4.0) (#4.0) (#4.0) x') +
   (dih_x (#4.0) a5 a1 square_2t0 x x') +
   (dih_x (#4.0) (#4.0) a1 (#4.0) x (#4.0) ) < acs(--(&.53)/(&.75))) \/
  (delta_x (#4.0) (#4.0) a1 x (#4.0) (#4.0) <. (#0.0)) \/
  (delta_x a1 (#4.0) a5 x' square_2t0 x <. (#0.0)) \/
  (delta_x a5 (#4.0) (#4.0) (#4.0) (#4.0) x' <. (#0.0)))))`;;

(* interval verification by Ferguson *)
let I_724922588_1=
  all_forall 
  (list_mk_comb(I_724922588_GEN,[`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_724922588_2=
  all_forall 
  (list_mk_comb(I_724922588_GEN,[`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_724922588_3=
  all_forall 
  (list_mk_comb(I_724922588_GEN,[`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_724922588_4=
  all_forall 
  (list_mk_comb(I_724922588_GEN,[`square_2t0`;`square_2t0`]));;

let CKC_928952883= list_mk_conj[I_724922588_4;I_724922588_3;I_724922588_2;I_724922588_1;
   I_713930036_4;I_713930036_3;I_713930036_2;I_713930036_1;  ];; (* kc group 18.12  *)

(*
LOC: 2002 k.c page 60
Group_18.13
*)


(* interval verification by Ferguson *)
let I_821730621_GEN= 
   `(\ a2 a4 a5 . 
 (ineq
[
((#8.0) , x, (square(#3.2)));
(square(#3.2),x',square_4t0)
]
   (((vor_0_x (#4.0) a2 (#4.0) (#4.0) x (#4.0))+
    (vor_0_x (#4.0) (#4.0) a4 (#4.0) x' x)+
    (vor_0_x (#4.0) a4 a5 (#4.0) (#4.0) x')
   <. (--(#0.221)))
   \/
  (cross_diag_x (#4.0) (#4.0) a4 x' (#4.0) x a5 (#4.0) square_2t0
        <. (square(#3.2))) \/
  (delta_x (#4.0) a2 (#4.0) (#4.0) x (#4.0) <. (#0.0)) \/
  (delta_x (#4.0) (#4.0) a4 (#4.0) x' x <. (#0.0)) \/
  (delta_x (#4.0) a4 a5 (#4.0) (#4.0) x' <. (#0.0)))))`;;


(* interval verification by Ferguson *)
let I_821730621_1=
  all_forall 
  (list_mk_comb(I_821730621_GEN,[`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_821730621_2=
  all_forall 
  (list_mk_comb(I_821730621_GEN,[`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_821730621_3=
  all_forall 
  (list_mk_comb(I_821730621_GEN,[`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_821730621_4=
  all_forall 
  (list_mk_comb(I_821730621_GEN,[`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_821730621_5=
  all_forall 
  (list_mk_comb(I_821730621_GEN,[`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_821730621_6=
  all_forall 
  (list_mk_comb(I_821730621_GEN,[`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_821730621_7=
  all_forall 
  (list_mk_comb(I_821730621_GEN,[`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_821730621_8=
  all_forall 
  (list_mk_comb(I_821730621_GEN,[`square_2t0`;`square_2t0`;`square_2t0`]));;


(* interval verification by Ferguson *)
let I_890642961_GEN= 
   `(\ a2 a4 a5 . 
 (ineq
[
((#8.0) , x, (square(#3.2)));
(square(#3.2),x',square_4t0)
]
   (((tau_0_x (#4.0) a2 (#4.0) (#4.0) x (#4.0))+
    (tau_0_x (#4.0) (#4.0) a4 (#4.0) x' x)+
    (tau_0_x (#4.0) a4 a5 (#4.0) (#4.0) x')
   >. (#0.486))
   \/
  (cross_diag_x (#4.0) (#4.0) a4 x' (#4.0) x a5 (#4.0) square_2t0
        <. (square(#3.2))) \/
  (delta_x (#4.0) a2 (#4.0) (#4.0) x (#4.0) <. (#0.0)) \/
  (delta_x (#4.0) (#4.0) a4 (#4.0) x' x <. (#0.0)) \/
  (delta_x (#4.0) a4 a5 (#4.0) (#4.0) x' <. (#0.0)))))`;;


(* interval verification by Ferguson *)
let I_890642961_1=
  all_forall 
  (list_mk_comb(I_890642961_GEN,[`#4.0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_890642961_2=
  all_forall 
  (list_mk_comb(I_890642961_GEN,[`#4.0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_890642961_3=
  all_forall 
  (list_mk_comb(I_890642961_GEN,[`#4.0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_890642961_4=
  all_forall 
  (list_mk_comb(I_890642961_GEN,[`#4.0`;`square_2t0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_890642961_5=
  all_forall 
  (list_mk_comb(I_890642961_GEN,[`square_2t0`;`#4.0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_890642961_6=
  all_forall 
  (list_mk_comb(I_890642961_GEN,[`square_2t0`;`#4.0`;`square_2t0`]));;

(* interval verification by Ferguson *)
let I_890642961_7=
  all_forall 
  (list_mk_comb(I_890642961_GEN,[`square_2t0`;`square_2t0`;`#4.0`]));;

(* interval verification by Ferguson *)
let I_890642961_8=
  all_forall 
  (list_mk_comb(I_890642961_GEN,[`square_2t0`;`square_2t0`;`square_2t0`]));;

let CKC_673800906= list_mk_conj[I_890642961_8;I_890642961_7;I_890642961_6;I_890642961_5;
   I_890642961_4;I_890642961_3;I_890642961_2;I_890642961_1;
   I_821730621_8;I_821730621_7;I_821730621_6;I_821730621_5;
   I_821730621_4;I_821730621_3;I_821730621_2;I_821730621_1;  ];; (* kc group 18.13  *)

(*
LOC: 2002 k.c page 60
Group_18.14
*)

(* interval verification by Ferguson *)
let I_341667126=
  all_forall `ineq
  [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0) , x4, (#8.0));
     (square_2t0 , x5, (#8.0) );
     (square_2t0 , x6, (#8.0) )
  ]
  (vor_0_x x1 x2 x3 x4 x5 x6 <. --(#0.168) - (#0.009))
  `;;

(* interval verification by Ferguson *)
let I_535906363=
  all_forall `ineq
  [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0) , x4, (#8.0));
     (square_2t0 , x5, (#8.0) );
     (square_2t0 , x6, (#8.0) )
  ]
  (tau_0_x x1 x2 x3 x4 x5 x6 > (#0.352) - (#0.05925))
  `;;

let CKC_315678695= list_mk_conj[I_535906363;I_341667126;  ];; (* kc group 18.14  *)

(*
LOC: 2002 k.c page 60
Group_18.15
*)

let I_516537931=
  all_forall `ineq
  [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#8.0)  , x5, square (#3.2));
     ((#8.0)  , x6, square (#3.2))
  ]
  (vor_0_x x1 x2 x3 x4 x5 x6 <. --(#0.168) )
  `;;


let I_130008809_1=
  all_forall `ineq
  [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#8.0)  , x5, square (#3.2));
     ((#8.0)  , x6, square (#3.2))
  ]
  (tau_0_x x1 x2 x3 x4 x5 x6  +
   (tau_0_x x1 (#4.0)  x3 (#4.0) x5 (#4.0)) >. (#0.31) )
  `;;


let I_130008809_2=
  all_forall `ineq
  [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#8.0)  , x5, square (#3.2));
     ((#8.0)  , x6, square (#3.2))
  ]
  (tau_0_x x1 x2 x3 x4 x5 x6  +
   (tau_0_x x1 square_2t0  x3 (#4.0) x5 (#4.0)) >. (#0.31) )
  `;;

let CKC_468742136= list_mk_conj[I_130008809_2;I_130008809_1;I_516537931;  ];; (* kc group 18.15  *)

(*
LOC: 2002 k.c page 60
Group_18.16
*)

let I_531861442=
  all_forall `ineq
  [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     (square_2t0 , x5, (#8.0) );
     ((#8.0)  , x6, square (#3.2))
  ]
  (vor_0_x x1 x2 x3 x4 x5 x6 <. --(#0.084) )
  `;;


(* interval verification in partK.cc *)
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

(* interval verification in partK.cc *)
let I_710875528=
  all_forall `ineq
  [((#4.0), x1, (#4.0) );
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, (#4.0) );
     ((#4.0), x4, (#4.0) );
     ((#8.0)  , x5, square (#3.2));
     ((#4.0), x6, (#4.0) )     
  ]
  (vor_0_x x1 x2 x3 x4 x5 x6 < (#0.009) + ((sqrt x5 - sqrt8)*(#0.1))  )
  `;;


let I_286122364=
  all_forall `ineq
  [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     (square_2t0 , x5, (#8.0) );
     ((#8.0)  , x6, square (#3.2))
  ]
  (tau_0_x x1 x2 x3 x4 x5 x6 >. (#0.176) )
  `;;

let CKC_938091791= list_mk_conj[I_286122364;I_710875528;I_292827481;I_531861442;  ];; (* kc group 18.16  *)

(* end of 2002:kc *)


(* 
LOC: 2002 IV
group hash codes spIV : 
*)


(*

Here are the composite inequalities 
for the various groups:

CIVA1_193836552
CIVA2_815492935
CIVA3_729988292
CIVA4_531888597
CIVA5_628964355
CIVA6_934150983
CIVA7_187932932
CIVA8_83777706
CIVA9_618205535
CIVA10_73974037

CIVA11_764978100
CIVA12_855294746
CIVA13_148776243
CIVA14_984628285
CIVA15_311189443
CIVA16_163548682
CIVA17_852270725
CIVA18_819209129
CIVA19_128523606
CIVA20_874876755

CIVA21_692155251
CIVA22_485049042
CIVA23_209361863
CIVA24_835344007


*)

(*
LOC: 2002 IV page 46.
Section A1
*)

(*
It says we may assume y6=2, and equality is entered below in the bounds
*)
(* interval verification by Ferguson *)
let I_757995764=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.23)));
     ((#4.0), x3, (square (#2.23)));
     ((square (#2.77)), x4, (#8.0));
    
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, (#4.0))
    ]
    (
            (beta (acs (  (sqrt x1) /  (#2.77))) (arclength (sqrt x1) (sqrt x3) (sqrt x5))) <. 
            (dih3_x x1 x2 x3 x4 x5 x6))`;;




(* interval verification by Ferguson *)
let I_735258244=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#3.2)), x4, (square (#3.2)));
    
        (square_2t0, x5, square_2t0);
     ((#4.0), x6, (#4.0))
    ]
    (
            (beta (acs (  (sqrt x1) /  (#2.51))) (arclength (sqrt x1) (sqrt x3) (sqrt x5))) <. 
            (dih3_x x1 x2 x3 x4 x5 x6))`;;




(* interval verification by Ferguson *)
let I_343330051=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, (square (#3.2)));
    
        (square_2t0, x5, square_2t0);
     (square_2t0, x6, square_2t0)
    ]
    (
            (beta (arclength (sqrt x1) t0 (#1.6)) (arclength (sqrt x1) (sqrt x2) (sqrt x6))) <. 
            (dih2_x x1 x2 x3 x4 x5 x6))`;;



(* interval verification by Ferguson *)
let I_49446087=
   all_forall `ineq 
    [((square (#2.2)), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, (square (#3.2)));
    
        ((square (#3.2)), x5, (square (#3.2)));
     ((#4.0), x6, (#4.0))
    ]
    (
            (beta (arclength (sqrt x1) t0 (#1.6)) (arclength (sqrt x1) (sqrt x2) (sqrt x6))) <. 
            (dih2_x x1 x2 x3 x4 x5 x6))`;;



(* interval verification by Ferguson *)
let I_799187442 =
  all_forall `ineq
    [
      ((#4.0), x1, (square (#2.2)));
       ((#4.0), x2, (square_2t0));
       (square_2t0, x3, square_2t0);
       ((square (#3.2)), x4, (square (#3.2)));
       ((square (#3.2)), x5, (square (#3.2)));
       ((#4.0), x6, (#4.0))
    ]
      (let y1 = (sqrt x1) in
       let y2 = (sqrt x2) in
       let psi = (arclength y1 t0 (#1.6)) in
       let eta126 = (eta_x x1 x2 x6) in
    ((dihR (y2/(&2)) eta126 (y1/(&.2 * cos(psi))))
       <.
       (dih2_x x1 x2 x3 x4 x5 x6)
    ))`;;


let I_275706375=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#2.77)), x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vort_x x1 x2 x3 x4 x5 x6 (#1.385)) <.  (#0.00005)) \/ 
        (  (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;




let I_324536936=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#2.77)), x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vort_x x1 x2 x3 x4 x5 x6 (#1.385)) <.  (#0.00005)) \/ 
        (  (eta_x x2 x3 x4) <.  (sqrt (#2.0))))`;;



let I_983547118=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#2.77)), x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (tauVt_x x1 x2 x3 x4 x5 x6 (#1.385)) >.  (#0.0682)) \/ 
        (  (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;


let I_206278009=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#2.77)), x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (tauVt_x x1 x2 x3 x4 x5 x6 (#1.385)) >.  (#0.0682)) \/ 
        (  (eta_x x2 x3 x4) <.  (sqrt (#2.0))))`;;


(* Group A1 *)
let CIVA1_193836552 = list_mk_conj [ 
  I_757995764;I_735258244;I_343330051;I_49446087;I_799187442 ;
  I_275706375;I_324536936;I_983547118;I_206278009;];;

(*

LOC: 2002 IV, page 46
Section A2
*)


let I_413688580=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
          ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (nu_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#4.3223)) +.  (  (#4.10113) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



let I_805296510=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (nu_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#0.9871)) +.  (  (#0.80449) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



let I_136610219=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (nu_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#0.8756)) +.  (  (#0.70186) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



let I_379204810=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (nu_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#0.3404)) +.  (  (#0.24573) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;




let I_878731435=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (nu_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#0.0024)) +.  (  (#0.00154) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



let I_891740103=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (nu_x x1 x2 x3 x4 x5 x6) <.  ( (#0.1196) +.  (  (--. (#0.07611)) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;

let CIVA2_815492935 = list_mk_conj [ 
  I_413688580;I_805296510;I_136610219;
  I_379204810;I_878731435;I_891740103;];;

(*
 
LOC: 2002 IV, page 46
Section A3
*)



let I_334002329=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (( --. ) (taunu_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#4.42873)) +.  (  (#4.16523) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;




let I_883139937=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (( --. ) (taunu_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#1.01104)) +.  (  (#0.78701) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



let I_507989176=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (( --. ) (taunu_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#0.99937)) +.  (  (#0.77627) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;




let I_244435805=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (( --. ) (taunu_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#0.34877)) +.  (  (#0.21916) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



let I_930176500=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (( --. ) (taunu_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#0.11434)) +.  (  (#0.05107) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



let I_815681339=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (( --. ) (taunu_x x1 x2 x3 x4 x5 x6)) <.  ( (#0.07749) +.  (  (--. (#0.07106)) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;

let CIVA3_729988292 = list_mk_conj 
 [ I_334002329;I_883139937;I_507989176;I_244435805;I_930176500;
   I_815681339;];;

(*
 
LOC: 2002 IV, page 47
Section A4
*)


(*
In this section and in section A5 we assumed dih_x ( <=. ) (#2.46)
*)
let I_649592321=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vorC0_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#3.421)) +.  (  (#2.28501) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_600996944=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vorC0_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#2.616)) +.  (  (#1.67382) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_70667639=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vorC0_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#1.4486)) +.  (  (#0.8285) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_99182343=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vorC0_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#0.79)) +.  (  (#0.390925) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_578762805=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vorC0_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#0.3088)) +.  (  (#0.12012) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_557125557=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vorC0_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#0.1558)) +.  (  (#0.0501) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;

let CIVA4_531888597= list_mk_conj 
   [ I_649592321;I_600996944;I_70667639;I_99182343;I_578762805;
     I_557125557;];;
(*
 
LOC: 2002 IV, page 47
Section A5
*)


(*
?comment at the beginning of the section
 
not indicated in file
*)

let I_719735900=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tauC0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#3.3407)) +.  (  (#2.1747) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_359616783=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tauC0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#2.945)) +.  (  (#1.87427) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_440833181=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tauC0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#1.5035)) +.  (  (#0.83046) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_578578364=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tauC0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#1.0009)) +.  (  (#0.48263) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;




let I_327398152=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tauC0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#0.7787)) +.  (  (#0.34833) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_314861952=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tauC0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#0.4475)) +.  (  (#0.1694) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_234753056=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tauC0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#0.2568)) +.  (  (#0.0822) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;


let CIVA5_628964355= list_mk_conj 
  [  I_719735900;I_359616783;I_440833181;I_578578364;I_327398152;
     I_314861952;I_234753056;];;
(*
 
LOC: 2002 IV, page 47
Section A6
*)

(*
In this section and in section A7 we assumed dih_x ( <=. ) (#2.46)
*)


let I_555481748=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vor_0_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#3.58)) +.  (  (#2.28501) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_615152889=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vor_0_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#2.715)) +.  (  (#1.67382) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_647971645=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vor_0_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#1.517)) +.  (  (#0.8285) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_516606403=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vor_0_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#0.858)) +.  (  (#0.390925) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_690552204=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vor_0_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#0.358)) +.  (  (#0.12012) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_852763473=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (vor_0_x x1 x2 x3 x4 x5 x6) <.  ( (--. (#0.186)) +.  (  (#0.0501) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;


let CIVA6_934150983 = list_mk_conj 
  [ I_555481748;I_615152889;I_647971645;I_516606403;I_690552204;
    I_852763473;];;

(*
 
LOC: 2002 IV, page 47
Section A7
*)


let I_679673664=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#3.48)) +.  (  (#2.1747) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_926514235=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#3.06)) +.  (  (#1.87427) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_459744700=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#1.58)) +.  (  (#0.83046) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_79400832=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#1.06)) +.  (  (#0.48263) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_277388353=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#0.83)) +.  (  (#0.34833) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_839852751=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#0.50)) +.  (  (#0.1694) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;



let I_787458652=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) <.  ( (--. (#0.29)) +.  (  (#0.0822) *.  (dih_x x1 x2 x3 x4 x5 x6)))) \/ 
        (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.46)))`;;


let CIVA7_187932932= list_mk_conj
  [ I_679673664;I_926514235;I_459744700;I_79400832;I_277388353;
    I_839852751;I_787458652;];;

(*
 
LOC: 2002 IV, page 47
Section A8
*)

(*
Need upper bound for y4 in all equations in this section
Change so that each y4 is equality.
*)


let I_499014780=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.23))`;;



let I_901845849=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.4167))`;;



let I_410091263=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#3.2)), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.65))`;;



let I_125103581=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, (#4.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#0.956))`;;



let I_504968542=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, (#4.0));
    
        ((#4.0), x5, (#8.0));
     ((#4.0), x6, square_2t0)
    ]
    (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#0.28))`;;



let I_770716154=
   all_forall `ineq 
    [((square (#2.7)), x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#3.2)), x4, (square (#3.2)));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.714))`;;



let I_666090270=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.7)));
     ((#4.0), x2, (square (#2.25)));
     ((#4.0), x3, square_2t0);
    
        ((square (#3.2)), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.714))`;;



let I_971555266=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (  (dih_x x1 x2 x3 x4 x5 x6) <.  (#2.184))`;;

let CIVA8_83777706= list_mk_conj
  [ I_499014780;I_901845849;I_410091263;I_125103581;I_504968542;
    I_770716154;I_666090270;I_971555266;];;
(*
 
LOC: 2002 IV, page 47--48
Section A9
*)


(* interval verification by Ferguson *)
let I_956875054=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((square (#2.77)), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
    (  (kappa (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5) (sqrt x6)) <.  (--. (#0.003521)))`;;



(* interval verification by Ferguson *)
let I_664200787=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#2.77)), x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (kappa (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5) (sqrt x6)) <.  (--. (#0.017))) \/ 
        (  (eta_x x2 x3 x4) <.  (sqrt (#2.0))))`;;



(* interval verification by Ferguson *)
let I_390273147=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((square (#2.77)), x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (kappa (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5) (sqrt x6)) <.  (--. (#0.017))) \/ 
        (  (eta_x x4 x5 x6) <.  (sqrt (#2.0))))`;;



(*
Equality has been assumed with x4 term
*)
(* interval verification by Ferguson *)
let I_654422246=
   all_forall `ineq 
    [((square (#2.57)), x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
         ((square (#3.2)), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (kappa (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5) (sqrt x6)) <.  (--. (#0.02274))) \/ 
        (  (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;



(*
Equality has been assumed with x4 term
*)
(* interval verification by Ferguson *)
let I_366536370=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.57)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
         ((square (#3.2)), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (kappa (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5) (sqrt x6)) <.  (--. (#0.029))) \/ 
        (  (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;



(*
Equality has been assumed with x4 term
*)
(* interval verification by Ferguson *)
let I_62532125=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.57)));
     ((#4.0), x2, (square (#2.25)));
     ((#4.0), x3, (square (#2.25)));
    
        ((square (#3.2)), x4, (square (#3.2)));
     ((#4.0), x5, (square (#2.25)));
     ((#4.0), x6, (square (#2.25)))
    ]
    (
        (  (kappa (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5) (sqrt x6)) <.  (--. (#0.03883))) \/ 
        (  (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;




(* interval verification by Ferguson *)
let I_370631902=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.57)));
     ((#4.0), x2, (square (#2.25)));
     ((#4.0), x3, (square (#2.25)));
    
        ((square (#3.2)), x4, (square (#3.2)));
     ((#4.0), x5, (square (#2.25)));
     ((#4.0), x6, square_2t0)
    ]
    (
        (  (kappa (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5) (sqrt x6)) <.  (--. (#0.0325))) \/ 
        (  (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;


let CIVA9_618205535= list_mk_conj 
  [ I_956875054;I_664200787;I_390273147;I_654422246;I_366536370;
    I_62532125;I_370631902;];;

(*
 
LOC: 2002 IV, page 48
Section A10
*)


let I_214637273=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (gamma_x x1 x2 x3 x4 x5 x6) <.  (octavor0_x x1 x2 x3 x4 x5 x6))`;;




let I_751772680=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (gamma_x x1 x2 x3 x4 x5 x6) <.  ( (octavor0_x x1 x2 x3 x4 x5 x6) +.  (#0.01561)))`;;




let I_366146051=
   all_forall `ineq 
    [((square (#2.57)), x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (gamma_x x1 x2 x3 x4 x5 x6) <.  ( (octavor0_x x1 x2 x3 x4 x5 x6) +.  (#0.00935)))`;;




let I_675766140=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.57)));
     ((square (#2.25)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (gamma_x x1 x2 x3 x4 x5 x6) <.  ( (octavor0_x x1 x2 x3 x4 x5 x6) +.  (#0.00928)))`;;



let I_520734758=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.57)));
     ((square (#2.25)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((square (#2.25)), x6, square_2t0)
    ]
    ( (gamma_x x1 x2 x3 x4 x5 x6) <.  (octavor0_x x1 x2 x3 x4 x5 x6))`;;

let CIVA10_73974037= list_mk_conj 
   [  I_214637273;I_751772680;I_366146051;I_675766140;I_520734758;];;
(*
 
LOC: 2002 IV, page 48
Section A11
*)


let I_378432183=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((#4.0), x2, (square (#2.45)));
     ((#4.0), x3, (square (#2.45)));
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (octavor_analytic_x x1 x2 x3 x4 x5 x6) <.  (octavor0_x x1 x2 x3 x4 x5 x6))`;;




let I_572206659=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((square (#2.45)), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (octavor_analytic_x x1 x2 x3 x4 x5 x6) <.  (octavor0_x x1 x2 x3 x4 x5 x6))`;;




let I_310679005=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (#0.003521)))`;;




let I_284970880=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((square (#2.45)), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (square (#2.77)));
     ((#4.0), x5, square_2t0);
     ((square (#2.45)), x6, square_2t0)
    ]
    ( (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (--. (#0.003521))))`;;




let I_972111620=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (--. (#0.009))))`;;




let I_875762896=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.57)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (octavor_analytic_x x1 x2 x3 x4 x5 x6) <.  (octavor0_x x1 x2 x3 x4 x5 x6)) \/ 
            ( (eta_x x1 x2 x6) <.  (sqrt (#2.0))))`;;




let I_385332676=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, (square (#2.2)));
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (octavor_analytic_x x1 x2 x3 x4 x5 x6) <.  ( (octavor0_x x1 x2 x3 x4 x5 x6) +.  (--. (#0.004131)))) \/ 
            ( (eta_x x1 x2 x6) >.  (sqrt (#2.0))) \/ 
            ( (eta_x x1 x3 x5) <.  (sqrt (#2.0))))`;;

let CIVA11_764978100= list_mk_conj 
  [  I_378432183;I_572206659;I_310679005;I_284970880;I_972111620;
     I_875762896;I_385332676;];;

(*
 
LOC: 2002 IV, page 48
Section A12
*)


(* interval verification by Ferguson *)
let I_970291025=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     (square_2t0, x2, (#8.0));
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (tau_analytic_x x1 x2 x3 x4 x5 x6) >. 
            ( (#0.13) +.  (  (#0.2) *.  ( (dih_x x1 x2 x3 x4 x5 x6) +.  (  pi /  (--. (#2.0))))))) \/ 
            ( (eta_x x1 x2 x6) >.  (sqrt (#2.0))))`;;




(* interval verification by Ferguson *)
let I_524345535=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     (square_2t0, x2, (#8.0));
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (tauVt_x x1 x2 x3 x4 x5 x6 (sqrt (#2.0))) >. 
            ( (#0.13) +.  (  (#0.2) *.  ( (dih_x x1 x2 x3 x4 x5 x6) +.  (  pi /  (--. (#2.0))))))) \/ 
            ( (eta_x x1 x2 x6) <.  (sqrt (#2.0))))`;;




let I_812894433=
   all_forall `ineq 
    [((square (#2.75)), x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (nu_x x1 x2 x3 x4 x5 x6) <.   ( (--. (#0.3429)) +.  (  (#0.24573) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;




(*
Equality used in dih_x equation
*)
let I_404793781=
   all_forall `ineq 
    [(square_2t0, x1, (square (#2.75)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     (square_2t0, x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (vorC0_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.0571))) \/ 
            ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#2.2)))`;;

let CIVA12_855294746= list_mk_conj 
  [  I_970291025;I_524345535;I_812894433;I_404793781;];;

(*
 
LOC: 2002 IV, page 48--49
Section A13
*)


let I_705592875=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (taunu_x x1 x2 x3 x4 x5 x6) >.  (#0.033))`;;




let I_747727191=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (tau_0_x x1 x2 x3 x4 x5 x6) >.  ( (#0.06585) +.  (--. (#0.0066))))`;;




let I_474496219=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (#8.0));
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  (#0.009))`;;



let I_649551700=
   all_forall `ineq 
    [((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)))
    ]
    ( (vor_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0)) <.  (#0.0461))`;;



(*
Weak inequality used ( <=. ) in next one below
*)
let I_74657942=
   all_forall `ineq 
    [((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)))
    ]
    ( (vor_0_x square_2t0 (#4.0) x3 x4 (#4.0) (#4.0)) <=.  (#0.0))`;;



let I_897129160=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#8.0), x4, (square (#3.2)))
    ]
    ( (vor_0_x x1 x2 square_2t0 x4 (#4.0) (#4.0)) <.  (#0.0))`;;



let I_760840103=
   all_forall `ineq 
    [((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)))
    ]
    ( (tau_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0)) >.  (#0.014))`;;



(*
Inequality used ( >=. ) in next one
*)
let I_675901554=
   all_forall `ineq 
    [((#8.0), x4, (square (#3.2)))
    ]
    ( (tau_0_x square_2t0 (#4.0) (#4.0) x4 (#4.0) (#4.0)) >=.  (#0.0))`;;



let I_712696695=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#8.0), x4, (square (#3.2)))
    ]
    ( (tau_0_x x1 x2 square_2t0 x4 (#4.0) (#4.0)) >.  (#0.06585))`;;




(* interval verification in partK.cc *)
let I_269048407=
   all_forall `ineq 
    [((square (#2.696)), x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
        ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (nu_x x1 x2 x3 x4 x5 x6) <. 
            ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (  (#0.01) *.  ( (  pi /  (#2.0)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6))))))`;;



(* interval verification in partK.cc *)
let I_553285469=
   all_forall `ineq 
    [((square (#2.6)), x1, (square (#2.696)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((square (#2.1)), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (nu_x x1 x2 x3 x4 x5 x6) <.  (vor_0_x x1 x2 x3 x4 x5 x6))`;;



(* interval verification in partK.cc *)
let I_293389410=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (mu_flat_x x1 x2 x3 x4 x5 x6) <.  ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (#0.0268)))`;;




(* interval verification in partK.cc *)
let I_695069283=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.17)));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (mu_flat_x x1 x2 x3 x4 x5 x6) <.  ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (#0.02)))`;;




(* interval verification in partK.cc *)
let I_814398901=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#8.0), x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.32))`;;




(* interval verification in partK.cc *)
let I_352079526=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (tauhat_x x1 x2 x3 x4 x5 x6) >.  (  (#3.07) *.  pt)) \/ 
            ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.32)))`;;



(* interval verification in partK.cc *)
let I_179025673 = 
  all_forall `ineq
	[
     ((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
        (square_2t0, x4, #8.0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
        ]
		    (
   ((tau_0_x x1 x2 x3 x4 x5 x6) >. ((#3.07)*pt + xiV + (&2 * xi'_gamma))) \/
   ((dih_x x1 x2 x3 x4 x5 x6 >. (#1.32))) \/
   ((eta_x x4 x5 x6 <. sqrt2))
		    )`;;


let CIVA13_148776243= list_mk_conj 
  [  I_705592875;I_747727191;I_474496219;I_649551700;I_74657942;
     I_897129160;I_760840103;I_675901554;I_712696695;I_269048407;
     I_553285469;I_293389410;I_695069283;I_814398901;I_352079526;
     I_179025673];;

(*
 
LOC: 2002 IV, page 49
Section A14
*)

(* interval verification by Ferguson *)
let I_424011442=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_4t0);
     ((#4.0), x5, (square (#3.2)));
     (x5, x6, (square (#3.2)))
    ]
    (
            ( (v0x x1 x2 x3 x4 x5 x6) <.  (#0.0)) \/ 
            ( (sqrt x4) >.  ( (sqrt x2) +.  (sqrt x3))) \/ 
            ( (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;





(* interval verification by Ferguson *)
let I_140881233=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_4t0);
     ((#4.0), x5, (square (#3.2)));
     (x5, x6, (square (#3.2)))
    ]
    (
            ( (v1x x1 x2 x3 x4 x5 x6) <.  (#0.0)) \/ 
            ( (sqrt x4) >.  ( (sqrt x2) +.  (sqrt x3))) \/ 
            ( (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;




(* interval verification by Ferguson *)
let I_601456709_1=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#8.0), x4, (square (#3.2)));
     ((#4.0), x5, (square (#2.189)));
     ((#4.0), x6, square_2t0)
    ]
    (
            ( ( (v0x x1 x2 x3 x4 x5 x6) +.  (  (#0.82) *.  (sqrt (#421.0)))) <.  (#0.0)) \/ 
            ( (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;




(* interval verification by Ferguson *)
let I_601456709_2=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#8.0), x4, (square (#3.2)));
     ((#4.0), x5, (square (#2.189)));
     ((#4.0), x6, square_2t0)
    ]
    (
            ( ( (v1x x1 x2 x3 x4 x5 x6) +.  (  (#0.82) *.  (sqrt (#421.0)))) <.  (#0.0)) \/ 
            ( (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;



(* interval verification by Ferguson *)
let I_292977281_1=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((square (#3.2)), x4, square_4t0);
     ((#4.0), x5, (square (#2.189)));
     ((#4.0), x6, (square (#3.2)))
    ]
    (
            ( ( (v0x x1 x2 x3 x4 x5 x6) +.  (  (#0.82) *.  (sqrt (#421.0)))) <.  (#0.0)) \/ 
            ( (sqrt x4) >.  ( (sqrt x2) +.  (sqrt x3))) \/ 
            ( (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;



(* interval verification by Ferguson *)
let I_292977281_2=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((square (#3.2)), x4, square_4t0);
     ((#4.0), x5, (square (#2.189)));
     ((#4.0), x6, (square (#3.2)))
    ]
    (
            ( ( (v1x x1 x2 x3 x4 x5 x6) +.  (  (#0.82) *.  (sqrt (#421.0)))) <.  (#0.0)) \/ 
            ( (sqrt x4) >.  ( (sqrt x2) +.  (sqrt x3))) \/ 
            ( (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;



(*
Two sets of bounds for x5   I used the more restrictive set
*)
(* interval verification by Ferguson *)
let I_927286061_1=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#8.0), x4, (square (#3.2)));
     ((square (#2.189)), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( ( (v0x x1 x2 x3 x4 x5 x6) +.  (  (#0.5) *.  (sqrt (#421.0)))) <.  (#0.0)) \/ 
            ( (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;




(*
Two sets of bounds for x5   I used the more restrictive set
*)
(* interval verification by Ferguson *)
let I_927286061_2=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#8.0), x4, (square (#3.2)));
     ((square (#2.189)), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( ( (v1x x1 x2 x3 x4 x5 x6) +.  (  (#0.5) *.  (sqrt (#421.0)))) <.  (#0.0)) \/ 
            ( (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;




(*
Two sets of bounds for x5   I used the more restrictive set

*)
(* interval verification by Ferguson *)
let I_340409511_1=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((square (#3.2)), x4, square_4t0);
    
        ((square (#2.189)), x5, (square (#3.2)));
     ((#4.0), x6, (square (#3.2)))
    ]
    (
            ( ( (v0x x1 x2 x3 x4 x5 x6) +.  (  (#0.5) *.  (sqrt (#421.0)))) <.  (#0.0)) \/ 
            ( (sqrt x4) >.  ( (sqrt x2) +.  (sqrt x3))) \/ 
            ( (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;




(*
Two sets of bounds for x5   I used the more restrictive set
*)
(* interval verification by Ferguson *)
let I_340409511_2=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((square (#3.2)), x4, square_4t0);
    
        ((square (#2.189)), x5, (square (#3.2)));
     ((#4.0), x6, (square (#3.2)))
    ]
    (
            ( ( (v1x x1 x2 x3 x4 x5 x6) +.  (  (#0.5) *.  (sqrt (#421.0)))) <.  (#0.0)) \/ 
            ( (sqrt x4) >.  ( (sqrt x2) +.  (sqrt x3))) \/ 
            ( (delta_x x1 x2 x3 x4 x5 x6) <.  (#0.0)))`;;



(* interval verification by Ferguson *)
let I_727498658=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#8.0), x4, square_4t0);
     ((#4.0), x5, (square (#3.2)));
     ((#4.0), x6, (square (#3.2)))
    ]
    (
            ( (delta_x x1 x2 x3 x4 x5 x6) <.  (#421.0)) \/ 
            ( (sqrt x4) >.  ( (sqrt x2) +.  (sqrt x3))) \/ 
            ( (eta_x x1 x3 x5) >.  t0))`;;


(* interval verification by Ferguson *)
let I_484314425 = all_forall `ineq
   [((#4.0), x1, square_2t0);
    ((#4.0), x3, square_2t0);
    ((#4.0), x5, square_2t0)
   ]
        (--(&.4)*doct*(u_x x1 x3 x5)*
                ((deriv (\x. (quo_x x1 x3 x)) x5) +.
                (deriv (\x. (quo_x x3 x1 x)) x5))
                <. (#0.82))`;;

(* interval verification by Ferguson *)
let I_440223030 = all_forall `ineq
   [((#4.0), x1, square_2t0);
    ((#4.0), x3, square_2t0);
    ((square (#2.189)), x5, square_2t0)
   ]
        (--(&.4)*doct*(u_x x1 x3 x5)*
                ((deriv (\x. (quo_x x1 x3 x)) x5) +.
                (deriv (\x. (quo_x x3 x1 x)) x5))
                <. (#0.50))`;;

(*
Handwritten note says to change ( >=. ) to ( >. )
 overlap_f is the function of 1998:IV.4.11, or 2002,IV,Sec.4.14
*)
(* interval verification by Ferguson *)
let I_115756648=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0)
    ]
    ( (overlap_f (sqrt x1) (sqrt x2)) >.  (#0.887))`;;


let CIVA14_984628285 = list_mk_conj 
  [  I_424011442;I_140881233;I_601456709_1;I_601456709_2;
     I_292977281_1;I_292977281_2;I_927286061_1;I_927286061_2;
     I_340409511_1;I_340409511_2;I_727498658;I_484314425;
     I_440223030;I_115756648;];;

(*
 
LOC: 2002 IV, page 49
Section A15
Remember to include this in the summary list-mk-conj
*)

(* interval verification by Ferguson *)
let I_329882546_1= all_forall `ineq
  [((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, square_4t0);
((#4.0), x5, (#4.0));
((#4.0), x6, (#4.0))
  ]
  ((sqrt x4 >. (sqrt x2 + (sqrt x3))) \/
  (sqrt x4 >. (sqrt x5 + (sqrt x6))) \/
  (delta_x x1 x2 x3 x4 x5 x6 <. (&.0)) \/
  ~(deriv (\x. vor_0_x x x2 x3 x4 x5 x6) x1 = (&.0)) \/
  (deriv2 (\x. vor_0_x x x2 x3 x4 x5 x6) x1 >. (&.0)))`;;

(* interval verification by Ferguson *)
let I_329882546_2= 
 all_forall `ineq
  [((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, square_4t0);
((#4.0), x5, (#4.0));
((#4.0), x6, (#4.0))
  ]
  ((sqrt x4 >. (sqrt x2 + (sqrt x3))) \/
  (sqrt x4 >. (sqrt x5 + (sqrt x6))) \/
  (delta_x x1 x2 x3 x4 x5 x6 <. (&.0)) \/
  ~(deriv (\x. (-- (tau_0_x x x2 x3 x4 x5 x6))) x1 = (&.0)) \/
  (deriv2 (\x. (-- (tau_0_x x x2 x3 x4 x5 x6))) x1 >. (&.0)))`;;

(* interval verification by Ferguson *)
let I_427688691_1= 
 all_forall `ineq
  [((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, square_4t0);
((#4.0), x5, (#4.0));
(square_2t0, x6, square_2t0)
  ]
  ((sqrt x4 >. (sqrt x2 + (sqrt x3))) \/
  (sqrt x4 >. (sqrt x5 + (sqrt x6))) \/
  (delta_x x1 x2 x3 x4 x5 x6 <. (&.0)) \/
  ~(deriv (\x. vor_0_x x x2 x3 x4 x5 x6) x1 = (&.0)) \/
  (deriv2 (\x. vor_0_x x x2 x3 x4 x5 x6) x1 >. (&.0)))`;;

(* interval verification by Ferguson *)
let I_427688691_2= 
 all_forall `ineq
  [((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, square_4t0);
((#4.0), x5, (#4.0));
(square_2t0, x6, square_2t0)
  ]
  ((sqrt x4 >. (sqrt x2 + (sqrt x3))) \/
  (sqrt x4 >. (sqrt x5 + (sqrt x6))) \/
  (delta_x x1 x2 x3 x4 x5 x6 <. (&.0)) \/
  ~(deriv (\x. (-- (tau_0_x x x2 x3 x4 x5 x6))) x1 = (&.0)) \/
  (deriv2 (\x. (-- (tau_0_x x x2 x3 x4 x5 x6))) x1 >. (&.0)))`;;

(* interval verification by Ferguson *)
let I_562103670_1= 
 all_forall `ineq
  [((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, square_4t0);
((#4.0), x5, (#4.0));
((#8.0), x6, (#8.0))
  ]
  ((sqrt x4 >. (sqrt x2 + (sqrt x3))) \/
  (sqrt x4 >. (sqrt x5 + (sqrt x6))) \/
  (delta_x x1 x2 x3 x4 x5 x6 <. (&.0)) \/
  ~(deriv (\x. vor_0_x x x2 x3 x4 x5 x6) x1 = (&.0)) \/
  (deriv2 (\x. vor_0_x x x2 x3 x4 x5 x6) x1 >. (&.0)))`;;

(* interval verification by Ferguson *)
let I_562103670_2= 
 all_forall `ineq
  [((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, square_4t0);
((#4.0), x5, (#4.0));
((#8.0), x6, (#8.0))
  ]
  ((sqrt x4 >. (sqrt x2 + (sqrt x3))) \/
  (sqrt x4 >. (sqrt x5 + (sqrt x6))) \/
  (delta_x x1 x2 x3 x4 x5 x6 <. (&.0)) \/
  ~(deriv (\x. (-- (tau_0_x x x2 x3 x4 x5 x6))) x1 = (&.0)) \/
  (deriv2 (\x. (-- (tau_0_x x x2 x3 x4 x5 x6))) x1 >. (&.0)))`;;

(* interval verification by Ferguson *)
let I_564506426_1= 
 all_forall `ineq
  [((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, square_4t0);
(square_2t0, x5, square_2t0);
(square_2t0, x6, square_2t0)
  ]
  ((sqrt x4 >. (sqrt x2 + (sqrt x3))) \/
  (sqrt x4 >. (sqrt x5 + (sqrt x6))) \/
  (delta_x x1 x2 x3 x4 x5 x6 <. (&.0)) \/
  ~(deriv (\x. vor_0_x x x2 x3 x4 x5 x6) x1 = (&.0)) \/
  (deriv2 (\x. vor_0_x x x2 x3 x4 x5 x6) x1 >. (&.0)))`;;

(* interval verification by Ferguson *)
let I_564506426_2= 
 all_forall `ineq
  [((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, square_4t0);
(square_2t0, x5, square_2t0);
(square_2t0, x6, square_2t0)
  ]
  ((sqrt x4 >. (sqrt x2 + (sqrt x3))) \/
  (sqrt x4 >. (sqrt x5 + (sqrt x6))) \/
  (delta_x x1 x2 x3 x4 x5 x6 <. (&.0)) \/
  ~(deriv (\x. (-- (tau_0_x x x2 x3 x4 x5 x6))) x1 = (&.0)) \/
  (deriv2 (\x. (-- (tau_0_x x x2 x3 x4 x5 x6))) x1 >. (&.0)))`;;

(* interval verification by Ferguson *)
let I_288224597_1= 
 all_forall `ineq
  [((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, square_4t0);
(square_2t0, x5, square_2t0);
((#8.0), x6, (#8.0))
  ]
  ((sqrt x4 >. (sqrt x2 + (sqrt x3))) \/
  (sqrt x4 >. (sqrt x5 + (sqrt x6))) \/
  (delta_x x1 x2 x3 x4 x5 x6 <. (&.0)) \/
  ~(deriv (\x. vor_0_x x x2 x3 x4 x5 x6) x1 = (&.0)) \/
  (deriv2 (\x. vor_0_x x x2 x3 x4 x5 x6) x1 >. (&.0)))`;;

(* interval verification by Ferguson *)
let I_288224597_2= 
 all_forall `ineq
  [((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, square_4t0);
(square_2t0, x5, square_2t0);
((#8.0), x6, (#8.0))
  ]
  ((sqrt x4 >. (sqrt x2 + (sqrt x3))) \/
  (sqrt x4 >. (sqrt x5 + (sqrt x6))) \/
  (delta_x x1 x2 x3 x4 x5 x6 <. (&.0)) \/
  ~(deriv (\x. (-- (tau_0_x x x2 x3 x4 x5 x6))) x1 = (&.0)) \/
  (deriv2 (\x. (-- (tau_0_x x x2 x3 x4 x5 x6))) x1 >. (&.0)))`;;

(* interval verification by Ferguson *)
let I_979916330_1= 
 all_forall `ineq
  [((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, square_4t0);
((#8.0), x5, (#8.0));
((#8.0), x6, (#8.0))
  ]
  ((sqrt x4 >. (sqrt x2 + (sqrt x3))) \/
  (sqrt x4 >. (sqrt x5 + (sqrt x6))) \/
  (delta_x x1 x2 x3 x4 x5 x6 <. (&.0)) \/
  ~(deriv (\x. vor_0_x x x2 x3 x4 x5 x6) x1 = (&.0)) \/
  (deriv2 (\x. vor_0_x x x2 x3 x4 x5 x6) x1 >. (&.0)))`;;

(* interval verification by Ferguson *)
let I_749968927_2= 
 all_forall `ineq
  [((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, square_4t0);
((#8.0), x5, (#8.0));
((#8.0), x6, (#8.0))
  ]
  ((sqrt x4 >. (sqrt x2 + (sqrt x3))) \/
  (sqrt x4 >. (sqrt x5 + (sqrt x6))) \/
  (delta_x x1 x2 x3 x4 x5 x6 <. (&.0)) \/
  ~(deriv (\x. (-- (tau_0_x x x2 x3 x4 x5 x6))) x1 = (&.0)) \/
  (deriv2 (\x. (-- (tau_0_x x x2 x3 x4 x5 x6))) x1 >. (&.0)))`;;

let CIVA15_311189443=  list_mk_conj 
  [  I_329882546_1;I_329882546_2;I_427688691_1;I_427688691_2;
     I_562103670_1;I_562103670_2;I_564506426_1;I_564506426_2;
     I_288224597_1;I_288224597_2;I_979916330_1;I_749968927_2;];;

(*
 
LOC: 2002 IV, page 49--50
Section A16

Comments from 2002 text:

Some of these follow from known results.
See II.4.5.1, F.3.13.1, F.3.13.3, F.3.13.4.

The case vor <=0 of the inequality sigma<=0 for flat quarters
follows by Rogers's monotonicity lemma I.8.6.2 and F.3.13.1,
because the circumradius of the flat quarter is ASSUME_TAC least
sqrt(2) when the analytic Voronoi function is used.  We also
use that vor(R(1,eta(2,2,2),sqrt(2)) = 0.
*)


let I_695180203_1=
  all_forall `ineq
    [
((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
(square_2t0, x4, (#8.0));
((#4.0), x5, square_2t0);
((#4.0), x6, square_2t0)
    ]
    (taumu_flat_x x1 x2 x3 x4 x5 x6 >. #0.06585)`;;

let I_695180203_2=
  all_forall `ineq
    [
((square (#2.2)), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((square(#2.6)), x4, (#8.0));
((#4.0), x5, square_2t0);
((#4.0), x6, square_2t0)
    ]
    ((#0.0063) + (tau_0_x x1 x2 x3 x4 x5 x6) >. #0.06585)`;;

let I_695180203_3=
  all_forall `ineq
    [
((#4.0), x1, (square (#2.2)));
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((square(#2.7)), x4, (#8.0));
((#4.0), x5, square_2t0);
((#4.0), x6, square_2t0)
    ]
    ((#0.0114) + (tau_0_x x1 x2 x3 x4 x5 x6) >. #0.06585)`;;

(* In this fourth case, we get half from each upright quarter. *)
let I_695180203_4=
  all_forall `ineq
    [
(square_2t0, x1, (#8.0));
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#4.0), x4, square_2t0);
((#4.0), x5, square_2t0);
((#4.0), x6, square_2t0)
    ]
    ((taunu_x x1 x2 x3 x4 x5 x6) >. (#0.06585)/(#2.0))`;;

let I_695180203_5=
  all_forall `ineq
    [
((#4.0), x1, square_2t0);
((square(#2.23)), x2, square_2t0);
((#4.0), x3, square_2t0);
((square(#2.77)), x4, (#8.0));
((#4.0), x5, square_2t0);
((#4.0), x6, square_2t0)
    ]
    (((tau_0_x x1 x2 x3 x4 x5 x6) >. #0.06585) \/
     (eta_x x4 x5 x6 <. (sqrt (#2.0))))`;;

(* direction of inequality corrected in 690626704_* on Dec 16, 2007, tch *)

let I_690626704_1=
  all_forall `ineq
    [
((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
(square_2t0, x4, (#8.0));
((#4.0), x5, square_2t0);
((#4.0), x6, square_2t0)
    ]
    (mu_flat_x x1 x2 x3 x4 x5 x6 <. #0.0)`;;

let I_690626704_2=
  all_forall `ineq
    [
((square (#2.2)), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((square(#2.6)), x4, (#8.0));
((#4.0), x5, square_2t0);
((#4.0), x6, square_2t0)
    ]
    ((--(#0.0063)) + (vor_0_x x1 x2 x3 x4 x5 x6) <. #0.0)`;;

let I_690626704_3=
  all_forall `ineq
    [
((#4.0), x1, (square (#2.2)));
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((square(#2.7)), x4, (#8.0));
((#4.0), x5, square_2t0);
((#4.0), x6, square_2t0)
    ]
    ((--(#0.0114)) + (vor_0_x x1 x2 x3 x4 x5 x6) <. #0.0)`;;

(* In this fourth case, we get half from each upright quarter. *)
let I_690626704_4=
  all_forall `ineq
    [
(square_2t0, x1, (#8.0));
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#4.0), x4, square_2t0);
((#4.0), x5, square_2t0);
((#4.0), x6, square_2t0)
    ]
    ((nu_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;

let I_690626704_5=
  all_forall `ineq
    [
((#4.0), x1, square_2t0);
((square(#2.23)), x2, square_2t0);
((#4.0), x3, square_2t0);
((square(#2.77)), x4, (#8.0));
((#4.0), x5, square_2t0);
((#4.0), x6, square_2t0)
    ]
    (((vor_0_x x1 x2 x3 x4 x5 x6) <. #0.0) \/
     (eta_x x4 x5 x6 <. (sqrt (#2.0))))`;;


let I_807023313=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (square (#2.77)));
     (square_2t0, x5, (square (#2.77)));
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  (--. (#0.05714))) \/ 
            ( (eta_x x4 x5 x6) >.  (sqrt (#2.0))))`;;


let I_590577214=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (square (#2.77)));
     (square_2t0, x5, (square (#2.77)));
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (tau_analytic_x x1 x2 x3 x4 x5 x6) >.  (#0.13943)) \/ 
            ( (eta_x x4 x5 x6) >.  (sqrt (#2.0))))`;;

(* STM 1/13/08.  Added parentheses.  This was not parsing correctly *)
let I_949210508_1=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#4.0), x4, square_2t0);
(square_2t0, x5, (#8.0));
(square_2t0, x6, (#8.0))
    ] 
    ((vor_0_x x1 x2 x3 x4 x5 x6 <. Z32) \/
       (eta_x x4 x5 x6 >. (sqrt (#2.0)) ))`;;

let I_949210508_2=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#4.0), x4, square_2t0);
((square(#2.77), x5, (#8.0)));
(square_2t0, x6, (#8.0))
    ] 
   (vor_0_x x1 x2 x3 x4 x5 x6 <. Z32)`;;

(* STM 1/13/08.  Added parentheses.  This was not parsing correctly *)
let I_671961774_1=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#4.0), x4, square_2t0);
(square_2t0, x5, (#8.0));
(square_2t0, x6, (#8.0))
    ] 
   ((tau_0_x x1 x2 x3 x4 x5 x6 >. (#0.13943)) \/
   (eta_x x4 x5 x6 >. (sqrt (#2.0)) ))`;;

let I_671961774_2=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#4.0), x4, square_2t0);
((square(#2.77), x5, (#8.0)));
(square_2t0, x6, (#8.0))
    ] 
   (tau_0_x x1 x2 x3 x4 x5 x6 >. (#0.13943))`;;

let CIVA16_163548682 = list_mk_conj 
 [  I_695180203_1;I_695180203_2;I_695180203_3;I_695180203_4;
    I_695180203_5;I_690626704_1;I_690626704_2;I_690626704_3;
    I_690626704_4;I_690626704_5;I_807023313;I_590577214;
    I_949210508_1;I_949210508_2;I_671961774_1;I_671961774_2;];;

(*
 
LOC: 2002 IV, page 50
Section A17
*)

(*

Six Cases:
  (k0,k1,k2)
  (3,0,0)X
  (2,1,0)X
  (2,0,1)X
  (1,2,0)X
  (1,0,2)
  (1,1,1)
  (0,3,0)
  (0,2,1)
  (0,1,2)
  (0,0,3)

*)

(* interval verification by Ferguson *)
let I_645264496_102=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#4.0), x4, square_2t0);
((#8.0), x5, (square (#3.2)));
((#8.0), x6, (square (#3.2)))
    ] 
   ((tau_0_x x1 x2 x3 x4 x5 x6)- (pi_prime_tau 1 0 2) >. D32)`;;

(* interval verification by Ferguson *)
let I_645264496_111=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#4.0), x4, square_2t0);
(square_2t0, x5, (#8.0));
((#8.0), x6, (square (#3.2)))
    ] 
   ((tau_0_x x1 x2 x3 x4 x5 x6)- (pi_prime_tau 1 1 1) >. D32)`;;

(* interval verification by Ferguson *)
let I_645264496_030=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
(square_2t0, x4, (#8.0));
(square_2t0, x5, (#8.0));
(square_2t0, x6, (#8.0))
    ] 
   ((tau_0_x x1 x2 x3 x4 x5 x6)- (pi_prime_tau 0 3 0) >. D33)`;;

(* interval verification by Ferguson *)
let I_645264496_021=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
(square_2t0, x4, (#8.0));
(square_2t0, x5, (#8.0));
((#8.0), x6, (square (#3.2)))
    ] 
   ((tau_0_x x1 x2 x3 x4 x5 x6)- (pi_prime_tau 0 2 1) >. D33)`;;

(* interval verification by Ferguson *)
let I_645264496_012=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
(square_2t0, x4, (#8.0));
((#8.0), x5, (square (#3.2)));
((#8.0), x6, (square (#3.2)))
    ] 
   ((tau_0_x x1 x2 x3 x4 x5 x6)- (pi_prime_tau 0 1 2) >. D33)`;;

(* interval verification by Ferguson *)
let I_645264496_003=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, (square (#3.2)));
((#8.0), x5, (square (#3.2)));
((#8.0), x6, (square (#3.2)))
    ] 
   ((tau_0_x x1 x2 x3 x4 x5 x6)- (pi_prime_tau 0 0 3) >. D33)`;;




(* interval verification by Ferguson *)
let I_910154674=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((square (#2.6)), x4, (#8.0));
     ((#8.0), x5, (square (#3.2)));
     ((#4.0), x6, square_2t0)
    ]
    ( ( (tau_0_x x1 x2 x3 x4 x5 x6) +.  (--. (#0.034052))) >.  (#0.13943))`;;



(* interval verification by Ferguson *)
let I_877743345=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, square_2t0);
     ((square (#3.2)), x5, (square (#3.2)));
     ((#4.0), x6, (#4.0))
    ]
    ( ( (tau_0_x x1 x2 x3 x4 x5 x6) +.  (--. (#0.034052)) +.  (--. (#0.0066))) >.  (#0.13943))`;;


let CIVA17_852270725 = list_mk_conj 
  [  I_645264496_102;I_645264496_111;I_645264496_030;I_645264496_021;
     I_645264496_012;I_645264496_003;I_910154674;I_877743345;];;

(*

LOC: 2002 IV, page 50
Section A18

*)


(* interval verification by Ferguson *)
let I_612259047_102=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#4.0), x4, square_2t0);
((#8.0), x5, (square (#3.2)));
((#8.0), x6, (square (#3.2)))
    ] 
   ((vor_0_x x1 x2 x3 x4 x5 x6)+ (pi_prime_sigma 1 0 2) <. Z32)`;;

(* interval verification by Ferguson *)
let I_612259047_111=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#4.0), x4, square_2t0);
(square_2t0, x5, (#8.0));
((#8.0), x6, (square (#3.2)))
    ] 
   ((vor_0_x x1 x2 x3 x4 x5 x6)+ (pi_prime_sigma 1 1 1) <. Z32)`;;

(* interval verification by Ferguson *)
let I_612259047_030=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
(square_2t0, x4, (#8.0));
(square_2t0, x5, (#8.0));
(square_2t0, x6, (#8.0))
    ] 
   ((vor_0_x x1 x2 x3 x4 x5 x6)+ (pi_prime_sigma 0 3 0) <. Z33)`;;

(* interval verification by Ferguson *)
let I_612259047_021=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
(square_2t0, x4, (#8.0));
(square_2t0, x5, (#8.0));
((#8.0), x6, (square (#3.2)))
    ] 
   ((vor_0_x x1 x2 x3 x4 x5 x6)+ (pi_prime_sigma 0 2 1) <. Z33)`;;

(* interval verification by Ferguson *)
let I_612259047_012=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
(square_2t0, x4, (#8.0));
((#8.0), x5, (square (#3.2)));
((#8.0), x6, (square (#3.2)))
    ] 
   ((vor_0_x x1 x2 x3 x4 x5 x6)+ (pi_prime_sigma 0 1 2) <. Z33)`;;

(* interval verification by Ferguson *)
let I_612259047_003=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x2, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, (square (#3.2)));
((#8.0), x5, (square (#3.2)));
((#8.0), x6, (square (#3.2)))
    ] 
   ((vor_0_x x1 x2 x3 x4 x5 x6)+ (pi_prime_sigma 0 0 3) <. Z33)`;;


let CIVA18_819209129 = list_mk_conj 
  [  I_612259047_102;I_612259047_111;I_612259047_030;I_612259047_021;
     I_612259047_012;I_612259047_003;];;

(*
 
LOC: 2002 IV, page 50
Section A19

Note: I might need to add some convexity results to make what
is stated below consistent with what is asserted in 2002-IV.

Without loss of generality in Section 19, we can divide the
quad along the shorter diagonal.
*)

(* interval verification by Ferguson *)
let I_357477295_1=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, (square (#3.2)));
(square_2t0, x5, (#8.0))
    ] 
   (((tau_0_x x1 (#4.0) x3 x4 x5 (#4.0))+ 
    (tau_0_x (#4.0) (#4.0) x3 x4 (#4.0) (#4.0)) >. (#0.235)) \/
  (cross_diag_x x1 (#4.0) x3 x4 x5 (#4.0) (#4.0) (#4.0) (#4.0) 
       <. (sqrt x4)))`;;

(* interval verification by Ferguson *)
let I_357477295_2=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, (square (#3.2)));
((#8.0), x5, (square (#3.2)))
    ] 
   (((tau_0_x x1 (#4.0) x3 x4 x5 (#4.0))+ 
    (tau_0_x (#4.0) (#4.0) x3 x4 (#4.0) (#4.0)) >. (#0.3109)) \/
  (cross_diag_x x1 (#4.0) x3 x4 x5 (#4.0) (#4.0) (#4.0) (#4.0) 
       <. (sqrt x4)))`;;

(* interval verification by Ferguson *)
let I_357477295_3=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, (square (#3.2)));
(square_2t0, x5, (#8.0))
    ] 
   (((vor_0_x x1 (#4.0) x3 x4 x5 (#4.0))+ 
    (vor_0_x (#4.0) (#4.0) x3 x4 (#4.0) (#4.0)) <. (--(#0.075))) \/
  (cross_diag_x x1 (#4.0) x3 x4 x5 (#4.0) (#4.0) (#4.0) (#4.0) 
       <. (sqrt x4)))`;;

(* interval verification by Ferguson *)
let I_357477295_4=
  all_forall `ineq
[((#4.0), x1, square_2t0);
((#4.0), x3, square_2t0);
((#8.0), x4, (square (#3.2)));
((#8.0), x5, (square (#3.2)))
    ] 
   (((vor_0_x x1 (#4.0) x3 x4 x5 (#4.0))+ 
    (vor_0_x (#4.0) (#4.0) x3 x4 (#4.0) (#4.0)) <. (--(#0.137))) \/
  (cross_diag_x x1 (#4.0) x3 x4 x5 (#4.0) (#4.0) (#4.0) (#4.0) 
       <. (sqrt x4)))`;;

let CIVA19_128523606 = list_mk_conj 
  [  I_357477295_1;I_357477295_2;I_357477295_3;I_357477295_4;];;

(*
 
LOC: 2002 IV, page 50--51
Section A20

Let $Q$ be a quadrilateral subcluster
whose edges are described by the vector
    $$(2,2,a_2,2,2,b_3,a_4,b_4).$$
Assume $b_4\ge b_3$, $b_4\in\{2t_0,2\sqrt2\}$,
$b_3\in\{2,2t_0,2\sqrt2\}$, $a_2,a_4\in\{2,2t_0\}$.  Assume that the
diagonal between corners $1$ and $3$ has length in $[2\sqrt2,3.2]$, and
that the other diagonal has length $\ge3.2$.  Let $k_0$, $k_1$, $k_2$ be
the number of $b_i$ equal to $2$, $2t_0$, $2\sqrt2$, respectively. If
$b_4=2t_0$ and  $b_3=2$, no such subcluster exists (the reader can check
that $\Delta(4,4,x_3,4,2t_0^2,x_6)<0$ under these conditions), and we
exclude this case.

b4 b3   k0 k1 k2
++ ++    0 0  2
++  +    0 1  1
++  0    1 0  1
 +  +    0 2  0
 +  0    1 1  0 X
 
Need Z42 and Z41 
     D42 and D41
*)

(* b4 b3 a2 a4 *)
(* interval verification by Ferguson *)
let I_193776341_GEN=
   `(\ b4 b3 a2 a4 k0 k1 k2. (
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[
((#8.0), (x4:real), (square (#3.2)))]
   (((vor_0_x x1 x2 x3 x4 x5 x6) +
    (vor_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) <.
    ((if (k1+k2 = 2) then Z42 else Z41) -
    ((#0.009)*(&.k2) + (&. (k0+ 2 *k2))*((#0.008)/(#3.0))))
    )
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))))`;;

(* interval verification by Ferguson *)
let I_193776341_1= 
 all_forall (list_mk_comb(I_193776341_GEN,
   [`#8.0`;`#8.0`;`#4.0`;`#4.0`;`0`;`0`;`2`]));;

(* interval verification by Ferguson *)
let I_193776341_2= 
 all_forall (list_mk_comb(I_193776341_GEN,
   [`#8.0`;`#8.0`;`#4.0`;`square_2t0`;`0`;`0`;`2`]));;

(* interval verification by Ferguson *)
let I_193776341_3=
  all_forall (list_mk_comb(I_193776341_GEN,
   [`#8.0`;`#8.0`;`square_2t0`;`square_2t0`;`0`;`0`;`2`]));;

(* interval verification by Ferguson *)
let I_193776341_4=
  all_forall (list_mk_comb(I_193776341_GEN,
   [`#8.0`;`#8.0`;`square_2t0`;`#4.0`;`0`;`0`;`2`]));;

(* interval verification by Ferguson *)
let I_193776341_5=
  all_forall (list_mk_comb(I_193776341_GEN,
   [`#8.0`;`square_2t0`;`#4.0`;`#4.0`;`0`;`1`;`1`]));;

(* interval verification by Ferguson *)
let I_193776341_6=
  all_forall (list_mk_comb(I_193776341_GEN,
   [`#8.0`;`square_2t0`;`#4.0`;`square_2t0`;`0`;`1`;`1`]));;

(* interval verification by Ferguson *)
let I_193776341_7=
  all_forall (list_mk_comb(I_193776341_GEN,
   [`#8.0`;`square_2t0`;`square_2t0`;`square_2t0`;`0`;`1`;`1`]));;

(* interval verification by Ferguson *)
let I_193776341_8=
  all_forall (list_mk_comb(I_193776341_GEN,
   [`#8.0`;`square_2t0`;`square_2t0`;`#4.0`;`0`;`1`;`1`]));;

(* interval verification by Ferguson *)
let I_193776341_9=
  all_forall (list_mk_comb(I_193776341_GEN,
   [`#8.0`;`#4.0`;`#4.0`;`#4.0`;`1`;`0`;`1`]));;

(* interval verification by Ferguson *)
let I_193776341_10=
  all_forall (list_mk_comb(I_193776341_GEN,
   [`#8.0`;`#4.0`;`#4.0`;`square_2t0`;`1`;`0`;`1`]));;

(* interval verification by Ferguson *)
let I_193776341_11=
  all_forall (list_mk_comb(I_193776341_GEN,
   [`#8.0`;`#4.0`;`square_2t0`;`square_2t0`;`1`;`0`;`1`]));;

(* interval verification by Ferguson *)
let I_193776341_12=
  all_forall (list_mk_comb(I_193776341_GEN,
   [`#8.0`;`#4.0`;`square_2t0`;`#4.0`;`1`;`0`;`1`]));;

(* interval verification by Ferguson *)
let I_193776341_13= all_forall (list_mk_comb(I_193776341_GEN,
   [`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`0`;`2`;`0`]));;

(* interval verification by Ferguson *)
let I_193776341_14=
  all_forall (list_mk_comb(I_193776341_GEN,
   [`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`0`;`2`;`0`]));;

(* interval verification by Ferguson *)
let I_193776341_15=
  all_forall (list_mk_comb(I_193776341_GEN,
   [`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`0`;`2`;`0`]));;

(* interval verification by Ferguson *)
let I_193776341_16=
  all_forall (list_mk_comb(I_193776341_GEN,
   [`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`0`;`2`;`0`]));;

(* interval verification by Ferguson *)
let I_898647773_GEN=
   `(\ b4 b3 a2 a4 k0 k1 k2. (
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[
((#8.0), (x4:real), (square (#3.2)))]
   (((tau_0_x x1 x2 x3 x4 x5 x6) +
    (tau_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) >.
    ((if (k1+k2 = 2) then D42 else D41) + (#0.04683) +
    ((#0.0066)*(&.k2) + ((&. (k0+ 2 *k2))-(#3.0))*((#0.008)/(#3.0))))
    )
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))))`;;


(* interval verification by Ferguson *)
let I_898647773_1=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`#8.0`;`#8.0`;`#4.0`;`#4.0`;`0`;`0`;`2`]));;

(* interval verification by Ferguson *)
let I_898647773_2= 
 all_forall (list_mk_comb(I_898647773_GEN,
   [`#8.0`;`#8.0`;`#4.0`;`square_2t0`;`0`;`0`;`2`]));;

(* interval verification by Ferguson *)
let I_898647773_3=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`#8.0`;`#8.0`;`square_2t0`;`square_2t0`;`0`;`0`;`2`]));;

(* interval verification by Ferguson *)
let I_898647773_4=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`#8.0`;`#8.0`;`square_2t0`;`#4.0`;`0`;`0`;`2`]));;

(* interval verification by Ferguson *)
let I_898647773_5=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`#8.0`;`square_2t0`;`#4.0`;`#4.0`;`0`;`1`;`1`]));;

(* interval verification by Ferguson *)
let I_898647773_6= all_forall (list_mk_comb(I_898647773_GEN,
   [`#8.0`;`square_2t0`;`#4.0`;`square_2t0`;`0`;`1`;`1`]));;

(* interval verification by Ferguson *)
let I_898647773_7=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`#8.0`;`square_2t0`;`square_2t0`;`square_2t0`;`0`;`1`;`1`]));;

(* interval verification by Ferguson *)
let I_898647773_8=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`#8.0`;`square_2t0`;`square_2t0`;`#4.0`;`0`;`1`;`1`]));;

(* interval verification by Ferguson *)
let I_898647773_9=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`#8.0`;`#4.0`;`#4.0`;`#4.0`;`1`;`0`;`1`]));;

(* interval verification by Ferguson *)
let I_898647773_10=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`#8.0`;`#4.0`;`#4.0`;`square_2t0`;`1`;`0`;`1`]));;

(* interval verification by Ferguson *)
let I_898647773_11=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`#8.0`;`#4.0`;`square_2t0`;`square_2t0`;`1`;`0`;`1`]));;

(* interval verification by Ferguson *)
let I_898647773_12=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`#8.0`;`#4.0`;`square_2t0`;`#4.0`;`1`;`0`;`1`]));;

(* interval verification by Ferguson *)
let I_898647773_13=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`square_2t0`;`square_2t0`;`#4.0`;`#4.0`;`0`;`2`;`0`]));;

(* interval verification by Ferguson *)
let I_898647773_14=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`square_2t0`;`square_2t0`;`#4.0`;`square_2t0`;`0`;`2`;`0`]));;

(* interval verification by Ferguson *)
let I_898647773_15=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`square_2t0`;`square_2t0`;`square_2t0`;`square_2t0`;`0`;`2`;`0`]));;

(* interval verification by Ferguson *)
let I_898647773_16=
  all_forall (list_mk_comb(I_898647773_GEN,
   [`square_2t0`;`square_2t0`;`square_2t0`;`#4.0`;`0`;`2`;`0`]));;

(* STM 1/13/08.  Added parentheses.  This was not parsing correctly *)
(* interval verification by Ferguson *)
let I_844634710_1=
  all_forall `
let a2 = (#4.0) in
let a4 = (#4.0) in
let b4 = (#8.0) in
let b3 = (#8.0) in
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[
((#8.0), (x4:real), (square (#3.2)))]
   ((((vor_0_x x1 x2 x3 x4 x5 x6) +
    (vor_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) <.
    Z42 - (#0.0461) - (#0.009) - (&.2)*(#0.008)))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))`;;

(* STM 1/13/08.  Added parentheses.  This was not parsing correctly *)
(* interval verification by Ferguson *)
let I_844634710_2=
  all_forall `
let a2 = (square_2t0) in
let a4 = (#4.0) in
let b4 = (#8.0) in
let b3 = (#8.0) in
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[
((#8.0), (x4:real), (square (#3.2)))]
   ((((vor_0_x x1 x2 x3 x4 x5 x6) +
    (vor_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) <.
    Z42 - (#0.0461) - (#0.009) - (&.2)*(#0.008)))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))`;;

(* STM 1/13/08.  Added parentheses.  This was not parsing correctly *)
(* interval verification by Ferguson *)
let I_844634710_3=
  all_forall `
let a2 = (#4.0) in
let a4 = (#4.0) in
let b4 = (#8.0) in
let b3 = (square_2t0) in
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[
((#8.0), (x4:real), (square (#3.2)))]
   ((((vor_0_x x1 x2 x3 x4 x5 x6) +
    (vor_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) <.
    Z42 - (#0.0461) - (#0.009) - (&.2)*(#0.008)))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))`;;

(* STM 1/13/08.  Added parentheses.  This was not parsing correctly *)
(* interval verification by Ferguson *)
let I_844634710_4=
  all_forall `
let a2 = (square_2t0) in
let a4 = (#4.0) in
let b4 = (#8.0) in
let b3 = (square_2t0) in
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[((#8.0), (x4:real), (square (#3.2)))]
   ((((vor_0_x x1 x2 x3 x4 x5 x6) +
    (vor_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) <.
    (Z42 - (#0.0461) - (#0.009) - (&.2)*(#0.008))))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))`;;


(* interval verification by Ferguson *)
let I_328845176_1=
  all_forall `
let a2 = (#4.0) in
let a4 = (#4.0) in
let b4 = (#8.0) in
let b3 = (#8.0) in
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[
((#8.0), (x4:real), (square (#3.2)))]
   ((((tau_0_x x1 x2 x3 x4 x5 x6) +
    (tau_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) >.
    D51 + (#0.04683)+(#0.008)+(&.2)*(#0.066)))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))`;;

(* interval verification by Ferguson *)
let I_328845176_2=
  all_forall `
let a2 = (square_2t0) in
let a4 = (#4.0) in
let b4 = (#8.0) in
let b3 = (#8.0) in
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[
((#8.0), (x4:real), (square (#3.2)))]
   ((((tau_0_x x1 x2 x3 x4 x5 x6) +
    (tau_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) >.
    D51 + (#0.04683)+(#0.008)+(&.2)*(#0.066)))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))`;;

(* STM 1/13/08.  Added parentheses.  This was not parsing correctly *)
(* interval verification by Ferguson *)
let I_328845176_3=
  all_forall `
let a2 = (#4.0) in
let a4 = (#4.0) in
let b4 = (#8.0) in
let b3 = (square_2t0) in
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[
((#8.0), (x4:real), (square (#3.2)))]
   ((((tau_0_x x1 x2 x3 x4 x5 x6) +
    (tau_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) >.
    D51 + (#0.04683)+(#0.008)+(&.2)*(#0.066)))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))`;;

(* STM 1/13/08.  Added parentheses.  This was not parsing correctly *)
(* interval verification by Ferguson *)
let I_328845176_4=
  all_forall `
let a2 = (square_2t0) in
let a4 = (#4.0) in
let b4 = (#8.0) in
let b3 = (square_2t0) in
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[((#8.0), (x4:real), (square (#3.2)))]
   ((((tau_0_x x1 x2 x3 x4 x5 x6) +
    (tau_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) >.
    D51 + (#0.04683)+(#0.008)+(&.2)*(#0.066)))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))`;;


(* interval verification by Ferguson *)
let I_233273785_1=
  all_forall `
let a2 = (#4.0) in
let a4 = (#4.0) in
let b4 = (#8.0) in
let b3 = (#4.0) in
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[
((#8.0), (x4:real), (square (#3.2)))]
   (((vor_0_x x1 x2 x3 x4 x5 x6) +
    (vor_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) <.
    s5 - (#0.0461) - (#0.008))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))`;;

(* interval verification by Ferguson *)
let I_233273785_2=
  all_forall `
let a2 = (square_2t0) in
let a4 = (#4.0) in
let b4 = (#8.0) in
let b3 = (#4.0) in
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[
((#8.0), (x4:real), (square (#3.2)))]
   (((vor_0_x x1 x2 x3 x4 x5 x6) +
    (vor_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) <.
    s5 - (#0.0461) - (#0.008))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))`;;

(* interval verification by Ferguson *)
let I_96695550_1=
  all_forall `
let a2 = (#4.0) in
let a4 = (#4.0) in
let b4 = (#8.0) in
let b3 = (#4.0) in
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[
((#8.0), (x4:real), (square (#3.2)))]
   (((tau_0_x x1 x2 x3 x4 x5 x6) +
    (tau_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) >.
      t5 + (#0.008))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))`;;

(* interval verification by Ferguson *)
let I_96695550_2=
  all_forall `
let a2 = (square_2t0) in
let a4 = (#4.0) in
let b4 = (#8.0) in
let b3 = (#4.0) in
let x1 = (a4) in
let x2 = (#4.0) in
let x3 = (#4.0) in
let x5 = (b3) in
let x6 = (b4) in 
 (ineq
[
((#8.0), (x4:real), (square (#3.2)))]
   (((tau_0_x x1 x2 x3 x4 x5 x6) +
    (tau_0_x (a2) x2 x3 x4 (#4.0) (#4.0)) >.
      t5 + (#0.008))
   \/
  (cross_diag_x x1 x2 x3 x4 x5 x6 a2 (#4.0) (#4.0)
       <. ((#3.2)))))`;;

let CIVA20_874876755 = list_mk_conj 
 [  I_193776341_1;I_193776341_2;I_193776341_3;I_193776341_4;
    I_193776341_5;I_193776341_6;I_193776341_7;I_193776341_8;
    I_193776341_9;I_193776341_10;I_193776341_11;I_193776341_12;
    I_193776341_13;I_193776341_14;I_193776341_15;I_193776341_16;
    I_898647773_1;I_898647773_2;I_898647773_3;I_898647773_4;
    I_898647773_5;I_898647773_6;I_898647773_7;I_898647773_8;
    I_898647773_9;I_898647773_10;I_898647773_11;I_898647773_12;
    I_898647773_13;I_898647773_14;I_898647773_15;I_898647773_16;
    I_844634710_1;I_844634710_2;I_844634710_3;I_844634710_4;
    I_328845176_1;I_328845176_2;I_328845176_3;I_328845176_4;
    I_233273785_1;I_233273785_2;I_96695550_1;I_96695550_2;];;
(*
 
LOC: 2002 IV, page 51
Section A21
*)



(* interval verification by Ferguson *)
let I_275286804=
   all_forall `ineq 
    [((#8.0), x4, (square (#3.2)));
     ((#8.0), x4', (square (#3.2)))
    ]
    ( ( 
   (vor_0_x (#4.0) (#4.0) (#4.0) x4 (#4.0) (#4.0)) +.  
   (vor_0_x (#4.0) (#4.0) (#4.0) x4' (#4.0) (#4.0)) +.  
    (vor_0_x (#4.0) (#4.0) (#4.0) x4 x4' (#4.0))) <. 
            ( (--. (#0.05704)) +.  (--. (#0.008))))`;;



(* interval verification by Ferguson *)
let I_627654828=
   all_forall `ineq 
    [((#8.0), x4, (square (#3.2)));
     ((#8.0), x4', (square (#3.2)))
    ]
    ( ( (tau_0_x (#4.0) (#4.0) (#4.0) x4 (#4.0) (#4.0)) +.  
    (tau_0_x (#4.0) (#4.0) (#4.0) x4' (#4.0) (#4.0)) +.  
    (tau_0_x (#4.0) (#4.0) (#4.0) x4 x4' (#4.0))) >. 
            ( (#0.27113) +.  (#0.008)))`;;



(* interval verification by Ferguson *)
let I_995177961=
   all_forall `ineq 
    [((#8.0), x4, (square (#3.2)));
     ((#8.0), x5, (square (#3.2)));
     ((#8.0), x6, (square (#3.2)))
    ]
    ( (vor_0_x (#4.0) (#4.0) (#4.0) x4 x5 x6) <.  
   ( (  (--. (#2.0)) *.  (#0.008)) +.  (--. (#0.11408)) +.  
     (  (--. (#3.0)) *.  (#0.0461))))`;;



(* interval verification by Ferguson *)
let I_735892048=
   all_forall `ineq 
    [((#8.0), x4, (square (#3.2)));
     ((#8.0), x5, (square (#3.2)));
     ((#8.0), x6, (square (#3.2)))
    ]
    ( (tau_0_x (#4.0) (#4.0) (#4.0) x4 x5 x6) >.  
     ( (#0.41056) +.  (#0.06688)))`;;

let CIVA21_692155251 = list_mk_conj 
  [  I_275286804;I_627654828;I_995177961;I_735892048;];;
(*
 
LOC: 2002 IV, page 51
Section A22

Note from text:
In $\A_{22}$ and $\A_{23}$, $y_1\in [2t_0,2\sqrt2]$,
$y_4\in[2\sqrt2,3.2]$, and $\dih<2.46$. $\vor_0(Q)$ denotes the
truncated Voronoi function on the union of an anchored simplex and an
adjacent special simplex. Let $S'$ be the special simplex.  By
deformations, $y_1(S')\in\{2,2t_0\}$.  If $y_1(S')=2t_0$, the
verifications follow from $\A_6$ and $\vor_0(S')\le0$.  We may assume
that $y_1(S')=2$.  Also by deformations, $y_5(S')=y_6(S')=2$.

*)


(* ineq changed from weak to strick on dih *)
(* interval verification by Ferguson *)
let I_53502142= 
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (((vor_0_x x1 x2 x3 x4 x5 x6) + (vor_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))
      <. (--(#3.58) + (#2.28501)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* ineq changed from weak to strick on dih *)
(* interval verification by Ferguson *)
let I_134398524=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (((vor_0_x x1 x2 x3 x4 x5 x6) + (vor_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))
      <. (--(#2.715) + (#1.67382)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* ineq changed from weak to strick on dih *)
(* interval verification by Ferguson *)
let I_371491817=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (((vor_0_x x1 x2 x3 x4 x5 x6) + (vor_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))
      <. (--(#1.517) + (#0.8285)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* ineq changed from weak to strick on dih *)
(* interval verification by Ferguson *)
let I_832922998=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (((vor_0_x x1 x2 x3 x4 x5 x6) + (vor_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))
      <. (--(#0.858) + (#0.390925)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* ineq changed from weak to strick on dih *)
(* interval verification by Ferguson *)
let I_724796759=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (((vor_0_x x1 x2 x3 x4 x5 x6) + (vor_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))
      <. (--(#0.358) + (#0.009)+ (#0.12012)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* ineq changed from weak to strick on dih *)
(* interval verification by Ferguson *)
let I_431940343=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4, (square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (((vor_0_x x1 x2 x3 x4 x5 x6) + (vor_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))
      <. (--(#0.186) + (#0.009)+ (#0.0501)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;




(* interval verification by Ferguson *)
let I_980721294=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  ( (  (--. (#3.58)) /  (#2.0)) +.  (  (#2.28501) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



(* interval verification by Ferguson *)
let I_989564937=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  ( (  (--. (#2.715)) /  (#2.0)) +.  (  (#1.67382) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



(* interval verification by Ferguson *)
let I_263355808=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  ( (  (--. (#1.517)) /  (#2.0)) +.  (  (#0.8285) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



(* interval verification by Ferguson *)
let I_445132132=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <.  ( (  (--. (#0.858)) /  (#2.0)) +.  (  (#0.390925) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;




(* interval verification by Ferguson *)
let I_806767374=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <. 
            ( (  ( (--. (#0.358)) +.  (#0.009)) /  (#2.0)) +.  (  (#0.12012) *.  (dih_x x1 x2 x3 x4 x5 x6)) +. 
            (  (#0.2) *.  ( (dih_x x1 x2 x3 x4 x5 x6) +.  (--. (#1.23))))))`;;




(* interval verification by Ferguson *)
let I_511038592=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_0_x x1 x2 x3 x4 x5 x6) <. 
            ( (  ( (--. (#0.186)) +.  (#0.009)) /  (#2.0)) +.  (  (#0.0501) *.  (dih_x x1 x2 x3 x4 x5 x6)) +. 
            (  (#0.2) *.  ( (dih_x x1 x2 x3 x4 x5 x6) +.  (--. (#1.23))))))`;;

let CIVA22_485049042 = list_mk_conj 
  [  I_53502142;I_134398524;I_371491817;I_832922998;
    I_724796759;I_431940343;I_980721294;I_989564937;
    I_263355808;I_445132132;I_806767374;I_511038592;];;

(*
 
LOC: 2002 IV, page 51--52
Section A23

Note from text (appearing after the first seven) :

Let $S'$ be the special simplex.  By deformations, we have
$y_5(S')=y_6(S')=2$, and $y_1(S')\in\{2,2t_0\}$.  If $y_1(S')=2t_0$, and
$y_4(S')\le3$, the inequalities listed above follow from Section~$\A_7$
and the inequality #8     \refno{66753311}

Similarly, the result follows if $y_2$ or $y_3\ge2.2$ from the
inequality  #9   \refno{762922223}


Because of these reductions, we may assume in the first batch of
inequalities of $\A_{23}$ that when $y_1(S')\ne2$, we have that
$y_1(S')=2t_0$, $y_5(S')=y_6(S')=2$, $y_4\in[3,3.2]$,
$y_2(S'),y_3(S')\le2.2$.  In all but {\tt (371464244)} and {\tt
(657011065)}, if $y_1(S')=2t_0$, we prove the inequality with
$\tau_0(S')$ replaced with its lower bound $0$.

Again if the cross-diagonal is $2t_0$, we break $Q$ in the other
direction. Let $S''$ be an upright quarter with $y_5=2t_0$. Set $\tau_0
= \tau_0(S'')$. We have ...

*)





(* interval verification by Ferguson *)
let I_4591018_1=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#3.48) + (#2.1747)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* interval verification by Ferguson *)
let I_193728878_1=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#3.06) + (#1.87427)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* interval verification by Ferguson *)
let I_2724096_1=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#1.58) + (#0.83046)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* interval verification by Ferguson *)
let I_213514168_1=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#1.06) + (#0.48263)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* interval verification by Ferguson *)
let I_750768322_1=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#0.83) + (#0.34833)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* interval verification by Ferguson *)
let I_371464244_1=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#0.5) + (#0.1694)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* interval verification by Ferguson *)
let I_657011065_1=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (#4.0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#0.29) + (#0.0014)+ (#0.0822)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;


(* interval verification by Ferguson *)
let I_4591018_2=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, (square (#2.2)));
     ((#4.0), x3, (square (#2.2)));
     ((square (#3.0)), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (square_2t0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#3.48) + (#2.1747)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* interval verification by Ferguson *)
let I_193728878_2=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, (square (#2.2)));
     ((#4.0), x3, (square (#2.2)));
     ((square (#3.0)), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (square_2t0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#3.06) + (#1.87427)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* interval verification by Ferguson *)
let I_2724096_2=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, (square (#2.2)));
     ((#4.0), x3, (square (#2.2)));
     ((square (#3.0)), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (square_2t0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#1.58) + (#0.83046)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* interval verification by Ferguson *)
let I_213514168_2=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, (square (#2.2)));
     ((#4.0), x3, (square (#2.2)));
     ((square (#3.0)), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (square_2t0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#1.06) + (#0.48263)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* interval verification by Ferguson *)
let I_750768322_2=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, (square (#2.2)));
     ((#4.0), x3, (square (#2.2)));
     ((square (#3.0)), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (square_2t0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#0.83) + (#0.34833)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* interval verification by Ferguson *)
let I_371464244_2=
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, (square (#2.2)));
     ((#4.0), x3, (square (#2.2)));
     ((square (#3.0)), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (square_2t0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#0.5) + (#0.1694)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;

(* interval verification by Ferguson *)
let I_657011065_2 =
   all_forall `ineq
   [(square_2t0,x1,(#8.0));
    ((#4.0), x2, (square (#2.2)));
     ((#4.0), x3, (square (#2.2)));
     ((square (#3.0)), x4,(square (#3.2)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
   ]
   (
   ((--(tau_0_x x1 x2 x3 x4 x5 x6) ) -
    (tau_0_x (square_2t0) x2 x3 x4 (#4.0) (#4.0))
    + (#0.06585) <.
    (--(#0.29) + (#0.0014)+ (#0.0822)*(dih_x x1 x2 x3 x4 x5 x6))) \/
    (dih_x x1 x2 x3 x4 x5 x6 >. (#2.46)))`;;


(* calcs 8 --9 *)
(* interval verification by Ferguson *)
let I_55753311=
   all_forall `ineq
   [ ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#8.0), x4,(square (#3.0)))
   ]
   (
     (tau_0_x (square_2t0) x2 x3 x4 (#4.0) (#4.0) ) >. (#0.06585)
    )`;;

(* interval verification by Ferguson *)
let I_762922223=
   all_forall `ineq
   [ ((#4.0), x2, (square (#2.2)));
     ((#4.0), x3, square_2t0);
     ((square (#3.0)), x4,(square (#3.2)))
   ]
   (
     (tau_0_x (square_2t0) x2 x3 x4 (#4.0) (#4.0) ) >. (#0.06585)
    )`;;


(* calcs 10 -- 16 *)
(* interval verification by Ferguson *)
let I_953023504=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) +.  
  (  (#0.06585) /  (#2.0))) <. 
            ( (  (--. (#3.48)) /  (#2.0)) +.  
       (  (#2.1747) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;

(* interval verification by Ferguson *)
let I_887276655=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) +.  
       (  (#0.06585) /  (#2.0))) <. 
            ( (  (--. (#3.06)) /  (#2.0)) +.  
   (  (#1.87427) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;

(* interval verification by Ferguson *)
let I_246315515=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) +.  
   (  (#0.06585) /  (#2.0))) <. 
            ( (  (--. (#1.58)) /  (#2.0)) +.  
      (  (#0.83046) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;

(* interval verification by Ferguson *)
let I_784421604=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) +.  
   (  (#0.06585) /  (#2.0))) <. 
            ( (  (--. (#1.06)) /  (#2.0)) +.  
   (  (#0.48263) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



(* interval verification by Ferguson *)
let I_258632246=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) +.  
    (  (#0.06585) /  (#2.0))) <. 
            ( (  (--. (#0.83)) /  (#2.0)) +.  
   (  (#0.34833) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



(* interval verification by Ferguson *)
let I_404164527=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) +.  
    (  (#0.06585) /  (#2.0))) <. 
            ( (  (--. (#0.50)) /  (#2.0)) +.  
     (  (#0.1694) *.  (dih_x x1 x2 x3 x4 x5 x6)) +. 
            (  (#0.03) *.  ( (dih_x x1 x2 x3 x4 x5 x6) +.  
       (--. (#1.23))))))`;;



(* interval verification by Ferguson *)
let I_163088471=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (( --. ) (tau_0_x x1 x2 x3 x4 x5 x6)) +.  
    (  (#0.06585) /  (#2.0))) <. 
            ( (  (--. (#0.29)) /  (#2.0)) +.  
      (  (#0.0014) /  (#2.0)) +.  
      (  (#0.0822) *.  (dih_x x1 x2 x3 x4 x5 x6)) +. 
            (  (#0.2) *.  ( (dih_x x1 x2 x3 x4 x5 x6) +.  
       (--. (#1.23))))))`;;

let CIVA23_209361863= list_mk_conj 
  [  I_4591018_1;I_193728878_1;I_2724096_1;I_213514168_1;
     I_750768322_1;I_371464244_1;I_657011065_1;I_4591018_2;
     I_193728878_2;I_2724096_2;I_213514168_2;I_750768322_2;
     I_371464244_2;I_657011065_2 ;I_55753311;I_762922223;
     I_953023504;I_887276655;I_246315515;I_784421604;
     I_258632246;I_404164527;I_163088471;];;
(*
 
LOC: 2002 IV, page 52
Section A24
*)


(* interval verification in partK.cc *)
(* interval verification by Ferguson *)
let I_968721007=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, (#4.0));
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, (#4.0));
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, (square (#2.75)))
    ]
    ( ( (tau_0_x x1 x2 x3 x4 x5 x6) +.  
   (  (#0.0822) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (#0.159))`;;



(* interval verification in partK.cc *)
(* interval verification by Ferguson *)
let I_783968228=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     (square_2t0, x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, (#4.0));
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, square_4t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.23))`;;



(* interval verification in partK.cc *)
(* interval verification by Ferguson *)
let I_745174731=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, (#4.0));
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, (#4.0));
     ((#4.0), x5, square_2t0);
     ((square (#2.75)), x6, square_4t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.23))`;;

let CIVA24_835344007= list_mk_conj 
  [  I_968721007;I_783968228;I_745174731;];;

(*
 
 
LOC: 2002 III, page 14.
Sec. 10. Group 1.
*)



let J_586468779=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <=.  pt)`;;



let J_984463800=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.874445))`;;



let J_208809199=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#0.8638))`;;



let J_995444025=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.37642101)) *.  (sol_x x1 x2 x3 x4 x5 x6)) +.  (#0.287389)))`;;



let J_49987949=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (#0.446634) *.  (sol_x x1 x2 x3 x4 x5 x6)) +.  (--. (#0.190249))))`;;



let J_825495074=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.419351)) *.  (sol_x x1 x2 x3 x4 x5 x6)) +.  (#0.2856354) +.  (#0.001)))`;;



(*
SKIP equation 7.  (sigma(quad) <= 0)
This is proved as a theorem and is not really an
interval arithmetic result.
*)

(*
 
LOC: 2002 III, page 14.
Group_2
*)


let J_544014470=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sol_x x1 x2 x3 x4 x5 x6) >. 
            ( (#0.551285) +.  (  (#0.199235) *.  ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6) +.  (--. (#6.0)))) +. 
            (  (--. (#0.377076)) *.  ( (sqrt x1) +.  (sqrt x2) +.  (sqrt x3) +.  (--. (#6.0))))))`;;



let J_382430711=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sol_x x1 x2 x3 x4 x5 x6) <. 
            ( (#0.551286) +.  (  (#0.320937) *.  ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6) +.  (--. (#6.0)))) +. 
            (  (--. (#0.152679)) *.  ( (sqrt x1) +.  (sqrt x2) +.  (sqrt x3) +.  (--. (#6.0))))))`;;



let J_568731327=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) >. 
            ( (#1.23095) +.  (  (--. (#0.359894)) *.  ( (sqrt x2) +.  (sqrt x3) +.  (sqrt x5) +.  (sqrt x6) +.  (--. (#8.0)))) +. 
            (  (#0.003) *.  ( (sqrt x1) +.  (--. (#2.0)))) +.  (  (#0.685) *.  ( (sqrt x4) +.  (--. (#2.0))))))`;;




let J_507227930=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <. 
            ( (#1.23096) +.  (  (--. (#0.153598)) *.  ( (sqrt x2) +.  (sqrt x3) +.  (sqrt x5) +.  (sqrt x6) +.  (--. (#8.0)))) +. 
            (  (#0.498) *.  ( (sqrt x1) +.  (--. (#2.0)))) +.  (  (#0.76446) *.  ( (sqrt x4) +.  (--. (#2.0))))))`;;



let J_789045970=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (#0.0553737) +. 
            (  (--. (#0.10857)) *.  ( (sqrt x1) +.  (sqrt x2) +.  (sqrt x3) +.  (sqrt x4) +.  (sqrt x5) +.  (sqrt x6) +.  (--. (#12.0))))))`;;



let J_710947756=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) +.  (  (#0.419351) *.  (sol_x x1 x2 x3 x4 x5 x6))) <. 
            ( (#0.28665) +.  (  (--. (#0.2)) *.  ( (sqrt x1) +.  (sqrt x2) +.  (sqrt x3) +.  (--. (#6.0))))))`;;



let J_649712615=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma1_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (#0.000001) +.  (  (--. (#0.129119)) *.  ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6) +.  (--. (#6.0)))) +. 
            (  (--. (#0.0845696)) *.  ( (sqrt x1) +.  (sqrt x2) +.  (sqrt x3) +.  (--. (#6.0))))))`;;


(*
 
LOC: 2002 III, page 14--15
Sec. 10, Group_3:
*)

(* interval verification in part3.cc, but labeled there as C619245724 *)
let J_539256862=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (#0.37898) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (--. (#0.4111))))`;;


(* interval verification in part3.cc, but labeled there as C678284947 *)
let J_864218323=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.142)) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (#0.23021)))`;;


(* interval verification in part3.cc, but labeled there as C970731712 *)
let J_776305271=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.3302)) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (#0.5353)))`;;


(* interval verification in part3.cc, but labeled there as C921602098 *)
let J_927432550=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma1_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (#0.3897) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (--. (#0.4666))))`;;


(* interval verification in part3.cc, but labeled there as C338482233 *)
let J_221945658=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma1_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (#0.2993) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (--. (#0.3683))))`;;


(* interval verification in part3.cc, but labeled there as C47923787 *)
let J_53415898=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma1_qrtet_x x1 x2 x3 x4 x5 x6) <=.  (#0.0))`;;


(* interval verification in part3.cc, but labeled there as C156673846 *)
let J_106537269=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma1_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.1689)) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (#0.208)))`;;


(* interval verification in part3.cc, but labeled there as C363044842 *)
let J_254627291=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma1_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.2529)) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (#0.3442)))`;;


(* interval verification in part3.cc, but labeled there as C68229886 *)
let J_170403135=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma32_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (#0.4233) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (--. (#0.5974))))`;;


(* interval verification in part3.cc, but labeled there as C996335124 *)
let J_802409438=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma32_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (#0.1083) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (--. (#0.255))))`;;


(* interval verification in part3.cc, but labeled there as C722658871 *)
let J_195296574=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma32_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.0953)) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (--. (#0.0045))))`;;


(* interval verification in part3.cc, but labeled there as C226224557  *)
let J_16189133=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma32_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.1966)) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (#0.1369)))`;;


(* interval verification in part3.cc, but labeled there as C914585134 *)
let J_584511898=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.419351)) *.  (sol_x x1 x2 x3 x4 x5 x6)) +. 
               (  (#0.796456) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (--. (#0.5786316))))`;;


(* interval verification in part3.cc, but labeled there as C296182719 *)
let J_98170671=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.419351)) *.  (sol_x x1 x2 x3 x4 x5 x6)) +. 
               (  (#0.0610397) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (#0.211419)))`;;


(* interval verification in part3.cc, but labeled there as C538860011 *)
let J_868828815=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.419351)) *.  (sol_x x1 x2 x3 x4 x5 x6)) +. 
               (  (--. (#0.0162028)) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (#0.308526)))`;;


(* interval verification in part3.cc, but labeled there as C886673381 *)
let J_809197575=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.419351)) *.  (sol_x x1 x2 x3 x4 x5 x6)) +. 
               (  (--. (#0.0499559)) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (#0.35641)))`;;


(* interval verification in part3.cc, but labeled there as C681494013 *)
let J_73203677=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.419351)) *.  (sol_x x1 x2 x3 x4 x5 x6)) +. 
               (  (--. (#0.64713719)) *.  (dih_x x1 x2 x3 x4 x5 x6)) +.  (#1.3225)))`;;

let C_830854305 = list_mk_conj[   
   J_539256862;J_864218323;J_776305271;J_927432550;J_221945658;
   J_53415898;J_106537269;J_254627291;J_170403135;J_802409438;
   J_195296574;J_16189133;J_584511898;J_98170671;J_868828815;
   J_809197575;J_73203677;];;

(*
SKIP statement about Quad clusters at end of Group_3
This is Prop 4.1 and Prop 4.2 -- a long list of quad ineqs.
These inequalities are in the file kep_inequalities2.ml
*)

let J_395086940=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (  (--. (#0.398)) *.  ( (sqrt x2) +.  (sqrt x3) +.  (sqrt x5) +.  (sqrt x6))) +. 
                  (  (#0.3257) *.  (sqrt x1)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6))) <.  (--. (#4.14938)))`;;



(*
LOC: 2002 III, page 15.
Sec. 10, Group_4
SKIP equation 5.
equation 5 is Prop 4.3 and Lemma 5.3.
Proposition 4.3 appears in kep_inequalities2.ml.
Lemma 5.3 is derived from other inequalities (Group_5), so it needn't
be listed separately here. 

*)

(*
LOC: 2002 III, page 15.
Sec. 10, Group_4
SKIP equation  6.  
These are identical to the inequalities of 2002-III-Appendix 1:
  A.2.1--11, A.3.1--11, A.4.1--4, A.6.1--9, A.6.1'--8', A.8.1--3.
  These are all listed below.
*)

(*
 
LOC: 2002 III, page 15.
Sec. 10, Group_5
*)


let J_550901847=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((square (#2.1773)), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (tau_sigma_x x1 x2 x3 x4 x5 x6) >.  (  (#0.55) *.  pt))`;;



let J_559163627=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((square (#2.1773)), x4, square_2t0);
     ((square (#2.1773)), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (tau_sigma_x x1 x2 x3 x4 x5 x6) >.  (  (#2.0) *.  (#0.55) *.  pt))`;;



let J_571492944=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, (square (#2.1773)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (tau_sigma_x x1 x2 x3 x4 x5 x6) >.  ( (--. (#0.29349)) +.  (  (#0.2384) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



let J_471806843=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, (square (#2.1773)));
     ((square (#2.1773)), x5, square_2t0);
     ((#4.0), x6, (square (#2.1773)))
    ]
    ( (tau_sigma_x x1 x2 x3 x4 x5 x6) >.  ( (--. (#0.26303)) +.  (  (#0.2384) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



let J_610154063=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, (square (#2.1773)));
     ((#4.0), x5, (square (#2.1773)));
     ((square (#2.1773)), x6, square_2t0)
    ]
    ( (tau_sigma_x x1 x2 x3 x4 x5 x6) >. 
            ( (--. (#0.5565)) +.  (  (#0.2384) *.  ( (dih_x x1 x2 x3 x4 x5 x6) +.  (dih2_x x1 x2 x3 x4 x5 x6)))))`;;



let J_466112442=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, (square (#2.1773)));
     ((#4.0), x5, (square (#2.1773)));
     ((#4.0), x6, (square (#2.1773)))
    ]
    ( (tau_sigma_x x1 x2 x3 x4 x5 x6) >. 
            ( (  (--. (#2.0)) *.  (#0.29349)) +.  (  (#0.2384) *.  ( (dih_x x1 x2 x3 x4 x5 x6) +.  (dih2_x x1 x2 x3 x4 x5 x6)))))`;;



let J_904445624=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, (square (#2.1773)));
     ((#4.0), x5, (square (#2.1773)));
     ((#4.0), x6, (square (#2.1773)))
    ]
    ( (tau_sigma_x x1 x2 x3 x4 x5 x6) >. 
            ( (  (--. (#3.0)) *.  (#0.29349)) +. 
               (  (#0.2384) *.  ( (dih_x x1 x2 x3 x4 x5 x6) +.  (dih2_x x1 x2 x3 x4 x5 x6) +. 
                            (dih3_x x1 x2 x3 x4 x5 x6)))))`;;

let C_636208429 = 
  list_mk_conj[ 
   J_550901847;J_559163627;J_571492944;J_471806843;J_610154063;
   J_466112442;J_904445624;];;

let J_241241504=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((square (#2.177303)), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <.  (  ( (#1.0) +.  (--. (#0.48))) *.  pt))`;;

(* Added March 10, 2005.  Requested by Lagarias for DCG *)
(* Note to Google flyspeck group, March 10, 2005 *)
let J_241241504_1=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#2.177303)), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <.  (  #0.028794285 ))`;; (* STM, added '#' *)

let J_144820927=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((square (#2.177303)), x4, square_2t0);
     ((square (#2.177303)), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <.  (  ( (#1.0) +.  (  (--. (#2.0)) *.  (#0.48))) *.  pt))`;;




let J_82950290=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, (square (#2.177303)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
                ( (#0.31023815) +.  (  (--. (#0.207045)) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



let J_938408928=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, (square (#2.177303)));
     ((square (#2.177303)), x5, square_2t0);
     ((#4.0), x6, (square (#2.177303)))
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
                ( (#0.28365) +.  (  (--. (#0.207045)) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;


let J_739415811=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, (square (#2.177303)));
     ((#4.0), x5, (square (#2.177303)));
     ((square (#2.177303)), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
                ( (#0.53852) +.  (  (--. (#0.207045)) *.  ( (dih_x x1 x2 x3 x4 x5 x6) +.  (dih2_x x1 x2 x3 x4 x5 x6)))))`;;



let J_898558502=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, (square (#2.177303)));
     ((#4.0), x5, (square (#2.177303)));
     ((#4.0), x6, (square (#2.177303)))
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
                ( (( --. ) (pt)) +.  (  (#2.0) *.  (#0.31023815)) +. 
                (  (--. (#0.207045)) *.  ( (dih_x x1 x2 x3 x4 x5 x6) +.  (dih2_x x1 x2 x3 x4 x5 x6)))))`;;



let J_413792383=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, (square (#2.177303)));
     ((#4.0), x5, (square (#2.177303)));
     ((#4.0), x6, (square (#2.177303)))
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <. 
                ( (  (--. (#2.0)) *.  pt) +.  (  (#3.0) *.  (#0.31023815)) +. 
                (  (--. (#0.207045)) *.  ( (dih_x x1 x2 x3 x4 x5 x6) +.  (dih2_x x1 x2 x3 x4 x5 x6) +. 
                                (dih3_x x1 x2 x3 x4 x5 x6)))))`;;

let C_129662166 = list_mk_conj [ 
   J_241241504;J_144820927;J_82950290;J_938408928;J_739415811;
   J_898558502;J_413792383;];;



(*
 
LOC: 2002 III, page 17.
Section A.2 (Flat Quarters)
*)



let J_845282627=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (dih2_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.35) *.  (sqrt x2)) +.  (  (--. (#0.15)) *.  (sqrt x1)) +. 
               (  (--. (#0.15)) *.  (sqrt x3)) +.  (  (#0.7022) *.  (sqrt x5)) +.  (  (--. (#0.17)) *.  (sqrt x4))) >.  (--. (#0.0123)))`;;



let J_370569407=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (dih3_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.35) *.  (sqrt x3)) +.  (  (--. (#0.15)) *.  (sqrt x1)) +. 
               (  (--. (#0.15)) *.  (sqrt x2)) +.  (  (#0.7022) *.  (sqrt x6)) +.  (  (--. (#0.17)) *.  (sqrt x4))) >.  (--. (#0.0123)))`;;



let J_339706797=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (dih2_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.13)) *.  (sqrt x2)) +.  (  (#0.631) *.  (sqrt x1)) +. 
               (  (#0.31) *.  (sqrt x3)) +.  (  (--. (#0.58)) *.  (sqrt x5)) +.  (  (#0.413) *.  (sqrt x4)) +.  (  (#0.025) *.  (sqrt x6))) >. 
            (#2.63363))`;;



let J_430633660=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (dih3_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.13)) *.  (sqrt x3)) +.  (  (#0.631) *.  (sqrt x1)) +. 
               (  (#0.31) *.  (sqrt x2)) +.  (  (--. (#0.58)) *.  (sqrt x6)) +.  (  (#0.413) *.  (sqrt x4)) +.  (  (#0.025) *.  (sqrt x5))) >. 
            (#2.63363))`;;



let J_623340094=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.714) *.  (sqrt x1)) +.  (  (--. (#0.221)) *.  (sqrt x2)) +. 
               (  (--. (#0.221)) *.  (sqrt x3)) +.  (  (#0.92) *.  (sqrt x4)) +.  (  (--. (#0.221)) *.  (sqrt x5)) +.  (  (--. (#0.221)) *.  (sqrt x6))) >. 
            (#0.3482))`;;



let J_27261595=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (dih_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.315)) *.  (sqrt x1)) +.  (  (#0.3972) *.  (sqrt x2)) +. 
               (  (#0.3972) *.  (sqrt x3)) +.  (  (--. (#0.715)) *.  (sqrt x4)) +.  (  (#0.3972) *.  (sqrt x5)) +.  (  (#0.3972) *.  (sqrt x6))) >. 
            (#2.37095))`;;



let J_211740764=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (sol_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.187)) *.  (sqrt x1)) +.  (  (--. (#0.187)) *.  (sqrt x2)) +. 
               (  (--. (#0.187)) *.  (sqrt x3)) +.  (  (#0.1185) *.  (sqrt x4)) +.  (  (#0.479) *.  (sqrt x5)) +.  (  (#0.479) *.  (sqrt x6))) >. 
            (#0.437235))`;;




let J_954401688=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (sol_x x1 x2 x3 x4 x5 x6) +.  (  (#0.488) *.  (sqrt x1)) +.  (  (#0.488) *.  (sqrt x2)) +. 
               (  (#0.488) *.  (sqrt x3)) +.  (  (--. (#0.334)) *.  (sqrt x5)) +.  (  (--. (#0.334)) *.  (sqrt x6))) >. 
            (#2.244))`;;



let J_563700199=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (mu_flat_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.159)) *.  (sqrt x1)) +.  (  (--. (#0.081)) *.  (sqrt x2)) +. 
               (  (--. (#0.081)) *.  (sqrt x3)) +.  (  (--. (#0.133)) *.  (sqrt x5)) +.  (  (--. (#0.133)) *.  (sqrt x6))) >. 
            (--. (#1.17401)))`;;



let J_847997083=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (mu_flat_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.419351)) *.  (sol_x x1 x2 x3 x4 x5 x6)) +.  (#0.1448) +. 
               (  (#0.0436) *.  ( (sqrt x5) +.  (sqrt x6) +.  (--. (#4.0)))) +.  (  (#0.079431) *.  (dih_x x1 x2 x3 x4 x5 x6))))`;;



let J_465440863=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (mu_flat_x x1 x2 x3 x4 x5 x6) <. 
            ( (#0.000001) +.  (  (--. (#0.197)) *.  ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6) +.  (  (--. (#2.0)) *.  (sqrt (#2.0))) +.  (--. (#4.0))))))`;;


(*
 
LOC: 2002 III, page 17-18
Appendix 1 (Some final cases)
Section A3 (upright quarters)
*)


let J_875717907=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (dih_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.636)) *.  (sqrt x1)) +.  (  (#0.462) *.  (sqrt x2)) +. 
               (  (#0.462) *.  (sqrt x3)) +.  (  (--. (#0.82)) *.  (sqrt x4)) +.  (  (#0.462) *.  (sqrt x5)) +.  (  (#0.462) *.  (sqrt x6))) >. 
            (#1.82419))`;;



let J_614510242=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.55) *.  (sqrt x1)) +.  (  (--. (#0.214)) *.  (sqrt x2)) +. 
               (  (--. (#0.214)) *.  (sqrt x3)) +.  (  (#1.24) *.  (sqrt x4)) +.  (  (--. (#0.214)) *.  (sqrt x5)) +.  (  (--. (#0.214)) *.  (sqrt x6))) >. 
            (#0.75281))`;;



let J_17441891=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (dih2_x x1 x2 x3 x4 x5 x6) +.  (  (#0.4) *.  (sqrt x1)) +.  (  (--. (#0.15)) *.  (sqrt x2)) +. 
               (  (#0.09) *.  (sqrt x3)) +.  (  (#0.631) *.  (sqrt x4)) +.  (  (--. (#0.57)) *.  (sqrt x5)) +.  (  (#0.23) *.  (sqrt x6))) >. 
            (#2.5481))`;;



let J_58663442=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (dih2_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.454)) *.  (sqrt x1)) +.  (  (#0.34) *.  (sqrt x2)) +. 
               (  (#0.154) *.  (sqrt x3)) +.  (  (--. (#0.346)) *.  (sqrt x4)) +.  (  (#0.805) *.  (sqrt x5))) >. 
            (--. (#0.3429)))`;;




let J_776139048=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (dih3_x x1 x2 x3 x4 x5 x6) +.  (  (#0.4) *.  (sqrt x1)) +.  (  (--. (#0.15)) *.  (sqrt x3)) +. 
               (  (#0.09) *.  (sqrt x2)) +.  (  (#0.631) *.  (sqrt x4)) +.  (  (--. (#0.57)) *.  (sqrt x6)) +.  (  (#0.23) *.  (sqrt x5))) >. 
            (#2.5481))`;;




let J_695202082=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (dih3_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.454)) *.  (sqrt x1)) +.  (  (#0.34) *.  (sqrt x3)) +. 
               (  (#0.154) *.  (sqrt x2)) +.  (  (--. (#0.346)) *.  (sqrt x4)) +.  (  (#0.805) *.  (sqrt x6))) >. 
            (--. (#0.3429)))`;;



let J_974811809=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (sol_x x1 x2 x3 x4 x5 x6) +.  (  (#0.065) *.  (sqrt x2)) +.  (  (#0.065) *.  (sqrt x3)) +. 
               (  (#0.061) *.  (sqrt x4)) +.  (  (--. (#0.115)) *.  (sqrt x5)) +.  (  (--. (#0.115)) *.  (sqrt x6))) >. 
            (#0.2618))`;;



let J_416984093=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (sol_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.239)) *.  (sqrt x1)) +.  (  (--. (#0.03)) *.  (sqrt x2)) +. 
               (  (--. (#0.03)) *.  (sqrt x3)) +.  (  (#0.12) *.  (sqrt x4)) +.  (  (#0.325) *.  (sqrt x5)) +.  (  (#0.325) *.  (sqrt x6))) >. 
            (#0.2514))`;;



let J_709137309=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (( --. ) (octa_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.054)) *.  (sqrt x2)) +.  (  (--. (#0.054)) *.  (sqrt x3)) +. 
               (  (--. (#0.083)) *.  (sqrt x4)) +.  (  (--. (#0.054)) *.  (sqrt x5)) +.  (  (--. (#0.054)) *.  (sqrt x6))) >. 
            (--. (#0.59834)))`;;



let J_889412880=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (octa_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (--. (#0.419351)) *.  (sol_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.079431) *.  (dih2_x x1 x2 x3 x4 x5 x6)) +. 
               (#0.06904) +.  (  (--. (#0.0846)) *.  ( (sqrt x1) +.  (--. (#2.8))))))`;;



let J_330814127=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, (square (#2.13)));
     ((#4.0), x3, (square (#2.13)));
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            (octa_x x1 x2 x3 x4 x5 x6) <. 
            ( (  (#0.07) *.  ( (sqrt x1) +.  (--. (#2.51)))) +.  (  (--. (#0.133)) *.  ( (sqrt x2) +.  (sqrt x3) +.  (sqrt x5) +.  (sqrt x6) +.  (--. (#8.0)))) +. 
               (  (#0.135) *.  ( (sqrt x4) +.  (--. (#2.0))))))`;;


(*
 
LOC: 2002 III, page 18.
Appendix 1. (Some final cases)
Section A4 (Truncated quad clusters)
*)



let J_739434119=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (dih_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.372)) *.  (sqrt x1)) +.  (  (#0.465) *.  (sqrt x2)) +. 
               (  (#0.465) *.  (sqrt x3)) +.  (  (#0.465) *.  (sqrt x5)) +.  (  (#0.465) *.  (sqrt x6))) >. 
            (#4.885))`;;



let J_353908222=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.26)));
     ((#4.0), x2, (square (#2.26)));
     ((#4.0), x3, (square (#2.26)));
    
        ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        ( ( (( --. ) (vor_0_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.06)) *.  (sqrt x2)) +.  (  (--. (#0.06)) *.  (sqrt x3)) +. 
               (  (--. (#0.185)) *.  (sqrt x5)) +.  (  (--. (#0.185)) *.  (sqrt x6))) >.  (--. (#0.9978))) \/ 
        ( (dih_x x1 x2 x3 x4 x5 x6) >=.  (#2.12)))`;;



let J_399226168=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.26)));
     ((#4.0), x2, (square (#2.26)));
     ((#4.0), x3, (square (#2.26)));
    
        ((#8.0), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        ( ( (( --. ) (vor_0_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.419351) *.  (sol_x x1 x2 x3 x4 x5 x6))) <.  (#0.3072)) \/ 
        ( (dih_x x1 x2 x3 x4 x5 x6) >=.  (#2.12)))`;;



let J_815275408=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (quo_x x1 x2 x6) +.  (  (#0.00758) *.  (sqrt x1)) +.  (  (#0.0115) *.  (sqrt x2)) +.  (  (#0.0115) *.  (sqrt x6))) >. 
            (#0.06333))`;;



(*
Handwritten in as new inequality
*)
let J_349475742=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (quo_x x1 x2 x6) >=.  (#0.0))`;;




(*
 
LOC: 2002 III, page 19.
Appendix 1. (Some final cases)
Section A6 (Quasi-regular tetrahedra)
*)


let J_61701725=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (sol_x x1 x2 x3 x4 x5 x6) +.  (  (#0.377076) *.  (sqrt x1)) +.  (  (#0.377076) *.  (sqrt x2)) +. 
               (  (#0.377076) *.  (sqrt x3)) +.  (  (--. (#0.221)) *.  (sqrt x4)) +.  (  (--. (#0.221)) *.  (sqrt x5)) +.  (  (--. (#0.221)) *.  (sqrt x6))) >. 
            (#1.487741)) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) >.  (#6.25)))`;;



let J_679487679=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (  (#0.221) *.  (sqrt x4)) +.  (  (#0.221) *.  (sqrt x5)) +.  (  (#0.221) *.  (sqrt x6)) +.  (( --. ) (sol_x x1 x2 x3 x4 x5 x6))) >. 
            (#0.76822)) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) >.  (#6.25)))`;;



let J_178057365=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (dih_x x1 x2 x3 x4 x5 x6) +.  (  (#0.34) *.  (sqrt x2)) +.  (  (#0.34) *.  (sqrt x3)) +. 
               (  (--. (#0.689)) *.  (sqrt x4)) +.  (  (#0.27) *.  (sqrt x5)) +.  (  (#0.27) *.  (sqrt x6))) >. 
            (#2.29295)) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) >.  (#6.25)))`;;



let J_285829736=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) +.  (  (#0.498) *.  (sqrt x1)) +.  (  (#0.731) *.  (sqrt x4)) +. 
               (  (--. (#0.212)) *.  (sqrt x5)) +.  (  (--. (#0.212)) *.  (sqrt x6))) >. 
            (#0.37884)) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) >.  (#6.25)))`;;




let J_364138508=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (( --. ) (sigma_qrtet_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.109)) *.  (sqrt x1)) +.  (  (--. (#0.109)) *.  (sqrt x2)) +. 
               (  (--. (#0.109)) *.  (sqrt x3)) +.  (  (--. (#0.14135)) *.  (sqrt x4)) +.  (  (--. (#0.14135)) *.  (sqrt x5)) +.  (  (--. (#0.14135)) *.  (sqrt x6))) >. 
            (--. (#1.5574737))) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) >.  (#6.25)))`;;




let J_217981292=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (( --. ) (sigma_qrtet_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.419351)) *.  (sol_x x1 x2 x3 x4 x5 x6)) +. 
               (  (--. (#0.2)) *.  (sqrt x1)) +.  (  (--. (#0.2)) *.  (sqrt x2)) +.  (  (--. (#0.2)) *.  (sqrt x3)) +. 
               (  (--. (#0.048)) *.  (sqrt x4)) +.  (  (--. (#0.048)) *.  (sqrt x5)) +.  (  (--. (#0.048)) *.  (sqrt x6))) >. 
            (--. (#1.77465))) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) >.  (#6.25)))`;;



let J_599117591=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (tau_sigma_x x1 x2 x3 x4 x5 x6) +.  (  (--. (#0.0845696)) *.  (sqrt x1)) +.  (  (--. (#0.0845696)) *.  (sqrt x2)) +. 
               (  (--. (#0.0845696)) *.  (sqrt x3)) +.  (  (--. (#0.163)) *.  (sqrt x4)) +.  (  (--. (#0.163)) *.  (sqrt x5)) +.  (  (--. (#0.163)) *.  (sqrt x6))) >. 
            (--. (#1.48542))) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) >.  (#6.25)))`;;



let J_163177561=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.13)));
     ((#4.0), x2, (square (#2.13)));
     ((#4.0), x3, (square (#2.13)));
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (dih_x x1 x2 x3 x4 x5 x6) +.  (  (#0.27) *.  (sqrt x2)) +.  (  (#0.27) *.  (sqrt x3)) +. 
               (  (--. (#0.689)) *.  (sqrt x4)) +.  (  (#0.27) *.  (sqrt x5)) +.  (  (#0.27) *.  (sqrt x6))) >. 
            (#2.01295)) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) >.  (#6.25)))`;;



let J_225583331=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.13)));
     ((#4.0), x2, (square (#2.13)));
     ((#4.0), x3, (square (#2.13)));
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (( --. ) (sigma_qrtet_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.14135)) *.  (sqrt x1)) +.  (  (--. (#0.14135)) *.  (sqrt x2)) +. 
            (  (--. (#0.14135)) *.  (sqrt x3)) +.  (  (--. (#0.14135)) *.  (sqrt x4)) +.  (  (--. (#0.14135)) *.  (sqrt x5)) +.  (  (--. (#0.14135)) *.  (sqrt x6))) >. 
            (--. (#1.7515737))) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) >.  (#6.25)))`;;




let J_891900056=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (sol_x x1 x2 x3 x4 x5 x6) +.  (  (#0.378) *.  (sqrt x1)) +.  (  (#0.378) *.  (sqrt x2)) +. 
               (  (#0.378) *.  (sqrt x3)) +.  (  (--. (#0.1781)) *.  (sqrt x4)) +.  (  (--. (#0.1781)) *.  (sqrt x5)) +.  (  (--. (#0.1781)) *.  (sqrt x6))) >. 
            (#1.761445)) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) <.  (#6.25)))`;;




let J_874759621=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (( --. ) (sol_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.171)) *.  (sqrt x1)) +.  (  (--. (#0.171)) *.  (sqrt x2)) +. 
               (  (--. (#0.171)) *.  (sqrt x3)) +.  (  (#0.3405) *.  (sqrt x4)) +.  (  (#0.3405) *.  (sqrt x5)) +.  (  (#0.3405) *.  (sqrt x6))) >. 
            (#0.489145)) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) <.  (#6.25)))`;;



let J_756881665=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (( --. ) (sigma_qrtet_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.1208)) *.  (sqrt x1)) +.  (  (--. (#0.1208)) *.  (sqrt x2)) +. 
               (  (--. (#0.1208)) *.  (sqrt x3)) +.  (  (--. (#0.0781)) *.  (sqrt x4)) +.  (  (--. (#0.0781)) *.  (sqrt x5)) +.  (  (--. (#0.0781)) *.  (sqrt x6))) >. 
            (--. (#1.2436))) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) <.  (#6.25)))`;;



let J_619846561=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (( --. ) (sigma_qrtet_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.419351)) *.  (sol_x x1 x2 x3 x4 x5 x6)) +. 
               (  (--. (#0.2)) *.  (sqrt x1)) +.  (  (--. (#0.2)) *.  (sqrt x2)) +.  (  (--. (#0.2)) *.  (sqrt x3)) +. 
               (  (#0.0106) *.  (sqrt x4)) +.  (  (#0.0106) *.  (sqrt x5)) +.  (  (#0.0106) *.  (sqrt x6))) >. 
            (--. (#1.40816))) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) <.  (#6.25)))`;;




let J_675872124=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.13)));
     ((#4.0), x2, (square (#2.13)));
     ((#4.0), x3, (square (#2.13)));
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (sol_x x1 x2 x3 x4 x5 x6) +.  (  (#0.356) *.  (sqrt x1)) +.  (  (#0.356) *.  (sqrt x2)) +.  (  (#0.356) *.  (sqrt x3)) +. 
               (  (--. (#0.1781)) *.  (sqrt x4)) +.  (  (--. (#0.1781)) *.  (sqrt x5)) +.  (  (--. (#0.1781)) *.  (sqrt x6))) >. 
            (#1.629445)) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) <.  (#6.25)))`;;




let J_498007387=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.13)));
     ((#4.0), x2, (square (#2.13)));
     ((#4.0), x3, (square (#2.13)));
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (( --. ) (sol_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.254)) *.  (sqrt x1)) +.  (  (--. (#0.254)) *.  (sqrt x2)) +.  (  (--. (#0.254)) *.  (sqrt x3)) +. 
               (  (#0.3405) *.  (sqrt x4)) +.  (  (#0.3405) *.  (sqrt x5)) +.  (  (#0.3405) *.  (sqrt x6))) >. 
            (--. (#0.008855))) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) <.  (#6.25)))`;;




let J_413387792=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.13)));
     ((#4.0), x2, (square (#2.13)));
     ((#4.0), x3, (square (#2.13)));
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        (
            ( (( --. ) (sigma_qrtet_x x1 x2 x3 x4 x5 x6)) +.  (  (--. (#0.167)) *.  (sqrt x1)) +.  (  (--. (#0.167)) *.  (sqrt x2)) +.  (  (--. (#0.167)) *.  (sqrt x3)) +. 
               (  (--. (#0.0781)) *.  (sqrt x4)) +.  (  (--. (#0.0781)) *.  (sqrt x5)) +.  (  (--. (#0.0781)) *.  (sqrt x6))) >. 
            (--. (#1.51017))) \/ 
         ( ( (sqrt x4) +.  (sqrt x5) +.  (sqrt x6)) <.  (#6.25)))`;;


(*
 
LOC: 2002 III, page 20.
Appendix 1. (Some final Cases)
Section A8 (Final cases)
*)


let J_135953363=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.13)));
     ((#4.0), x2, (square (#2.13)));
     ((#4.0), x3, (square (#2.13)));
    
        ((square (#2.93)), x4, square_4t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
        ( (dih_x x1 x2 x3 x4 x5 x6) >.  (#1.694)) \/ 
        ( ( (sqrt x2) +.  (sqrt x3) +.  (sqrt x5) +.  (sqrt x6)) >.  (#8.709)))`;;




let J_324141781=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.13)));
     ((#4.0), x2, (square (#2.13)));
     ((#4.0), x3, (square (#2.13)));
    
        ((#8.0), x4, (square (#2.93)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (dih2_x x1 x2 x3 x4 x5 x6) +.  (  (#0.59) *.  (sqrt x1)) +.  (  (#0.1) *.  (sqrt x2)) +.  (  (#0.1) *.  (sqrt x3)) +. 
              (  (#0.55) *.  (sqrt x4)) +.  (  (--. (#0.6)) *.  (sqrt x5)) +.  (  (--. (#0.12)) *.  (sqrt x6))) >.  (#2.6506))`;;



let J_778150947=
   all_forall `ineq 
    [((#4.0), x1, (square (#2.13)));
     ((#4.0), x2, (square (#2.13)));
     ((#4.0), x3, (square (#2.13)));
    
        ((#8.0), x4, (square (#2.93)));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (dih2_x x1 x2 x3 x4 x5 x6) +.  (  (#0.35) *.  (sqrt x1)) +.  (  (--. (#0.24)) *.  (sqrt x2)) +.  (  (#0.05) *.  (sqrt x3)) +. 
              (  (#0.35) *.  (sqrt x4)) +.  (  (--. (#0.72)) *.  (sqrt x5)) +.  (  (--. (#0.18)) *.  (sqrt x6))) <.  (#0.47))`;;



(*
LOC: DCG II, page 147 (published DCG pages).
Cases (8) (9) (10) (11)
Used in Formulation
*)

let J_629256313=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
         (square_2t0, x5, (#8.0));
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  (#0.0)) \/ 
            ( (eta_x x1 x2 x6) >.  (#2.0)) \/ 
            ( (eta_x x2 x3 x4) >.  (#2.0)) \/ 
            ( (eta_x x1 x3 x5) >.  (#2.0)) \/ 
            ( (eta_x x4 x5 x6) >.  (#2.0)))`;;


let J_917032944=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
    
         (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    (
            ( (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  (#0.0)) \/ 
            ( (eta_x x1 x2 x6) >.  (#2.0)) \/ 
            ( (eta_x x2 x3 x4) >.  (#2.0)) \/ 
            ( (eta_x x1 x3 x5) >.  (#2.0)) \/ 
            ( (eta_x x4 x5 x6) >.  (#2.0)))`;;


let J_738318844=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
         (square_2t0, x4, (#8.0));
     (square_2t0, x5, (#8.0));
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  (#0.0)) \/ 
            ( (eta_x x1 x2 x6) >.  (#2.0)) \/ 
            ( (eta_x x2 x3 x4) >.  (#2.0)) \/ 
            ( (eta_x x1 x3 x5) >.  (#2.0)) \/ 
            ( (eta_x x4 x5 x6) >.  (#2.0)))`;;


let J_587618947=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
         (square_2t0, x4, (#8.0));
     (square_2t0, x5, (#8.0));
     (square_2t0, x6, (#8.0))
    ]
    (
            ( (vor_analytic_x x1 x2 x3 x4 x5 x6) <.  (#0.0)) \/ 
            ( (eta_x x1 x2 x6) >.  (#2.0)) \/ 
            ( (eta_x x2 x3 x4) >.  (#2.0)) \/ 
            ( (eta_x x1 x3 x5) >.  (#2.0)) \/ 
            ( (eta_x x4 x5 x6) >.  (#2.0)))`;;


(*

 LOC: DCG Sphere Packing II, page 147, Calc 4.5.1.

 Note case of equality is equality five  (#4.0) and x4=(#8.0).
 In the following inequality, we need that this is the unique case
 of equality.
*)

let J_346093004=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
         (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (
            ( (gamma_x x1 x2 x3 x4 x5 x6) <=.  (#0.0)) \/ 
            ( (eta_x x1 x2 x6) >.  (#2.0)) \/ 
            ( (eta_x x2 x3 x4) >.  (#2.0)) \/ 
            ( (eta_x x1 x3 x5) >.  (#2.0)) \/ 
            ( (eta_x x4 x5 x6) >.  (#2.0)))`;;



(* I, SPI-1997 Lemma 9.17 *)

let J_534566617 = 
  all_forall `ineq
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
   (((vor_analytic_x x1 x2 x3 x4 x5 x6) < --((#1.8))*pt) \/
   (rad2_x x1 x2 x3 x4 x5 x6 <. (#1.9881)))`;;



(*
 
LOC: 2002 Form, Appendix 1, page 19
Formulation
*)

(*
LOC: 2002 Form, Appendix 1, page 19
 2002_Calc_3.13.1

*)

let J_5901405=
   all_forall `ineq 
    [((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     (square_2t0, x1, (#8.0));
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    (( (vor_analytic_x x1 x2 x3 x4 x5 x6) <=.  (#0.0)) \/
    (chi_x x5 x6 x1  x2 x3 x4 >. (#0.0)   ))`;;


(*
LOC: 2002 Form, Appendix 1, page 19
 2002_Calc_3.13.2:
 We need that equality implies that x1=8 and the other edges are 4.0.
*)
let J_40003553=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (vor_analytic_x x1 x2 x3 x4 x5 x6) <=.  (#0.0))`;;


(*
LOC: 2002 Form, Appendix 1, page 19
 2002_Calc_3.13.3
*)
let J_522528841=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
    
        ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (  (#2.0) *.  (gamma_x x1 x2 x3 x4 x5 x6)) +.  
       (vor_0_x x1 x2 x3 x4 x5 x6) +. 
     (( --. ) (vor_0_x_flipped x1 x2 x3 x4 x5 x6))) <=.  (#0.0))`;;


(*
LOC: 2002 Form, Appendix 1, page 19
 2002_Calc_3.13.4
*)
let J_892806084=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (vor_analytic_x x1 x2 x3 x4 x5 x6) +.  
     (vor_analytic_x_flipped x1 x2 x3 x4 x5 x6) +. 
               (vor_0_x x1 x2 x3 x4 x5 x6) +.  
      (( --. ) (vor_0_x_flipped x1 x2 x3 x4 x5 x6))) <=.  (#0.0))`;;


(*
LOC: 2002 Form, Appendix 1, page 19
 2002_Calc_4.1.1
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
LOC: 2002 Form, Appendix 1, page 20
 2002_Formulation_4.7.1:
*)
let J_554253147=
   all_forall `ineq 
    [        
     (square_2t0, x4, (#8.0));
     ((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (mu_flat_x x1 x2 x3 x4 x5 x6) +.  (mu_flipped_x x1 x2 x3 x4 x5 x6) +. 
           (  (crown (  (sqrt x1) /  (#2.0))) *.  ( (#1.0) +.  (  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) /  pi))) +. 
           (  (#2.0) *.  (anc (sqrt x1) (sqrt x2) (sqrt x6)))) <. 
           ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (vor_0_x_flipped x1 x2 x3 x4 x5 x6)))`;;


(*
LOC: 2002 Form, Appendix 1, page 20
 2002_Formulation_4.7.2:
*)
let J_906566422=
   all_forall `ineq 
    [((square (#1.255)), x, (#4.0))
    ]
    ( (crown (sqrt x)) <.  (--. (#0.1378)))`;;


(*
LOC: 2002 Form, Appendix 1, page 20
 2002_Formulation_4.7.3:
*)
let J_703457064=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (anc (sqrt x1) (sqrt x2) (sqrt x6)) <.  (#0.0263))`;;



(*
LOC: 2002 Form, Appendix 1, page 20
 2002_Formulation_4.7.4
*)
let J_175514843=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (mu_upright_x x1 x2 x3 x4 x5 x6) +. 
           (  (--. (#0.1378)) *.  ( (#1.0) +.  (  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) /  (  (#2.0) *.  pi)))) +. 
           (  (#2.0) *.  (#0.0263))) <. 
           (vor_0_x x1 x2 x3 x4 x5 x6))`;;


(*
LOC: 2002 Form, Appendix 1, page 20
 2002_Formulation_4.7.5
*)
let J_855677395=
   all_forall `ineq 
    [((square (#2.69)), x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (mu_upright_x x1 x2 x3 x4 x5 x6) +.  (mu_flipped_x x1 x2 x3 x4 x5 x6)) <. 
           ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (vor_0_x_flipped x1 x2 x3 x4 x5 x6) +. 
              (  (#0.02) *.  ( (  pi /  (#2.0)) +.  (( --. ) (dih_x x1 x2 x3 x4 x5 x6))))))`;;


(* ****************************************************** *)
(* NEW INEQUALITIES THAT DO NOT APPEAR IN THE 1998 PROOF  *)
(* BLUEPRINT REVISION INEQUALITIES                        *)


(* DEPRECATED INEQUALITIES ********************************)
(* THESE ARE INEQUALITIES IN THE 1998, THAT ARE NOT USED  *)
(* IN THE BLUEPRINT VERSION *******************************)




(*
end of document
*)

