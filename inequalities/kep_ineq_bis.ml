(* Added inequalities 2008 *)


(* EXPUNGE 3-CROWDED. 
LOC: DCG errata : 
http://flyspeck.googlecode.com/svn/trunk/dcg_errata/dcg_errata.tex
(svn 338)
Added March7,2008.
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
   ((gamma_x  x1 x2 x3 x4 x5 x6 < octavor_analytic_x x1 x2 x3 x4 x5 x6 +
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
   ((kappa y1 y2 y3 y4 y5 y6 < -- (#2.0)*xi_gamma + (#0.029)))`;;


(* L41e257
LOC: DCG errata : 
http://flyspeck.googlecode.com/svn/trunk/dcg_errata/dcg_errata.tex
(svn 338)
Added March7,2008.
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
    dih_x (#2.51) (#2.51) x3 x4 x5 (#2.51) - (#0.0084)))`;;


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
    dih_x (#2.51) (#2.51) x3 x4 x5 (#2.51) - (#0.0084)))`;;

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


