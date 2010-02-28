(* inequalities used in the text part of the kepler conjecture *)

(* They are not ALL listed here.

The following are in kep_inequalities2.ml
996268658 P2
824762926 P2
675785884 P2
657406669 P2
551665569 P2
325738864 P2
314974315 P2
277330628 P2
193592217 P2

The following need to be moved here, but they are composites
of several inequalites.

984628285 C
971555266 C
940884472 C
934150983 C
874876755 C
855294746 C
852270725 C
83777706 C
830854305 C
815492935 C
764978100 C
73974037 C
729988292 C
692155251 C
636208429 C
628964355 C
618205535 C
531888597 C
485049042 C
311189443 C
209361863 C
193836552 C
187932932 C
163548682 C
148776243 C
129662166 C
128523606 C
*)

parse_as_infix("+.",(16,"right"));
parse_as_infix("-.",(18,"left"));
parse_as_infix("*.",(20,"right"));
parse_as_infix("**.",(24,"left")); 
parse_as_infix("<.",(12,"right"));
parse_as_infix("<=.",(12,"right"));
parse_as_infix(">.",(12,"right"));
parse_as_infix(">=.",(12,"right"));
override_interface("+.",`real_add:real->real->real`);
override_interface("-.",`real_sub:real->real->real`);
override_interface("*.",`real_mul:real->real->real`);
override_interface("**.",`real_pow:real->num->real`);
(* boolean *)
override_interface("<.",`real_lt:real->real->bool`);
override_interface("<=.",`real_le:real->real->bool`);
override_interface(">.",`real_gt:real->real->bool`);
override_interface(">=.",`real_ge:real->real->bool`);
(* unary *)
override_interface("--.",`real_neg:real->real`);
override_interface("&.",`real_of_num:num->real`);
override_interface("||.",`real_abs:real->real`);;


let I_115383627=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     (square_2t0, x6, square_4t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.51) \/
      (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0)) `;;


let I_115756648=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0)
    ]
    ( (overlap_f (sqrt x1) (sqrt x2)) >.  (#0.887))`;;

let I_122081309=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#8.0), x4, (#8.0));
     (square_2t0, x5, square_2t0);
     (square_2t0, x6, square_4t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.77) \/
      (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;


let I_135427691=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     (square_2t0, x4, (#8.0));
     (square_2t0, x5, square_2t0);
     (square_2t0, x6, square_4t0)
    ]
    (
         (
            ( (tau_0_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (--. (#0.12))) \/ 
           ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.2)) \/
           (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;



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


let I_2298281931=
all_forall `ineq
   [
   ((#4.0),x1,square_2t0);
   ((#4.0),x2,square_2t0);
   ((#4.0),x3,square_2t0);
   ((#4.0),x4,(#8.0)); 
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


let J_241241504_1=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((square (#2.177303)), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (sigma_qrtet_x x1 x2 x3 x4 x5 x6) <.  (  #0.028794285 ))`;;


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

let I_467530297=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_2t0);
     (square_2t0, x6, square_4t0)
    ]
    (
         (
           ( (tau_0_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (--. (#0.1376))) \/ 
           ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.2)) \/
           (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;


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

let J_554253147=
   all_forall `ineq 
    [        
     (square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x3, square_2t0);
     ((#4.0), x4,square_2t0);
     ((#4.0), x5, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (mu_upright_x x1 x2 x3 x4 x5 x6) +.  (mu_flipped_x x1 x2 x3 x4 x5 x6) +. 
           (  (crown (  (sqrt x1) /  (#2.0))) *.  ( (#1.0) +.  (  (( --. ) (dih_x x1 x2 x3 x4 x5 x6)) /  pi))) +. 
           (  (#2.0) *.  (anc (sqrt x1) (sqrt x2) (sqrt x6)))) <. 
           ( (vor_0_x x1 x2 x3 x4 x5 x6) +.  (vor_0_x_flipped x1 x2 x3 x4 x5 x6)))`;;

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

let I_576221766=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#8.0), x4, (#8.0));
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, square_4t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.93) \/
      (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;

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
            ( (eta_x x1 x2 x6) >.  (sqrt (#2.0))) \/ 
            ( (eta_x x2 x3 x4) >.  (sqrt (#2.0))) \/ 
            ( (eta_x x1 x3 x5) >.  (sqrt (#2.0))) \/ 
            ( (eta_x x4 x5 x6) >.  (sqrt (#2.0))))`;;

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



let I_603910880=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     (square_2t0, x4, (#8.0));
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, square_4t0)
    ]
    (
         (
            ( (tau_0_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (--. (#0.266))) \/ 
           ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.2)) \/
           (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;


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
            ( (eta_x x1 x2 x6) >. (sqrt (#2.0))) \/ 
            ( (eta_x x2 x3 x4) >. (sqrt (#2.0))) \/ 
            ( (eta_x x1 x3 x5) >. (sqrt (#2.0))) \/ 
            ( (eta_x x4 x5 x6) >. (sqrt (#2.0))))`;;


let I_644534985=
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, square_2t0);
     ((#4.0), x5, square_2t0);
     (square_2t0, x6, square_4t0)
    ]
    (
         (
           ( (tau_0_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >.  (--. (#0.2391))) \/ 
           ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.2)) \/
           (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;

let I_690646028=  
   all_forall `ineq 
    [((#4.0), x1, square_2t0);
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, square_2t0);
     (square_2t0, x5, square_4t0);
     ((#4.0), x6, square_2t0)
    ]
    ( ( (dih_x x1 x2 x3 x4 x5 x6) +.  (  (#0.5) *.  ( (#2.402) -.  (sqrt x4)))) <.  (  pi /  (#2.0)) \/
     (delta_x x1 x2 x3 x4 x5 x6 < (#0.0)))`;;

let I_69064028=I_690646028;; (* because of a typo *)


let J_703457064=
   all_forall `ineq 
    [(square_2t0, x1, (#8.0));
     ((#4.0), x2, square_2t0);
     ((#4.0), x6, square_2t0)
    ]
    ( (anc (sqrt x1) (sqrt x2) (sqrt x6)) <.  (#0.0263))`;;

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
            ( (eta_x x1 x2 x6) >.  (sqrt (#2.0))) \/ 
            ( (eta_x x2 x3 x4) >.  (sqrt (#2.0))) \/ 
            ( (eta_x x1 x3 x5) >.  (sqrt (#2.0))) \/ 
            ( (eta_x x4 x5 x6) >.  (sqrt (#2.0))))`;;


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


let I_821707685=
   all_forall `ineq 
    [((#4.0), x1, (#6.3001));
     ((#4.0), x2, (square (#2.168)));
     ((#4.0), x3, (square (#2.168)));
     ((#4.0), x4, (#6.3001));
     ((#4.0), x5, (#6.3001));
     (square_2t0, x6, square_4t0)
    ]
    ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.63) \/ 
      (delta_x x1 x2 x3 x4 x5 x6) <. (#0.0))`;;

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

let J_906566422=
   all_forall `ineq 
    [((square (#1.255)), x, (#2.0))
    ]
    ( (crown (sqrt x)) <.  (--. (#0.1378)))`;;

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
            ( (eta_x x1 x2 x6) >.  (sqrt (#2.0))) \/ 
            ( (eta_x x2 x3 x4) >.  (sqrt (#2.0))) \/ 
            ( (eta_x x1 x3 x5) >.  (sqrt (#2.0))) \/ 
            ( (eta_x x4 x5 x6) >.  (sqrt (#2.0))))`;;

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

