


(**
 * Inequalities for the proof of the Dodecahedral Conjecture
 *) 

(* real number operations *)
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


(*
LOC: 2002 k.c page 42.
17.1  Group_1
val rand = Random.rand (3498743,108217949);
Random.randRange(0,valOf Int.maxInt) rand;
*)

(* interval verification in partK.cc *)
let D_576061419 =
   all_forall `ineq 
    [((#, x1, (#6.3001));
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

