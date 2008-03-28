


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


(* 
 * t = 1.25841
 * 2t = 2.51682
 * (2t)^2 = 6.3343829124
 *)
let dodecTruncSq = kepler_def `dodecTruncSq = #6.3343829124`
let four = kepler_def `four = #4.0`
let zero = kepler_def `zero = #0.0`

let tmp = `basicTet (x1 > x1)`

let basicTet =
  let bnds = `ineq 
    [(four, x1, dodecTruncSq);
     (four, x2, dodecTruncSq);
     (four, x3, dodecTruncSq);
     (four, x4, dodecTruncSq);
     (four, x5, dodecTruncSq);
     (four, x6, dodecTruncSq)]` 
  and mk_times x y = mk_binop `( *. )` x y 
  and mk_plus x y = mk_binop `( +. )` x y 
  and mk_gt x y = mk_binop `( >. )` x y 
  and mk_p (vol,sol,dih,const) = 
    let vt = mk_times vol `vol_x x1 x2 x3 x4 x5 x6` 
    and st = mk_times sol `sol_x x1 x2 x3 x4 x5 x6` 
    and dt = mk_times dih `dih_x x1 x2 x3 x4 x5 x6` in
      mk_gt (mk_plus vt (mk_plus st (mk_plus dt const))) `zero` in
    fun args -> all_forall (mk_comb(bnds,mk_p args))

(* interval verification in partK.cc *)
let D_576061419 = 
  basicTet 
    ( (tau_sigma_x x1 x2 x3 x4 x5 x6) -.  (  (#0.2529) *.  (dih_x x1 x2 x3 x4 x5 x6))) >. 
                (--. (#0.3442))) \/ 
            ( (dih_x x1 x2 x3 x4 x5 x6) <.  (#1.51)))`;;

