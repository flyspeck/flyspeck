(* system dependent :

   load_path :=
     ["/Users/thomashales/Desktop/flyspeck_google/source/inequalities/"]
        @ (!load_path)
*)

(*
needs "Examples/analysis.ml";;
needs "Examples/transc.ml";;
no longer needs "Jordan/lib_ext.ml";;
*)

let kepler_def = (* local_definition "kepler";; *) new_definition;;

prioritize_real();;

let max_real = new_definition(`max_real x y =
        if (y < x) then x else y`);;

let min_real = new_definition(`min_real x y =
        if (x < y) then x else y`);;

let min_num = new_definition
  `min_num (X:num->bool) = @m. (m IN X) /\ (!n. (n IN X) ==> (m <= n))`;;


let deriv = new_definition(`deriv f x = @d. (f diffl d)(x)`);;
let deriv2 = new_definition(`deriv2 f = (deriv (deriv f))`);;

(* ------------------------------------------------------------------ *)
(*  Extend atn to allow zero denominators.                            *)
(* ------------------------------------------------------------------ *)

(* new argument order 2/14/2008 to make it compatible with the 
   ANSI C arctan2 function.  Also reworked for better numerical
   stability in the regions that matter for us.  The way things
   are defined, it gives atn2(0,0) = -pi.  This is a bit strange,
   but we never need its value at the origin anyway.
*)

let atn2 = new_definition(`atn2(x,y) =
    if ( x > abs y ) then atn(y / x) else
    (if (y > &0) then ((pi / &2) - atn(x / y)) else
    (if (y < &0) then (-- (pi/ &2) - atn (x / y)) else ( -- pi )))`);;

(* ------------------------------------------------------------------ *)

let sqrt8 = kepler_def (`sqrt8 = sqrt (&8) `);;
let sqrt2 = kepler_def (`sqrt2 = sqrt (&2) `);;

(* ------------------------------------------------------------------ *)

let t0 = kepler_def (`t0 = (#1.255)`);;
let two_t0 = kepler_def(`two_t0 = (#2.51)`);;
let square_2t0 = kepler_def(`square_2t0 = two_t0*two_t0`);;
let square_4t0 = kepler_def(`square_4t0 = (&4)*square_2t0`);;
let pt = kepler_def(`pt = (&4)*(atn (sqrt2/(&5))) - (pi/(&3))`);;
let square = kepler_def(`square x = x*x`);;

(* ------------------------------------------------------------------ *)
(*  Standard constants.                                               *)
(* ------------------------------------------------------------------ *)

let zeta = kepler_def(`zeta= (&1)/((&2) * atn (sqrt2/(&5)))`);;
let doct = kepler_def(`doct= (pi - (&2)/zeta)/sqrt8`);;
let dtet = kepler_def(`dtet = sqrt2/zeta`);;
let pi_rt18 = kepler_def(`pi_rt18= pi/(sqrt (&18))`);;

(* ------------------------------------------------------------------ *)
(*  Technical constants.                                              *)
(* ------------------------------------------------------------------ *)

let rogers=kepler_def(`rogers= sqrt2/zeta`);;
let compression_cut=kepler_def(`compression_cut=(#1.41)`);;
let squander_target=kepler_def(`squander_target =
        ((&4)*pi*zeta - (&8))*pt`);;
let xiV=kepler_def(`xiV=(#0.003521)`);;
let xi_gamma=kepler_def(`xi_gamma=(#0.01561)`);;
let xi'_gamma=kepler_def(`xi'_gamma=(#0.00935)`);;
let xi_kappa=kepler_def(`xi_kappa= -- (#0.029)`);;
let xi_kappa_gamma=kepler_def(`xi_kappa_gamma=
        xi_kappa+xi_gamma`);;
let pi_max =kepler_def(`xi_max = (#0.006688)`);;
let t4 = kepler_def(`t4= (#0.1317)`);;
let t5 = kepler_def(`t5= (#0.27113)`);;
let t6 = kepler_def(`t6= (#0.41056)`);;
let t7 = kepler_def(`t7= (#0.54999)`);;
let t8 = kepler_def(`t8= (#0.6045)`);;
let t9 = kepler_def(`t9= (#0.6978)`);;
let t10= kepler_def(`t10=(#0.7891)`);;
let s5 = kepler_def(`s5= --(#0.05704)`);;
let s6 = kepler_def(`s6= --(#0.11408)`);;
let s7 = kepler_def(`s7= --(#0.17112)`);;
let s8 = kepler_def(`s8= --(#0.22816)`);;
let s9 = kepler_def(`s9= --(#0.1972)`);;

(* Note this is what s10 is in DCG p128, but for the blueprint
   it should be made -eps0 so that the 8pt bound holds by margin eps0 *)
let s10= kepler_def(`s10= #0.0`);;
let eps0 = kepler_def(`eps0 = #0.000000000001`);; (* eps0 = 10^-12 *)


let Z31 = kepler_def(`Z31 = (#0.00005)`);;
let Z32 = kepler_def(`Z32 = -- (#0.05714)`);;
let Z33 = kepler_def(`Z33 = s6 - (#3.0)*Z31`);;
let Z41 = kepler_def(`Z41 = s5 - Z31`);;
let Z42 = kepler_def(`Z42 = s6 - (#2.0)*Z31`);;

let D31 = kepler_def(`D31 = t4 - (#0.06585)`);; (* = 0.06585 *)
let D32 = kepler_def(`D32 = (#0.13943)`);;
let D33 = kepler_def(`D33 = t6 - (#0.06585)*(#3.0)`);;
let D41 = kepler_def(`D41 = t5 - (#0.06585)`);;
let D42 = kepler_def(`D42 = t6 - (#2.0)*(#0.06585)`);;
let D51 = kepler_def(`D51 = t6 - (#0.06585)`);;

(* ------------------------------------------------------------------ *)
(*  Ferguson's thesis constants from DCG-2006-Sec 17.4                *)
(* ------------------------------------------------------------------ *)

let pp_a1 = kepler_def(`pp_a1 = #0.38606588081240521`);;
let pp_a2 = kepler_def(`pp_a2 = #0.4198577862`);;
let pp_d0 = kepler_def(`pp_d0 = #1.4674`);;
let pp_m  = kepler_def(`pp_m = #0.3621`);;
let pp_b  = kepler_def(`pp_b = #0.49246`);;
let pp_a  = kepler_def(`pp_a = #0.0739626`);;
let pp_bc  = kepler_def(`pp_bc = #0.253095`);;
let pp_c = kepler_def(`pp_c = #0.1533667634670977`);;
let pp_d = kepler_def(`pp_d = #0.2265`);;
(* solt0 = Solid[2,2,2,2,2,Sqrt[8]] *)
let pp_solt0 = kepler_def(`pp_solt0 = &2 * atn2 (&1, sqrt8)`);;

(* ------------------------------------------------------------------ *)
(*  This polynomial is essentially the Cayley-Menger determinant.     *)
(* ------------------------------------------------------------------ *)
let delta_x = kepler_def (`delta_x x1 x2 x3 x4 x5 x6 =
        x1*x4*(--x1 + x2 + x3 -x4 + x5 + x6) +
        x2*x5*(x1 - x2 + x3 + x4 -x5 + x6) +
        x3*x6*(x1 + x2 - x3 + x4 + x5 - x6)
        -x2*x3*x4 - x1*x3*x5 - x1*x2*x6 -x4*x5*x6`);;

(* ------------------------------------------------------------------ *)
(*   The partial derivative of delta_x with respect to x4.            *)
(* ------------------------------------------------------------------ *)

let delta_x4 = kepler_def(`delta_x4 x1 x2 x3 x4 x5 x6
        =  -- x2* x3 -  x1* x4 + x2* x5
        + x3* x6 -  x5* x6 + x1* (-- x1 +  x2 +  x3 -  x4 +  x5 +  x6)`);;

let delta_x6 = kepler_def(`delta_x6 x1 x2 x3 x4 x5 x6
	= -- x1 * x2 - x3*x6 + x1 * x4
	+ x2* x5 - x4* x5 + x3*(-- x3 + x1 + x2 - x6 + x4 + x5)`);;

(* ------------------------------------------------------------------ *)
(*  Circumradius       .                                              *)
(* ------------------------------------------------------------------ *)

(* same as ups_x 
let u_x = kepler_def(
        `u_x x1 x2 x3 = (--(x1*x1+x2*x2+x3*x3)) +
        (&2) * (x1*x2+x2*x3+x3*x1)`);;
*)

let ups_x = kepler_def(`ups_x x1 x2 x6 = --x1*x1 - x2*x2 - x6*x6 + &2 *x1*x6 + &2 *x1*x2 + &2 *x2*x6`);;


let eta_x = kepler_def(`eta_x x1 x2 x3 =
        (sqrt ((x1*x2*x3)/(ups_x x1 x2 x3)))
        `);;

let eta_y = kepler_def(`eta_y y1 y2 y3 =
                let x1 = y1*y1 in
                let x2 = y2*y2 in
                let x3 = y3*y3 in
                eta_x x1 x2 x3`);;

let rho_x = kepler_def(`rho_x x1 x2 x3 x4 x5 x6 =
        --x1*x1*x4*x4 - x2*x2*x5*x5 - x3*x3*x6*x6 +
        (&2)*x1*x2*x4*x5 + (&2)*x1*x3*x4*x6 + (&2)*x2*x3*x5*x6`);;

let rad2_y = kepler_def(`rad2_y y1 y2 y3 y4 y5 y6 =
        let (x1,x2,x3,x4,x5,x6)= (y1*y1,y2*y2,y3*y3,y4*y4,y5*y5,y6*y6) in
        (rho_x x1 x2 x3 x4 x5 x6)/((delta_x x1 x2 x3 x4 x5 x6)*(&4))`);;


let chi_x = kepler_def(`chi_x x1 x2 x3 x4 x5 x6
        = -- (x1*x4*x4) + x1*x4*x5 + x2*x4*x5 -  x2*x5*x5
        + x1*x4*x6 + x3*x4*x6 +
   x2*x5*x6 + x3*x5*x6 -  (&2) * x4*x5*x6 -  x3*x6*x6`);;



(* ------------------------------------------------------------------ *)
(*   The formula for the dihedral angle of a simplex.                 *)
(*   The variables xi are the squares of the lengths of the edges.    *)
(*   The angle is computed along the first edge (x1).                 *)
(* ------------------------------------------------------------------ *)

let dih_x = kepler_def(`dih_x x1 x2 x3 x4 x5 x6 =
       let d_x4 = delta_x4 x1 x2 x3 x4 x5 x6 in
       let d = delta_x x1 x2 x3 x4 x5 x6 in
       pi/ (&2) +  atn2( (sqrt ((&4) * x1 * d)),--  d_x4)`);;


let dih_y = kepler_def(`dih_y y1 y2 y3 y4 y5 y6 =
       let (x1,x2,x3,x4,x5,x6)= (y1*y1,y2*y2,y3*y3,y4*y4,y5*y5,y6*y6) in
       dih_x x1 x2 x3 x4 x5 x6`);;

let dih2_y = kepler_def(`dih2_y y1 y2 y3 y4 y5 y6 =
        dih_y y2 y1 y3 y5 y4 y6`);;

let dih3_y = kepler_def(`dih3_y y1 y2 y3 y4 y5 y6 =
        dih_y y3 y1 y2 y6 y4 y5`);;

let dih2_x = kepler_def(`dih2_x x1 x2 x3 x4 x5 x6 =
        dih_x x2 x1 x3 x5 x4 x6`);;

let dih3_x = kepler_def(`dih3_x x1 x2 x3 x4 x5 x6 =
	dih_x x3 x1 x2 x6 x4 x5`);;


(* ------------------------------------------------------------------ *)
(*   Harriot-Euler formula for the area of a spherical triangle       *)
(*   in terms of the angles: area = alpha+beta+gamma - pi             *)
(* ------------------------------------------------------------------ *)

let sol_x = kepler_def(`sol_x x1 x2 x3 x4 x5 x6 =
        (dih_x x1 x2 x3 x4 x5 x6) +
        (dih_x x2 x3 x1 x5 x6 x4) +  (dih_x x3 x1 x2 x6 x4 x5) -  pi`);;

let sol_y = kepler_def(`sol_y y1 y2 y3 y4 y5 y6 =
        (dih_y y1 y2 y3 y4 y5 y6) +
        (dih_y y2 y3 y1 y5 y6 y4) +  (dih_y y3 y1 y2 y6 y4 y5) -  pi`);;


(* ------------------------------------------------------------------ *)
(*   The Cayley-Menger formula for the volume of a simplex            *)
(*   The variables xi are the squares of the lengths of the edges.    *)
(* ------------------------------------------------------------------ *)

let vol_x = kepler_def(`vol_x x1 x2 x3 x4 x5 x6 =
        (sqrt (delta_x x1 x2 x3 x4 x5 x6))/ (&12)`);;

(* ------------------------------------------------------------------ *)
(*   Some lower dimensional funcions and Rogers simplices.            *)
(* ------------------------------------------------------------------ *)

let beta = kepler_def(`beta psi theta =
        let arg = ((cos psi)*(cos psi) -  (cos theta)*(cos theta))/
        ((&1) -  (cos theta)*(cos theta))  in
        (acs (sqrt arg))`);;

let arclength = kepler_def(`arclength a b c =
        pi/(&2) + (atn2( (sqrt (ups_x (a*a) (b*b) (c*c))),(c*c - a*a  -b*b)))`);;


let volR = kepler_def(`volR a b c =
        (sqrt (a*a*(b*b-a*a)*(c*c-b*b)))/(&6)`);;

let solR = kepler_def(`solR a b c =
        (&2)*atn2( sqrt(((c+b)*(b+a))), sqrt ((c-b)*(b-a)))`);;

let dihR = kepler_def(`dihR a b c =
        atn2( sqrt(b*b-a*a),sqrt (c*c-b*b))`);;

let vorR = kepler_def(`vorR a b c =
        (&4)*(--doct*(volR a b c) + (solR a b c)/(&3))`);;

let denR = kepler_def(`denR a b c =
        (solR a b c)/((&3)*(volR a b c))`);;

let tauR = kepler_def(`tauR a b c =
        --(volR a b c) + (solR a b c)*zeta*pt`);;

let quoin = kepler_def(`quoin a b c =
        let u = sqrt ((c*c-b*b)/(b*b-a*a)) in
        if ((a>=b) \/ (b>=c)) then (&0) else
        (--(a*a + a*c-(&2)*c*c)*(c-a)*atn(u)/(&6) +
        a*(b*b-a*a)*u/(&6) 
        - ((&2)/(&3))*c*c*c*(atn2((b+c),(u*(b-a)))))`);;

let qy = kepler_def(`qy y1 y2 y3 t =
        quoin (y1/(&2)) (eta_y y1 y2 y3) t`);;

let quo_x = kepler_def(`quo_x x y z = qy (sqrt x) (sqrt y) (sqrt z) t0`);;

let qn = kepler_def(`qn y1 y2 z t =
        --(&4)*doct*((qy y1 y2 z t) +(qy y2 y1 z t))`);;

let phi = kepler_def(`phi h t =
        (&2)*((&2) - doct*h*t*(h+t))/(&3)`);;

let phi0 = kepler_def(`phi0 =
        phi t0 t0`);;

let eta0 = kepler_def(`eta0 h =
        eta_y ((&2)*h) (two_t0) (&2)`);;
        
let crown = kepler_def(`crown h =
        let e = eta0 h in
        (&2)*pi*((&1)- h/e)*(phi h e - phi0)`);;

let anc = kepler_def(`anc y1 y2 y6 =
        let h1 = y1/(&2) in
        let h2 = y2/(&2) in
        let b = eta_y y1 y2 y6 in
        let c = eta0 h1 in
        if (b>c) then (&0) else
                --(dihR h1 b c)*(crown h1)/((&2)*pi)
                -(solR h1 b c)*phi0 + (vorR h1 b c)
                -(dihR h2 b c)*((&1)-h2/t0)*((phi h2 t0)-phi0)
                -(solR h2 b c)*(phi0) + (vorR h2 b c)`);;

let K0 = kepler_def(`K0 y1 y2 y6 = 
	(vorR (y1/(&2)) (eta_y y1 y2 y6) (sqrt2)) +
	(vorR (y2/(&2)) (eta_y y1 y2 y6) (sqrt2)) -
        (dihR (y1/(&2)) (eta_y y1 y2 y6) (sqrt2))*
          (&1 - (y1/(sqrt8)))*(phi (y1/(&2)) sqrt2)`);;

let AH = kepler_def(`AH h t = (&1 - (h/t))*((phi h t) - (phi t t))`);;

let BHY = kepler_def(`BHY y = (AH (y/(&2)) t0) + phi0`);;

(*

(* This definition still needs to be finished *)
let overlap_f = kepler_def(
  `overlap_f y1 y2 =
    let ell = (#3.2) in
    let lam = (#1.945) in
    let dih1 = dih_y y1 t0 y2 lam ell lam in
    let dih2 = dih_y y2 t0 y1 lam ell lam in
    let s = sol_y y2 t0 y1 lam ell lam in
    let phi1 = phi (y1/(&2)) t0 in
    let phi2 = phi (y2/(&2)) t0 in
    (&2)*(zeta*pt - phi0)*s 
      + (&2)*dih1*((&1) - (y1/two_t0))*(phi0-phi1)
      + (&2)*dih2*((&1) - (y2/two_t0))*(phi0-phi2)
   + xxxxx-- need to insert tau terms ---xxxxx`);;
*)


(* ------------------------------------------------------------------ *)
(*   Analytic and truncated Voronoi function                          *)
(* ------------------------------------------------------------------ *)

let KY = kepler_def(`KY y1 y2 y3 y4 y5 y6 =
   (K0 y1 y2 y6) + (K0 y1 y3 y5) + 
  (dih_y y1 y2 y3 y4 y5 y6)*
    (&1 - (y1/(sqrt8)))*(phi (y1/(&2)) sqrt2)`);;

let KX = kepler_def(`KX x1 x2 x3 x4 x5 x6 =
   KY (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5) (sqrt x6)`);;

let vor_analytic_x = kepler_def(`vor_analytic_x x1 x2 x3 x4 x5 x6 =
        let del = sqrt (delta_x x1 x2 x3 x4 x5 x6) in
        let u126 = ups_x x1 x2 x6 in
        let u135 = ups_x x1 x3 x5 in
        let u234 = ups_x x2 x3 x4 in
        let vol = ((&1)/((&48)*del))*
                ((x1*(x2+x6-x1)+x2*(x1+x6-x2))*(chi_x x4 x5 x3 x1 x2 x6)/u126
               +(x2*(x3+x4-x2)+x3*(--x3+x4+x2))*(chi_x x6 x5 x1 x3 x2 x4)/u234
               +(x1*(--x1+x3+x5)+x3*(x1-x3+x5))*(chi_x x4 x6 x2 x1 x3 x5)/u135)
       in
       (&4)*(--doct*vol + (sol_x x1 x2 x3 x4 x5 x6)/(&3))`);;

let vor_analytic_x_flipped = kepler_def(`vor_analytic_x_flipped x1 x2 x3 x4 x5 x6 =
        vor_analytic_x x1 x5 x6 x4 x2 x3`);;

let octavor_analytic_x = kepler_def(`octavor_analytic_x 
  x1 x2 x3 x4 x5 x6 =
  (#0.5)*((vor_analytic_x x1 x2 x3 x4 x5 x6) + (vor_analytic_x_flipped x1 x2 x3 x4 x5 x6))`);;

let tau_analytic_x = kepler_def(`tau_analytic_x x1 x2 x3 x4 x5 x6 =
        (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - 
                (vor_analytic_x x1 x2 x3 x4 x5 x6)`);;

(* bug found 3/21/2008: had parenthesis misplaced. -tch *)

let kappa = kepler_def(`kappa y1 y2 y3 y4 y5 y6 =
        (crown (y1/(&2)))*(dih_y y1 y2 y3 y4 y5 y6)/((&2)*pi) 
        + (anc y1 y2 y6) + (anc y1 y3 y5)`);;

let kappa_dih_y = kepler_def(`kappa_dih_y y1 y2 y3 y5 y6 d =
        (crown (y1/(&2)))*d/((&2)*pi) 
        + (anc y1 y2 y6) + (anc y1 y3 y5)`);;


let level_at = kepler_def(`level_at h t = if (h<t) then h else t`);;

let vorstar = kepler_def(`vorstar h1 h2 h3 a1 a2 a3 t=
       let phit = phi t t in
        a1*((&1)-(level_at h1 t)/t)*(phi h1 t - phit)
        +a2*((&1)-(level_at h2 t)/t)*(phi h2 t - phit)
        +a3*((&1)-(level_at h3 t)/t)*(phi h3 t - phit)
        +(a1+a2+a3-pi)*phit`);;

let vort_y = kepler_def(`vort_y y1 y2 y3 y4 y5 y6 t =
        let h1 = y1/(&2) in
        let h2 = y2/(&2) in
        let h3 = y3/(&2) in
        let a1 = dih_y y1 y2 y3 y4 y5 y6 in
        let a2 = dih2_y y1 y2 y3 y4 y5 y6 in
        let a3 = dih3_y y1 y2 y3 y4 y5 y6 in
        (vorstar h1 h2 h3 a1 a2 a3 t)+
                (qn y1 y2 y6 t)+(qn y2 y3 y4 t)+(qn y1 y3 y5 t)`);;

let vor_0_y = kepler_def(`vor_0_y y1 y2 y3 y4 y5 y6 =
	vort_y y1 y2 y3 y4 y5 y6 t0`);;

let tau_0_y = kepler_def(`tau_0_y y1 y2 y3 y4 y5 y6 =
        (sol_y y1 y2 y3 y4 y5 y6)*zeta*pt - (vor_0_y y1 y2 y3 y4 y5
        y6)`);;

let vor_0_x = kepler_def(`vor_0_x x1 x2 x3 x4 x5 x6=
        let (y1,y2,y3,y4,y5,y6) = (sqrt x1,sqrt x2,sqrt x3,
                sqrt x4,sqrt x5,sqrt x6) in
        vor_0_y y1 y2 y3 y4 y5 y6`);;

let tau_0_x = kepler_def(`tau_0_x x1 x2 x3 x4 x5 x6 =
        (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - 
                (vor_0_x x1 x2 x3 x4 x5 x6)`);;

let vort_x = kepler_def(`vort_x x1 x2 x3 x4 x5 x6 t =
        let (y1,y2,y3,y4,y5,y6) = (sqrt x1,sqrt x2,sqrt x3,
                sqrt x4,sqrt x5,sqrt x6) in
        vort_y y1 y2 y3 y4 y5 y6 t`);;

let tauVt_x = kepler_def(`tauVt_x x1 x2 x3 x4 x5 x6 t =
        (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - 
                (vort_x x1 x2 x3 x4 x5 x6 t)`);;

let vorA_x = kepler_def(`vorA_x x1 x2 x3 x4 x5 x6 =
    if ((x5 <= (square (#2.77))) /\ (x6 <= (square (#2.77))) /\
	(((eta_x x4 x5 x6) < sqrt2)))
    then (vor_analytic_x x1 x2 x3 x4 x5 x6 )
    else (vor_0_x x1 x2 x3 x4 x5 x6)`);;

let tauA_x = kepler_def(`tauA_x x1 x2 x3 x4 x5 x6 =
        (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - 
                (vorA_x x1 x2 x3 x4 x5 x6)`);;

let vorC0_x = kepler_def(`vorC0_x x1 x2 x3 x4 x5 x6 =
    if ((x4 <= (square (#2.77))) \/ 
	((eta_x x4 x5 x6 <= sqrt2) /\ (eta_x x2 x3 x4 <= sqrt2)))
    then (vor_analytic_x x1 x2 x3 x4 x5 x6 )
    else (vor_0_x x1 x2 x3 x4 x5 x6)`);;

let tauC0_x = kepler_def(`tauC0_x x1 x2 x3 x4 x5 x6 =
        (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - 
                (vorC0_x x1 x2 x3 x4 x5 x6)`);;

let vorC_x = kepler_def(`vorC_x x1 x2 x3 x4 x5 x6 =
    if ((x4 <= (square (#2.77))) \/ 
	((eta_x x4 x5 x6 <= sqrt2) /\ (eta_x x2 x3 x4 <= sqrt2)) \/
       ((square (#2.45) <= x2) /\ ((square (#2.45) <= x6))))
    then (vor_analytic_x x1 x2 x3 x4 x5 x6 )
    else (vor_0_x x1 x2 x3 x4 x5 x6)`);;

let tauC_x = kepler_def(`tauC_x x1 x2 x3 x4 x5 x6 =
        (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - 
                (vorC_x x1 x2 x3 x4 x5 x6)`);;


let v0x = kepler_def(`v0x x1 x2 x3 x4 x5 x6 =
	let (y1,y2,y3) = (sqrt x1,sqrt x2,sqrt x3) in
	(-- (BHY y1))*y1*(delta_x6 x1 x2 x3 x4 x5 x6) +
	(BHY y2)* y2* (ups_x x1 x3 x5) +
	  (-- (BHY y3))*y3*(delta_x4 x1 x2 x3 x4 x5 x6)`);;

let v1x = kepler_def(`v1x x1 x2 x3 x4 x5 x6 =
	let (y1,y2,y3) = (sqrt x1,sqrt x2,sqrt x3) in
	(-- (BHY y1 - (zeta*pt)))*y1*(delta_x6 x1 x2 x3 x4 x5 x6) +
	(BHY y2 - (zeta*pt))* y2* (ups_x x1 x3 x5) +
	  (-- (BHY y3 - (zeta*pt)))*y3*(delta_x4 x1 x2 x3 x4 x5 x6)`);;


(* ------------------------------------------------------------------ *)
(*   The function gamma is called the "compression" in the proof      *)
(*   of the Kepler conjecture.  It is interpreted as a linearized     *)
(*   density of a simplex.                                            *)
(* ------------------------------------------------------------------ *)

let gamma_x = kepler_def(`gamma_x x1 x2 x3 x4 x5 x6 =
        --doct*(vol_x x1 x2 x3 x4 x5 x6) + ((&2)/(&3))*
        ((dih_x x1 x2 x3 x4 x5 x6) + (dih_x x2 x3 x1 x5 x6 x4)+
        (dih_x x3 x1 x2 x6 x4 x5) + (dih_x x4 x5 x3 x1 x2 x6)+
        (dih_x x5 x6 x1 x2 x3 x4) + (dih_x x6 x5 x1 x3 x2 x4))
        - (&4)*pi/(&3)`);;

let tau_gamma_x = kepler_def(`tau_gamma_x x1 x2 x3 x4 x5 x6 =
         (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - 
                (gamma_x x1 x2 x3 x4 x5 x6)`);;

                (* 1.41^2 = 1.9881 *)
let rad2_x = kepler_def(`rad2_x x1 x2 x3 x4 x5 x6 =
        (rho_x x1 x2 x3 x4 x5 x6)/((delta_x x1 x2 x3 x4 x5 x6)*(&4))`);;

let sigma_qrtet_x = kepler_def(`sigma_qrtet_x x1 x2 x3 x4 x5 x6=
        let r = rad2_x x1 x2 x3 x4 x5 x6 in
        let r_cut = (#1.9881) in
        if (r >= r_cut) then
                vor_analytic_x x1 x2 x3 x4 x5 x6
        else gamma_x x1 x2 x3 x4 x5 x6`);;

let sigma1_qrtet_x = kepler_def(`sigma1_qrtet_x x1 x2 x3 x4 x5 x6=
	sigma_qrtet_x x1 x2 x3 x4 x5 x6 - (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt`);;

let tau_sigma_x = kepler_def `tau_sigma_x x1 x2 x3 x4 x5 x6=
       -- (sigma1_qrtet_x x1 x2 x3 x4 x5 x6)`;;

let sigma32_qrtet_x = kepler_def(`sigma32_qrtet_x x1 x2 x3 x4 x5 x6=
	sigma_qrtet_x x1 x2 x3 x4 x5 x6 - 
            (#3.2)*(sol_x x1 x2 x3 x4 x5 x6)*zeta*pt`);;

let mu_flat_x = kepler_def(`mu_flat_x x1 x2 x3 x4 x5 x6 =
        let r1 = eta_x x2 x3 x4 in
        let r2 = eta_x x4 x5 x6 in
        if ((r1 >= sqrt2)\/(r2 >= sqrt2)) 
                then vor_analytic_x x1 x2 x3 x4 x5 x6
        else gamma_x x1 x2 x3 x4 x5 x6`);;

let taumu_flat_x = kepler_def(`taumu_flat_x x1 x2 x3 x4 x5 x6 =
	(sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - 
          (mu_flat_x x1 x2 x3 x4 x5 x6)`);;

let mu_upright_x = kepler_def(`mu_upright_x x1 x2 x3 x4 x5 x6 =
        let r1 = eta_x x1 x2 x6 in
        let r2 = eta_x x1 x3 x5 in
        if ((r1 >= sqrt2)\/(r2 >= sqrt2)) 
                then vor_analytic_x x1 x2 x3 x4 x5 x6
        else gamma_x x1 x2 x3 x4 x5 x6`);;

let mu_flipped_x = kepler_def(`mu_flipped_x x1 x2 x3 x4 x5 x6 =
	mu_upright_x x1 x5 x6 x4 x2 x3`);;



let vor_0_x_flipped = kepler_def(`vor_0_x_flipped x1 x2 x3 x4 x5 x6=
        vor_0_x x1 x5 x6 x4 x2 x3`);;

let octavor0_x = kepler_def(`octavor0_x x1 x2 x3 x4 x5 x6 = 
     (#0.5)* (vor_0_x x1 x2 x3 x4 x5 x6 + (vor_0_x_flipped x1 x2 x3 x4 x5 x6))`);;

(* STM changed to use mu_flipped_x and vor_0_x_flipped instead of the definition *)
(* let nu_x = kepler_def(`nu_x x1 x2 x3 x4 x5 x6 = *)
(*         ((&1)/(&2))* *)
(*         ( *)
(*                (mu_upright_x x1 x2 x3 x4 x5 x6)+ *)
(*                (mu_upright_x x1 x5 x6 x4 x2 x3)+ *)
(*                (vor_0_x x1 x2 x3 x4 x5 x6)- *)
(*                (vor_0_x x1 x5 x6 x4 x2 x3))`);; *)
let nu_x = kepler_def(`nu_x x1 x2 x3 x4 x5 x6 =
        ((&1)/(&2))*
        (
               (mu_upright_x x1 x2 x3 x4 x5 x6)+
               (mu_flipped_x x1 x2 x3 x4 x5 x6)+
               (vor_0_x x1 x2 x3 x4 x5 x6)-
               (vor_0_x_flipped x1 x2 x3 x4 x5 x6))`);;

(* STM changed to use vor_0_x_flipped instead of the definition *)
(* let nu_gamma_x = kepler_def(`nu_gamma_x x1 x2 x3 x4 x5 x6 = *)
(*         ((&1)/(&2))* *)
(*         ( *)
(*                (&2 * (gamma_x x1 x2 x3 x4 x5 x6))+ *)
(*                (vor_0_x x1 x2 x3 x4 x5 x6)- *)
(*                (vor_0_x x1 x5 x6 x4 x2 x3))`);; *)
let nu_gamma_x = kepler_def(`nu_gamma_x x1 x2 x3 x4 x5 x6 =
        ((&1)/(&2))*
        (
               (&2 * (gamma_x x1 x2 x3 x4 x5 x6))+
               (vor_0_x x1 x2 x3 x4 x5 x6)-
               (vor_0_x_flipped x1 x2 x3 x4 x5 x6))`);;

let taunu_x = kepler_def(`taunu_x x1 x2 x3 x4 x5 x6 =
	(sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - (nu_x x1 x2 x3 x4 x5 x6)`);;



(* score for upright quarters in a quasi-regular octahedron.
   I don't think I had a name for this specifically. *)
(* let octa_x = kepler_def(`octa_x x1 x2 x3 x4 x5 x6 =  *)
(* 	(#0.5)*( *)
(*                (mu_upright_x x1 x2 x3 x4 x5 x6)+ *)
(*                (mu_upright_x x1 x5 x6 x4 x2 x3))`);; *)

let octa_x = kepler_def(`octa_x x1 x2 x3 x4 x5 x6 = 
	(#0.5)*(
               (mu_upright_x x1 x2 x3 x4 x5 x6)+
               (mu_flipped_x x1 x2 x3 x4 x5 x6))`);;

let sigmahat_x = kepler_def(`sigmahat_x x1 x2 x3 x4 x5 x6 =
        let r234 = eta_x x2 x3 x4 in
        let r456 = eta_x x4 x5 x6 in
        let v0 = (if (sqrt2 <= r456) then
	              (vor_0_x x1 x2 x3 x4 x5 x6) 
	          else if (sqrt2 <= r234) then
	            (vor_analytic_x x1 x2 x3 x4 x5 x6)
	          else 
	            (gamma_x x1 x2 x3 x4 x5 x6)) in
	let v1 = (if ((r234 <= sqrt2) /\ (r456 <= sqrt2)) then
		      max_real v0 (gamma_x x1 x2 x3 x4 x5 x6) 
		  else v0) in
	let v2 = (if (sqrt2 <= r234) then
		    max_real v1 (vor_analytic_x x1 x2 x3 x4 x5 x6)
		  else v1) in
	let v3 = (if ((square (#2.6)) <= x4) /\ ((square (#2.2)) <= x1)
		  then max_real v2 	  (vor_0_x x1 x2 x3 x4 x5 x6) 
		  else v2) in
	let v4 = (if ((square (#2.7) <= x4))
		  then 
		    max_real v3 (vor_0_x x1 x2 x3 x4 x5 x6) 
		  else v3) in
	  if (sqrt2 <= r456) 
	  then
	    max_real v4 (vor_analytic_x x1 x2 x3 x4 x5 x6)
	  else v4`);;

let sigmahat_x' = kepler_def(`sigmahat_x' x1 x2 x3 x4 x5 x6 =
    let r234 = eta_x x2 x3 x4 in
    let r456 = eta_x x4 x5 x6 in
    let P1 = sqrt2 <= r456 in
    let P2 = sqrt2 <= r234 in
    let P3 = square (#2.2) <= x1 in
    let P4 = square (#2.6) <= x4 in
    let P5 = square (#2.7) <= x4 in
    if ~P1 /\ P2 /\ ~P5 /\ (~P3 \/ ~P4) then 
      vor_analytic_x x1 x2 x3 x4 x5 x6
    else if ~P1 /\ ~P2 /\ ~P5 /\ (~P3 \/ ~P4) then
      gamma_x x1 x2 x3 x4 x5 x6
    else if ~P1 /\ ~P2 /\ P4 /\ (P3 \/ P5) then
      max_real (gamma_x x1 x2 x3 x4 x5 x6) (vor_0_x x1 x2 x3 x4 x5 x6)
    else
      max_real (vor_analytic_x x1 x2 x3 x4 x5 x6) (vor_0_x x1 x2 x3 x4 x5 x6)`);;

let sigmahatpi_x = kepler_def(`sigmahatpi_x x1 x2 x3 x4 x5 x6 =
        let r234 = eta_x x2 x3 x4 in
        let r456 = eta_x x4 x5 x6 in
	let piF = (#2.0)*(xiV) + (xi_gamma) in
        let v0 = (if (sqrt2 <= r456) then
	  (vor_0_x x1 x2 x3 x4 x5 x6) 
	else if (sqrt2 <= r234) then
	  (vor_analytic_x x1 x2 x3 x4 x5 x6)
	else 
	  (gamma_x x1 x2 x3 x4 x5 x6)) in
	let v1 = (if ((r234 <= sqrt2) /\ (r456 <= sqrt2)) then
		    max_real v0 (gamma_x x1 x2 x3 x4 x5 x6) 
		  else v0) in
	let v2 = (if (sqrt2 <= r234) then
		    max_real v1 (vor_analytic_x x1 x2 x3 x4 x5 x6)
		  else v1) in
	let v3 = (if ((square (#2.6)) <= x4) /\ ((square (#2.2)) <= x2)
		  then max_real v2 (piF + (vor_0_x x1 x2 x3 x4 x5 x6)) 
		  else v2) in
	let v4 = (if ((square (#2.7) <= x4))
		  then 
		    max_real v3 (piF + (vor_0_x x1 x2 x3 x4 x5 x6) )
		  else v3) in
	  if (sqrt2 <= r456) 
	  then
	    max_real v4 (vor_analytic_x x1 x2 x3 x4 x5 x6)
	  else v4`);;
    

let tauhat_x = kepler_def(`tauhat_x x1 x2 x3 x4 x5 x6 =
    (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - (sigmahat_x x1 x2 x3 x4 x5 x6)`);;

let tauhatpi_x = kepler_def(`tauhatpi_x x1 x2 x3 x4 x5 x6 =
    (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - (sigmahatpi_x x1 x2 x3 x4 x5 x6)`);;

let pi_prime_tau = kepler_def
  `pi_prime_tau k0 k1 k2 = 
    if (k2=0) then (&0)
    else if (k0=1) /\ (k1=1) /\ (k2=1) then (#0.0254)
    else (#0.04683 + (&k0 + &(2*k2) - #3.0)*((#0.008)/(#3.0))
     + (&k2) * (#0.0066))`;;

let pi_prime_sigma = kepler_def
  `pi_prime_sigma k0 (k1:num) k2 = 
    if (k2=0) then (&0)
    else if (k0=1) /\ (k2=1) then (#0.009)
    else (& (k0 + 2*k2))*((#0.008)/(#3.0)) + (&k2)* (#0.009)`;;


(* ------------------------------------------------------------------ *)
(* The following definitions also appear in Jordan/misc_defs_and_lemmas.ml *)
(* ------------------------------------------------------------------ *)

(* mk_local_interface "kepler";; *)

overload_interface
 ("+", `euclid_plus:(num->real)->(num->real)->(num->real)`);;

make_overloadable "*#" `:A -> B -> B`;;

let euclid_scale = kepler_def
  `euclid_scale t f = \ (i:num). (t* (f i))`;;

overload_interface ("*#",`euclid_scale`);; (* `kepler'euclid_scale`);; *)

parse_as_infix("*#",(20,"right"));;

let euclid_neg = kepler_def `euclid_neg (f:num->real) = \ (i:num). (-- (f i))`;;

(* This is highly ambiguous: -- f x can be read as
   (-- f) x or as -- (f x).  *)
overload_interface ("--",`euclid_neg`);; (* `kepler'euclid_neg`);; *)

overload_interface
  ("-", `euclid_minus:(num->real)->(num->real)->(num->real)`);;

let euclid_plus = kepler_def
  `euclid_plus (f:num->real) g = \ (i:num). (f i) + (g i)`;;

let euclid_minus = kepler_def
  `euclid_minus (f:num->real) g = \(i:num). (f i) - (g i)`;;

let euclid = kepler_def `euclid n v <=> !m. (n <= m) ==> (v (m:num) = &0)`;;

let euclid0 = kepler_def `euclid0 = \(i:num). &0`;;

let coord = kepler_def `coord i (f:num->real) = f i`;;

let dot = kepler_def `dot f g =
  let (n = (min_num (\m. (euclid m f) /\ (euclid m g)))) in
  sum (0,n) (\i. (f i)*(g i))`;;

let norm = kepler_def `norm f = sqrt(dot f f)`;;


let d_euclid = kepler_def `d_euclid f g = norm (f - g)`;;


(* ------------------------------------------------------------------ *)
(* Three space *)
(* ------------------------------------------------------------------ *)

let real3_exists = prove( `?f. (!n. (n> 2) ==> (f n = &0))`,
       EXISTS_TAC `(\j:num. &0)` THEN
       BETA_TAC THEN (REWRITE_TAC[])
			);;

let real3 = new_type_definition "real3" ("mk_real3","dest_real3") real3_exists;;

overload_interface
 ("+", `real3_plus:real3->real3 ->real3`);;

let real3_scale = new_definition
  `real3_scale t v = mk_real3 (t *# dest_real3 v)`;;

overload_interface ("*#",`real3_scale`);;

let real3_neg = new_definition `real3_neg v = mk_real3 (-- dest_real3 v)`;;

(* This is highly ambiguous: -- f x can be read as
   (-- f) x or as -- (f x).  *)
overload_interface ("--",`real3_neg`);; 

overload_interface
  ("-", `real3_minus:real3->real3->real3`);;

let real3_plus =new_definition
  `real3_plus v w = mk_real3 (euclid_plus (dest_real3 v) (dest_real3 w))`;;

let real3_minus = new_definition
  `real3_minus v w = mk_real3 (euclid_minus (dest_real3 v)  (dest_real3 w))`;;

let coord3 = new_definition `coord3 i v = coord i (dest_real3 v)`;;

let dot3 = new_definition `dot3 v w = dot (dest_real3 v) (dest_real3 w)`;;

let norm3 = new_definition `norm3 v = sqrt(dot3 v v)`;;

let d3 = new_definition `d3 v w = norm3 (v - w)`;;

let dirac_delta = new_definition `dirac_delta (i:num) = 
     (\j. if (i=j) then (&1) else (&0))`;;

let mk_vec3 = new_definition `mk_vec3 a b c = 
  a *# (dirac_delta 0) + b *# (dirac_delta 1) + c *# (dirac_delta 2)`;;

let real3_of_triple = new_definition `real3_of_triple (a,b,c) = mk_real3 (mk_vec3 a b c)`;;

let triple_of_real3 = new_definition `triple_of_real3 v = (coord3 0 v,coord3 1 v, coord3 2 v)`;;

let orig3 = new_definition `orig3 = real3_of_triple (&0,&0,&0)`;;

(* ------------------------------------------------------------------ *)
(*   Cross diagonal  and Enclosed                                     *)
(* ------------------------------------------------------------------ *)


(* find point in euclidean 3 space atdistance a b c 
   from 
   v1 = mk_vec3 0 0 0;
   v2 = mk_vec3 y4 0 0;
   v3 = mk_vec3 v3_1 v3_2 0;
*)
let findpoint = kepler_def `findpoint a b c y4 v3_1 v3_2 sgn =
  let y5 = sqrt (v3_1*v3_1 + v3_2*v3_2) in
  let w1 = (a*a + y4*y4 - b*b)/((&2)*y4) in
  let w2 = (a*a + y5*y5 -c*c - (&2)*w1*v3_1)/((&2)*v3_2) in
  let w3 = sgn* (sqrt(a*a - w1*w1 - w2*w2)) in
  mk_vec3 w1 w2 w3`;;

let enclosed = kepler_def `enclosed y1 y2 y3 y4 y5 y6 y1' y2' y3' = 
   let v1 = mk_vec3 (&0) (&0) (&0) in
   let v2 = mk_vec3 y4 (&0) (&0) in
   let a = ((y5*y5) + (y4*y4) - (y6*y6))/((&2)*y4) in
   let b = sqrt((y5*y5) - (a*a)) in
   let v3 = mk_vec3 a b (&0) in
   let v4 = findpoint y3 y2 y1  y4 a b (#1.0) in
   let v5 = findpoint y3' y2' y1'  y4 a b (--(#1.0)) in
   d_euclid v4 v5`;;

let cross_diag = kepler_def `cross_diag y1 y2 y3 y4 y5 y6 y7 y8 y9= 
   enclosed y1 y5 y6 y4 y2 y3 y7 y8 y9`;;

let cross_diag_x = kepler_def `cross_diag_x x1 x2 x3 x4 x5 x6 x7 x8 x9=
   cross_diag (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5)
    (sqrt x6) (sqrt x7) (sqrt x8) (sqrt x9)`;;

(* ------------------------------------------------------------------ *)
(*   Definitions of Affine Geometry (from BLUEPRINT : Trigonometry )  *)
(* ------------------------------------------------------------------ *)

(* Notes on unique existence of definitions:

>         min_num
Exists uniquely on all nonempty subsets of N. 
Can be uniquely extended to all subsets by defining min_num {} = 0

>         deriv
This is the derivative of a function of a real variable.  Its domain is more difficult to describe.

>         aff
Exists uniquely on all finite subsets of R3.
It will only be used on finite sets.
Can be uniquely extended to all subsets by defining aff S = S, when S is infinite

>         aff_sgn
It is only used on finite sets.
Assuming that aff has first been extended to all subsets as above, then
aff_sgn sgn S S1 exists uniquely for all sgn, all S, and all finite S1
Can be uniquely extended to all subsets by defining aff_sgn sgn sgn S S1 = S1, when S1 is infinite

>         min_polar
Exists uniquely on all nonempty finite sets of ordered pairs of real numbers
Can be uniquely extended to all sets of ordered pairs by setting min_polar X = ( &0, &0 ), when X is empty or infinite.
This definition actually holds for some infinite sets, but I never use it, except on finite sets, so you are free
to redefine it to be (&0,&0) on infinite sets.

>         iter
iter is uniquely defined with no domain conditions, no preconditions

>         azim
Exists uniquely when the stated non collinearity preconditions are met: ~(collinear {v, w, w1}) /\ ~(collinear {v, w, w2})
(The preconditions azim_hyp, orthonormality, and e3 normalization are not domain constraints, because they do not restrict v w w1 w2.)
Can be uniquely extended to all cases, by setting azim w1 w2 w3 w4 = &0, when the non-collinearity preconditions are not met.


>         azim_cycle
azim_cycle W v w p exists uniquely under the preconditions (W p)  /\ (cyclic_set W v w).
It is only used when the preconditions are met.
Can be uniquely extended to all cases, by setting azim_cycle W v w p = p, when these two preconditions are not met.



*)

let aff_insert = new_definition `aff_insert v S w = 
   ( ?(u:real3) t.  (v INSERT S) u /\ (w = (t *# v) + (&1 - t)*# u))`;;

let aff_insert_sym = new_definition 
     `aff_insert_sym = (!x y S. ~(x=y) ==> 
         aff_insert x (aff_insert y S) = aff_insert y (aff_insert x S))`;;

let aff_spec = prove(
  `?g. aff_insert_sym ==> 
      ((g {} = {}) /\  (!v S.  (FINITE S) ==> (g (v INSERT S) =
	(if (v IN S) then (g S) else (aff_insert v (g S))))))`,
     (REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM]) THEN
     (REWRITE_TAC[aff_insert_sym]) THEN
     (STRIP_TAC) THEN
     (MATCH_MP_TAC SET_RECURSION_LEMMA) THEN
     (ASM_REWRITE_TAC[]));;

let aff_def = new_specification ["aff"] aff_spec;;  (* blueprint def:affine *)

let aff_sgn_insert = new_definition `aff_sgn_insert sgn v S w = 
    ( ?(u:real3) t.  (v INSERT S) u /\ ( w= (t*# v) + (&1 - t) *# u) /\ (sgn t))`;;

let aff_sgn_insert_sym = new_definition 
     `aff_sgn_insert_sym sgn =  (!x y S. ~(x=y)  ==> 
         aff_sgn_insert sgn x (aff_sgn_insert sgn y S) = aff_sgn_insert sgn y (aff_sgn_insert sgn x S))`;;

let aff_sgn_spec = prove(
  `?g. !sgn S1. aff_sgn_insert_sym sgn ==> 
      ((g sgn S1 {} = aff S1) /\  (!v S.  (FINITE S) ==> (g sgn S1 (v INSERT S) =
	(if (v IN S) then (g sgn S1  S) else (aff_sgn_insert sgn v (g sgn S1 S))))))`,
     (REWRITE_TAC[GSYM SKOLEM_THM]) THEN
     (REPEAT STRIP_TAC) THEN
     (REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM]) THEN
     (REWRITE_TAC[aff_sgn_insert_sym]) THEN
     (STRIP_TAC) THEN
     (MATCH_MP_TAC SET_RECURSION_LEMMA) THEN
     (ASM_REWRITE_TAC[]));;

let aff_sgn = new_specification ["aff_sgn"] aff_sgn_spec;; (* blueprint def:affine *)

let aff_gt_def = new_definition `aff_gt = aff_sgn (\t. (t > &0) )`;;
let aff_ge_def = new_definition `aff_ge = aff_sgn (\t. (t >= &0) )`;;
let aff_lt_def = new_definition `aff_lt = aff_sgn (\t. (t < &0) )`;;
let aff_le_def = new_definition `aff_le = aff_sgn (\t. (t <= &0) )`;;
let conv = new_definition `conv S = aff_ge {} S`;;
let conv0 = new_definition `conv0 S = aff_gt {} S`;;
let cone = new_definition `cone v S = aff_ge {v} S`;;
let cone0 = new_definition `cone0 v S = aff_gt {v} S`;;
let voronoi = new_definition `voronoi v S = { x | !w. ((S w) /\ ~(w=v)) ==> (d3 x v < d3 x w) }`;;

let line = new_definition `line x = (?v w. ~(v  =w) /\ (x = aff {v,w}))`;;
let collinear = new_definition `collinear S = (?x. line x /\ S SUBSET x)`;; 
let plane = new_definition `plane x = (?u v w. ~(collinear {u,v,w}) /\ (x = aff {u,v,w}))`;;
let closed_half_plane = new_definition `closed_half_plane x = (?u v w. ~(collinear {u,v,w}) /\ (x = aff_ge {u,v} {w}))`;;
let open_half_plane = new_definition `open_half_plane x = (?u v w. ~(collinear {u,v,w}) /\ (x = aff_gt {u,v} {w}))`;;
let coplanar = new_definition `coplanar S = (?x. plane x /\ S SUBSET x)`;;
let closed_half_space = new_definition `closed_half_space x = (?u v w w'. ~(coplanar {u,v,w,w'}) /\ (x = aff_ge {u,v,w} {w'}))`;;
let open_half_space = new_definition `open_half_space x = (?u v w w'. ~(coplanar {u,v,w,w'}) /\ (x = aff_gt {u,v,w} {w'}))`;;

(* ANGLE *)

let arcV = new_definition `arcV u v w = acs ((dot3 (v - u) (w - u))/((norm3 (v-u)) * (norm3 (w-u))))`;;

let cross = new_definition `cross u v = let (x,y,z) = triple_of_real3 u in 
      let (x',y',z') = triple_of_real3 v in
      (real3_of_triple (y*z' - y'*z, z*x' - z'*x, x*y' - x'*y))`;;

let dihV = new_definition  `dihV w0 w1 w2 w3 = 
     let va = w2 - w0 in
     let vb = w3 - w0 in
     let vc = w1 - w0 in
     let vap = (dot3 vc vc) *# va - (dot3 va vc)*# vc in
     let vbp = (dot3 vc vc) *# vb - (dot3 vb vc)*# vc in
       arcV orig3 vap vbp`;;

(* conventional ordering on variables *)

let ylist = new_definition `ylist w0 w1 w2 w3 = 
      ((d3 w0 w1),(d3 w0 w2),(d3 w0 w3),(d3 w2 w3),(d3 w1 w3),(d3 w1 w2))`;;

let xlist = new_definition `xlist w0 w1 w2 w3 =
    let (y1,y2,y3,y4,y5,y6) = ylist w0 w1 w2 w3 in
    (y1 pow 2, y2 pow 2, y3 pow 2, y4 pow 2, y5 pow 2, y6 pow 2)`;;

let euler_p = new_definition `euler_p v0 v1 v2 v3 = 
    (let (y1,y2,y3,y4,y5,y6) = ylist v0 v1 v2 v3 in
     let w1 = v1 - v0 in
     let w2 = v2 - v0 in
     let w3 = v3 - v0 in
    y1*y2*y3 + y1*(dot3 w2 w3) + y2*(dot3 w3 w1) + y3*(dot3 w1 w2))`;;

(* polar coordinates *)

let radius = new_definition `radius x y = sqrt((x pow 2) + (y pow 2))`;;
let polar_angle = new_definition `polar_angle x y = 
         let theta = atn2(x,y) in
	 if (theta < &0) then (theta + (&2 * pi)) else theta`;;
let polar_c = new_definition `polar_c x y = (radius x y,polar_angle x y)`;;

let less_polar = new_definition `less_polar (x,y) (x',y') = 
        let (r,theta) = polar_c x y in
	let (r',theta') = polar_c x' y' in
        (theta < theta') \/ ((theta =theta') /\ (r < r'))`;;

let min_polar = new_definition `min_polar V = ( @ u. V u /\ (!w. V w /\ ~(u = w) ==> (less_polar u w)))`;;

let polar_cycle = new_definition `polar_cycle V v =  
       let W = {u  | V u /\ less_polar v u} in
       if (W = EMPTY) then min_polar V else min_polar W`;;

(* iterates of a function must be done already, but I don't know where *)

let iter_spec = prove(`?iter. !f u:A. (iter 0 f u = u) /\ (!n. (iter (SUC n) f u = f(iter n f u)))`,
    (SUBGOAL_THEN `?g. !f (u:A).  (g f u 0 = u) /\ (!n. (g f u (SUC n) = f (g f u n)))` CHOOSE_TAC) THENL
     ([REWRITE_TAC[GSYM SKOLEM_THM;num_RECURSION_STD];REWRITE_TAC[]]) THEN
     (EXISTS_TAC `\ (i:num) (f:A->A)  (u:A). (g f u i):A`) THEN
      (BETA_TAC) THEN
     (ASM_REWRITE_TAC[]));;

let iter = new_specification ["iter"] iter_spec;;

(*
let polar_power_spec = prove(`?fn. !V v.  (fn V v 0 = v ) /\ (!n. (fn V v (SUC n) = polar_cycle V (fn V v n)))`, 
     (REWRITE_TAC[GSYM SKOLEM_THM;num_RECURSION_STD]));;

let polar_power = new_specification ["polar_power"] polar_power_spec;;
*)

let orthonormal = new_definition `orthonormal e1 e2 e3 = 
     ((dot3 e1 e1 = &1) /\ (dot3 e2 e2 = &1) /\ (dot3 e3 e3 = &1) /\
     (dot3 e1 e2 = &0) /\ (dot3 e1 e3 = &0) /\ (dot3 e2 e3 = &0) /\
     (dot3 (cross e1 e2) e3 > &0))`;;

(* spherical coordinates *)
let azim_hyp_def = new_definition `azim_hyp = (!v w w1 w2. ?theta. !e1 e2 e3. ?psi h1 h2 r1 r2.
   ~(collinear {v, w, w1}) /\ ~(collinear {v, w, w2}) /\
   (orthonormal e1 e2 e3) /\ ((d3 w v) *# e3 = (w - v)) ==>
   ((&0 <= theta) /\ (theta < &2 * pi) /\ (&0 < r1) /\ (&0 < r2) /\
   (w1 = (r1 * cos(psi)) *# e1 + (r1 * sin(psi)) *# e2 + h1 *# (w-v)) /\
   (w2 = (r2 * cos(psi + theta)) *# e1 + (r2 * sin(psi + theta)) *# e2 + h2 *# (w-v))))`;;

let azim_spec = prove(`?theta. !v w w1 w2 e1 e2 e3. ?psi h1 h2 r1 r2.
   (azim_hyp) ==>
   ~(collinear {v, w, w1}) /\ ~(collinear {v, w, w2}) /\
   (orthonormal e1 e2 e3) /\ ((d3 w v) *# e3 = (w - v)) ==>
   ((&0 <= theta v w w1 w2) /\ (theta v w w1 w2 < &2 * pi) /\ (&0 < r1) /\ (&0 < r2) /\
   (w1 = (r1 * cos(psi)) *# e1 + (r1 * sin(psi)) *# e2 + h1 *# (w-v)) /\
   (w2 = (r2 * cos(psi + theta v w w1 w2)) *# e1 + (r2 * sin(psi + theta v w w1 w2)) *# e2 + h2 *# (w-v)))`,
   (REWRITE_TAC[GSYM SKOLEM_THM;GSYM RIGHT_IMP_EXISTS_THM;GSYM RIGHT_IMP_FORALL_THM]) THEN
     (REWRITE_TAC[azim_hyp_def]) THEN
     (REPEAT STRIP_TAC) THEN
     (ASM_REWRITE_TAC[RIGHT_IMP_EXISTS_THM]));;

let azim_def = new_specification ["azim"] azim_spec;;


let cyclic_set = new_definition `cyclic_set W v w = 
     (~(v=w) /\ (FINITE W) /\ (!p q h. W p /\ W q /\ (p = q + h *# (v - w)) ==> (p=q)) /\
        (W INTER (aff {v,w}) = EMPTY))`;;




let azim_cycle_hyp_def = new_definition `azim_cycle_hyp = 
  (?sigma.  !W proj v w e1 e2 e3 p. 
        (W p) /\
        (cyclic_set W v w) /\ ((d3 v w) *# e3 = (w-v)) /\
	(orthonormal e1 e2 e3) /\ 
	(!u x y. (proj u = (x,y)) <=> (?h. (u = v + x *# e1 + y *# e2 + h *# e3))) ==>
	(proj (sigma W v w p) = polar_cycle (IMAGE proj W) (proj p)))`;;

let azim_cycle_spec = prove(`?sigma. !W proj v w e1 e2 e3 p.
   (azim_cycle_hyp) ==> ( (W p) /\
        (cyclic_set W v w) /\ ((d3 v w) *# e3 = (w-v)) /\
	(orthonormal e1 e2 e3) /\ 
	(!u x y. (proj u = (x,y)) <=> (?h. (u = v + x *# e1 + y *# e2 + h *# e3)))) ==> (proj (sigma W v w p) = polar_cycle (IMAGE proj W) (proj p))`,
	(REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM;GSYM RIGHT_IMP_FORALL_THM]) THEN
	  (REWRITE_TAC[azim_cycle_hyp_def])
	   );;

let azim_cycle_def = new_specification ["azim_cycle"] azim_cycle_spec;;	

(* ------------------------------------------------------------------ *)
(*   Format of inequalities in the archive.                           *)
(* ------------------------------------------------------------------ *)

let ineq = kepler_def `ineq (bounds:(real#real#real) list) (A:bool) = 
   ((!(a,x,b). ((MEM (a,x,b) bounds) ==> ((a <= x) /\ (x <= b)))) /\ A)`;;

let all_forall bod = 
  let mk_forall = mk_binder "!" in
  itlist (curry mk_forall) (frees bod) bod;;
