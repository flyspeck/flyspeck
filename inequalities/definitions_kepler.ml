

let kepler_def = local_definition "kepler";;

prioritize_real();;

let max_real = new_definition(`max_real x y =
        if (y <. x) then x else y`);;

let min_real = new_definition(`min_real x y =
        if (x <. y) then x else y`);;

let deriv = new_definition(`deriv f x = @d. (f diffl d)(x)`);;
let deriv2 = new_definition(`deriv2 f = (deriv (deriv f))`);;

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
let xi_kappa=kepler_def(`xi_kappa= --. (#0.029)`);;
let xi_kappa_gamma=kepler_def(`xi_kappa_gamma=
        xi_kappa+xi_gamma`);;
let pi_max =kepler_def(`xi_max = (#0.006688)`);;
let t4 = kepler_def(`t4= (#0.1317)`);;
let t5 = kepler_def(`t5= (#0.27113)`);;
let t6 = kepler_def(`t6= (#0.41056)`);;
let t7 = kepler_def(`t7= (#0.54999)`);;
let t8 = kepler_def(`t8= (#0.6045)`);;
let s5 = kepler_def(`s5= --(#0.05704)`);;
let s6 = kepler_def(`s6= --(#0.11408)`);;
let s7 = kepler_def(`s7= --(#0.17112)`);;
let s8 = kepler_def(`s8= --(#0.22816)`);;

let Z31 = kepler_def(`Z31 = (#0.00005)`);;
let Z32 = kepler_def(`Z32 = --. (#0.05714)`);;
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

let u_x = kepler_def(
        `u_x x1 x2 x3 = (--(x1*x1+x2*x2+x3*x3)) + 
        (&2) * (x1*x2+x2*x3+x3*x1)`);;

let eta_x = kepler_def(`eta_x x1 x2 x3 = 
        (sqrt ((x1*x2*x3)/(u_x x1 x2 x3)))
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
(*   This doesn't work when delta =0                                  *)
(* ------------------------------------------------------------------ *)

let dih_x = kepler_def(`dih_x x1 x2 x3 x4 x5 x6 = 
       let d_x4 = delta_x4 x1 x2 x3 x4 x5 x6 in
       let d = delta_x x1 x2 x3 x4 x5 x6 in
       pi/ (&2) +  atn(--  d_x4/ (sqrt ((&4) * x1 * d)))`);;


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
        pi/(&2) + (atn ((c*c - a*a  -b*b)/(sqrt (u_x (a*a) (b*b) (c*c)))))`);;


let volR = kepler_def(`volR a b c =
        (sqrt (a*a*(b*b-a*a)*(c*c-b*b)))/(&6)`);;

let solR = kepler_def(`solR a b c =
        (&2)*atn( sqrt ((c-b)*(b-a)/((c+b)*(b+a))))`);;

let dihR = kepler_def(`dihR a b c =
        atn (sqrt ((c*c-b*b)/(b*b-a*a)))`);;

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
        - ((&2)/(&3))*c*c*c*(atn((u*(b-a))/(b+c))))`);;

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
	(vorR (y1/(&.2)) (eta_y y1 y2 y6) (sqrt2)) +
	(vorR (y2/(&.2)) (eta_y y1 y2 y6) (sqrt2)) -
        (dihR (y1/(&.2)) (eta_y y1 y2 y6) (sqrt2))*
		      (&.1 - (y1/(sqrt8)))*(phi (y1/(&.2)) sqrt2)`);;

let AH = kepler_def(`AH h t = (&.1 -. (h/t))*((phi h t) - (phi t t))`);;

let BHY = kepler_def(`BHY y = (AH (y/(&.2)) t0) + phi0`);;

(*

(* This definition still needs to be finished *)
let overlap_f = kepler_def(
  `overlap_f y1 y2 =
    let ell = (#3.2) in
    let lam = (#1.945) in
    let dih1 = dih_y y1 t0 y2 lam ell lam in
    let dih2 = dih_y y2 t0 y1 lam ell lam in
    let s = sol_y y2 t0 y1 lam ell lam in
    let phi1 = phi (y1/(&.2)) t0 in
    let phi2 = phi (y2/(&.2)) t0 in
    (&2)*(zeta*pt - phi0)*s 
      + (&.2)*dih1*((&.1) - (y1/two_t0))*(phi0-phi1)
      + (&.2)*dih2*((&.1) - (y2/two_t0))*(phi0-phi2)
   + xxxxx-- need to insert tau terms ---xxxxx`);;
*)


(* ------------------------------------------------------------------ *)
(*   Analytic and truncated Voronoi function                          *)
(* ------------------------------------------------------------------ *)

let KY = kepler_def(`KY y1 y2 y3 y4 y5 y6 =
   (K0 y1 y2 y6) + (K0 y1 y3 y5) + 
  (dih_y y1 y2 y3 y4 y5 y6)*
    (&.1 - (y1/(sqrt8)))*(phi (y1/(&.2)) sqrt2)`);;

let KX = kepler_def(`KX x1 x2 x3 x4 x5 x6 =
   KY (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5) (sqrt x6)`);;

let vor_analytic_x = kepler_def(`vor_analytic_x x1 x2 x3 x4 x5 x6 =
        let del = sqrt (delta_x x1 x2 x3 x4 x5 x6) in
        let u126 = u_x x1 x2 x6 in
        let u135 = u_x x1 x3 x5 in
        let u234 = u_x x2 x3 x4 in
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

let kappa = kepler_def(`kappa y1 y2 y3 y4 y5 y6 =
        (crown y1/(&2))*(dih_y y1 y2 y3 y4 y5 y6)/((&2)*pi) 
        + (anc y1 y2 y6) + (anc y1 y3 y5)`);;

let level_at = kepler_def(`level_at h t = if (h<t) then h else t`);;

let vorstar = kepler_def(`vorstar h1 h2 h3 a1 a2 a3 t=
        a1*((&1)-(level_at h1 t)/t)*(phi h1 t - phi0)
        +a2*((&1)-(level_at h2 t)/t)*(phi h2 t - phi0)
        +a3*((&1)-(level_at h3 t)/t)*(phi h3 t - phi0)
        +(a1+a2+a3-pi)*phi0`);;

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
    if ((x5 <=. (square (#2.77))) /\ (x6 <=. (square (#2.77))) /\
	(((eta_x x4 x5 x6) <. sqrt2)))
    then (vor_analytic_x x1 x2 x3 x4 x5 x6 )
    else (vor_0_x x1 x2 x3 x4 x5 x6)`);;

let tauA_x = kepler_def(`tauA_x x1 x2 x3 x4 x5 x6 =
        (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - 
                (vorA_x x1 x2 x3 x4 x5 x6)`);;

let vorC0_x = kepler_def(`vorC0_x x1 x2 x3 x4 x5 x6 =
    if ((x4 <=. (square (#2.77))) \/ 
	((eta_x x4 x5 x6 <=. sqrt2) /\ (eta_x x2 x3 x4 <=. sqrt2)))
    then (vor_analytic_x x1 x2 x3 x4 x5 x6 )
    else (vor_0_x x1 x2 x3 x4 x5 x6)`);;

let tauC0_x = kepler_def(`tauC0_x x1 x2 x3 x4 x5 x6 =
        (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - 
                (vorC0_x x1 x2 x3 x4 x5 x6)`);;

let vorC_x = kepler_def(`vorC_x x1 x2 x3 x4 x5 x6 =
    if ((x4 <=. (square (#2.77))) \/ 
	((eta_x x4 x5 x6 <=. sqrt2) /\ (eta_x x2 x3 x4 <=. sqrt2)) \/
       ((square (#2.45) <=. x2) /\ ((square (#2.45) <=. x6))))
    then (vor_analytic_x x1 x2 x3 x4 x5 x6 )
    else (vor_0_x x1 x2 x3 x4 x5 x6)`);;

let tauC_x = kepler_def(`tauC_x x1 x2 x3 x4 x5 x6 =
        (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - 
                (vorC_x x1 x2 x3 x4 x5 x6)`);;


let v0x = kepler_def(`v0x x1 x2 x3 x4 x5 x6 =
	let (y1,y2,y3) = (sqrt x1,sqrt x2,sqrt x3) in
	(--. (BHY y1))*y1*(delta_x6 x1 x2 x3 x4 x5 x6) +
	(BHY y2)* y2* (u_x x1 x3 x5) +
	  (--. (BHY y3))*y3*(delta_x4 x1 x2 x3 x4 x5 x6)`);;

let v1x = kepler_def(`v1x x1 x2 x3 x4 x5 x6 =
	let (y1,y2,y3) = (sqrt x1,sqrt x2,sqrt x3) in
	(--. (BHY y1 - (zeta*pt)))*y1*(delta_x6 x1 x2 x3 x4 x5 x6) +
	(BHY y2 - (zeta*pt))* y2* (u_x x1 x3 x5) +
	  (--. (BHY y3 - (zeta*pt)))*y3*(delta_x4 x1 x2 x3 x4 x5 x6)`);;


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
       --. (sigma_qrtet_x x1 x2 x3 x4 x5 x6)`;;

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

let nu_x = kepler_def(`nu_x x1 x2 x3 x4 x5 x6 =
        ((&1)/(&2))*
        (
               (mu_upright_x x1 x2 x3 x4 x5 x6)+
               (mu_upright_x x1 x5 x6 x4 x2 x3)+
               (vor_0_x x1 x2 x3 x4 x5 x6)-
               (vor_0_x x1 x5 x6 x4 x2 x3))`);;

let nu_gamma_x = kepler_def(`nu_gamma_x x1 x2 x3 x4 x5 x6 =
        ((&1)/(&2))*
        (
               (&.2 * (gamma_x x1 x2 x3 x4 x5 x6))+
               (vor_0_x x1 x2 x3 x4 x5 x6)-
               (vor_0_x x1 x5 x6 x4 x2 x3))`);;

let taunu_x = kepler_def(`taunu_x x1 x2 x3 x4 x5 x6 =
	(sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - (nu_x x1 x2 x3 x4 x5 x6)`);;



(* score for upright quarters in a quasi-regular octahedron.
   I don't think I had a name for this specifically. *)
let octa_x = kepler_def(`octa_x x1 x2 x3 x4 x5 x6 = 
	(#0.5)*(
               (mu_upright_x x1 x2 x3 x4 x5 x6)+
               (mu_upright_x x1 x5 x6 x4 x2 x3))`);;

let sigmahat_x = kepler_def(`sigmahat_x x1 x2 x3 x4 x5 x6 =
        let r234 = eta_x x2 x3 x4 in
        let r456 = eta_x x4 x5 x6 in
        let v0 = (if (sqrt2 <=. r456) then
	  (vor_0_x x1 x2 x3 x4 x5 x6) 
	else if (sqrt2 <=. r234) then
	  (vor_analytic_x x1 x2 x3 x4 x5 x6)
	else 
	  (gamma_x x1 x2 x3 x4 x5 x6)) in
	let v1 = (if ((r234 <=. sqrt2) /\ (r456 <=. sqrt2)) then
		    max_real v0 (gamma_x x1 x2 x3 x4 x5 x6) 
		  else v0) in
	let v2 = (if (sqrt2 <=. r234) then
		    max_real v1 (vor_analytic_x x1 x2 x3 x4 x5 x6)
		  else v1) in
	let v3 = (if ((square (#2.6)) <=. x4) /\ ((square (#2.2)) <=. x2)
		  then max_real v2 	  (vor_0_x x1 x2 x3 x4 x5 x6) 
		  else v2) in
	let v4 = (if ((square (#2.7) <=. x4))
		  then 
		    max_real v3 (vor_0_x x1 x2 x3 x4 x5 x6) 
		  else v3) in
	  if (sqrt2 <=. r456) 
	  then
	    max_real v4 (vor_analytic_x x1 x2 x3 x4 x5 x6)
	  else v4`);;



let sigmahatpi_x = kepler_def(`sigmahatpi_x x1 x2 x3 x4 x5 x6 =
        let r234 = eta_x x2 x3 x4 in
        let r456 = eta_x x4 x5 x6 in
	let piF = (#2.0)*(xiV) + (xi_gamma) in
        let v0 = (if (sqrt2 <=. r456) then
	  (vor_0_x x1 x2 x3 x4 x5 x6) 
	else if (sqrt2 <=. r234) then
	  (vor_analytic_x x1 x2 x3 x4 x5 x6)
	else 
	  (gamma_x x1 x2 x3 x4 x5 x6)) in
	let v1 = (if ((r234 <=. sqrt2) /\ (r456 <=. sqrt2)) then
		    max_real v0 (gamma_x x1 x2 x3 x4 x5 x6) 
		  else v0) in
	let v2 = (if (sqrt2 <=. r234) then
		    max_real v1 (vor_analytic_x x1 x2 x3 x4 x5 x6)
		  else v1) in
	let v3 = (if ((square (#2.6)) <=. x4) /\ ((square (#2.2)) <=. x2)
		  then max_real v2 (piF +. (vor_0_x x1 x2 x3 x4 x5 x6)) 
		  else v2) in
	let v4 = (if ((square (#2.7) <=. x4))
		  then 
		    max_real v3 (piF +. (vor_0_x x1 x2 x3 x4 x5 x6) )
		  else v3) in
	  if (sqrt2 <=. r456) 
	  then
	    max_real v4 (vor_analytic_x x1 x2 x3 x4 x5 x6)
	  else v4`);;
    

let tauhat_x = kepler_def(`tauhat_x x1 x2 x3 x4 x5 x6 =
    (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - (sigmahat_x x1 x2 x3 x4 x5 x6)`);;

let tauhatpi_x = kepler_def(`tauhatpi_x x1 x2 x3 x4 x5 x6 =
    (sol_x x1 x2 x3 x4 x5 x6)*zeta*pt - (sigmahatpi_x x1 x2 x3 x4 x5 x6)`);;

let pi_prime_tau = kepler_def
  `pi_prime_tau k0 k1 k2 = 
    if (k2=0) then (&.0)
    else if (k0=1) /\ (k1=1) /\ (k2=1) then (#0.0254)
    else (#0.04683 +. (&.k0 + &.(2*k2) - #3.0)*((#0.008)/(#3.0))
     + (&.k2) * (#0.0066))`;;

let pi_prime_sigma = kepler_def
  `pi_prime_sigma k0 (k1:num) k2 = 
    if (k2=0) then (&.0)
    else if (k0=1) /\ (k2=1) then (#0.009)
    else (&. (k0 + 2*k2))*((#0.008)/(#3.0)) + (&.k2)* (#0.009)`;;

(* ------------------------------------------------------------------ *)
(*   Cross diagonal  and Enclosed                                     *)
(* ------------------------------------------------------------------ *)


let dirac_delta = kepler_def `dirac_delta (i:num) = 
     (\j. if (i=j) then (&.1) else (&.0))`;;

let mk_vec3 = kepler_def `mk_vec3 a b c = 
  a *# (dirac_delta 0) + b *# (dirac_delta 1) + c *# (dirac_delta 2)`;;

(* find point in euclidean 3 space atdistance a b c 
   from 
   v1 = mk_vec3 0 0 0;
   v2 = mk_vec3 y4 0 0;
   v3 = mk_vec3 v3_1 v3_2 0;
*)
let findpoint = kepler_def `findpoint a b c y4 v3_1 v3_2 sgn =
  let y5 = sqrt (v3_1*v3_1 + v3_2*v3_2) in
  let w1 = (a*a + y4*y4 - b*b)/((&.2)*y4) in
  let w2 = (a*a + y5*y5 -c*c - (&.2)*w1*v3_1)/((&.2)*v3_2) in
  let w3 = sgn* (sqrt(a*a - w1*w1 - w2*w2)) in
  mk_vec3 w1 w2 w3`;;

let enclosed = kepler_def `enclosed y1 y2 y3 y4 y5 y6 y1' y2' y3' = 
   let v1 = mk_vec3 (&.0) (&.0) (&.0) in
   let v2 = mk_vec3 y4 (&.0) (&.0) in
   let a = ((y5*y5) + (y4*y4) - (y6*y6))/((&.2)*y4) in
   let b = sqrt((y5*y5) - (a*a)) in
   let v3 = mk_vec3 a b (&.0) in
   let v4 = findpoint y3 y2 y1  y4 a b (#1.0) in
   let v5 = findpoint y3' y2' y1'  y4 a b (--(#1.0)) in
   d_euclid v4 v5`;;

let cross_diag = kepler_def `cross_diag y1 y2 y3 y4 y5 y6 y7 y8 y9= 
   enclosed y1 y5 y6 y4 y2 y3 y7 y8 y9`;;

let cross_diag_x = kepler_def `cross_diag_x x1 x2 x3 x4 x5 x6 x7 x8 x9=
   cross_diag (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5)
    (sqrt x6) (sqrt x7) (sqrt x8) (sqrt x9)`;;



  

(* ------------------------------------------------------------------ *)
(*   Format of inequalities in the archive.                           *)
(* ------------------------------------------------------------------ *)

let ineq = kepler_def `ineq (bounds:(real#real#real) list) (A:bool) = 
   (!(a,x,b). ((MEM (a,x,b) bounds) ==> ((a <=. x) /\ (x <=. b)))) /\ A`;;

let all_forall bod = 
  let mk_forall = mk_binder "!" in
  itlist (curry mk_forall) (frees bod) bod;;
