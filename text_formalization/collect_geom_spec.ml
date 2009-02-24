(* Nguyen Quang Truong *)
needs "Multivariate/vectors.ml";; (* Eventually should load entire *) 	   
needs "Examples/analysis.ml";; (* multivariate-complex theory. *)	   
needs "Examples/transc.ml";; (* Then it won't need these three. *)
needs "convex_header.ml";; 
needs "definitions_kepler.ml";;
let ups_x = new_definition ` ups_x x1 x2 x6 =
         --x1 * x1 - x2 * x2 - x6 * x6 +
         &2 * x1 * x6 +
         &2 * x1 * x2 +
         &2 * x2 * x6 `;;
let rho = new_definition ` rho (x12 :real) x13 x14 x23 x24 x34 =
         --(x14 * x14 * x23 * x23) -
         x13 * x13 * x24 * x24 -
         x12 * x12 * x34 * x34 +
         &2 *
         (x12 * x14 * x23 * x34 +
          x12 * x13 * x24 * x34 +
          x13 * x14 * x23 * x24) `;;
let chi = new_definition ` chi x12 x13 x14 x23 x24 x34 =
         x13 * x23 * x24 +
         x14 * x23 * x24 +
         x12 * x23 * x34 +
         x14 * x23 * x34 +
         x12 * x24 * x34 +
         x13 * x24 * x34 -
         &2 * x23 * x24 * x34 -
         x12 * x34 * x34 -
         x14 * x23 * x23 -
         x13 * x24 * x24 `;;
let delta = new_definition ` delta x12 x13 x14 x23 x24 x34 =
   --(x12 * x13 * x23) -
         x12 * x14 * x24 -
         x13 * x14 * x34 -
         x23 * x24 * x34 +
         x12 * x34 * (--x12 + x13 + x14 + x23 + x24 - x34) + 
         x13 * x24 * (x12 - x13 + x14 + x23 - x24 + x34 ) +
         x14 * x23 * ( x12 + x13 - x14 - x23 + x24 + x34 ) `;;

let eta_v = new_definition ` eta_v v1 v2 (v3: real^N) =
        let e1 = dist (v2, v3) in
  	  let e2 = dist (v1, v3) in
  	  let e3 = dist (v2, v1) in
  	  e1 * e2 * e3 / sqrt ( ups_x (e1 pow 2 ) ( e2 pow 2) ( e3 pow 2 ) ) `;;

let plane_norm = new_definition `
  plane_norm p <=>
         (?n v0. ~(n = vec 0) /\ p = {v | n dot (v - v0) = &0}) `;;

let circumradius = new_definition ` circumradius s = (@r. ? x. x IN s /\
  r = dist( x , circumcenter s ) )`;;

let delta_x12 = new_definition ` delta_x12 x12 x13 x14 x23 x24 x34 =
  -- x13 * x23 + -- x14 * x24 + x34 * ( -- x12 + x13 + x14 + x23 + x24 + -- x34 )
  + -- x12 * x34 + x13 * x24 + x14 * x23 `;;

let delta_x13 = new_definition` delta_x13 x12 x13 x14 x23 x24 x34 =
  -- x12 * x23 + -- x14 * x34 + x12 * x34 + x24 * ( x12 + -- x13 + x14 + x23 + 
  -- x24 + x34 ) + -- x13 * x24 + x14 * x23 `;;

let delta_x14 = new_definition`delta_x14 x12 x13 x14 x23 x24 x34 =
         --x12 * x24 +
         --x13 * x34 +
         x12 * x34 +
         x13 * x24 +
         x23 * (x12 + x13 + --x14 + --x23 + x24 + x34) +
         --x14 * x23`;;

let delta_x34 = new_definition` delta_x34 x12 x13 x14 x23 x24 x34 =
-- &2 * x12 * x34 +
     --x13 * x14 +
     --x23 * x24 +
     x13 * x24 +
     x14 * x23 +
     --x12 * x12 +
     x12 * x14 +
     x12 * x24 +
     x12 * x13 +
     x12 * x23`;;


let max_real3 = new_definition ` max_real3 x y z = max_real (max_real x y ) z `;;
let ups_x_pow2 = new_definition` ups_x_pow2 x y z = ups_x ( x*x ) ( y * y) ( z * z)`;;


let condA = new_definition `condA (v1:real^3) v2 v3 v4 x12 x13 x14 x23 x24 x34 = 
  ( ~ ( v1 = v2 ) /\ coplanar {v1,v2,v3,v4} /\
  ( dist ( v1, v2) pow 2 ) = x12 /\
  dist (v1,v3) pow 2 = x13 /\
  dist (v1,v4) pow 2 = x14 /\
  dist (v2,v3) pow 2 = x23 /\ dist (v2,v4) pow 2 = x24 )`;;
(* def 26. p 22 *)
let condC = new_definition ` condC M13 m12 m14 M24 m34 (m23:real) =
  ((! x. x IN {M13, m12, m14, M24, m34, m23 } ==> &0 <= x ) /\
  M13 <= m12 + m23 /\
  M13 <= m14 + m34 /\ 
  M24 < m12 + m14 /\
  M24 < m23 + m34 /\ 
  &0 <= delta (M13 pow 2) (m12 pow 2) (m14 pow 2) (M24 pow 2) (m34 pow 2 )
   (m23 pow 2 ) )`;;

let condF = new_definition` condF m14 m24 m34 M23 M13 M12 =
         ((!x. x IN {m14, m24, m34, M23, M13, M12} ==> &0 < x) /\
         M12 < m14 + m24 /\
         M13 < m14 + m34 /\
         M23 < m24 + m34 /\
         &0 <
         delta (m14 pow 2) (m24 pow 2) (m34 pow 2) (M23 pow 2) (M13 pow 2)
         (M12 pow 2)) `;;

let condS = new_definition ` condS m m34 M13 M23 <=>
     (!t. t IN {m, m34, M13, M23} ==> &0 < t) /\
     M13 < m + m34 /\
     M23 < m + m34 /\
     M13 pow 2 < M23 pow 2 + &4 * m * m /\
     M23 pow 2 < M13 pow 2 + &4 * m * m /\
     (!r. delta (&4 * m * m) (M13 pow 2) (M23 pow 2) r (M13 pow 2) (M23 pow 2) = &0
          ==> r < &4 * m34 * m34) `;;

let cos_arc = new_definition` cos_arc (a:real) b c = 
   ( a pow 2 + b pow 2 - c pow 2 )/ ( &2 * a * b ) `;;

let muy_v = new_definition ` muy_v (x1: real^N ) (x2:real^N) (x3:real^N) (x4:real^N)
(x5:real^N) x45 = 
          (let x12 = dist (x1,x2) pow 2 in
          let x13 = dist (x1,x3) pow 2 in
          let x14 = dist (x1,x4) pow 2 in
          let x15 = dist (x1,x5) pow 2 in
          let x23 = dist (x2,x3) pow 2 in
          let x24 = dist (x2,x4) pow 2 in
          let x25 = dist (x2,x5) pow 2 in
          let x34 = dist (x3,x4) pow 2 in
          let x35 = dist (x3,x5) pow 2 in
          cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45) `;;
(* dedinition of E. page 34 *)
let sqrt_of_ge_root = new_definition `
sqrt_of_ge_root y14 y24 y34 y12 y13 y23 y15 y25 y35 =
         (@r. ?le ge a.
                  le <= ge /\
                  r = sqrt ge /\
                  (!x. cayleyR (y12 pow 2) (y13 pow 2) (y14 pow 2)
                       (y15 pow 2)
                       (y23 pow 2)
                       (y24 pow 2)
                       (y25 pow 2)
                       (y34 pow 2)
                       (y35 pow 2)
                       x =
                       a * (x - le) * (x - ge))) `;;
(* Lemma 2, page 6 *)
let RHUFIIB = new_axiom ` !x12 x13 x14 x23 x24 x34.
         rho x12 x13 x14 x23 x24 x34 * ups_x x34 x24 x23 =
         chi x12 x13 x14 x23 x24 x34 pow 2 +
         &4 * delta x12 x13 x14 x23 x24 x34 * x34 * x24 * x23 `;;
(* Lemma 3, *)
let NUHSVLM = new_axiom ` !x1 x2 x3 x4 (x5 :real^3). 
                 let x12 = dist (x1,x2) pow 2 in
         let x13 = dist (x1,x3) pow 2 in
         let x14 = dist (x1,x4) pow 2 in
         let x15 = dist (x1,x5) pow 2 in
         let x23 = dist (x2,x3) pow 2 in
         let x24 = dist (x2,x4) pow 2 in
         let x25 = dist (x2,x5) pow 2 in
         let x34 = dist (x3,x4) pow 2 in
         let x35 = dist (x3,x5) pow 2 in
         let x45 = dist (x4,x5) pow 2 in
         &0 <= ups_x x12 x13 x23 /\
         &0 <= delta x12 x13 x14 x23 x24 x34 /\
         cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 = &0 `;;
(* lemma 4, page 7 *)
let JVUNDLC = new_axiom ` ! a b (c:real ) s. s = ( a + b + c ) / &2 ==>
 &16 * s * (s - a) * (s - b) * (s - c) =
             ups_x (a pow 2) (b pow 2) (c pow 2)`;;
(* lemma 5, page 12 *)
let RCEABUJ = new_axiom ` ! a (b:real^3) x. line x /\ {a,b} SUBSET x /\ ~( a = b) 
    ==> x = aff {a,b} `;;
(* lem 6. p 12 *)
let BXVMKNF = new_axiom ` ! u v:real ^3. ~( u=v) ==> plane_norm ( bis u v ) `;;
(* la 7. p 12 *)
let SMWTDMU = new_axiom ` !x y z p.
         plane p /\ ~collinear {x, y, z} /\ {x, y, z} SUBSET p
         ==> p = aff {x, y, z}`;;
(* le 8. p 12 *)
let SGFCDZO = new_axiom `! v1 v2 v3:real^3 t1 t2 (t3:real). 
         t1 % v1 + t2 % v2 + t3 % v3 = vec 0 /\
         t1 + t2 + t3 = &0 /\
         ~(t1 = &0 /\ t2 = &0 /\ t3 = &0)
         ==> collinear {v1, v2, v3}`;;
let lemma8 = SGFCDZO;;
(* le 9. p 13 *)
let FHFMKIY = new_axiom ` ! (v1: real^3) v2 v3 x12 x13 x23.
         x12 = dist (v1,v2) pow 2 /\
         x13 = dist (v1,v3) pow 2 /\
         x23 = dist (v2,v3) pow 2
         ==> (collinear {v1, v2, v3} <=> ups_x x12 x13 x23 = &0)`;;
let lemma9 = FHFMKIY;;
(* le 10. p 14 *)
let ZPGPXNN = new_axiom `! v1 v2 (v:real^3).
         dist (v1,v2) < dist (v,v1) + dist (v,v2) ==> ~(v IN conv {v1, v2})`;;
let lemma10 = ZPGPXNN;;
(* le 11. p14 *)
let FAFKVLR = new_axiom ` ? t1 t2 t3. ! v1 v2 v3 (v:real^3).
   v IN ( affine hull {v1,v2,v3} ) /\
   ~collinear {v1, v2, v3} 
             ==> v = t1 v1 v2 v3 v % v1 + t2 v1 v2 v3 v % v2 + t3 v1 v2 v3 v % v3 /\
                 t1 v1 v2 v3 v + t2 v1 v2 v3 v + t3 v1 v2 v3 v = &1 /\
                 (!ta tb tc. v = ta % v1 + tb % v2 + tc % v3
                    ==> ta = t1 v1 v2 v3 v /\
                        tb = t2 v1 v2 v3 v /\
                        tc = t3 v1 v2 v3 v )`;;

let equivalent_lemma = prove(` (?t1 t2 t3.
         !v1 v2 v3 (v:real^N).
             v IN affine hull {v1, v2, v3} /\ ~collinear {v1, v2, v3}
             ==> v =
                 t1 v1 v2 v3 v % v1 + t2 v1 v2 v3 v % v2 + t3 v1 v2 v3 v % v3 /\
                 t1 v1 v2 v3 v + t2 v1 v2 v3 v + t3 v1 v2 v3 v = &1 /\
                 (!ta tb tc.
                      v = ta % v1 + tb % v2 + tc % v3
                      ==> ta = t1 v1 v2 v3 v /\
                          tb = t2 v1 v2 v3 v /\
                          tc = t3 v1 v2 v3 v))  <=>
     
          ( !v1 v2 v3 (v:real^N).
             v IN affine hull {v1, v2, v3} /\ ~collinear {v1, v2, v3}
          ==> (?t1 t2 t3.
                   v = t1 % v1 + t2 % v2 + t3 % v3 /\
                   t1 + t2 + t3 = &1 /\
                   (!ta tb tc.
                        v = ta % v1 + tb % v2 + tc % v3
                        ==> ta = t1 /\ tb = t2 /\ tc = t3))) `,
REWRITE_TAC[GSYM SKOLEM_THM; LEFT_FORALL_IMP_THM; RIGHT_EXISTS_IMP_THM]);;

let lemma11 = REWRITE_RULE[equivalent_lemma] FAFKVLR;;
let COEFS = new_specification ["coef1"; "coef2"; "coef3"] FAFKVLR;;
let plane_3p = new_definition `plane_3p (a:real^3) b c =
         {x | ~collinear {a, b, c} /\
              (?ta tb tc. ta + tb + tc = &1 /\ x = ta % a + tb % b + tc % c)}`;;
(* le 12. p 15 *)
let CNXIFFC = new_axiom ` ! (v1:real^3) (v2:real^3) (v3:real^3) (v:real^3). ~ collinear {v1,v2,v3} /\ v IN affine hull 
{v1, v2, v3} 
  ==> ( &0 < coef1 v1 v2 v3 v <=> v IN aff_gt {v2,v3} {v1} ) /\
  ( &0 = coef1 v1 v2 v3 v <=> v IN aff {v2,v3} ) /\
  ( coef1 v1 v2 v3 v < &0 <=> v IN aff_lt {v2,v3} {v1} ) /\
   ( &0 < coef2 v1 v2 v3 v <=> v IN aff_gt {v3,v1} {v2} ) /\
  ( &0 = coef2 v1 v2 v3 v <=> v IN aff {v3,v1} ) /\
  ( coef2 v1 v2 v3 v < &0 <=> v IN aff_lt {v3,v1} {v2} )/\
   ( &0 < coef3 v1 v2 v3 v <=> v IN aff_gt {v1,v2} {v3} ) /\
  ( &0 = coef3 v1 v2 v3 v <=> v IN aff {v1,v2} ) /\
  ( coef3 v1 v2 v3 v < &0 <=> v IN aff_lt {v1,v2} {v3})`;;
let lemma12 = CNXIFFC;;
(* le 13. p 15 *)
let MYOQCBS = new_axiom ` ! v1 v2 v3 (v:real^3). ~ collinear {v1,v2,v3}/\
  v IN affine hull {v1,v2,v3} ==>
   ( v IN conv {v1,v2,v3} <=> &0 <= coef1 v1 v2 v3 v /\ &0 <= coef2 v1 v2 v3 v /\
   &0 <= coef3 v1 v2 v3 v ) /\ 
   ( v IN conv0 {v1,v2,v3} <=> &0 < coef1 v1 v2 v3 v /\ &0 < coef2 v1 v2 v3 v /\
   &0 < coef3 v1 v2 v3 v )`;;
let lemma13 = MYOQCBS;;
(* le 14. p 15 *)
let TXDIACY = new_axiom `! a b c d (v0: real^3) r.
         &0 < r /\ {a, b, c, d} SUBSET normball v0 r
         ==> conv {a, b, c, d} SUBSET normball v0 r `;;
(* le 15. p 16 *)
let POLFLZY = new_axiom ` ! x1 x2 x3 (x4: real^3).  
         let x12 = dist (x1,x2) pow 2 in
         let x13 = dist (x1,x3) pow 2 in
         let x14 = dist (x1,x4) pow 2 in
         let x23 = dist (x2,x3) pow 2 in
         let x24 = dist (x2,x4) pow 2 in
         let x34 = dist (x3,x4) pow 2 in
         coplanar {x1, x2, x3, x4} <=> delta x12 x13 x14 x23 x24 x34 = &0 `;;
(* =============== *)
(* ====  *   ===== *)
(* ==   * *     == *)
(*       *         *)
(*    3 rd time    *)
(* =============== *)

(* le 16 *)
let SDIHJZK = new_axiom`! (v1:real^3) v2 v3 (a01: real) a02 a03.
         ~collinear {v1, v2, v3} /\
         (let x12 = d3 v1 v2 pow 2 in
          let x13 = d3 v1 v3 pow 2 in
          let x23 = d3 v2 v3 pow 2 in delta a01 a02 a03 x23 x13 x12 = &0)
         ==> (?!v0. a01 = d3 v0 v1 pow 2 /\
                    a02 = d3 v0 v2 pow 2 /\
                    a03 = d3 v0 v3 pow 2 /\
                    (let x12 = d3 v1 v2 pow 2 in
                     let x13 = d3 v1 v3 pow 2 in
                     let x23 = d3 v2 v3 pow 2 in
                     let vv = ups_x x12 x13 x23 in
                     let t1 = delta_x12 a01 a02 a03 x23 x13 x12 / vv in
                     let t2 = delta_x13 a01 a02 a03 x23 x13 x12 / vv in
                     let t3 = delta_x14 a01 a02 a03 x23 x13 x12 / vv in
                     v0 = t1 % v1 + t2 % v2 + t3 % v3))`;;

(* le 17, p 17 *)
let CDEUSDF = new_axiom `!(va:real^3) vb vc a b c.
     a = d3 vb vc /\ b = d3 va vc /\ c = d3 va vb /\ ~collinear {va, vb, vc}
     ==> (?p. p IN affine hull {va, vb, vc} /\
              (?c. !w. w IN {va, vb, vc} ==> c = dist (p,w)) /\
              (!p'. p' IN affine hull {va, vb, vc} /\
                    (?c. !w. w IN {va, vb, vc} ==> c = dist (p',w))
                    ==> p = p')) /\
         (let al_a =
              (a pow 2 * (b pow 2 + c pow 2 - a pow 2)) /
              (&2 * ups_x (a pow 2) (b pow 2) (c pow 2)) in
          let al_b =
              (b pow 2 * (a pow 2 + c pow 2 - b pow 2)) /
              (&2 * ups_x (a pow 2) (b pow 2) (c pow 2)) in
          let al_c =
              (c pow 2 * (a pow 2 + b pow 2 - c pow 2)) /
              (&2 * ups_x (a pow 2) (b pow 2) (c pow 2)) in
          al_a % va + al_b % vb + al_c % vc = circumcenter {va, vb, vc}) /\
         radV {va, vb, vc} = eta_y a b c`;;

let CDEUSDF_CHANGE = new_axiom `!(va:real^3) vb vc a b c.
     a = d3 vb vc /\ b = d3 va vc /\ c = d3 va vb /\ ~collinear {va, vb, vc}
     ==> (?p. p IN affine hull {va, vb, vc} /\
              (?c. !w. w IN {va, vb, vc} ==> c = dist (p,w)) /\
              (!p'. p' IN affine hull {va, vb, vc} /\
                    (?c. !w. w IN {va, vb, vc} ==> c = dist (p',w))
                    ==> p = p')) /\
         (let al_a =
              (a pow 2 * (b pow 2 + c pow 2 - a pow 2)) /
              (ups_x (a pow 2) (b pow 2) (c pow 2)) in
          let al_b =
              (b pow 2 * (a pow 2 + c pow 2 - b pow 2)) /
              (ups_x (a pow 2) (b pow 2) (c pow 2)) in
          let al_c =
              (c pow 2 * (a pow 2 + b pow 2 - c pow 2)) /
              (ups_x (a pow 2) (b pow 2) (c pow 2)) in
          al_a % va + al_b % vb + al_c % vc = circumcenter {va, vb, vc}) /\
         radV {va, vb, vc} = eta_y a b c`;;
(* le 18, p 17 *)
let WSMRDKN = new_axiom `!x y z p.
         d3 x z pow 2 < d3 x y pow 2 + d3 y z pow 2 /\
         ~collinear {x, y, z} /\
         p = circumcenter {x, y, z}
         ==> p IN aff_gt {x, z} {y}  `;;


(* le 19. p 17 *)
let BYOWBDF = new_axiom`! a b c a' b' ( c':real).
&0 < a /\
         a <= a' /\
         &0 < b /\
         b <= b' /\
         &0 < c /\
         c <= c' /\
         a' pow 2 <= b pow 2 + c pow 2 /\
         b' pow 2 <= a pow 2 + c pow 2 /\
         c' pow 2 <= a pow 2 + b pow 2
         ==> eta_y a b c <= eta_y a' b' c' `;;

(* le 20, p 18 *)
let BFYVLKP = new_axiom ` ! x y z: real^3.
   &2 <= d3 x y /\
         d3 x y <= #2.52 /\
         &2 <= d3 x z /\
         d3 x z <= #2.2 /\
         &2 <= d3 y z /\
         d3 y z <= #2.2
         ==> ~collinear {x, y, z} /\ radV {x, y, z} < sqrt (&2)`;;
(* le 21. p 18 *)
let WDOMZXH = new_axiom` ! y. &2 <= y /\ y <= sqrt8 ==> eta_y y (&2) #2.51 < #1.453`;;
(* le 22. p 18 *)
let ZEDIDCF = new_axiom ` ! v0 v1 (v2:real^3).
         &2 <= d3 v0 v1 /\
         d3 v0 v1 <= #2.51 /\
         #2.45 <= d3 v1 v2 /\
         d3 v1 v2 <= #2.51 /\
         #2.77 <= d3 v0 v2 /\
         d3 v0 v2 <= sqrt8
         ==> sqrt2 < radV {v0, v1, v2}`;;
(* le 23, p 19 *)
let NHSJMDH = new_axiom ` ! y. #2.696 <= y /\ y <= sqrt8 ==>
     eta_y y (&2) (#2.51) <= eta_y y #2.45 (#2.45) `;;

(* le 24 , p 19 *)
let HVXIKHW = new_axiom ` ! x y z. &0 <= x /\ &0 <= y /\ &0 <= z /\ 
          &0 < ups_x_pow2 x y z ==> max_real3 x y z / &2 <= eta_y x y z `;;
(* le 25. p 19 *)
let HMWTCNS = new_axiom ` ! a b (c:real^3). 
             packing {a, b, c} /\ ~ collinear {a,b,c} 
         ==> &2 / sqrt (&3) <= radV {a, b, c}`;;
(* le 26 . p 20 *)
let POXDVXO = new_axiom ` ! v1 v2 (v3:real^3) p.
         ~collinear {v1, v2, v3} /\
         p = circumcenter {v1, v2, v3}
         ==> (p - &1 / &2 % (v1 + v2)) dot (v1 - v2) = &0 /\
         ( p - &1 / &2 % ( v2 + v3 )) dot (v2 - v3 ) = &0 /\
         ( p - &1 / &2 % ( v3 + v1 )) dot ( v3 - v1 ) = &0 `;;
(* le 27. p 20 *)
let MAEWNPU = new_axiom` ? b c. ! x12 x13 x14 x23 x24 x34.
  delta x12 x13 x14 x23 x24 x34 = -- x12 * ( x34  pow 2 ) + b x12 x13 x14 x23 x24 * x34 +
  c x12 x13 x14 x23 x24`;;

let DELTA_COEFS = new_specification ["b_coef"; "c_coef"] MAEWNPU;;
(* le 28. p 20 *)
let AGBWHRD = new_axiom ` ! x12 x13 x14 x23 x24.
   !x12 x13 x14 x23 x24.
         b_coef x12 x13 x14 x23 x24 pow 2 +
         &4 * x12 * c_coef x12 x13 x14 x23 x24 =
         ups_x x12 x23 x13 * ups_x x12 x24 x14 `;;

(* le 29 . p 21 *)
let VCRJIHC = new_axiom` ! x34 x12 x13 v1 x14 v3 x23 v2 v4 x24.
  condA v1 v2 v3 v4 x12 x13 x14 x23 x24 x34 ==>
  muy_delta x12 x13 x14 x23 x24 ( dist( v3,v4) pow 2 ) = &0 `;;
(* le 30. p21 *)
let EWVIFXW = new_axiom` !v1 v2 v3 v4 x12 x13 x14 x23 x24 x34 a b c.
     condA v1 v2 v3 v4 x12 x13 x14 x23 x24 x34 /\
     (!x12 x13 x14 x23 x24 x34.
          muy_delta x12 x13 x14 x23 x24 x34 =
          a x12 x13 x14 x23 x24 * x34 pow 2 +
          b x12 x13 x14 x23 x24 * x34 +
          c x12 x13 x14 x23 x24 )
     ==> (v3 IN aff {v1, v2} \/ v4 IN aff {v1, v2} <=>
          b x12 x13 x14 x23 x24 pow 2 -
          &4 * a x12 x13 x14 x23 x24 * c x12 x13 x14 x23 x24 =
          &0)`;;

(* le 31. p 21 *)
let FFBNQOB = new_axiom` !v1 v2 v3 v4 x12 x13 x14 x23 x24 x34. 
        !v1 v2 v3 v4 x12 x13 x14 x23 x24 x34.
         condA v1 v2 v3 v4 x12 x13 x14 x23 x24 x34 /\
         ~(conv {v3, v4} INTER affine hull {v1, v2} = {})
         ==> muy_delta x12 x13 x14 x23 x24 (dist (v3,v4) pow 2) = &0 /\
             (!root. muy_delta x12 x13 x14 x23 x24 root = &0
                     ==> root <= dist (v3,v4) pow 2) `;;
(* le 32 . p 21 *)
let CHHSZEO = new_axiom `!v1 v2 v3 v4 x12 x13 x14 x23 x24 x34.
         condA v1 v2 v3 v4 x12 x13 x14 x23 x24 x34 /\
         conv {v3, v4} INTER affine hull {v1, v2} = {}
         ==> muy_delta x12 x13 x14 x23 x24 (dist (v3,v4) pow 2) = &0 /\
             (!root. muy_delta x12 x13 x14 x23 x24 root = &0
                     ==>dist (v3,v4) pow 2 <= root )`;;

(* le 33. P 22 *)

let CMUDPKT = new_axiom` !x34 x12 x13 v1 x14 v3 x23 v2 v4 x24 x34' x34'' a.
         condA v1 v2 v3 v4 x12 x13 x14 x23 x24 x34 /\ x34' <= x34'' /\
  (! x. muy_delta x12 x13 x14 x23 x24 x = a * ( x - x34' ) * ( x - x34'')) 
  ==> delta_x34 x12 x13 x14 x23 x24 x34' =
             sqrt (ups_x x12 x13 x23 * ups_x x12 x14 x24) /\
             delta_x34 x12 x13 x14 x23 x24 x34' =
             --sqrt (ups_x x12 x13 x23 * ups_x x12 x14 x24) `;;

(* le 34. p 22 *)
let CXWOCGN = new_axiom` !M13 m12 m14 M24 m34 m23 (v1:real^3) v2 v3 v4.
         condC M13 m12 m14 M24 m34 m23 /\
  CARD {v1,v2,v3,v4} = 4 /\
  m12 <= d3 v1 v2 /\ 
  m23 <= d3 v2 v3 /\
  m34 <= d3 v3 v4 /\ 
  m14 <= d3 v1 v4 /\ 
  d3 v1 v3 < M13 /\
  d3 v2 v4 <= M24 ==>
  conv {v1,v3} INTER conv {v2,v4} = {} `;;

(* le 35. p 22 *)
let THADGSB = new_axiom` !M13 m12 m14 M24 m34 m23 v1 v2 v3 v4.
         (!x. x IN {M13, m12, m14, M24, m34, m23} ==> &0 <= x) /\
         M13 < m12 + m23 /\
         M13 < m14 + m34 /\
         M24 < m12 + m14 /\
         M24 < m23 + m34 /\
         &0 <
         delta (M13 pow 2) (m12 pow 2) (m14 pow 2) (M24 pow 2) (m34 pow 2)
         (m23 pow 2) /\
         CARD {v1, v2, v3, v4} = 4 /\ 
   m12 <= d3 v1 v2 /\
         m23 <= d3 v2 v3 /\
         m34 <= d3 v3 v4 /\
         m14 <= d3 v1 v4 /\
         d3 v1 v3 < M13 /\
         d3 v2 v4 <= M24 ==> conv {v1,v3} INTER conv {v2,v4} = {} `;;
(* le 36. p 23 *)
let ZZSBSIO = new_axiom` ! u v w. CARD {u,v,w} = 3 /\ packing {u,v,w} /\
  dist (u,v) < sqrt8 ==>  dist (u,v) / &2 < dist (w, &1 / &2 % ( u + v )) `;;

(* le 37. p24 *)
let JGYWWBX = new_axiom ` ~ (?v1 v2 w1 (w2:real^3).
           CARD {v1, v2, w1, w2} = 4 /\
           packing {v1, v2, w1, w2} /\
           dist (v1,w2) >= sqrt8 /\
           dist (v1,v2) <= #3.2 /\
           dist (w1,w2) <= sqrt8 /\
           ~(conv {v1, v2} INTER conv {w1, w2} = {}))`;;
(* le 38. p 24 *)
let PAHFWSI = new_axiom` !v1 v2 v3 v4.
         CARD {v1, v2, v3, v4} = 4 /\
         packing {v1, v2, v3, v4} /\
         dist (v1,v3) <= #3.2 /\
         #2.51 <= dist (v1,v2) /\
         dist (v2,v4) <= #2.51
         ==> conv {v1, v3} INTER conv {v2, v4} = {} `;;
(* le 39. p 24 *)
let UVGVIXB = new_axiom ` ! v1 v2 w1 w2.
         CARD {v1, v2, w1, w2} = 4 /\
         packing {v1, v2, w1, w2} /\
         dist (w1,w2) <= #2.51 /\
         dist (v1,v2) <= #3.07
         ==> conv {w1, w2} INTER conv {v1, v2} = {}`;;
(* le 40. p 25 *)
let PJFAXXI = new_axiom` ! v1 v2 w1 w2.
 CARD {v1, v2, w1, w2} = 4 /\
         packing {v1, v2, w1, w2} /\
         dist (v1,v2) <= #3.2 /\
         dist (w1,w2) <= #2.51 /\
         #2.2 <= dist (v1,w1)
         ==> conv {v1, v2} INTER conv {w1, w2} = {}`;;
(* le 41. p 25 *)
let YXWIPMH = new_axiom ` ! v1 v2 v3 (v4:real^3).
 CARD {v1,v2,v3,v4} = 4 /\ 
 d3 v1 v2 = #2.51 /\
         d3 v1 v3 = &2 /\
         d3 v1 v4 = &2 /\
         d3 v2 v3 = &2 /\
         d3 v2 v4 = &2
         ==> d3 v3 v4 <= #3.114467 `;;
(* le 42. p 25 *)
let PAATDXJ = new_axiom ` ! v1 v2 v3 (v4:real^3).
         CARD {v1,v2,v3,v4} = 4 /\ 
         d3 v1 v2 = #2.51 /\
         d3 v1 v4 = #2.51 /\
         d3 v2 v3 = &2 /\
         d3 v3 v4 = &2 /\
         sqrt8 <= d3 v2 v4
         ==> d3 v1 v3 < #3.488 `;;

(* le 43 . p 26 *)
let YJHQPAL = new_axiom `
!m14 m24 m34 M23 M13 M12.
         condF m14 m24 m34 M23 M13 M12
         ==> ~(?v1 v2 v3 v4.
                   coplanar {v1, v2, v3, v4} /\
                   v4 IN conv {v1, v2, v3} /\
                   (let y12 = d3 v1 v2 in
                    let y13 = d3 v1 v3 in
                    let y14 = d3 v1 v4 in
                    let y23 = d3 v2 v3 in
                    let y24 = d3 v2 v4 in
                    let y34 = d3 v3 v4 in
                    m14 <= y14 /\
                    m24 <= y24 /\
                    m34 <= y34 /\
                    y23 <= M23 /\
                    y13 <= M13 /\
                    y12 <= M12))`;;
(* le 44 . p 27 *)
let MPXSJDI = new_axiom` !m M13 M23 m34. condS m m34 M13 M23
     ==> ~(?v1 v2 v3 v4.
               coplanar {v1, v2, v3, v4} /\
               v4 IN conv {v1, v2, v3} /\
               m <= d3 v1 v4 /\
               m <= d3 v2 v4 /\
               m34 <= d3 v3 v4 /\
               d3 v2 v3 <= M23 /\
               d3 v1 v3 <= M13)`;;
(* le 45. p 30 *)

let VMZBXSQ = new_axiom` !v0 v1 v2 (v3: real^3).
     packing {v0, v1, v2, v3} /\
     CARD {v0, v1, v2, v3} = 4 /\
     d3 v0 v1 <= #2.51 /\
     d3 v0 v2 <= #2.51 /\
     d3 v0 v3 <= #2.51 /\
     d3 v1 v2 <= #3.2 /\
     #2.51 <= d3 v1 v3
     ==> rcone_gt v0 v3 (d3 v0 v3 / #2.51) INTER cone v0 {v1, v2} = {}`;;
let LEMMA45 = VMZBXSQ;;
(* le 46 . p 31 *)
let QNXDWNU = new_axiom` !v0 v1 v2 (v3:real^3).
     packing {v0, v1, v2, v3} /\
     CARD {v0, v1, v2, v3} = 4 /\
     d3 v0 v2 <= #2.23 /\
     d3 v0 v3 <= #2.23 /\
     #2.77 <= d3 v2 v3 /\
     d3 v2 v3 <= sqrt8 /\
     (!x. x IN {v0, v2, v3} ==> d3 v1 x <= #2.51)
     ==> rcone_gt v0 v1 (d3 v0 v1 / #2.77) INTER cone v0 {v2, v3} = {}`;;
let LEMMA46 = QNXDWNU ;;
(* le 47. p 32 *)
let PNUMEHN = new_axiom`! v0 v1 v2 (v3 :real^3). packing {v0,v1,v2,v3} /\ 
  #2.51 <= d3 v1 v2 /\ #2.51 <= d3 v1 v3 /\
  d3 v2 v3 <= #3.2 ==>
  let y = d3 v0 v1 in
  let h = cos_arc y ( #1.255 ) ( #1.6 ) in
  cone v0 {v2,v3} INTER rcone_gt v0 v1 h = {} `;;
let LEMAA47 = PNUMEHN ;;

(* le 48 . p 33 *)
let HLAHAUS = new_axiom` !v0 v1 v2 (v3:real^3).
     packing {v0, v1, v2, v3} /\
     d3 v1 v2 = &2 /\
     #3.2 <= d3 v1 v3 /\
     d3 v2 v3 <= #3.2 /\
     ( let y = d3 v0 v1 in
      #2.2 <= y /\ y <= #2.51 )
      ==> (let y = d3 v0 v1 in
           let h = cos_arc y #2.255 #1.6 in
           cone v0 {v2, v3} INTER rcone_gt v0 v1 h = {})`;;
(* le 49 . p 33 *)

let RISDLIH = new_axiom` ! v0 v1 v2 (v3:real^3). d3 v0 v2 <= #2.51 /\
     d3 v0 v3 <= #2.51 /\
     d3 v1 v2 = &2 /\
     #3.2 <= d3 v1 v3 /\
     (let y = d3 v0 v1 in
      &2 <= y /\ y <= #2.2 /\ d3 v2 v3 <= #3.2 ) 
      ==> ((let y = d3 v0 v1 in let h = cos_arc y #1.255 #1.6 in h = &1))`;;
(* ====================== *)

(* lemma 50. p 34 *)
let LTCTBAN = GEN_ALL (new_axiom ` cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 = 
ups_x x12 x13 x23 * x45 pow 2 + cayleytr x12 x13 x14 x15 x23 x24 x25 x34 x35 ( &0 )
* x45 + cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 ( &0 ) `);;
(* lemma 51. p 34 *)
let GJWYYPS = new_axiom`!x12 x13 x14 x15 x23 x24 x25 x34 x35 a b c.
    (! x45.  cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 =
     a  * x45 pow 2 + b * x45 + c )
     ==> b pow 2 - &4 * a * c =
         &16 * delta x12 x13 x14 x23 x24 x34 * delta x12 x13 x15 x23 x25 x35`;;
(* le 52 *)
let PFDFWWV = new_axiom ` ! v1 v2 v3 v4 (v5:real^3).
  muy_v v1 v2 v3 v4 v5 ( (d3 v4 v5) pow 2 ) = &0 `;;
(* le 53 .p 35 *)
let GDLRUZB = new_axiom `!v1 v2 v3 v4 v5 a b c.
         coplanar {v1, v2, v3, v4} \/ coplanar {v1, v2, v3, v5} <=>
         (!a b c.
              (!x. muy_v v1 v2 v3 v4 v5 x = a * x pow 2 + b * x + c)
              ==> b pow 2 - &4 * a * c = &0)`;;
(* le 54. p 35 *)
let KGSNYDS = new_axiom `! v1 v2 v3 v4 (v5:real^3).
  ~ collinear {v1,v2,v3} /\ conv {v4,v5} INTER affine hull {v1,v2,v3} = {} 
 ==> muy_v v1 v2 v3 v4 v5 (( d3 v4 v5) pow 2 )  = &0 /\
   (! x. muy_v v1 v2 v3 v4 v5 x = &0 ==>
   x <= ( d3 v4 v5) pow 2 ) `;;
(* le 55. p 36 *)
let KGSNYDS = new_axiom `! v1 v2 v3 v4 (v5:real^3).
  ~ collinear {v1,v2,v3} /\ ~ (conv0 {v4,v5} INTER affine hull {v1,v2,v3} = {} )
 ==> muy_v v1 v2 v3 v4 v5 (( d3 v4 v5) pow 2 )  = &0 /\
   (! x. muy_v v1 v2 v3 v4 v5 x = &0 ==>
    d3 v4 v5 pow 2 <= x )`;;
(* le 56. p 36 *)
let QHSEWMI = new_axiom `!v1 v2 v3 w1 w2.
     ~(conv {w1, w2} INTER conv {v1, v2, v3} = {}) /\
     ~(w1 IN conv {v1, v2, v3})
     ==> w2 IN cone w1 {v1, v2, v3}`;;
(* lemma 57. p 36 *)
let LEMMA57 = new_axiom ` !v1 v2 v3 w1 (w2: real^3).
     packing {v1, v2, v3, w1, w2} /\
     CARD {v1, v2, v3, w1, w2} = 5 /\
     ~collinear {v1, v2, v3} /\
     radV {v1, v2, v3} < sqrt2 /\
     d3 w1 w2 < sqrt8
     ==> conv {v1, v2, v3} INTER conv {w1, w2} = {}`;;
let DOUFCOI = LEMMA57;;





















(* lemma 59. p 36 *)
let LEMMA59 = new_axiom ` !v1 v2 v3 v4 ( v5:real^3).
         packing {v1, v2, v3, v4, v5} /\
         CARD {v1, v2, v3, v4,v5} = 5 /\
         d3 v2 v3 <= #2.52 /\
         d3 v3 v4 <= #2.52 /\
         d3 v4 v2 <= #2.52 /\
         d3 v1 v5 <= sqrt8 /\
         ~(conv {v1, v5} INTER conv {v2, v3, v4} = {})
         ==> (!aa bb.
                  aa IN {v1, v5} /\ bb IN {v2, v3, v4} ==> d3 aa bb <= #2.2)`;;
let FRCXQKB = LEMMA59 ;;
(* lemma 60 , p 38 *)
let LEMMA60 = new_axiom `!v0 v1 v2 v3 v4.
     packing {v1, v2, v3, v4, v0} /\
     CARD {v1, v2, v3, v4, v0} = 5 /\
     (!x. x IN {v1, v2, v3, v4} ==> d3 v0 x <= #2.51) /\
     d3 v1 v3 <= #2.51 /\
     d3 v2 v4 <= #2.51
     ==> {v0} = cone v0 {v1, v3} INTER cone v0 {v1, v4}`;;
let ZHBBLXP = LEMMA60 ;;
(* le 62. p 40 *)
let LEMMA62 = new_axiom` ! v0 v1 v2 v (w:real^3).
  ~ ( CARD {v0, v1, v2, v, w} = 5 /\
         ~(conv {v, w} INTER cone v0 {v1, v2} = {}) /\
         (!u. u IN {v1, v2, v, w} ==> &2 <= d3 u v0 /\ d3 u v0 <= #2.51) /\
         #3.2 <= d3 v v1 /\
         &2 <= d3 v v2 /\
         &2 <= d3 w v2 /\
         &2 <= d3 w v1 /\
         d3 v w <= #2.2 /\
         &2 <= d3 v2 v1 /\
         d3 v1 v2 <= #3.2  ) `;;
let VNZLYWT = LEMMA62;;
(* le 63. p 42 *)
let LEMMA63 = new_axiom` ! v0 v1 v2 v3 (w:real^3).
CARD {v0, v1, v2, v3, w} = 5 /\
         #2.51 <= d3 w v0 /\
         d3 w v0 <= sqrt8 /\
         d3 v1 v3 <= sqrt8 /\
         (!u. u IN {v0, v1, v2, v3, w} ==> d3 u v0 <= #2.51) /\
         ~(conv {v1, v3} INTER conv {v0, w, v2} = {})
         ==> min (d3 v1 v2) (d3 v2 v3) <= #2.51 /\
             (min (d3 v1 v2) (d3 v2 v3) = #2.51
              ==> d3 v1 v2 = #2.51 /\ d3 v2 v3 = two_t0) `;;
let VAXNRNE = LEMMA62;;
(* le 64. p 42 *)
let LEMMA64 = new_axiom`! v0 v1 v2 v3 (v4:real^3).
  CARD {v0, v1, v2, v3, v4} = 5 /\
         (!u v. u IN {v0, v2} /\ v IN {v1, v3, v4} ==> d3 u v <= two_t0) /\
         d3 v1 v3 <= sqrt8 /\
         d3 v0 v2 <= sqrt8 /\
         ~(conv {v1, v3} INTER conv {v0, v2, v4} = {})
         ==> d3 v1 v4 <= #3.2`;;
let GMOKOTN = LEMMA64;;
(* le 65. p 43 *)
let LEMMA65 = new_axiom ` ! v0 v1 v2 (v3:real^3).
  CARD {v0, v1, v2, v3} = 4 /\
         d3 v0 v1 <= two_t0 /\
         twp_t0 <= d3 v1 v2 /\
         (?a b c.
              {a, b, c} = {v0, v2, v3} /\
              d3 a b <= two_t0 /\
              d3 b c <= two_t0 /\
              d3 a c <= sqrt8)
         ==> rcone_gt v0 v1 (d3 v0 v1 / sqrt8) INTER cone v0 {v2, v3} = {} `;;
let EFXWFNQ = LEMMA65;;
(* lemma 66. p 43 *)
let LEMMA66 = new_axiom ` ! v1 v2 v3 (v0:real^3).
  CARD {v0, v1, v2, v3} = 4 /\
         packing {v0, v1, v2, v3} /\
         d3 v1 v2 <= #2.51 /\
         d3 v2 v3 <= #2.51 /\
         d3 v1 v3 <= sqrt8 /\
         ~(normball v0 (sqrt (&2)) INTER conv {v1, v2, v3} = {})
         ==> (!x. x IN {v1, v2, v3} ==> d3 v0 x <= #2.51) `;;
let LOKDUSSU = LEMMA66 ;;

(* le 67. p 44 *)
let LEMMA67 = new_axiom ` ! v1 v2 v3 (v0:real^3).
  CARD {v0, v1, v2, v3} = 4 /\
         packing {v0, v1, v2, v3} /\
         d3 v1 v2 <= #2.51 /\
         d3 v2 v3 <= #2.51 /\
         d3 v1 v3 <= sqrt8 ==>
normball vo ( #1.255 ) INTER conv {v1,v2,v3} = {} `;;
let FFSXOWD = LEMMA67 ;;

(* le 68 . p 44 *)


let LEMMA68 = new_axiom ` ! v v1 v2 v3 (v4:real^3).
CARD {v, v1, v2, v3, v4} = 5 /\
         packing {v1, v2, v3, v4, v} /\
         (!x y. {x, y} SUBSET {v1, v2, v3, v4} ==> d3 x y <= sqrt8)
         ==> ~(v IN conv {v1, v2, v3, v4}) `;;
let ZODWCKJ = LEMMA68 ;;

(* le 69 . p45 *)

let LEMMA69 = new_axiom ` ! v v1 v2 v3 (v4:real^3).
CARD {v, v1, v2, v3, v4} = 5 /\
         packing {v1, v2, v3, v4, v} /\
 (!x y. {x, y} SUBSET {v1, v2, v3, v4} /\ ~ ( {x,y} = {v1,v2} ) ==> d3 x y < sqrt8)
==> ~ ( v IN conv {v1,v2,v3,v4} ) `;;
let KCGHSFF = LEMMA69 ;;

(* le 70. p 45 *)


let LEMMA70 = new_axiom ` ! v5 v1 v2 v3 (v4:real^3).
CARD {v5, v1, v2, v3, v4} = 5 /\
         packing {v1, v2, v3, v4, v5} /\
         (!x y.
              {x, y} SUBSET {v1, v2, v3, v4, v5} /\ ~({x, y} = {v1, v4})
              ==> d3 x y <= sqrt8)
         ==> ~(v5 IN conv {v1, v2, v3, v4}) `;;
let TEAULMK = LEMMA70 ;;
 (* le 71 , p 46 *)
