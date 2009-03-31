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

let delta_x23 = new_definition ` delta_x23 x12 x13 x14 x23 x24 x34 =
         --x12 * x13 +
         --x24 * x34 +
         x12 * x34 +
         x13 * x24 +
         --x14 * x23 +
         x14 * (x12 + x13 - x14 - x23 + x24 + x34) `;;


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
let RHUFIIB =  ` !x12 x13 x14 x23 x24 x34.
         rho x12 x13 x14 x23 x24 x34 * ups_x x34 x24 x23 =
         chi x12 x13 x14 x23 x24 x34 pow 2 +
         &4 * delta x12 x13 x14 x23 x24 x34 * x34 * x24 * x23 `;;
(* Lemma 3, *)
let NUHSVLM =  ` !x1 x2 x3 x4 (x5 :real^3). 
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
let JVUNDLC =  ` ! a b (c:real ) s. s = ( a + b + c ) / &2 ==>
 &16 * s * (s - a) * (s - b) * (s - c) =
             ups_x (a pow 2) (b pow 2) (c pow 2)`;;
(* lemma 5, page 12 *)
let RCEABUJ =  ` ! a (b:real^3) x. line x /\ {a,b} SUBSET x /\ ~( a = b) 
    ==> x = aff {a,b} `;;
(* lem 6. p 12 *)
let BXVMKNF =  ` ! u v:real ^3. ~( u=v) ==> plane_norm ( bis u v ) `;;
(* la 7. p 12 *)
let SMWTDMU =  ` !x y z p.
         plane p /\ ~collinear {x, y, z} /\ {x, y, z} SUBSET p
         ==> p = aff {x, y, z}`;;
(* le 8. p 12 *)
let SGFCDZO =  `! v1 v2 v3:real^3 t1 t2 (t3:real). 
         t1 % v1 + t2 % v2 + t3 % v3 = vec 0 /\
         t1 + t2 + t3 = &0 /\
         ~(t1 = &0 /\ t2 = &0 /\ t3 = &0)
         ==> collinear {v1, v2, v3}`;;
let lemma8 = SGFCDZO;;
(* le 9. p 13 *)
let FHFMKIY =  ` ! (v1: real^3) v2 v3 x12 x13 x23.
         x12 = dist (v1,v2) pow 2 /\
         x13 = dist (v1,v3) pow 2 /\
         x23 = dist (v2,v3) pow 2
         ==> (collinear {v1, v2, v3} <=> ups_x x12 x13 x23 = &0)`;;
let lemma9 = FHFMKIY;;
(* le 10. p 14 *)
let ZPGPXNN =  `! v1 v2 (v:real^3).
         dist (v1,v2) < dist (v,v1) + dist (v,v2) ==> ~(v IN conv {v1, v2})`;;
let lemma10 = ZPGPXNN;;
(* le 11. p14 *)
let FAFKVLR =  new_axiom ` ? t1 t2 t3. ! v1 v2 v3 (v:real^3).
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
(* let COEFS = new_specification ["coef1"; "coef2"; "coef3"] FAFKVLR;; *)
let plane_3p = new_definition `plane_3p (a:real^3) b c =
         {x | ~collinear {a, b, c} /\
              (?ta tb tc. ta + tb + tc = &1 /\ x = ta % a + tb % b + tc % c)}`;;
(* le 12. p 15 *)
let CNXIFFC =  ` ! (v1:real^3) (v2:real^3) (v3:real^3) (v:real^3). ~ collinear {v1,v2,v3} /\ v IN affine hull 
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
let MYOQCBS =  ` ! v1 v2 v3 (v:real^3). ~ collinear {v1,v2,v3}/\
  v IN affine hull {v1,v2,v3} ==>
   ( v IN conv {v1,v2,v3} <=> &0 <= coef1 v1 v2 v3 v /\ &0 <= coef2 v1 v2 v3 v /\
   &0 <= coef3 v1 v2 v3 v ) /\ 
   ( v IN conv0 {v1,v2,v3} <=> &0 < coef1 v1 v2 v3 v /\ &0 < coef2 v1 v2 v3 v /\
   &0 < coef3 v1 v2 v3 v )`;;
let lemma13 = MYOQCBS;;
(* le 14. p 15 *)

let TXDIACY =  `! (a:real^3) b c d (v0: real^3) r.
 {a, b, c, d} SUBSET normball v0 r
         ==> convex hull {a, b, c, d} SUBSET normball v0 r `;;

(* le 15. p 16 *)
let POLFLZY =  ` ! x1 x2 x3 (x4: real^3).  
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
let SDIHJZK = `! (v1:real^3) v2 v3 (a01: real) a02 a03.
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
let CDEUSDF =  `!(va:real^3) vb vc a b c.
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

let CDEUSDF_CHANGE =  `!(va:real^3) vb vc a b c.
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
let WSMRDKN =  `!x y z p.
         d3 x z pow 2 < d3 x y pow 2 + d3 y z pow 2 /\
         ~collinear {x, y, z} /\
         p = circumcenter {x, y, z}
         ==> p IN aff_gt {x, z} {y}  `;;


(* le 19. p 17 *)
let BYOWBDF = `! a b c a' b' ( c':real).
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
let BFYVLKP =  ` ! x y z: real^3.
   &2 <= d3 x y /\
         d3 x y <= #2.52 /\
         &2 <= d3 x z /\
         d3 x z <= #2.2 /\
         &2 <= d3 y z /\
         d3 y z <= #2.2
         ==> ~collinear {x, y, z} /\ radV {x, y, z} < sqrt (&2)`;;
(* le 21. p 18 *)
let WDOMZXH = ` ! y. &2 <= y /\ y <= sqrt8 ==> eta_y y (&2) #2.51 < #1.453`;;
(* le 22. p 18 *)
let ZEDIDCF =  ` ! v0 v1 (v2:real^3).
         &2 <= d3 v0 v1 /\
         d3 v0 v1 <= #2.51 /\
         #2.45 <= d3 v1 v2 /\
         d3 v1 v2 <= #2.51 /\
         #2.77 <= d3 v0 v2 /\
         d3 v0 v2 <= sqrt8
         ==> sqrt2 < radV {v0, v1, v2}`;;
(* le 23, p 19 *)
let NHSJMDH =  ` ! y. #2.696 <= y /\ y <= sqrt8 ==>
     eta_y y (&2) (#2.51) <= eta_y y #2.45 (#2.45) `;;

(* le 24 , p 19 *)
let HVXIKHW =  ` ! x y z. &0 <= x /\ &0 <= y /\ &0 <= z /\ 
          &0 < ups_x_pow2 x y z ==> max_real3 x y z / &2 <= eta_y x y z `;;
(* le 25. p 19 *)
let HMWTCNS =  ` ! a b (c:real^3). 
             packing {a, b, c} /\ ~ collinear {a,b,c} 
         ==> &2 / sqrt (&3) <= radV {a, b, c}`;;
(* le 26 . p 20 *)
let POXDVXO =  ` ! v1 v2 (v3:real^3) p.
         ~collinear {v1, v2, v3} /\
         p = circumcenter {v1, v2, v3}
         ==> (p - &1 / &2 % (v1 + v2)) dot (v1 - v2) = &0 /\
         ( p - &1 / &2 % ( v2 + v3 )) dot (v2 - v3 ) = &0 /\
         ( p - &1 / &2 % ( v3 + v1 )) dot ( v3 - v1 ) = &0 `;;
(* le 27. p 20 *)
let MAEWNPU = new_axiom ` ? b c. ! x12 x13 x14 x23 x24 x34.
  delta x12 x13 x14 x23 x24 x34 = -- x12 * ( x34  pow 2 ) + b x12 x13 x14 x23 x24 * x34 +
  c x12 x13 x14 x23 x24`;;

let DELTA_COEFS = new_specification ["b_coef"; "c_coef"] MAEWNPU;;
(* le 28. p 20 *)
let AGBWHRD =  ` ! x12 x13 x14 x23 x24.
   !x12 x13 x14 x23 x24.
         b_coef x12 x13 x14 x23 x24 pow 2 +
         &4 * x12 * c_coef x12 x13 x14 x23 x24 =
         ups_x x12 x23 x13 * ups_x x12 x24 x14 `;;

(* le 29 . p 21 *)
let VCRJIHC = ` ! x34 x12 x13 v1 x14 v3 x23 v2 v4 x24.
  condA v1 v2 v3 v4 x12 x13 x14 x23 x24 x34 ==>
  muy_delta x12 x13 x14 x23 x24 ( dist( v3,v4) pow 2 ) = &0 `;;
(* le 30. p21 *)
let EWVIFXW = ` !v1 v2 v3 v4 x12 x13 x14 x23 x24 x34 a b c.
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
let FFBNQOB = ` !v1 v2 v3 v4 x12 x13 x14 x23 x24 x34. 
        !v1 v2 v3 v4 x12 x13 x14 x23 x24 x34.
         condA v1 v2 v3 v4 x12 x13 x14 x23 x24 x34 /\
         ~(conv {v3, v4} INTER affine hull {v1, v2} = {})
         ==> muy_delta x12 x13 x14 x23 x24 (dist (v3,v4) pow 2) = &0 /\
             (!root. muy_delta x12 x13 x14 x23 x24 root = &0
                     ==> root <= dist (v3,v4) pow 2) `;;
(* le 32 . p 21 *)
let CHHSZEO =  `!v1 v2 v3 v4 x12 x13 x14 x23 x24 x34.
         condA v1 v2 v3 v4 x12 x13 x14 x23 x24 x34 /\
         conv {v3, v4} INTER affine hull {v1, v2} = {}
         ==> muy_delta x12 x13 x14 x23 x24 (dist (v3,v4) pow 2) = &0 /\
             (!root. muy_delta x12 x13 x14 x23 x24 root = &0
                     ==>dist (v3,v4) pow 2 <= root )`;;

(* le 33. P 22 *)

let CMUDPKT = ` !x34 x12 x13 v1 x14 v3 x23 v2 v4 x24 x34' x34'' a.
         condA v1 v2 v3 v4 x12 x13 x14 x23 x24 x34 /\ x34' <= x34'' /\
  (! x. muy_delta x12 x13 x14 x23 x24 x = a * ( x - x34' ) * ( x - x34'')) 
  ==> delta_x34 x12 x13 x14 x23 x24 x34' =
             sqrt (ups_x x12 x13 x23 * ups_x x12 x14 x24) /\
             delta_x34 x12 x13 x14 x23 x24 x34' =
             --sqrt (ups_x x12 x13 x23 * ups_x x12 x14 x24) `;;

(* le 34. p 22 *)
let CXWOCGN = ` !M13 m12 m14 M24 m34 m23 (v1:real^3) v2 v3 v4.
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
let THADGSB = ` !M13 m12 m14 M24 m34 m23 v1 v2 v3 v4.
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
         d3 v1 v3 <= M13 /\
         d3 v2 v4 <= M24 ==> conv {v1,v3} INTER conv {v2,v4} = {} `;;
(* le 36. p 23 *)
let ZZSBSIO = ` ! u v w. CARD {u,v,w} = 3 /\ packing {u,v,w} /\
  dist (u,v) < sqrt8 ==>  dist (u,v) / &2 < dist (w, &1 / &2 % ( u + v )) `;;

(* le 37. p24 *)
let JGYWWBX =  ` ~ (?v1 v2 w1 (w2:real^3).
           CARD {v1, v2, w1, w2} = 4 /\
           packing {v1, v2, w1, w2} /\
           dist (v1,w2) >= sqrt8 /\
           dist (v1,v2) <= #3.2 /\
           dist (w1,w2) <= sqrt8 /\
           ~(conv {v1, v2} INTER conv {w1, w2} = {}))`;;
(* le 38. p 24 *)
let PAHFWSI = ` !(v1:real^3) v2 v3 v4.
         CARD {v1, v2, v3, v4} = 4 /\
         packing {v1, v2, v3, v4} /\
         dist (v1,v3) <= #3.2 /\
         #2.51 <= dist (v1,v2) /\
         dist (v2,v4) <= #2.51
         ==> conv {v1, v3} INTER conv {v2, v4} = {} `;;
(* le 39. p 24 *)
let UVGVIXB =  ` ! (v1:real^3) v2 w1 w2.
         CARD {v1, v2, w1, w2} = 4 /\
         packing {v1, v2, w1, w2} /\
         dist (w1,w2) <= #2.51 /\
         dist (v1,v2) <= #3.07
         ==> conv {w1, w2} INTER conv {v1, v2} = {}`;;
(* le 40 . p 25 *)
let PJFAYXI = ` ! (v1:real^3) v2 w1 w2.
 CARD {v1, v2, w1, w2} = 4 /\
         packing {v1, v2, w1, w2} /\
         dist (v1,v2) <= #3.2 /\
         dist (w1,w2) <= #2.51 /\
         #2.2 <= dist (v1,w1)
         ==> conv {v1, v2} INTER conv {w1, w2} = {}`;;
(* le 41. p 25 *)
let YXWIPMH =  ` ! v1 v2 v3 (v4:real^3).
 CARD {v1,v2,v3,v4} = 4 /\ 
 d3 v1 v2 = #2.51 /\
         d3 v1 v3 = &2 /\
         d3 v1 v4 = &2 /\
         d3 v2 v3 = &2 /\
         d3 v2 v4 = &2
         ==> d3 v3 v4 <= #3.114467 `;;
(* le 42. p 25 *)
let PAATDXJ =  ` ! v1 v2 v3 (v4:real^3).
         CARD {v1,v2,v3,v4} = 4 /\ 
         d3 v1 v2 = #2.51 /\
         d3 v1 v4 = #2.51 /\
         d3 v2 v3 = &2 /\
         d3 v3 v4 = &2 /\
         sqrt8 <= d3 v2 v4
         ==> d3 v1 v3 < #3.488 `;;

(* le 43 . p 26 *)
let YJHQPAL =  `
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
let MPXSJDI = ` !m M13 M23 m34. condS m m34 M13 M23
     ==> ~(?v1 v2 v3 v4.
               coplanar {v1, v2, v3, v4} /\
               v4 IN conv {v1, v2, v3} /\
               m <= d3 v1 v4 /\
               m <= d3 v2 v4 /\
               m34 <= d3 v3 v4 /\
               d3 v2 v3 <= M23 /\
               d3 v1 v3 <= M13)`;;
(* le 45. p 30 *)

let VMZBXSQ = ` !v0 v1 v2 (v3: real^3).
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
let QNXDWNU = ` !v0 v1 v2 (v3:real^3).
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
let PNUMEHN = `! v0 v1 v2 (v3 :real^3). packing {v0,v1,v2,v3} /\ 
  #2.51 <= d3 v1 v2 /\ #2.51 <= d3 v1 v3 /\
  d3 v2 v3 <= #3.2 ==>
  let y = d3 v0 v1 in
  let h = cos_arc y ( #1.255 ) ( #1.6 ) in
  cone v0 {v2,v3} INTER rcone_gt v0 v1 h = {} `;;
let LEMAA47 = PNUMEHN ;;

(* le 48 . p 33 *)
let HLAHAUS = ` !v0 v1 v2 (v3:real^3).
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

let RISDLIH = ` ! v0 v1 v2 (v3:real^3). d3 v0 v2 <= #2.51 /\
     d3 v0 v3 <= #2.51 /\
     d3 v1 v2 = &2 /\
     #3.2 <= d3 v1 v3 /\
     (let y = d3 v0 v1 in
      &2 <= y /\ y <= #2.2 /\ d3 v2 v3 <= #3.2 ) 
      ==> ((let y = d3 v0 v1 in let h = cos_arc y #1.255 #1.6 in h = &1))`;;
(* ====================== *)

(* lemma 50. p 34 *)

let LTCTBAN = `! x12 x13 x14 x15 x23 x24 x25 x34 x35 x45.
 cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 = 
ups_x x12 x13 x23 * x45 pow 2 + cayleytr x12 x13 x14 x15 x23 x24 x25 x34 x35 ( &0 )
* x45 + cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 ( &0 ) `;;
(* lemma 51. p 34 *)
let GJWYYPS = `!x12 x13 x14 x15 x23 x24 x25 x34 x35 a b c.
    (! x45.  cayleyR x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 =
     a  * x45 pow 2 + b * x45 + c )
     ==> b pow 2 - &4 * a * c =
         &16 * delta x12 x13 x14 x23 x24 x34 * delta x12 x13 x15 x23 x25 x35`;;

(* le 52 *)
let PFDFWWV =  ` ! v1 v2 v3 v4 (v5:real^3).
  muy_v v1 v2 v3 v4 v5 ( (d3 v4 v5) pow 2 ) = &0 `;;
(* le 53 .p 35 *)
let GDLRUZB =  `!v1 v2 v3 v4 v5 a b c.
         coplanar {v1, v2, v3, v4} \/ coplanar {v1, v2, v3, v5} <=>
         (!a b c.
              (!x. muy_v v1 v2 v3 v4 v5 x = a * x pow 2 + b * x + c)
              ==> b pow 2 - &4 * a * c = &0)`;;
(* le 54. p 35 *)
let KGSNYDS =  `! v1 v2 v3 v4 (v5:real^3).
  ~ collinear {v1,v2,v3} /\ conv {v4,v5} INTER affine hull {v1,v2,v3} = {} 
 ==> muy_v v1 v2 v3 v4 v5 (( d3 v4 v5) pow 2 )  = &0 /\
   (! x. muy_v v1 v2 v3 v4 v5 x = &0 ==>
   x <= ( d3 v4 v5) pow 2 ) `;;
(* le 55. p 36 *)
let KGSNYDS =  `! v1 v2 v3 v4 (v5:real^3).
  ~ collinear {v1,v2,v3} /\ ~ (conv0 {v4,v5} INTER affine hull {v1,v2,v3} = {} )
 ==> muy_v v1 v2 v3 v4 v5 (( d3 v4 v5) pow 2 )  = &0 /\
   (! x. muy_v v1 v2 v3 v4 v5 x = &0 ==>
    d3 v4 v5 pow 2 <= x )`;;
(* le 56. p 36 *)
let QHSEWMI =  `!v1 v2 v3 w1 w2.
     ~(conv {w1, w2} INTER conv {v1, v2, v3} = {}) /\
     ~(w1 IN conv {v1, v2, v3})
     ==> w2 IN cone w1 {v1, v2, v3}`;;
(* lemma 57. p 36 *)
let LEMMA57 =  ` !v1 v2 v3 w1 (w2: real^3).
     packing {v1, v2, v3, w1, w2} /\
     CARD {v1, v2, v3, w1, w2} = 5 /\
     ~collinear {v1, v2, v3} /\
     radV {v1, v2, v3} < sqrt2 /\
     d3 w1 w2 < sqrt8
     ==> conv {v1, v2, v3} INTER conv {w1, w2} = {}`;;
let DOUFCOI = LEMMA57;;


let LEMMA58 =  `! m12 m13 m14 m25 m35 m45 M23 M34 M24 M15.
  (!x. x IN {m12, m13, m14, m25, m35, m45, M23, M34, M24, M15}
              ==> &0 <= x) /\
         condC M15 m12 m13 M23 m35 m25 /\
         condC M15 m13 m14 M34 m45 m35 /\
         condC M15 m12 m24 M24 m45 m25 /\
         condF m25 m35 m45 M34 M24 M23 /\
         condF m12 m13 m14 M34 M24 M23 /\
         M15 < sqrt_of_ge_root m12 m13 m14 M34 M24 M23 m25 m35 m45
         ==> ~(?(v1:real^3) v2 v3 v4 v5.
                   CARD {v11, v2, v3, v4, v5} = 5 /\
                   ~collinear {v2, v3, v4} /\
                   ~(conv {v1, v5} INTER conv {v2, v3, v4} = {}) /\
  (let x12 = dist (x1,x2) in
                    let x13 = dist (x1,x3) in
                    let x14 = dist (x1,x4) in
                    let x15 = dist (x1,x5) in
                    let x23 = dist (x2,x3) in
                    let x24 = dist (x2,x4) in
                    let x25 = dist (x2,x5) in
                    let x34 = dist (x3,x4) in
                    let x35 = dist (x3,x5) in
                    let x45 = dist (x4,x5) in
                    x15 <= M15 /\
                    x23 <= M23 /\
                    x24 <= M24 /\
                    x34 <= M34 /\
                    x12 >= m12 /\
                    x13 >= m13 /\
                    x14 >= m14 /\
                    x25 >= m25 /\
                    x35 >= m35 /\
                    x45 >= m45)) `;;
let UQQVJON = LEMMA58;;



(* lemma 59. p 36 *)
let LEMMA59 =  ` !v1 v2 v3 v4 ( v5:real^3).
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
let LEMMA60 =  `!v0 v1 v2 v3 v4.
     packing {v1, v2, v3, v4, v0} /\
     CARD {v1, v2, v3, v4, v0} = 5 /\
     (!x. x IN {v1, v2, v3, v4} ==> d3 v0 x <= #2.51) /\
     d3 v1 v3 <= #2.51 /\
     d3 v2 v4 <= #2.51
     ==> {v0} = cone v0 {v1, v3} INTER cone v0 {v1, v4}`;;
let ZHBBLXP = LEMMA60 ;;
(* le 62. p 40 *)
let LEMMA62 = ` ! v0 v1 v2 v (w:real^3).
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
let LEMMA63 = ` ! v0 v1 v2 v3 (w:real^3).
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
let LEMMA64 = `! v0 v1 v2 v3 (v4:real^3).
  CARD {v0, v1, v2, v3, v4} = 5 /\
         (!u v. u IN {v0, v2} /\ v IN {v1, v3, v4} ==> d3 u v <= two_t0) /\
         d3 v1 v3 <= sqrt8 /\
         d3 v0 v2 <= sqrt8 /\
         ~(conv {v1, v3} INTER conv {v0, v2, v4} = {})
         ==> d3 v1 v4 <= #3.2`;;
let GMOKOTN = LEMMA64;;
(* le 65. p 43 *)
let LEMMA65 =  ` ! v0 v1 v2 (v3:real^3).
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
let LEMMA66 =  ` ! v1 v2 v3 (v0:real^3).
  CARD {v0, v1, v2, v3} = 4 /\
         packing {v0, v1, v2, v3} /\
         d3 v1 v2 <= #2.51 /\
         d3 v2 v3 <= #2.51 /\
         d3 v1 v3 <= sqrt8 /\
         ~(normball v0 (sqrt (&2)) INTER conv {v1, v2, v3} = {})
         ==> (!x. x IN {v1, v2, v3} ==> d3 v0 x <= #2.51) `;;
let LOKDUSSU = LEMMA66 ;;

(* le 67. p 44 *)
let LEMMA67 =  ` ! v1 v2 v3 (v0:real^3).
  CARD {v0, v1, v2, v3} = 4 /\
         packing {v0, v1, v2, v3} /\
         d3 v1 v2 <= #2.51 /\
         d3 v2 v3 <= #2.51 /\
         d3 v1 v3 <= sqrt8 ==>
normball vo ( #1.255 ) INTER conv {v1,v2,v3} = {} `;;
let FFSXOWD = LEMMA67 ;;

(* le 68 . p 44 *)


let LEMMA68 =  ` ! v v1 v2 v3 (v4:real^3).
CARD {v, v1, v2, v3, v4} = 5 /\
         packing {v1, v2, v3, v4, v} /\
         (!x y. {x, y} SUBSET {v1, v2, v3, v4} ==> d3 x y <= sqrt8)
         ==> ~(v IN conv {v1, v2, v3, v4}) `;;
let ZODWCKJ = LEMMA68 ;;

(* le 69 . p45 *)

let LEMMA69 =  ` ! v v1 v2 v3 (v4:real^3).
CARD {v, v1, v2, v3, v4} = 5 /\
         packing {v1, v2, v3, v4, v} /\
 (!x y. {x, y} SUBSET {v1, v2, v3, v4} /\ ~ ( {x,y} = {v1,v2} ) ==> d3 x y < sqrt8)
==> ~ ( v IN conv {v1,v2,v3,v4} ) `;;
let KCGHSFF = LEMMA69 ;;

(* le 70. p 45 *)


let LEMMA70 =  ` ! v5 v1 v2 v3 (v4:real^3).
CARD {v5, v1, v2, v3, v4} = 5 /\
         packing {v1, v2, v3, v4, v5} /\
         (!x y.
              {x, y} SUBSET {v1, v2, v3, v4, v5} /\ ~({x, y} = {v1, v4})
              ==> d3 x y <= sqrt8)
         ==> ~(v5 IN conv {v1, v2, v3, v4}) `;;
let TEAULMK = LEMMA70 ;;
 (* le 71 , p 46 *)
let LEMMA71 =  ` ! w v v0 v1 (v2:real^3).
   let t = #2.51 in
         CARD {w, v, v0, v1, v2} = 5 /\
         packing {w, v, v0, v1, v2} /\
         d3 v v1 <= t /\
         d3 v v2 <= t /\
         d3 v0 v1 <= t /\
         d3 v0 v2 <= t /\
         d3 v0 v <= sqrt8 /\
         t <= d3 v0 w /\
         d3 v0 w <= sqrt8 /\
         w IN cone v0 {v1, v2, v}
         ==> d3 w v <= t `;;
let EIYPZVL = LEMMA71;;
(* le 72. p 47 *)
let LEMMA72 = ` ! w v1 v2 v3 (v4:real^3). 
  CARD {w, v1, v2, v3, v4} = 5 /\
         packing {w, v1, v2, v3, v4} /\
         (let t = #2.51 in
          d3 v2 v3 <= t /\
          d3 v3 v4 <= t /\
          d3 v2 v4 <= t /\
          t <= d3 v1 v2 /\
          t <= d3 v1 v3 /\
          d3 v1 v4 <= t /\
          d3 v1 w <= sqrt8 /\
          d3 v1 v2 <= sqrt8 /\
          d3 v1 v3 <= sqrt8)
         ==> ~(w IN cone v1 {v2, v3, v4}) `;;
let VZETXZC = LEMMA72 ;;
(* le 73 . p 47 *)
let LEMMA73 =  ` ! v1 v2 v3 (v4:real^3) a01 a02 a03 .
  let x12 = d3 v1 v2 pow 2 in
         let x13 = d3 v1 v3 pow 2 in
         let x23 = d3 v2 v3 pow 2 in
         CARD {v1, v2, v3, v4} = 4 /\
         packing {v1, v2, v3, v4} /\
         ~coplanar {v1, v2, v3, v4} /\
  &0 <= a01 /\ &0 <= a02 /\ &0 <= a03 /\ 
  delta a01 a02 a03 x12 x13 x23 >= &0
         ==> (?v0. v0 IN aff_ge {v1, v2, v3} {v4} /\
                   d3 v0 v1 pow 2 = a01 /\
                   d3 v0 v2 pow 2 = a02 /\
                   d3 v0 v3 pow 2 = a03 /\
                   (!vv0. vv0 IN aff_ge {v1, v2, v3} {v4} /\
                          d3 vv0 v1 pow 2 = a01 /\
                          d3 vv0 v2 pow 2 = a02 /\
                          d3 vv0 v3 pow 2 = a03
                          ==> vv0 = v0) /\
                   ( v0 IN aff {v1,v2,v3} <=> 
                     delta a01 a02 a03 x12 x13 x23 = &0 )) `;;
(* le 74 . p 48 *)
let LFYTDXC = new_axiom ` ? p. ! v1 v2 v3 (v4:real^3) r.
  let s = {v1, v2, v3, v4} in
         CARD s = 4 /\
         packing s /\
         ~coplanar s /\
         eta_y (d3 v1 v2 pow 2) (d3 v1 v3 pow 2) (d3 v2 v3 pow 2) <= r
         ==> p v1 v2 v3 v4 r IN aff_ge {v1, v2, v3} {v4} /\
                   r = d3 ( p v1 v2 v3 v4 r ) v1 /\
                   r = d3 ( p v1 v2 v3 v4 r ) v2 /\
                   r = d3 ( p v1 v2 v3 v4 r )  v3 /\
                   (!w. w IN aff_ge {v1, v2, v3} {v4} /\
                        r = d3 w v1 /\
                        r = d3 w v2 /\
                        r = d3 w v3
                        ==> w = ( p v1 v2 v3 v4 r ) ) `;;

let LEMMA74 = LFYTDXC;;
let point_eq = new_specification ["point_eq"] LFYTDXC;;


(* le 75 . p 48 *)
let LEMMA75 = ` !v1 v2 v3 (v4:real^3) r p p' u. let s = {v1,v2,v3,v4} in
let x12 = d3 v1 v2 pow 2 in
let x13 = d3 v1 v3 pow 2 in
let x23 = d3 v2 v3 pow 2 in
~ coplanar s /\
CARD s = 4 /\
eta_y x12 x13 x23 < r /\
p' = point_eq v1 v2 v3 v4 r /\
p = circumcenter {v1,v2,v3} /\ u IN aff {v1,v2,v3} ==>
( p' - p ) dot ( u - p ) = &0 `;;
let TIEEBHT = LEMMA75;;

(* le 76 . p49 *)
let LEMMA76 = new_axiom` ?t1 t2 t3 t4.
     !v1 v2 v3 v4 (v: real^3).
         ~coplanar {v1, v2, v3, v4}
         ==> t1 v1 v2 v3 v4 v +
             t2 v1 v2 v3 v4 v +
             t3 v1 v2 v3 v4 v +
             t4 v1 v2 v3 v4 v =
             &1 /\
             v =
             t1 v1 v2 v3 v4 v % v1 +
             t2 v1 v2 v3 v4 v % v2 +
             t3 v1 v2 v3 v4 v % v3 +
             t4 v1 v2 v3 v4 v % v4 /\
             (!ta tb tc td.
                  v = ta % v1 + tb % v2 + tc % v3 + td % v4 /\
                  ta + tb + tc + td = &1
                  ==> ta = t1 v1 v2 v3 v4 v /\
                      tb = t2 v1 v2 v3 v4 v /\
                      tc = t3 v1 v2 v3 v4 v /\
                      td = t4 v1 v2 v3 v4 v) `;;
let ECSEVNC = LEMMA76 ;;
let COEFS_4 = new_specification ["COEF4_1"; "COEF4_2"; "COEF4_3"; "COEF4_4"] ECSEVNC ;;

(* le 77. p 49 *)let LEMMA77 = ` ! v1 v2 v3 v4 (v:real^3).
  ~ coplanar {v1,v2,v3,v4} ==>
  ( COEF4_1 v1 v2 v3 v4 v < &0 <=> v IN aff_lt {v2,v3, v4} {v1} ) /\
  ( COEF4_1 v1 v2 v3 v4 v = &0 <=> v IN aff {v2,v3,v4} ) /\
  ( COEF4_1 v1 v2 v3 v4 v > &0 <=> v IN aff_gt {v2,v3,v4} {v1} ) /\
  ( COEF4_2 v1 v2 v3 v4 v < &0 <=> v IN aff_lt {v1,v3, v4} {v2} ) /\
  ( COEF4_2 v1 v2 v3 v4 v = &0 <=> v IN aff {v1,v3,v4} ) /\
  ( COEF4_2 v1 v2 v3 v4 v > &0 <=> v IN aff_gt {v1,v3,v4} {v2} ) /\  
  ( COEF4_3 v1 v2 v3 v4 v < &0 <=> v IN aff_lt {v2,v1, v4} {v3} ) /\
  ( COEF4_3 v1 v2 v3 v4 v = &0 <=> v IN aff {v2,v1,v4} ) /\
  ( COEF4_3 v1 v2 v3 v4 v > &0 <=> v IN aff_gt {v2,v1,v4} {v3} )/\  
  ( COEF4_4 v1 v2 v3 v4 v < &0 <=> v IN aff_lt {v2,v1, v3} {v4} ) /\
  ( COEF4_4 v1 v2 v3 v4 v = &0 <=> v IN aff {v2,v1,v3} ) /\
  ( COEF4_4 v1 v2 v3 v4 v > &0 <=> v IN aff_gt {v2,v1,v3} {v4} )`;;

(* le 78 . p 50 *)
let LEMMA78 = ` ! v1 v2 v3 v4 (v:real^3).
  ~coplanar {v1, v2, v3, v4}
         ==> (v IN conv {v1, v2, v3, v4} <=>
              &0 <= COEF4_1 v1 v2 v3 v4 v /\
              &0 <= COEF4_2 v1 v2 v3 v4 v /\
              &0 <= COEF4_3 v1 v2 v3 v4 v /\
              &0 <= COEF4_4 v1 v2 v3 v4 v) /\
             (v IN conv0 {v1, v2, v3, v4} <=>
              &0 < COEF4_1 v1 v2 v3 v4 v /\
              &0 < COEF4_2 v1 v2 v3 v4 v /\
              &0 < COEF4_3 v1 v2 v3 v4 v /\
              &0 < COEF4_4 v1 v2 v3 v4 v) `;;
let ZRFMKPY = LEMMA78;;


(* le 79 . p 50 *)
let LEMMA79 = ` ! v0 v1 v2 v3 (v4:real^3).
  let tt = #2.51 in
         let ss = sqrt (&8) in
         CARD {v0, v1, v2, v3, v4} = 5 /\
         packing {v1, v2, v3, v4, v0} /\
         (!v. v IN {v2, v3, v4} ==> d3 v1 v <= #2.51 /\ &2 <= d3 v1 v) /\
         tt < d3 v1 v0 /\
         d3 v1 v0 < ss /\
  d3 v0 v3 <= tt /\
  d3 v2 v4 <= tt /\
  d3 v0 v4 < ss /\
  d3 v0 v2 < ss /\
  ~(  tt < d3 v0 v2 /\ tt < d3 v0 v4 ) 
  ==> ~ ( v3 IN aff_ge {v0,v1} {v2,v4} ) `;;

let COEBRMF = LEMMA79 ;;

(* le 80. p 51 *)
let LEMMA80 = ` ! v0 v1 v2 v3 (v4:real^N).
   CARD {v0, v1, v2, v3, v4} = 5 /\
         (?x. ~(x = v0) /\ x IN cone v0 {v1, v3} INTER cone v0 {v2, v4})
         ==> ~(conv {v1, v3} INTER cone v0 {v2, v4} = {} /\
               conv {v2, v4} INTER cone v0 {v1, v3} = {})`;;
let JVDAFRS = LEMMA80;;

let LEMMA81 = ` ! v1 v2 v3 (v4:real^3).
  let s = {v1,v2,v3,v4} in
  CARD s = 4 /\ ~ coplanar s ==>
  conv s = aff_ge ( s DIFF {v1} ) {v1} INTER 
  aff_ge ( s DIFF {v2} ) {v2} INTER 
  aff_ge ( s DIFF {v3} ) {v3} INTER 
  aff_ge ( s DIFF {v4} ) {v4} `;;
let ARIKWRQ = LEMMA81 ;;

(* le 82. p 52 *)
let LEMMA82 =  ` ! v1 v2 v3 (v4:real^3). let s = {v1,v2,v3,v4} in
  CARD s = 4 /\ coplanar s ==>
  conv0 s = aff_gt ( s DIFF {v1} ) {v1} INTER 
  aff_gt ( s DIFF {v2} ) {v2} INTER 
  aff_gt ( s DIFF {v3} ) {v3} INTER 
  aff_gt ( s DIFF {v4} ) {v4} `;;
(* le 83. p 52 *)
let LEMMA83 =  ` !(e1:real^3) e2 e3 a b c a' b' c' t1 t2 t3.
  e1 = basis 1 /\
     e2 = basis 2 /\
     e3 = basis 3 /\
     &0 < a /\
     a <= b /\
     b <= c /\
     &0 < a' /\
     a' <= b' /\
     b' <= c' /\
     a <= a' /\
     b <= b' /\
     c <= c' /\
     (!x. x IN {t1, t2, t3} ==> &0 < x) /\
     t1 + t2 + t3 < &1 /\
     v =
     ((t1 + t2 + t3) * a) % e1 +
     ((t2 + t3) * sqrt (b pow 2 - a pow 2)) % e2 +
     (t3 * sqrt (c pow 2 - b pow 2)) % e3 /\
  v' = ((t1 + t2 + t3) * a') % e1 +
     ((t2 + t3) * sqrt (b' pow 2 - a' pow 2)) % e2 +
     (t3 * sqrt (c' pow 2 - b' pow 2)) % e3 ==>
  norm v <= norm v' `;;
let TYUNJNA = LEMMA83 ;;

(* le 84. p 53 *)
let LEMMA84 =  ` ! x1 x2 x3 (x4:real^3).
  CARD {x1,x2,x3,x4} = 4 ==>
         let x12 = dist (x1,x2) pow 2 in
         let x13 = dist (x1,x3) pow 2 in
         let x14 = dist (x1,x4) pow 2 in
         let x23 = dist (x2,x3) pow 2 in
         let x24 = dist (x2,x4) pow 2 in
         let x34 = dist (x3,x4) pow 2 in
  &0 <= rho x12 x13 x14 x23 x24 x34  `;;
let SHOGYBS = LEMMA84;;

(* le 85. p53 *)

let VBVYGGT =  ` ! v1 v2 v3 (v4:real^3).
  CARD {v1, v2, v3, v4} = 4 /\ ~coplanar {v1, v2, v3, v4}
         ==> (?!p. p = circumcenter {v1, v2, v3, v4} /\
                   (let x12 = dist (v1,v2) pow 2 in
                    let x13 = dist (v1,v3) pow 2 in
                    let x14 = dist (v1,v4) pow 2 in
                    let x23 = dist (v2,v3) pow 2 in
                    let x24 = dist (v2,v4) pow 2 in
                    let x34 = dist (v3,v4) pow 2 in
                    let chi11 = chi x12 x13 x14 x34 x24 x23 in
                    let chi22 = chi x12 x24 x23 x34 x13 x14 in
                    let chi33 = chi x34 x13 x23 x12 x24 x14 in
                    let chi44 = chi x34 x24 x14 x12 x13 x23 in
                    p =
                    &1 / (&2 * delta x12 x13 x14 x23 x24 x34) %
                    (chi11 % v1 + chi22 % v2 + chi33 % v3 + chi44 % v4))) `;;
let LEMMA85 = VBVYGGT;;

(* le 86. p 54 *)

let GDRQXLG = ` ! v1 v2 v3 (v4:real^3).
  let s = {v1, v2, v3, v4} in
let x12 = dist (v1,v2) pow 2 in
                    let x13 = dist (v1,v3) pow 2 in
                    let x14 = dist (v1,v4) pow 2 in
                    let x23 = dist (v2,v3) pow 2 in
                    let x24 = dist (v2,v4) pow 2 in
                    let x34 = dist (v3,v4) pow 2 in

     CARD s = 4 /\ ~coplanar s
     ==> radV s =
         sqrt (rho x12 x13 x14 x23 x24 x34) /
         (&2 * sqrt (delta x12 x13 x14 x23 x24 x34))` ;;
let LEMMA86 = GDRQXLG;;

(* le 87. p 54 *)

let ZJEWPAP = ` ! v1 v2 v3 (v4:real^3).
  let s = {v1, v2, v3, v4} in CARD s = 4 /\ ~ coplanar s 
  ==> radV {v1,v2,v3}  <= radV s  `;;


(* LE 88, p 55 *)
let LEMMA88 = ` ! v1 v2 v3 (v4:real^3).
         CARD {v1, v2, v3, v4} = 4
         ==> (let s = {v1, v2, v3, v4} in
              let x12 = dist (v1,v2) pow 2 in
              let x13 = dist (v1,v3) pow 2 in
              let x14 = dist (v1,v4) pow 2 in
              let x23 = dist (v2,v3) pow 2 in
              let x24 = dist (v2,v4) pow 2 in
              let x34 = dist (v3,v4) pow 2 in
              orientation s v1 (\t. t < &0) <=>
              chi x12 x13 x14 x23 x24 x34 < &0) `;;
let VSMPQYO = LEMMA88;;

(* LE 89. p 55 *)

let LEMMA89 =  ` ! (v1:real^3) v2 v3 v4.
     let s = {v1, v2, v3, v4} in
     ~coplanar s
     ==> (circumcenter s IN conv0 s <=>
          orientation s v1 (\x. &0 < x) /\
          orientation s v2 (\x. &0 < x) /\
          orientation s v3 (\x. &0 < x) /\
          orientation s v4 (\x. &0 < x))`;;
let PVLJZLA = LEMMA89;;
(* le 90. p 55 *)

let IAALCFJ =  ` ! (v1:real^3) v2 v3 v4.
     let s = {v1, v2, v3, v4} in
     CARD s = 4 /\
     packing s /\
     (!x y. {x, y} SUBSET s ==> d3 x y <= sqrt8) /\
     orientation s v1 (\x. x < &0)
     ==> (!x. x IN {v2, v3, v4} ==> orientation s x (\x. &0 <= x))`;;
let LEMMA90 = IAALCFJ ;;

(* le 91 . p 55 *)

let YOEEQPC = ` ! (v1:real^3) v2 v3 v4.
     let s = {v1, v2, v3, v4} in
     let tt = #2.51 in
     CARD s = 4 /\
     packing s /\
     tt <= d3 v2 v4 /\
     d3 v2 v4 <= sqrt8 /\
     d3 v2 v3 <= tt /\
     d3 v3 v4 <= tt /\
     orientation s v1 (\x. x < &0)
     ==> (!x. x IN {v2, v3, v4} ==> d3 v1 x <= tt)`;;

(* le 92. p 56 *)
let YJTLEGD = ` ! (v1:real^3) v2 v3 v0.
  let s = {v1, v2, v3, v0} in
     let tt = #2.51 in
     CARD s = 4 /\
     packing s /\
     (!x y. {x, y} SUBSET {v1, v2, v3} ==> d3 x y <= tt) /\
     orientation s v0 (\x. x < &0)
     ==> (!x. x IN {v1, v2, v3} ==> &2 <= d3 v0 x /\ d3 v0 x <= tt)`;;

let LEMMA92 = YJTLEGD;;

(* le 93. p 56 *)
let NJBVVWG = `! (v1:real^3) v2 v3 v4 x.
  let s = {v1, v2, v3, v4} in
     CARD s = 4 /\ packing s /\ x IN s /\ radV (s DELETE x) < sqrt (&2)
     ==> orientation s x (\x. &0 < x)`;;

let LEMMA93 = NJBVVWG ;;



(* le 95 . p 57 *)
let GLQHFGH =  ` !v0 v1 v2 (v3:real^3).
  let s = {v0, v1, v2, v3} in
     CARD s = 4 /\
     packing s /\
     (!x y. {x, y} SUBSET {v1, v2, v3} ==> d3 x y <= sqrt8)
     ==> (~(conv {v1, v2, v3} INTER voronoi v0 s = {})
          ==> orientation s v0 (\x. x < &0)) /\
         (~(conv {v1, v2, v3} INTER voronoi_le v0 s = {})
          ==> orientation s v0 (\x. x <= &0))`;;
let LEMMA95 = GLQHFGH;;
(* le 97. p 58 *)
let TCQPONA =  ` ! (v:real^3) v1 v2 v3.
  CARD {v, v1, v2, v3} = 4 /\
     packing {v, v1, v2, v3} /\
     (!a b. {a, b} SUBSET {v1, v2, v3} ==> d3 a b <= #2.51) /\
     ~(conv {v1, v2, v3} INTER voronoi v {v1, v2, v3} = {})
     ==> (!x. x IN {v1, v2, v3} ==> &2 <= d3 x v /\ d3 x v < #2.51)`;;
let LEMMA97 = TCQPONA ;;

(* le 98. p 59 *)
let CEWWWDQ =  ` ! (v:real^3) v1 v2 v3.
     let s = {v, v1, v2, v3} in
     let dd = #2.51 in
     CARD s = 4 /\
     packing s /\
     d3 v1 v3 <= dd /\
     d3 v2 v3 <= dd /\
     d3 v1 v3 <= sqrt8 /\
     ~(conv (s DELETE v) INTER voronoi v s = {})
     ==> (!x. x IN {v1, v2, v3} ==> &2 <= d3 v x /\ d3 v x <= dd)`;;
let LEMMA98 = CEWWWDQ;;

(* le 99. *)
let CKLAKTB =  ` !(w:real^3) v0 v1 v2 x.
     (!x y. {x, y} SUBSET {v0, v1, v2} ==> d3 x y < sqrt (&8)) /\
     CARD {w, v0, v1, v2} = 4 /\ packing {w, v0, v1, v2} /\
     ~(conv {x, w} INTER cone v0 {v1, v2} = {}) /\
     d3 x v0 < d3 x v1 /\
     d3 x v0 < d3 x v2 /\
     d3 x w < d3 x v0
     ==> ~(conv {x, w} INTER conv {v0, v1, v2} = {})`;;
let LEMMA99 = CKLAKTB ;;

(* le 100. p 60 *)

let UMMNOJN = ` ! (x:real^3) w v0 v1 v2.
  CARD {w, v0, v1, v2} = 4 /\
     packing {w, v0, v1, v2} /\
     conv {x, w} INTER cone v0 {v1, v2} = {} /\
     d3 x v0 < d3 x v1 /\
     d3 x v0 < d3 x v2 /\
     d3 x w < d3 x v0 /\
     (!x y. {x, y} SUBSET {v0, v1, v2} ==> d3 x y < sqrt (&8)) /\
     ((!x y. {x, y} SUBSET {v0, v1, v2} ==> d3 x y <= #2.51) \/
      (?x y.
           {x, y} SUBSET {v0, v1, v2} /\
           ~(d3 x y <= #2.51) /\
           (!xx yy.
                {xx, yy} SUBSET {v0, v1, v2} /\ ~(d3 xx yy <= #2.51)
                ==> {xx, yy} = {x, y}))) ==>
  (! x. x IN {v0,v1,v2} ==> d3 w x <= #2.51 )/\
  ~ ( conv {x,w} INTER conv {v0,v1,v2} = {} ) `;;
let LEMMA100 = UMMNOJN;;
(* le 101, not presented in the book *)

(* le 102. p 60 *)
let XBNRPGQ = ` ! v0 v1 w0 (w1:real^3) c0 c1.
  let s = {v0, v1, w0, w1} in
     let F' = {v0, v1, w1} in
     CARD {v0, v1, w0, w1} = 4 /\
     packing {v0, v1, w0, w1} /\
     sqrt (&2) <= radV s /\
     ~coplanar s /\
     radV {v0, v1, w0} < sqrt (&2) /\
     c0 = circumcenter {v0, v1, w0} /\
     d3 v0 c1 = sqrt (&2) /\
     d3 v1 c1 = sqrt (&2) /\
     d3 w0 c1 = sqrt (&2) /\
     c1 IN aff_gt {v0, v1, w0} {w1} /\
     radV F' < sqrt (&2) /\
     (?u v w.
          F' = {u, v, w} /\
          d3 u v <= #2.51 /\
          d3 v w <= #2.51 /\
          d3 u w <= sqrt (&8) /\
          (?xa. xa IN F' /\ d3 xa w0 > #2.51))
     ==> conv {c0, c1} INTER aff {v0, v1, w0} = {}` ;;
let LEMMA102 = XBNRPGQ;;

(* le 103. p 61 *)

let MITDERY = ` ! v0 v w (w':real^3) c.
  let tt = #2.51 in
     let s = {v0, v, w, w'} in
     CARD s = 4 /\
     tt <= d3 v v0 /\
     d3 v v0 <= sqrt8 /\
     tt < d3 w w' /\
     d3 w w' <= sqrt8 /\
     (!x y.
          {x, y} SUBSET s /\ ~({x, y} = {v, v0} \/ {x, y} = {w, w'})
          ==> d3 x y <= tt) /\
     c <= radV s
     ==> rogers v0 w v w' c SUBSET conv s`;;
let LEMMA103 = MITDERY;;

(* le 104. p 61 *)
let BAJSVHC =  ` ! v1 v2 v3 v4 (v5:real^3).
   CARD {v1, v2, v3, v4, v5} = 5 /\
     ~coplanar {v1, v2, v3, v4} /\
     v5 IN aff_ge {v1, v3} {v2, v4} /\
     ~(v5 IN aff {v1, v3})
     ==> aff_ge {v1, v3} {v2, v4} =
         aff_ge {v1, v3} {v2, v5} UNION aff_ge {v1, v3} {v4, v5} /\
         aff_gt {v1, v3} {v2, v5} INTER aff_gt {v1, v3} {v4, v5} = {}`;;
let LEMMA104 = BAJSVHC;;

(* le 105. p 62 *)

let TBMYVLM = ` !v0 v1 v2 v3 (v4:real^3) .
     let s = {v0, v1, v2, v3, v4} in
     CARD s = 5 /\
     (!x. x IN {v1, v2, v3} ==> ~coplanar (s DELETE x)) /\
     v4 IN cone v0 {v1, v2, v3}
     ==> (!x. x IN
              aff_ge {v0, v4} {v1, v2} UNION
              aff_ge {v0, v4} {v1, v3} UNION
              aff_ge {v0, v4} {v2, v3}) /\
         (!x y.
              ~(x = y) /\ {x, y} SUBSET {v1, v2, v3}
              ==> aff_gt {v0, v4} ({v1, v2, v3} DELETE x) INTER
                  aff_gt {v0, v4} ({v1, v2, v3} DELETE y) =
                  {})`;;
let LEMMA105 = TBMYVLM;;
(* le 106. p 63 *)
let TQLZOUG = ` !v0 (v1:real^3) v2 v3 R R0 c3 s.
  s = {v0, v1, v2, v3} /\
     p = circumcenter s /\
     c3 = circumcenter {v0, v1, v2} /\
     R = rogers v0 v1 v2 v3 (radV s) /\
     R0 = rogers0 v0 v1 v2 v3 (radV s) /\
     CARD s = 4 /\
     packing s /\
     (!x. x IN {v1, v2, v3} ==> orientation s x (\x. &0 < x)) /\
     d3 v1 v2 < sqrt (&8) /\
     d3 v2 v3 < sqrt (&8) /\
     d3 v3 v1 < sqrt (&8)
     ==> voronoi v0 s INTER
         aff_ge {v0, p} {v1, c3} INTER
         cone v0 {v1, v2, v3} SUBSET
         R /\
         R0 =
         voronoi v0 s INTER
         aff_gt {v0, p} {v1, c3} INTER
         cone0 v0 {v1, v2, v3}`;;
let LEMMA106 = TQLZOUG;;

(* le 107. p 64 *)

let UREVUCX = ` !v0 v1 v2 (v3:real^3).
       let s = {v0, v1, v2, v3} in
     CARD s = 4 /\
     packing s /\
     (!x. x IN {v1, v2, v3} ==> orientation s x (\x. &0 < x)) /\
     (!x y. {x, y} SUBSET {v1, v2, v3} ==> d3 x y < sqrt (&8))
     ==> UNIONS {rogers0 v0 u v w (radV s) | {u, v, w} = {v1, v2, v3}} SUBSET
         cone v0 {v1, v2, v3} INTER voronoi v0 s /\
         cone v0 {v1, v2, v3} INTER voronoi v0 s SUBSET
         UNIONS {rogers v0 u v w (radV s) | {u, v, w} = {v1, v2, v3}}`;;
let LEMMA107 = UREVUCX;;


(* le 108. p 65 *)
let RKWVONN = ` !v0 v1 v2 (v3:real^3).
      let s = {v0, v1, v2, v3} in
     CARD s = 4 /\
     packing s /\
     (!x. x IN {v1, v2, v3} ==> orientation s x (\x. &0 < x)) /\
     (!x y. {x, y} SUBSET {v1, v2, v3} ==> d3 x y < sqrt (&8))
     ==> voronoi_le v0 s INTER aff_le {v1, v2, v3} {v0} SUBSET
         cone v0 {v1, v2, v3}`;;
let LEMMA108 = RKWVONN;;



let phi_fun = new_definition ` phi_fun  S v u = 
  { x| ? x'. x' IN aff_gt {v} {x} /\ dist (x',u ) = dist (x',v) /\
  ( ! w. w IN S ==> dist (x',v) <= dist (x',w) ) }`;;

(* le 109. p 65 *)
let EMLLARA = ` !u (v:real^3) w.
     (collinear {u, v, w} ==> bis u v INTER bis v w = {}) /\
  ( ~collinear {u, v, w} ==> line ( bis u v INTER bis v w )) `;;

let LEMMA109 = EMLLARA;;

(* le 110. p 66 *)
let DKCSJPZ = `! u v (w:real^3) x p.
  let s = {u, v, w} in
     x IN phi_fun s v u INTER phi_fun s v w /\
     ~(u = w) /\
     plane p /\
     v IN p /\
     bis u v INTER bis v w SUBSET p
     ==> x IN p`;;

let LEMMA110 = DKCSJPZ;;


let phi_fun' = new_definition ` phi_fun' S v u w = 
  {x | FINITE S /\
              (?x''. x IN aff_gt {v} {x'', u} /\
                     dist (x'',u) = dist (x'',v) /\
                     dist (x'',u) = dist (x'',w) /\
                     (!w'. w' IN S ==> dist (x'',v) <= dist (x'',w')))} `;;

(* le 111. p 66 *)
let QXSXGMC = ` ! (u:real^3) v S. convex ( phi_fun S u v ) `;;
let LEMMA111 = QXSXGMC;;

(* le 112 . p 67 *)

let IXOUEVV = ` ! u v (w:real^3) S. 
  FINITE ( S UNION { u, v, w} ) /\ 
  packing ( S UNION { u, v, w} ) /\
  dist (u,v) < sqrt (&8) 
  ==> phi_fun' S v u w SUBSET phi_fun S v u `;;

let LEMMA112 = IXOUEVV;;

(* le 113. p 67 *)
let KMTAMFH = ` ! v0 v1 v2 (v3:real^3).
  let S = {v0, v1, v2, v3} in
     CARD S = 4 /\
     ~coplanar S /\
     d3 v1 v2 < sqrt (&8) /\
     d3 v2 v3 < sqrt (&8) /\
     ~(cone v2 {v1, v3} INTER phi_fun {v0, v1, v3} v2 v0 = {})
     ==> orientation S v0 (\x. x <= &0)`;;
let LEMMA113 = KMTAMFH;;

(* le 114. p 68 *)
let JHOQMMR = ` ! v0 v1 u1 (u2:real^3).
  let s = {v0, v1, u1, u2} in
     let y = d3 v1 v0 in
     let bb = eta_y (&2) #2.51 y in
     CARD s = 4 /\
     packing s /\
     d3 v0 v1 < sqrt (&8) /\
     d3 v0 u1 < sqrt (&8) /\
     d3 v0 u2 < sqrt (&8) /\
     d3 u1 u2 < sqrt (&8) /\
     #2.51 < d3 v1 v0 /\
     ((?a b.
           {a, b} SUBSET {v0, u1, u2} /\
           #2.51 < d3 a b /\
           (!aa bb.
                {aa, bb} SUBSET {v0, u1, u2} /\ ~({aa, bb} = {a, b})
                ==> d3 aa bb <= #2.51)) \/
      (!aa bb.
           {aa, bb} SUBSET {v0, u1, u2} /\ ~({aa, bb} = {a, b})
           ==> d3 aa bb <= #2.51)) /\
     x IN cone v0 {u1, u2} INTER rcone_gt v0 v1 (y / ( &2 * bb ))
     ==> (!x. x IN {d3 v1 u1, d3 v1 u2, d3 v0 u1, d3 v0 u2} ==> x <= #2.51) /\
         radV s < bb`;;
let LEMMA114 = JHOQMMR;;

(* le 115. pa 68 *)
let YFTQMLF = ` ! v0 v1 u1 (u2:real^3).
  let s = {v0, v1, u1, u2} in
     let y = d3 v1 v0 in
     let bb = eta_y (&2) #2.51 y in
     CARD s = 4 /\
     packing s /\
     d3 v0 v1 < sqrt (&8) /\
     d3 v0 u1 < sqrt (&8) /\
     d3 v0 u2 < sqrt (&8) /\
     d3 u1 u2 < sqrt (&8) /\
     #2.51 < d3 v1 v0 /\
     ((?a b.
           {a, b} SUBSET {v0, u1, u2} /\
           #2.51 < d3 a b /\
           (!aa bb.
                {aa, bb} SUBSET {v0, u1, u2} /\ ~({aa, bb} = {a, b})
                ==> d3 aa bb <= #2.51)) \/
      (!aa bb.
           {aa, bb} SUBSET {v0, u1, u2} /\ ~({aa, bb} = {a, b})
           ==> d3 aa bb <= #2.51)) /\
     ~(w' IN affine hull {v0, v1, u1}) /\
     ~(cone v0 {u1, u2} INTER rogers v0 u1 v1 w' bb = {})
     ==> (!x. x IN {d3 v1 u1, d3 v1 u2, d3 v0 u1, d3 v0 u2} ==> x <= #2.51) /\
         radV s < bb`;;
let LEMMA115 = YFTQMLF ;;

(* LE 116 . p 69 *)
let GQMZTHN = ` !(v0:real^3) v1 w u1 u2 b p y.
     let s = {v0, v1, w, u1, u2} in
     CARD s = 5 /\
     packing s /\
     d3 v0 u1 < sqrt (&8) /\
     d3 v0 u2 < sqrt (&8) /\
     d3 u1 u2 < sqrt (&8) /\
     d3 w v0 <= #2.51 /\
     #2.51 < d3 v0 v1 /\
     d3 v0 v1 < sqrt (&8) /\
     d3 v1 w <= #2.51 /\
     ((?a b.
           {a, b} SUBSET {v0, u1, u2} /\
           #2.51 < d3 a b /\
           (!aa bb.
                {aa, bb} SUBSET {v0, u1, u2} /\ ~({aa, bb} = {a, b})
                ==> d3 aa bb <= #2.51)) \/
      (!a b. {a, b} SUBSET {v0, u1, u2} ==> d3 a b <= #2.51)) /\
     y = d3 v0 v1 /\
     b = eta_y (&2) #2.51 y /\
     ~(phi_fun {w, u1, u2} v0 w INTER
       cone v0 {u1, u2} INTER
       rogers0 v0 w v1 p b =
       {}) /\
     ~(p IN affine hull {v0, w, v1})
     ==> d3 w u1 <= #2.51 /\
         d3 w u2 <= #2.51 /\
         ((?u. u IN {u1, u2} /\
               ~(rogers0 v0 w v1 p b INTER cone v0 {w, u} = {})) \/
          d3 u1 u2 < sqrt (&8) /\
          v1 IN cone0 v0 {w, u1, u2} /\
          d3 v1 u1 <= #2.51 /\
          d3 w u2 <= #2.51 \/
          #2.51 < d3 u1 u2 /\
          d3 u1 u2 < sqrt (&8) /\
          w IN aff_ge {v0, v1} {u1, u2})`;;
let LEMMA116 = GQMZTHN;;

(* definition in page 70 *)
let split = new_definition` split v0 v1 w u1 w' p =
  ( radV {v0, v1, w, u1} < eta_y (d3 w v0) (&2) #2.51 /\
         u1 IN aff_ge {v0, v1, w} {p}
         ==> w' IN aff_gt {v0, v1} {w, u1} /\
             radV {v0, v1, w, w'} >= eta_y (d3 v0 v1) (&2) #2.51 /\
             d3 w' v1 <= #2.51 /\
             d3 w' v0 <= #2.51 /\
             #2.77 <= d3 w' w ) `;;


(* le 117. p 68 *)
let KWOHVUP = `! (v0:real^3) v1 w u1 u2 w' b p y.
  let s = {v0, v1, w, u1, u2, w'} in
     let ca = sqrt (&8) in
     let ha = #2.51 in
     CARD s = 6 /\
     packing s /\
     ~(p IN affine hull {v0, w, v1}) /\
     split v0 v1 w u1 w' p /\
     d3 v0 u1 < ca /\
     d3 v0 u2 < ca /\
     d3 u1 u2 < ca /\
     d3 v0 v1 < ca /\
     ha < d3 v0 v1 /\
     d3 w v0 <= ha /\
     d3 w v1 <= ha /\
     ((?a b.
           {a, b} SUBSET {v0, u1, u2} /\
           #2.51 < d3 a b /\
           (!aa bb.
                {aa, bb} SUBSET {v0, u1, u2} /\ ~({aa, bb} = {a, b})
                ==> d3 aa bb <= #2.51)) \/
      (!a b. {a, b} SUBSET {v0, u1, u2} ==> d3 a b <= #2.51)) /\
     y = d3 v1 v0 /\
     b = eta_y (&2) ha y /\
     ~(phi_fun {v1, w, u1, u2} v0 u1 INTER
       cone v0 {u1, u2} INTER
       rogers0 v0 w v1 p b =
       {})
     ==> d3 v0 v1 <= #2.51 /\
         d3 v1 u1 <= #2.51 /\
         d3 v1 w <= #2.51 /\
         u2 IN aff_gt {v0, u1} {v1, w} \/
         d3 v0 u1 <= ha /\
         d3 v1 u1 <= ha /\
         d3 u1 w < ha /\
         rogers0 v0 w v1 p b SUBSET aff_ge {v0, v1, w} {u1} \/
         (!v u. v IN {v0, v1} /\ u IN {u1, u2} ==> d3 u v <= #2.51) /\
         d3 w' v0 <= ha /\
         d3 w' v1 <= ha /\
         w' IN aff_gt {v0, v1} {u1, u2}`;;
let LEMMA117 = KWOHVUP;;


(* le 118. p 72 *)
let UJCUNAS = ` !v0 v1 w u1 u2 w' p F_SET R b y.
     let s = {v0, v1, w, u1, u2, w'} in
     let zzz = #2.51 in
     let set_d = {v0, u1, u2} in
     CARD s = 6 /\
     packing s /\
     ~(p IN affine hull {v0, w, v1}) /\
     split v0 v1 w u1 w' p /\
     split v0 v1 w u2 w' p /\
     d3 v0 u1 < sqrt8 /\
     d3 v0 u2 < sqrt8 /\
     d3 u1 u2 < sqrt8 /\
     d3 w v0 <= zzz /\
     zzz < d3 v0 v1 /\
     d3 v0 v1 < sqrt8 /\
     d3 v1 w <= zzz /\
     ((?a b.
           {a, b} SUBSET set_d /\
           zzz < d3 a b /\
           (!aa bb.
                {aa, bb} SUBSET set_d /\ ~({aa, bb} = {a, b})
                ==> d3 aa bb <= zzz)) \/
      (!a b. {a, b} SUBSET set_d ==> d3 a b <= zzz)) /\
     y = d3 v1 v0 /\
     b = eta_y (&2) zzz y /\
     F_SET = cone v0 {u1, u2} /\
     R = rogers0 v0 w v1 p b
     ==> d3 w u1 <= zzz /\
         d3 w u2 <= zzz /\
         (!u. u = u1 \/ u = u2 ==> ~(R INTER cone v0 {w, u} = {})) \/
         d3 w u1 <= zzz /\
         d3 w u2 <= zzz /\
         d3 u1 u2 < sqrt8 /\
         v1 IN cone0 v0 {w, u1, u2} /\
         d3 v1 u1 <= zzz /\
         d3 v1 u2 <= zzz \/
         d3 w u1 <= zzz /\
         d3 w u2 <= zzz /\
         zzz < d3 u1 u2 /\
         d3 u1 u2 < sqrt8 /\
         w IN aff_ge {v0, v1} {u1, u2} \/
         (?u u'.
              {u, u'} = {u1, u2} /\
              d3 v0 u <= zzz /\
              d3 v1 u <= zzz /\
              d3 u w <= zzz /\
              u' IN aff_gt {v0, u} {v1, w}) \/
         (?u. u IN {u1, u2} /\
              d3 v0 u <= zzz /\
              d3 v1 u <= zzz /\
              d3 u w <= zzz /\
              R SUBSET aff_ge {v0, v1, w} {u}) \/
         (!v u''. v IN {v0, v1} /\ u'' IN {u1, u2} ==> d3 v u'' <= zzz) /\
         d3 w' v0 <= zzz /\
         d3 w' v1 <= zzz /\
         w' IN aff_gt {v0, v1} {u1, u2}`;;
let LEMMA118 = UJCUNAS;;
(* le 119 . p 73 *)

let DVLHHMF = ` ! R' R0 b v0 v w w' u.
     let s = {v0, v, w, w', u} in
     let zz = #2.51 in
     CARD s = 5 /\
     packing s /\
     zz < d3 v0 v /\
     d3 v0 v < sqrt8 /\
     zz < d3 w w' /\
     (!v' w''. v' IN {v0, v} /\ w'' IN {w, w', u} ==> d3 v' w'' <= zz) /\
     b = eta_y (&2) zz (d3 v v0) /\
     b <= radV {v0, v, w, w'} /\
     ~(conv {w, u} INTER aff_ge {v0, v} {w'} = {}) /\
     R0 = rogers0 v0 w v u b /\
     R' = R0 INTER voronoi v0 {w, u} INTER phi_fun {v0, w, u} v0 u /\
     ~(R' = {})
     ==> (!x. x IN R' ==> ~(conv {x, u} INTER conv {v0, v, w'} = {})) /\
         d3 u w' <= zz`;;

let LEMMA119 = DVLHHMF;;

(* le 120 . 74 *)
let UIXOFDB = ` !v0 v1 v1' w1 w2 b b'.
     let s = {v0, v1, v1', w1, w2} in
     let zz = #2.51 in
     CARD s = 5 /\
     packing s /\
     zz <= d3 v0 v1 /\
     d3 v0 v1 < sqrt8 /\
     zz <= d3 v0 v1' /\
     d3 v0 v1' < sqrt8 /\
     (!v w. v IN {v0, v1} /\ w IN {w1, w2} ==> d3 v w <= zz) /\
     ~coplanar {v0, v1, w1, w2} /\
     b' = d3 v0 v1' / (&2 * eta_y (d3 v0 v1') (&2) zz) /\
     b = d3 v0 v1 / (&2 * eta_y (d3 v0 v1) (&2) zz)
     ==> rogers0 v0 w1 v1 w2 b INTER rcone_ge v0 v1' b' = {}`;;
let LEMMA120 = UIXOFDB;;

(* le 121. p74 *)
let MJNUTQH = ` !v0 v1 v2 w1 w2 p1 p2.
     let s = {v0, v1, v2, w1, w2} in
     let zz = #2.51 in
     CARD s = 5 /\
     packing s /\
     zz <= d3 v0 v1 /\
     d3 v0 v1 < sqrt8 /\
     zz <= d3 v0 v2 /\
     d3 v0 v2 < sqrt8 /\
     (!w. w IN {w1, w2} ==> d3 v0 w <= zz) /\
     d3 v1 w1 <= zz /\
     d3 v2 w2 <= zz /\
     ~coplanar {v0, v1, w1, p1} /\
     ~coplanar {v0, v2, w2, p2} /\
     b1 = eta_y (d3 v0 v1) (&2) zz /\
     b2 = eta_y (d3 v0 v2) (&2) zz /\
     ~(rogers v0 w1 v1 p1 b1 INTER rogers v0 w2 v2 p2 b2 = {})
     ==> d3 v1 w2 <= zz /\
         (d3 w1 w2 <= zz /\
          (~(rogers0 v0 w2 v2 p2 b2 INTER aff_ge {v0} {v1, w1} = {}) \/
           aff_ge {v0, v1, w1} {w2} = aff_ge {v0, v1, w1} {p1}) \/
          zz < d3 w1 w2 /\
          ~(phi_fun {v0, v1, w1, w2} v0 w2 INTER rogers v0 w1 v1 p1 b1 = {}) /\
          radV {v0, v1, w1, w2} < b1 /\
          aff_ge {v0, v1, w1} {w2} = aff_ge {v0, v1, w1} {p1}) \/
         d3 v2 w1 <= zz /\
         (d3 w1 w2 <= zz /\
          (~(rogers0 v0 w1 v1 p1 b1 INTER aff_ge {v0} {v2, w2} = {}) \/
           aff_ge {v0, v2, w2} {w1} = aff_ge {v0, v2, w2} {p2}) \/
          zz < d3 w1 w2 /\
          ~(phi_fun {v0, v1, w1, w2} v0 w1 INTER rogers v0 w2 v2 p2 b2 = {}) /\
          radV {v0, v2, w1, w2} < b2 /\
          aff_ge {v0, v2, w2} {w2} = aff_ge {v0, v2, w2} {p2})`;;

let LEMMA121 = MJNUTQH;;

(* le 122 . 75 *)

let MPJEZGP = ` !t0 t1 t2 t3 t4 v0 v1 v2 v3 v4.
     CARD {v0, v1, v2, v3, v4} = 5 /\
     t0 % v0 + t1 % v1 + t2 % v2 + t3 % v3 + t4 % v4 = vec 0 /\
     t4 < &0 /\
     t0 + t1 + t2 + t3 + t4 = &0
     ==> ((!t. t IN {t1, t2, t3} ==> &0 <= t) <=> v4 IN cone v0 {v1, v2, v3}) /\
         (&0 <= t1 /\ &0 <= t3 /\ t2 <= &0 <=>
          ~(cone v0 {v2, v4} INTER cone v0 {v1, v3} = {})) /\
         (&0 <= t1 /\ &0 <= t2 /\ t3 <= &0 <=>
          ~(cone v0 {v3, v4} INTER cone v0 {v1, v2} = {})) /\
         (&0 <= t1 /\ &0 <= t2 /\ t3 <= &0 <=>
          ~(cone v0 {v1, v4} INTER cone v0 {v2, v3} = {})) /\
         (&0 <= t1 /\ t2 <= &0 /\ t3 <= &0 <=> v1 IN cone v0 {v2, v3, v4}) /\
         (&0 <= t2 /\ t1 <= &0 /\ t3 <= &0 <=> v2 IN cone v0 {v1, v3, v4}) /\
         (&0 <= t3 /\ t1 <= &0 /\ t2 <= &0 <=> v3 IN cone v0 {v2, v1, v4}) /\
         (&0 <= t0 /\ t1 <= &0 /\ t2 <= &0 /\ t3 <= &0 <=>
          v0 IN conv {v1, v2, v3, v4}) /\
         ~(t0 < &0 /\ (!t. t IN {t1, t2, t3} ==> t <= &0))`;;

let LEMMA122 = MPJEZGP;;


(* le 123 . p 76 *)
let GFVQUPP = ` !x1 x2 x3 x4.
     let x12 = dist (x1,x2) pow 2 in
     let x13 = dist (x1,x3) pow 2 in
     let x14 = dist (x1,x4) pow 2 in
     let x23 = dist (x2,x3) pow 2 in
     let x24 = dist (x2,x4) pow 2 in
     let x34 = dist (x3,x4) pow 2 in
     (!x. x IN {x12, x13, x14, x34, x24} ==> x <= #2.517 pow 2) /\
     #2.65 pow 2 <= x23
     ==> delta_x23 x12 x13 x14 x34 x24 x23 > &0`;;

let LEMMA123 = GFVQUPP;;


(* le 124 . p 76 *)
let TFKALQL = ` !v1 v2 v3 v4.
     let s = {v1, v2, v3, v4} in
     let x12 = dist (v1,v2) pow 2 in
     let x13 = dist (v1,v3) pow 2 in
     let x14 = dist (v1,v4) pow 2 in
     let x23 = dist (v2,v3) pow 2 in
     let x24 = dist (v2,v4) pow 2 in
     let x34 = dist (v3,v4) pow 2 in
     CARD s = 4 /\
     packing s /\
     x12 <= #2.3 pow 2 /\
     (!x. x IN {x13, x14, x34, x24} ==> x <= #2.517 pow 2) /\
     #2.51 pow 2 <= x23
     ==> delta_x23 x12 x13 x24 x34 x24 x23 > &0`;;

let LEMMA124 = TFKALQL;;

(* le 125 . p 77 *)

let AAGNQFL = `!v0 v1 v2 v3 v4.
     let s = {v0, v1, v2, v3, v4} in
     CARD s = 5 /\
     packing s /\
     (!u v.
          {u, v} SUBSET s /\ ~({u, v} = {v1, v3} \/ {u, v} = {v2, v4})
          ==> d3 u v <= #2.51) /\
     v1 IN cone v0 {v2, v3, v4}
     ==> d3 v1 v3 < #2.65`;;

let LEMMA125 = AAGNQFL;;

(* le 126 . p 77 *)
let QOKQFRE = ` !v0 v1 v2 v3 v4.
     let s = {v0, v1, v2, v3, v4} in
     CARD s = 5 /\
     packing s /\
     (!u v.
          {u, v} SUBSET s /\ ~({u, v} = {v1, v3} \/ {u, v} = {v2, v4})
          ==> d3 u v <= #2.51) /\
     d3 v0 v1 <= #2.3 /\
     v1 IN cone v0 {v2, v3, v4}
     ==> d3 v1 v3 < #2.51`;;

let LEMMA126 = QOKQFRE ;;

let quadp = new_definition ` quadp v0 v1 v2 v3 v4 =
  ~ (cone0 v0 {v1,v3} INTER cone0 v0 {v2,v4} = {} ) `;;

let quadc0 = new_definition ` quadc0 v0 v1 v2 v3 v4 =
         (@h. quadp v0 v1 v2 v3 v4 /\
              h =
              cone0 v0 {v1, v2, v3} INTER
              cone0 v0 {v1, v3} INTER
              cone0 v0 {v1, v3, v4}) `;;
(* le 127. p 78 *)
let DFLUMBW = `!v0 v1 v2 v3 v4.
     CARD {v0, v1, v2, v3, v4} = 5 /\ quadp v0 v1 v2 v3 v4
     ==> quadc0 v0 v1 v2 v3 v4 = quadc0 v0 v2 v3 v4 v1`;;

let LEMMA127 = DFLUMBW;;

(* le 128 . p 78 *)

let HTYDGWI = ` !v0 v1 v2 v3 v4.
     CARD {v0, v1, v2, v3, v4} = 5 /\
     packing {v0, v1, v2, v3, v4} /\
     (!v. v IN {v1, v2, v3, v4} ==> d3 v0 v <= #2.51) /\
     quadp v0 v1 v2 v3 v4 /\
     d3 v1 v3 < sqrt8 /\
     d3 v2 v4 < sqrt8
     ==> d3 v1 v2 <= #2.51 /\
         d3 v2 v3 <= #2.51 /\
         d3 v3 v4 <= #2.51 /\
         d3 v1 v4 <= #2.51`;;
let LEMMA128 = HTYDGWI;;
(* le 129. p 79 *)
let XLHACRX = ` !v0 v1 v2 v3 v4 w.
     CARD {v0, v1, v2, v3, v4, w} = 6 /\
     packing {v0, v1, v2, v3, v4, w} /\
     (!x. x IN {v1, v2, v3, v4} ==> d3 v0 x <= #2.51) /\
     quadp v0 v1 v2 v3 v4 /\
     d3 v1 v3 < sqrt8 /\
     d3 v2 v4 < sqrt8 /\
     w IN quadc0 v0 v1 v2 v3 v4 /\
     d3 w v0 < sqrt8
     ==> (!x. x IN {v1, v2, v3, v4} ==> d3 w x <= #2.51)`;;
let LEMMA129 = XLHACRX;;

let c_def38 = new_definition ` c_def38 S v' v1 v2 v3 v4 h1 h2 h3 h4 l k
  = ( CARD ({v', v1, v2, v3, v4} UNION S) = 5 + CARD S /\
 packing ({v', v1, v2, v3, v4} UNION S) /\
 quadp v' v1 v2 v3 v4 /\
 S SUBSET quadc0 v' v1 v2 v3 v4 /\
 (!vi. vi IN {v1, v2, v3, v4} ==> &2 <= d3 vi v' /\ d3 vi v' <= k) /\
 d3 v1 v2 <= k /\
 d3 v2 v3 <= k /\
 d3 v3 v4 <= k /\
 d3 v4 v1 <= k /\
 &2 <= d3 v1 v2 /\
 &2 <= d3 v2 v3 /\
 &2 <= d3 v3 v4 /\
 &2 <= d3 v4 v1 /\
 &2 <= d3 v1 v3 /\
 &2 <= d3 v2 v4 /\
 (!v. v IN S
      ==> &2 <= d3 v v' /\
          d3 v v' <= l /\
          h1 <= d3 v v1 /\
          h2 <= d3 v v2 /\
          h3 <= d3 v v3 /\
          h4 <= d3 v v4) )`;;


g ` ! h1 h2 h3 h4 l k. 
  (! x. x IN {h1,h2,h3,h4,l } ==> &2 <= x /\ x <= sqrt8 ) /\
  #2.51 <= k /\ k <= #2.517 /\
  c_def38 S v' v1 v2 v3 v4 h1 h2 h3 h4 l k /\
  h `;;
(* le 131 . p 80 *)
let GMEPVPW = ` ! k. #2.51 <= k /\
 k <= #2.517 /\
 ~(?v0 v1 v2 v3 v4 (w1:real^3) w2.
       CARD {v0, v1, v2, v3, v4, w1, w2} = 7 /\
       packing {v0, v1, v2, v3, v4, w1, w2} /\
       c_def38 {w1, w2} v0 v1 v2 v3 v4 (&2) (&2) (&2) (&2) k k /\
       (!vv. vv IN {v1, v2, v3, v4} ==> d3 v0 vv <= k) /\
       d3 v1 v2 <= k /\
       d3 v2 v3 <= k /\
       d3 v3 v4 <= k /\
       d3 v4 v1 <= k)`;;
let LEMMA131 = GMEPVPW;;



(* le 132 . p 80 *)
let VTIVSIF = ` !v0 (v1:real^3) v2 v3 v4 v5.
     CARD {v0, v1, v2, v3, v4, v5} = 6 /\
     packing {v0, v1, v2, v3, v4, v5} /\
     quadp v0 v1 v2 v3 v4 /\
     v5 IN quadc0 v0 v1 v2 v3 v4 /\
     (!vv. vv IN {v1, v2, v3, v4} ==> d3 v0 vv <= #2.51) /\
     d3 v1 v2 <= #2.51 /\
     d3 v2 v3 <= #2.51 /\
     d3 v3 v4 <= #2.51 /\
     d3 v4 v1 <= #2.51 /\
     (!xx. xx IN {v2, v3, v4} ==> #2.51 <= d3 v5 xx)
     ==> #2.51 < d3 v0 v5`;;

let LEMMA132 = VTIVSIF;;

(* le 133 . p 81 *)
let TPXUMUZ = ` !v0 v1 v2 v3 v4 v5.
     CARD {v0, v1, v2, v3, v4, v5} = 6 /\
     packing {v0, v1, v2, v3, v4, v5} /\
     quadp v0 v1 v2 v3 v4 /\
     v5 IN quadc0 v0 v1 v2 v3 v4 /\
     (!u v.
          {u, v} SUBSET {v0, v1, v2, v3, v4, v5} /\
          ~({u, v} = {v1, v3} \/
            {u, v} = {v2, v4} \/
            {u, v} = {v5, v4} \/
            {u, v} = {v5, v3})
          ==> d3 u v <= #2.51) /\
     #2.51 <= d3 v5 v3 /\
     #2.51 <= d3 v5 v4
     ==> (d3 v5 v4 <= sqrt8 \/ d3 v5 v3 <= sqrt8) /\
         (d3 v5 v4 <= #3.02 /\ d3 v5 v3 <= #3.02) /\
         #2.3 <= d3 v5 v0 `;;

let LEMMA133 = TPXUMUZ;;


(* le 134. p 82 *)

let YWPHYZU = ` !v0 v1 v2 v3 v4 v5.
     CARD {v0, v1, v2, v3, v4, v5} = 6 /\
     packing {v0, v1, v2, v3, v4, v5} /\
     d3 v0 v5 < sqrt8 /\
     (!u v. u IN {v0, v5} /\ v IN {v1, v2} ==> d3 u v <= #2.51) /\
     ~(conv {v3, v4} INTER conv {v0, v1, v5} = {}) /\
     ~(conv {v3, v4} INTER conv {v0, v2, v5} = {})
     ==> sqrt8 < d3 v3 v4`;;

let LEMMA134 = YWPHYZU;;

(* le 135 . p 82 *)

let PYURAKS = ` !v0 w w' v1 v2 v3.
     CARD {v0, w, w', v1, v2, v3} = 6 /\
     packing {v0, w, w', v1, v2, v3} /\
     d3 v1 v2 < sqrt8 /\
     d3 v1 v3 <= #2.51 /\
     d3 v2 v3 <= #2.51 /\
     {w, w'} SUBSET cone v0 {v1, v2, v3} /\
     d3 v0 w <= sqrt8
     ==> sqrt8 < d3 v0 w'`;;

let LEMMA135 = PYURAKS;;



let small = new_definition ` small s = 
 ( CARD s = 3 /\
         packing s /\
         (!x y. {(x:real^3) , y} SUBSET s ==> d3 x y < sqrt8) /\
         (!x y z.
              {x, y, z} = s /\ #2.51 < d3 x y /\ #2.51 < d3 y z
              ==> radV s < sqrt (&2)) ) `;;
(* le 136 . p *)

let BLATMSI = ` !v1 v2 v3 v4 w w' s.
  CARD {v1, v2, v3, v4, w, w'} = 6 /\
     packing {v1, v2, v3, v4, w, w'} /\
     s = {v1, v2, v3, v4} /\
     (!v. v IN s ==> small (s DELETE v)) /\
     ~(conv {w, w'} INTER conv s = {}) /\
     d3 w w' < sqrt8
     ==> ~(conv {w, w'} INTER conv0 s = {})`;;

let LEMMA136 = BLATMSI;;

(* le 137. p 84 *)

let MLTDJJV = ` !v1 v2 v3 v0 w w' s.
     CARD {v1, v2, v3, v0, w, w'} = 6 /\
     packing {v1, v2, v3, v0, w, w'} /\
     s = {v1, v2, v3, v0} /\
     d3 w w' < sqrt8 /\
     (!v. v IN s ==> small (s DELETE v)) /\
     (!x y. {x, y} SUBSET {v1, v2, v3} ==> d3 x y <= #2.51)
     ==> conv {w, w'} INTER conv s = {} `;;

let LEMMA137 = MLTDJJV;;


(* le 138 . p 85 *)
let ZDKDXFM = ` !v0 v1 v2 v3 w w'.
     CARD {v0, v1, v2, v3, w, w'} = 6 /\
     packing {v0, v1, v2, v3, w, w'} /\
     d3 w w' < sqrt8 /\
     (!v. v IN {v0, v1, v2, v3} ==> small ({v0, v1, v2, v3} DELETE v)) /\
     #2.51 < d3 v1 v3 /\
     #2.51 < d3 v2 v0 /\
     ~(conv {w, w'} INTER conv0 {v0, v1, v2, v3} = {})
     ==> #2.51 < d3 w w' /\
         (!u vi. u IN {w, w'} /\ vi IN {v0, v1, v2, v3} ==> d3 u vi <= #2.51)`;;

(* le 139 . 85 *)
let XHMHKIZ = ` !v0 v1 v2 v3 w.
     CARD {v0, v1, v2, v3, w} = 5 /\
     packing {v0, v1, v2, v3, w} /\
     (!x y. {x, y} SUBSET {v1, v2, v3} ==> d3 x y <= sqrt8) /\
     ~(conv {v0, w} INTER conv0 {v0, v1, v2, v3} = {})
     ==> ~(conv {v0, w} INTER conv0 {v1, v2, v3} = {})`;;

(* le 140 . p 86 *)
let TIMIDQM = ` !v0 v1 v2 w0 w1 w2 x.
     CARD {v0, v1, v2, w0, w1, w2} = 6 /\
     packing {v0, v1, v2, w0, w1, w2} /\
     small {v0, v1, v2} /\
     small {w0, w1, w2} /\
     x IN conv {v0, v1, v2} INTER conv {w0, w1, w2}
     ==> (?v0' v1' v2' w0' w1' w2'.
              {v0, v1, v2} = {v0', v1', v2'} /\
              {w0, w1, w2} = {w0', w1', w2'} /\
              d3 w0' w1' <= #2.51 /\
              d3 w1' w2' <= #2.51 /\
              #2.51 < d3 w0' w2' /\
              d3 v0' v2' < sqrt8 /\
              d3 v0' v1' <= #2.51 /\
              d3 v1' v2' <= #2.51 /\
              #2.51 < d3 v0' v2' /\
              d3 v0' v2' < sqrt8 /\
              ~(conv {v0', v2'} INTER {w0, w1, w2} = {}) /\
              ~(conv {w0', w2'} INTER {v0, v1, v2} = {}))`;;

let LEMMA140 = TIMIDQM;;

(* le 141 . p 87 *)


let KGTJGLX = ` !u0 v1 v2 w1 w2.
     CARD {u0, v1, v2, w1, w2} = 5 /\
     packing {u0, v1, v2, w1, w2} /\
     small {u0, v1, v2} /\
     small {u0, w1, w2} /\
     ~(conv0 {u0, v1, v2} INTER conv0 {u0, w1, w2} = {})
     ==> ~(conv {v1, v2} INTER conv {u0, w1, w2} = {} /\
           conv {w1, w2} INTER conv {u0, v1, v2} = {})`;;

let LEMMA141 = KGTJGLX;;

(* le 142 . p 87 *)

let RTBONNT = ` !v1 v2 v3 v4 w1 w2 w3.
     CARD {v1, v2, v3, v4, w1, w2, w3} = 7 /\
     packing {v1, v2, v3, v4, w1, w2, w3} /\
     Sv = {v1, v2, v3, v4} /\
     Sw = {w1, w2, w3} /\
     small Sw /\
     (!v. v IN Sv ==> small (Sv DELETE v))
     ==> conv Sv INTER conv Sw = {}`;;

let LEMMA142 = RTBONNT ;;

(* le 143 . p88 *)


let JMHCAKG = ` !v1 v2 v3 v4 w1 w2 w3.
     let sv = {v1, v2, v3, v4} in
     let sw = {w1, w2, w3} in
     let s = {v1, v2, v3, v4, w1, w2} in
     v1 = w1 /\
     CARD s = 6 /\
     packing s /\
     small sw /\
     (!v. v IN sv ==> small (sv DELETE v)) /\
     (?vv. ~(vv = v1) /\ vv IN conv sv INTER conv sw)
     ==> (?ww1 ww2 ww3 vv1 vv2 vv3 vv4.
              {ww1, ww2, ww3} = {w1, w2, w3} /\
              {vv1, vv2, vv3, vv4} = {v1, v2, v3, v4} /\
              ~(conv {ww1, ww3} INTER conv {vv2, vv3, vv4} = {}) /\
              ~(conv {vv2, vv4} INTER conv {ww1, ww2, ww3} = {}) /\
              #2.51 < d3 ww1 ww3 /\
              #2.51 < d3 vv2 vv4 /\
              d3 ww1 vv4 <= #2.51 /\
              d3 vv4 ww3 <= #2.51 /\
              d3 ww3 vv2 <= #2.51 /\
              d3 vv2 ww1 <= #2.51) \/
         (?ww1 ww2 ww3 vv1 vv2 vv3 vv4.
              {ww1, ww2, ww3} = {w1, w2, w3} /\
              {vv1, vv2, vv3, vv4} = {v1, v2, v3, v4} /\
              (?vi vj.
                   ~(vi = vj) /\
                   {vi, vj} SUBSET sv /\
                   ~(conv {ww2, ww3} INTER conv (sv DELETE vi) = {} \/
                     conv {ww2, ww3} INTER conv (sv DELETE vj) = {})) /\
              #2.51 < d3 vv2 vv3 /\
              #2.51 < d3 vv1 vv3 /\
              (!wi vj. wi IN {ww2, ww3} /\ vj IN sv ==> d3 wi vj <= #2.51))`;;

let LEMMA143 = JMHCAKG ;;


(* le 144. p 89 *)
let UGQMJJA = `!v1 v2 v3 v4 w3 w1 w2.
     CARD {v1, v2, v3, v4, w1} = 5 /\
     packing {v1, v2, v3, v4, w1} /\
     w1 = v1 /\
     w2 = v2 /\
     sv = {v1, v2, v3, v4} /\
     sw = {w1, w2, w3} /\
     small sw /\
     (!v. v IN sv ==> small (sv DELETE v)) /\
     (?x. ~(x IN conv {v1, v2}) /\ x IN conv sv INTER conv sw)
     ==> (?ww1 vv2.
              {ww1, vv2} = {w1, v2} /\
              ~(conv {ww1, w3} INTER conv {vv2, v3, v4} = {}) /\
              #2.51 < d3 ww1 w3) \/
         ~(conv {v3, v4} INTER conv sw = {}) /\ #2.51 < d3 v3 v4`;;

let LEMMA144 = UGQMJJA;;


(* le 145. p 89 *)
let ZILQMDQ = ` !v1 v2 v3 v4 w1 w2 w3 w4.
     let sv = {v1, v2, v3, v4} in
     let sw = {w1, w2, w3, w4} in
     CARD {v1, v2, v3, v4, w1, w2, w3, w4} = 8 /\
     packing {v1, v2, v3, v4, w1, w2, w3, w4} /\
     (!v. v IN sv ==> small (sv DELETE v)) /\
     (!w. w IN sw ==> small (sw DELETE w))
     ==> conv sv INTER conv sw = {}`;;

let LEMMA145 = ZILQMDQ ;;


(* le 146. p 90 *)

let AQKANYN = ` !v1 v2 v3 v4 w1 w2 w3 w4.
     let sv = {v1, v2, v3, v4} in
     let sw = {w1, w2, w3, w4} in
     CARD {v1, v2, v3, v4, w2, w3, w4} = 7 /\
     packing {v1, v2, v3, v4, w2, w3, w4} /\
     w1 = v1 /\
     (!v. v IN sv ==> small (sv DELETE v)) /\
     (!w. w IN sw ==> small (sw DELETE w))
     ==> conv sv INTER conv sw = {v1}`;;


let LEMMA146 = AQKANYN;;