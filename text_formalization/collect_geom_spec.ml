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
(* How can I write the definition of R(xij)? Do I have to compute the determinant *)
let eta_v = new_definition ` eta_v v1 v2 (v3: real^N) =
        let e1 = dist (v2, v3) in
  	  let e2 = dist (v1, v3) in
  	  let e3 = dist (v2, v1) in
  	  e1 * e2 * e3 / sqrt ( ups_x (e1 pow 2 ) ( e2 pow 2) ( e3 pow 2 ) ) `;;

(* Lemma 2, page 6 *)
let RHUFIIB = new_axiom ` !x12 x13 x14 x23 x24 x34.
         rho x12 x13 x14 x23 x24 x34 * ups_x x34 x24 x23 =
         chi x12 x13 x14 x23 x24 x34 pow 2 +
         &4 * delta x12 x13 x14 x23 x24 x34 * x34 * x24 * x23 `;;
(* Lemma 3, *)
let NUHSVLM = new_axiom ` !x1 x2 x3 x4 (x5 :real^3). 
         let x12 = dist (x1,x2) in
         let x13 = dist (x1,x3) in
         let x14 = dist (x1,x4) in
         let x23 = dist (x2,x3) in
         let x24 = dist (x2,x4) in
         let x34 = dist (x3,x4) in
         let x15 = dist (x1,x5) in
         let x25 = dist (x2,x5) in
         let x35 = dist (x3,x5) in
         let x45 = dist (x4,x5) in
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
let BXVMKNF = new_axiom ` ! u v:real ^3. ~( u=v) ==> plane ( bis u v ) `;;
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
(* le 9. p 13 *)
let FHFMKIY = new_axiom ` ! (v1: real^3) v2 v3 x12 x13 x23.
         x12 = dist (v1,v2) pow 2 /\
         x13 = dist (v1,v3) pow 2 /\
         x23 = dist (v2,v3) pow 2
         ==> (collinear {v1, v2, v3} <=> ups_x x12 x13 x23 = &0)`;;
(* le 10. p 14 *)
let ZPGPXNN = new_axiom `! v1 v2 (v:real^3).
         dist (v1,v2) < dist (v,v1) + dist (v,v2) ==> ~(v IN conv {v1, v2})`;;
(* le 11. p14 *)
let FAFKVLR = new_axiom ` ? t1 t2 t3. ! v1 v2 v3 (v:real^3) p.
   plane p /\ {v1, v2, v3} SUBSET p /\
   ~collinear {v1, v2, v3} /\ v IN p
             ==> v = t1 v1 v2 v3 v % v1 + t2 v1 v2 v3 v % v2 + t3 v1 v2 v3 v % v3 /\
                 t1 v1 v2 v3 v + t2 v1 v2 v3 v + t3 v1 v2 v3 v = &1 /\
                 (!ta tb tc. v = ta % v1 + tb % v2 + tc % v3
                    ==> ta = t1 v1 v2 v3 v /\
                        tb = t2 v1 v2 v3 v /\
                        tc = t3 v1 v2 v3 v )`;;

let COEFS = new_specification [" coef1"; "coef2"; "coef3"] FAFKVLR;;
let plane_3p = new_definition `plane_3p (a:real^3) b c =
         {x | ~collinear {a, b, c} /\
              (?ta tb tc. ta + tb + tc = &1 /\ x = ta % a + tb % b + tc % c)}`;;
(* le 12. p 15 *)
let CNXIFFC = new_axiom ` ! v1 v2 v3 v. ~ collinear {v1,v2,v3} /\ v IN plane_3p v1 v2 v3 
  ==> ( &0 < coef1 v1 v2 v3 v <=> v1 IN aff_gt {v2,v3} {v} ) /\
  ( &0 = coef1 v1 v2 v3 v <=> v IN aff {v2,v3} ) /\
  ( coef1 v1 v2 v3 v < &0 <=> v1 IN aff_lt {v2,v3} {v} )`;;
(* le 13. p 15 *)
let MYOQCBS = new_axiom ` ! v1 v2 v3 (v:real^3). ~ collinear {v1,v2,v3} ==>
   ( v IN conv {v1,v2,v3} <=> &0 <= coef1 v1 v2 v3 v /\ &0 <= coef2 v1 v2 v3 v /\
   &0 <= coef3 v1 v2 v3 v ) /\ 
   ( v IN conv0 {v1,v2,v3} <=> &0 < coef1 v1 v2 v3 v /\ &0 < coef2 v1 v2 v3 v /\
   &0 < coef3 v1 v2 v3 v )`;;
(* le 14. p 15 *)
let TXDIACY = new_axiom `! a b c d (v0: real^3) r.
         &0 < r /\ {a, b, c, d} SUBSET normball v0 r
         ==> conv {a, b, c, d} SUBSET normball v0 r `;;
(* le 15. p 16 *)
let POLFLZY = new_axiom ` ! x1 x2 x3 (x4: real^3).  
         let x12 = dist (x1,x2) in
         let x13 = dist (x1,x3) in
         let x14 = dist (x1,x4) in
         let x23 = dist (x2,x3) in
         let x24 = dist (x2,x4) in
         let x34 = dist (x3,x4) in
         coplane {x1, x2, x3, x4} <=> delta x12 x13 x14 x23 x24 x34 = &0 `;;
let circumradius = new_definition ` circumradius s = (@r. ? x. x IN s /\
  r = dist( x , circumcenter s ) )`;;
(* =============== *)
(* ====  *   ===== *)
(* ==   * *     == *)
(*       *         *)
(*    3 rd time    *)
(* =============== *)
(* le 17, p 17 *)
let CDEUSDF = new_axiom`! va vb (vc:real^3) a b c. a = d3 vb vc /\
         b = d3 va vc /\
         c = d3 va vb /\
         ~collinear {va, vb, vc}
         ==> (let al_a =
                  (a pow 2 * (b pow 2 + c pow 2 - a pow 2)) /
                  (&2 * ups_x (a pow 2) (b pow 2) (c pow 2)) in
              let al_b =
                  (b pow 2 * (a pow 2 + c pow 2 - b pow 2)) /
                  (&2 * ups_x (a pow 2) (b pow 2) (c pow 2)) in
              let al_c =
                  (c pow 2 * (a pow 2 + b pow 2 - c pow 2)) /
                  (&2 * ups_x (a pow 2) (b pow 2) (c pow 2)) in
              al_a % va + al_b % vb + al_c % vc = circumcenter {va, vb, vc}) 
              /\ radV {va, vb, vc} = eta_y a b c `;;
(* le 18, p 17 *)
let WSMRDKN = new_axiom `! x y z: real^3 p.
  d3 x z pow 2 < d3 x y pow 2 + d3 y z pow 2 /\
         p = circumcenter {x, y, z}
         ==> conv0 {y, p} INTER aff {x, z} = {}`;;
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

let max_real3 = new_definition ` max_real3 x y z = max_real (max_real x y ) z `;;
let ups_x_pow2 = new_definition` ups_x_pow2 x y z = ups_x ( x*x ) ( y * y) ( z * z)`;;

(* le 24 , p 19 *)
let HVXIKHW = new_axiom ` ! x y z. &0 <= x /\ &0 <= y /\ &0 <= z /\ 
          &0 < ups_x_pow2 x y z ==> max_real3 x y z / &2 <= eta_y x y z `;;
(* le 25. p 19 *)
let HMWTCNS = new_axiom ` ! a b (c:real^3). 
            CARD {a, b, c} = 3 /\ packing {a, b, c}
         ==> &2 / sqrt (&3) <= circumradius {a, b, c}`;;
(* le 26 . p 20 *)
let POXDVXO = new_axiom ` ! v1 v2 (v3:real^3) p.
         !v1 v2 v3 p.
         CARD {v1, v2, v3} = 3 /\
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
let condA = new_definition `condA (v1:real^3) v2 v3 v4 x12 x13 x14 x23 x24 x34 = 
  ( ~ ( v1 = v2 ) /\
  ( dist ( v1, v2) pow 2 ) = x12 /\
  dist (v1,v3) pow 2 = x13 /\
  dist (v1,v4) pow 2 = x14 /\
  dist (v2,v3) pow 2 = x23 /\ dist (v2,v4) pow 2 = x24 )`;;
let muy_delta = new_definition ` muy_detal = delta `;;

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
          c x12 x13 x14 x23 x24 x34)
     ==> (v3 IN aff {v1, v2} \/ v4 IN aff {v1, v2} <=>
          b x12 x13 x14 x23 x24 pow 2 -
          &4 * a x12 x13 x14 x23 x24 * c x12 x13 x14 x23 x24 x34 =
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

(* le 36. p 23 *)
let ZZSBSIO = new_axiom` ! u v w. CARD {u,v,w} = 3 /\ packing {u,v,w} /\
  dist (u,v) < sqrt8 ==>  dist (u,v) / &2 < dist (w, &1 / &2 % ( u + v )) `;;

(* le 37. p24 *)
let JGYWWBX = new_axiom `~(?v1 v2 w1 (w2:real^3).
           CARD {v1, v2, w1, w2} = 4 /\
           packing {v1, v2, w1, w2} /\
           dist (v1,w2) >= sqrt8 /\
           dist (v1,v2) <= #3.2 /\
           dist (w1,w2) <= sqrt8 /\
           ~(conv {v1, v2} INTER conv {w1, w2} = {}))`;;

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
         ==> d3 v1 v3 < #3.488

(* le 56. p 36 *)
let QHSEWMI = new_axiom `!v1 v2 v3 w1 w2.
     ~(conv {w1, w2} INTER conv {v1, v2, v3} = {}) /\
     ~(w1 IN conv {v1, v2, v3})
     ==> w2 IN cone w1 {v1, v2, v3}`;;
