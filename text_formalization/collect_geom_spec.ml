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
         x13 * x34 * (x12 - x13 + x14 + x23 - x24 + x34 ) +
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
let RCEABUJ = new_axiom ` ! a (b:real^3) x y. line x /\ {a,b} SUBSET x /\ ~( a = b) 
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
let FAFKVLR = new_axiom `! v1 v2 (v3: real ^3) v p. plane p /\
         {v1, v2, v3} SUBSET p /\
         ~collinear {v1, v2, v3} /\
         v IN p
         ==> (?!t1 t2 t3. v = t1 % v1 + t2 % v2 + t3 % v3)`;;
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
(* le 25. p 19 *)
let HMWTCNS = new_axiom ` ! a b (c:real^3). 
            CARD {a, b, c} = 3 /\ packing {a, b, c}
         ==> &2 / sqrt (&3) <= circumradius {a, b, c}`;;
