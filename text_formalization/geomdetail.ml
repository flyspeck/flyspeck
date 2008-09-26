

(* ------------------------------------------------------------------------- *)
(* A few bits of general derived syntax.                                     *)
(* ------------------------------------------------------------------------- *)
needs "database_more.ml";;
needs "definitions_kepler.ml";;
needs "Multivariate/convex.ml";;

let voronoi_trg = new_definition `voronoi_trg v S = { x | !w. ((S w) /\ ~(w=v))
==> (dist ( x , v ) < dist ( x , w )) }`;;


let conv0_2 = new_definition ` conv0_2 s = conv0 s `;;


let convex = new_definition
	   
`convex s <=>
	   
!x y u v. x IN s /\ y IN s /\ &0 <= u /\ &0 <= v /\ (u + v = &1)
	   
==> (u % x + v % y) IN s`;;
(* aff is deprecated *)	   
let aff = new_definition `aff = ( hull ) affine`;;	   
	   


let conv_trg = new_definition ` conv_trg s = convex hull s`;;

 let border = new_definition ` border s = { x | ! ep. ep > &0 /\ ( ? a b. ~ (b IN s ) /\
 dist (b, x) < ep /\ a IN s /\ dist (a, x) < ep ) }`;;
 
	   


(*
let packing = new_definition `packing (s:real^3 -> bool) = (! x y.  s x /\ s y /\ ( ~(x=y))
  ==> dist ( x, y) >= &2 ) `;;
*)



let center_pac = new_definition ` center_pac s v = ( packing s /\ s v )`;;

let voronoi2 = new_definition ` voronoi2 v S = {x| x IN voronoi_trg v S /\ d3 x v < &2 }`;;

let t0 = new_definition ` t0 = #1.255`;;

let quasi_tri = new_definition ` quasi_tri tri s = ( packing s /\ 
  tri SUBSET s /\
  CARD tri = 3 /\
  (! x y.  ( x IN tri /\ y IN tri /\ (~(x=y)) ) ==> ( d3 x y <= &2 * t0 )))`;;

let simplex = new_definition ` simplex (d:real^3 -> bool) s = ( packing s /\
  d SUBSET s /\
  CARD d = 4 )`;;

let quasi_reg_tet = new_definition ` quasi_reg_tet x s = ( simplex x s /\
   (! v w. ( v IN x /\ w IN x /\ 
    ( ~ ( v = w))) 
  ==> ( d3 v w <= &2 * t0 )) )`;;

let quarter = new_definition ` quarter q s = ( simplex q s /\ 
  (? v w. ! x y. v IN q /\ w IN q /\ x IN q /\ y IN q
    /\ ( d3 v w <= sqrt ( &8 ) ) /\ (d3 v w >= &2 )
  /\ ( ~( {v , w } = { x , y}) ==> ( d3 x y > &2 /\ d3 x y <= &2 * t0 )) ))`;;

let diagonal = new_definition ` diagonal dgcheo d s = ( quarter d s /\
  ( ? x y. x IN d /\ y IN d /\ { x, y } = dgcheo /\ d3 x y >= &2 * t0 ))`;;

let strict_qua = new_definition ` strict_qua d s = ( quarter d s /\ 
  ( ? x y. x IN d /\ y IN d /\ d3 x y > &2 * t0 /\ d3 x y < sqrt( &8 ) ))`;;

let strict_qua2 = new_definition ` strict_qua2 d (ch:real^3 -> bool ) s = ( quarter d s /\ CARD ch = 2 /\ ch SUBSET d 
  /\ ( ? x y. ch x /\ ch y /\ d3 x y > &2 * t0 /\ d3 x y < sqrt ( &8 ) ) )`;;



let quartered_oct = new_definition `quartered_oct  (v:real^3)  (w:real^3) (v1:real^3)  (v2:real^3)  (v3:real^3)  (v4:real^3)  s =
         ( packing s /\
         ( &2 * t0 < dist (v,w) /\ dist (v,w) < sqrt (&8) ) /\
         (!x. x IN {v1, v2, v3, v4}
              ==> dist (x,v) <= &2 * t0 /\ dist (x,w) <= &2 * t0) /\
         {v, w, v1, v2, v3, v4} SUBSET s /\
         (&2 <= dist (v1,v2) /\ dist (v1,v2) <= &2 * t0) /\
         (&2 <= dist (v2,v3) /\ dist (v2,v3) <= &2 * t0) /\
         (&2 <= dist (v3,v4) /\ dist (v3,v4) <= &2 * t0) /\
         &2 <= dist (v4,v1) /\
         dist (v4,v1) <= &2 * t0 ) `;;


let adjacent_pai = new_definition ` adjacent_pai v v1 v2 v3 v4 s = ( strict_qua2 { v , v1 , v3 , v2 } { v1 , v3 } s
  /\ strict_qua2 { v , v1 , v3 , v4 } { v1 , v3 } s /\
  ( conv0 { v , v1 , v3 , v2 } INTER conv0 { v , v1 , v3 , v4 } = {} ) )`;;

let conflicting_dia = new_definition ` conflicting_dia v v1 v3 v2 v4 s = ( adjacent_pai v v1 v3 v2 v4 s
/\ adjacent_pai v v2 v4 v1 v3 s )`;;

let interior_pos = new_definition `interior_pos v v1 v3 v2 v4 s = ( conflicting_dia v v1 v3 v2 v4 s 
  /\ ~( conv0_2 { v1, v3 } INTER conv0 { v , v2 , v4 } = {} ))`;;

let isolated_qua = new_definition ` isolated_qua q s = ( quarter q s /\ ~( ? v v1 v2 v3 v4. q = 
  {v, v1, v2, v3} /\ adjacent_pai v v1 v2 v3 v4 s))`;;

let isolated_pai = new_definition ` isolated_pai q1 q2 s = ( isolated_qua q1 s /\ isolated_qua q2 s /\
  ~ (conv0 q1 INTER conv0 q2 = {}))`;;


let anchor = new_definition ` anchor (v:real^3) v1 v2 = ( d3 v1 v2 <= sqrt ( &8 ) /\
  d3 v1 v2 >= &2 * t0 /\ d3 v v1 <= &2 * t0 /\ d3 v v2 <= &2 * t0 )`;;

let anchor_points = new_definition ` anchor_points v w = { t | &2 * t0 <= d3 v w /\
  anchor t v w }`;;


new_definition ` Q_SYS s = {q | quasi_reg_tet q s \/
              strict_qua q s /\
              (?c d.
                   !qq. c IN q /\
                        d IN q /\
                        d3 c d > &2 * t0 /\
                        (quasi_reg_tet qq s \/ strict_qua qq s) /\
                        conv0_2 {c, d} INTER conv0 qq = {}) \/
              strict_qua q s /\
              (CARD
               {t | ?v w.
                        v IN q /\ w IN q /\ &2 * t0 < d3 v w /\ anchor t v w} >
               4 \/
               CARD
               {t | ?v w.
                        v IN q /\ w IN q /\ &2 * t0 < d3 v w /\ anchor t v w} =
               4 /\
               ~(?v1 v2 v3 v4 v w. v IN q /\
                     w IN q /\
                     {v1, v2, v3, v4} SUBSET anchor_points v w 
                      /\
                     
                     &2 * t0 < d3 v w /\
                     quartered_oct v w v1 v2 v3 v4 s))
  \/ (? v w v1 v2 v3 v4. q = { v, w, v1, v2} /\ quartered_oct v w v1 v2 v3 v4 s )
  \/ (? v v1 v3 v2 v4. ( q = {v, v1, v2, v3} \/ q = {v, v1, v3, v4} ) /\
  interior_pos v v1 v3 v2 v4 s /\ anchor_points v1 v3 = { v, v2, v4} /\
  anchor_points v2 v4 = { v, v1, v3 } )}`;; 

let barrier = new_definition ` barrier s = { { (v1 : real^3 ) , ( v2 :real^3 ) , (v3 :real^3) } |
  quasi_tri { v1 , v2 , v3 } s \/ 
  (? v4. ( { v1 , v2 , v3 } UNION { v4 }) IN Q_SYS s ) } `;;

let obstructed = new_definition ` obstructed x y s = ( ? bar. bar IN barrier s /\
  ( ~ (conv0_2 { x , y } INTER conv_trg bar = {})))`;;

let unobstructed = new_definition ` unobstructed x y s = ( ~( obstructed x y s ))`;;

let VC_trg = new_definition ` VC_trg x s = { z | d3 x z < &2 /\ ~obstructed x z s /\
  (! y. y IN s /\ ~ ( x = y ) /\ ~(obstructed z y s)   ==> d3 x z < d3 y z )} `;;  (* /\ ~(obstructed z y s) doing *) 

let VC_INFI_trg = new_definition ` VC_INFI_trg s = { z | ( ! x. x IN s /\
  ~( z IN VC_trg x s ))}`;;


let lambda_x = new_definition `lambda_x x s = {w | w IN s /\ d3 w x < &2 /\
~obstructed w x s }`;;

let VC = new_definition `VC v s = { x | v IN lambda_x x s /\ 
(!w. w IN lambda_x x s /\ ~(w = v) ==> d3 x v < d3 x w) }`;;

let VC_INFI = new_definition ` VC_INFI s = { z | ( ! x. ~( z IN VC x s ))}`;;

let trg_sub_bo = prove ( `A SUBSET B <=> (!x. A x ==> B x)`, SET_TAC[] );;

let trg_sub_se = prove ( `A SUBSET B <=> (!x. x IN A  ==> x IN B )`, SET_TAC[] );;

let trg_setbool = prove (`x IN A <=> A x `, SET_TAC[] );;

let trg_boolset = prove (` A x <=>  x IN A `, SET_TAC[] );;

let trg_in_union = prove (` x IN ( A UNION B ) <=> x IN A \/ x IN B `, SET_TAC[]);;

let not_in_set3 = prove ( `~ ( x IN { z | A z /\ B z /\ C z } ) <=> ~ A x \/ ~ B x \/ ~ C x `,
  SET_TAC[]);;

let trg_d3_sym = prove ( ` d3 x y = d3 y x `, SIMP_TAC[d3; DIST_SYM]);;

let affine_hull_e = prove (`affine hull {} = {}`, REWRITE_TAC[AFFINE_EMPTY; AFFINE_HULL_EQ]);;

let wlog = MESON[]` (! a b. ( P a b = P b a ) /\ ( Q a b \/ Q b a ) ) ==> ((? a b . P a b ) <=> ( ? a b. P a b 
  /\ Q a b ))`;;
let wlog_real = MESON[REAL_ARITH `( ! a b:real. a <= b \/ b <= a )`] ` (! a:real b:real . P a b = P b a ) ==> ((? a:real b . P a b ) <=> ( ? a b. P a b 
  /\ a <= b ))`;;
let dkdx = MESON[REAL_ARITH ` ! a b:real. a <= b \/ b <= a `]`! P. (!a b u v m n p . P a b u v m n p <=> P b a v u m n p)
     ==> ((?a b u v m n p. P a b u v m n p) <=> (?a b u v m n p. P a b u v m n p /\ a <= b))`;;


let tarski_arith = new_axiom `! bar. bar IN barrier s /\
                               ~(conv_trg bar INTER conv0_2 { v0 , x } ={}) /\ 
                               ~ ( v0 IN bar ) /\
                                 x IN voronoi2 v0 s /\ 
                              ~ ( x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s} ) 
                            ==> { v0 } UNION bar IN Q_SYS s `;;
let simp_def = new_axiom ` (!v0 v1 v2.
          aff_ge {v0} {v1, v2} =
          {t | ?u v w.
                   &0 <= v /\
                   &0 <= w /\
                   u + v + w = &1 /\
                   t = u % v0 + v % v1 + w % v2}) /\
     (!v0 v1 v2 v3.
          aff_gt {v0} {v1, v2, v3} =
          {t | ?x y z w.
                   &0 < y /\
                   &0 < z /\
                   &0 < w /\
                   x + y + z + w = &1 /\
                   t = x % v0 + y % v1 + z % v2 + w % v3}) /\
     (!v0 v1 v2 v3.
          aff_le {v1, v2, v3} {v0} =
          {t | ?a b c d.
                   d <= &0  /\
                   a + b + c + d = &1 /\
                   t = a % v1 + b % v2 + c % v3 + d % v0}) /\
     ( ! v0 v1. conv0_2 { v0, v1 } = { x | ? t. &0 < t /\ t < &1 /\ x = t % v0 + (&1 - t ) % v1 } )`;;



let conv0_3_trg = new_definition ` conv0_3_trg s = { x | ?a b c t z r. ~( a = b ) /\ ~( b = c) /\ ~(c = a )
   /\ a IN s /\ b IN s /\ c IN s
   /\ &0 < t /\ t < &1 /\ &0 < z /\ z < &1 /\ &0 < r /\ r < &1 
   /\ t + z + r = &1 /\ x = t % a + z % b + r % c}`;;
(*This definition only correct with s with CARD s = 3*)

let AFFINE_HULL_SINGLE = prove(`!x. affine hull {x} = {x}`,
  SIMP_TAC[AFFINE_SING; AFFINE_HULL_EQ]);;

let usefull = MESON[] ` (!x. a x ==> b x ) ==>(?x. a x ) ==> c ==> d <=> (!x. a x ==> b x) ==> (?x. a x /\ b x ) ==> c ==> d `;;

let v1_in_convex3 = prove (` ! v1 v2 v3. v1 IN {t | ?a b c.
              &0 <= a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 /\ t = a % v1 + b % v2 + c % v3}`, REPEAT GEN_TAC THEN REWRITE_TAC[ IN_ELIM_THM] THEN EXISTS_TAC ` &1 ` THEN EXISTS_TAC ` &0 ` THEN EXISTS_TAC ` &0 ` THEN REWRITE_TAC[ VECTOR_ARITH ` &1 % v1 + &0 % v2 + &0 % v3 = v1 `] THEN REAL_ARITH_TAC);;

let v3_in_convex3 = prove (`! v1 v2 v3. v3 IN
 {t | ?a b c. &0 <= a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 /\ t = a % v1 + b % v2 + c % v3}`, PURE_ONCE_REWRITE_TAC [ VECTOR_ARITH ` a % v1 + b % v2 + c % v3 = c % v3 + a % v1 + b % v2`] THEN REWRITE_TAC[ SET_RULE ` {t | ?a b c. &0 <= a /\ &0 <= b /\ &0 <= c /\ t = c % v3 + a % v1 + b % v2} =
  {t | ? c a b. &0 <= c /\ &0 <= a /\ &0 <= b /\ t = c % v3 + a % v1 + b % v2}`] THEN REWRITE_TAC[v1_in_convex3]
THEN 
PURE_ONCE_REWRITE_TAC[ REAL_RING ` a + b + c = c + a + b`] THEN
REWRITE_TAC [  SET_RULE `
  {t | ?a b c.
              &0 <= a /\
              &0 <= b /\
              &0 <= c /\
              c + a + b = &1 /\
              t = c % v3 + a % v1 + b % v2}
  = {t | ?c a b. &0 <= c /\
              &0 <= a /\
              &0 <= b /\
                           c + a + b = &1 /\
              t = c % v3 + a % v1 + b % v2}` ] THEN REWRITE_TAC[v1_in_convex3]);;


let v1v2v3_in_convex3 = prove (` ! v1 v2 v3 . v1 IN {t | ?a b c. &0 <= a /\ &0 <= b /\ &0 <= c /\ 
a + b + c = &1 /\ t = a % v1 + b % v2 + c % v3}
   /\ v2 IN {t | ?a b c. &0 <= a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 /\ t = a % v1 + b % v2 + c % v3}
  /\ v3 IN {t | ?a b c. &0 <= a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 /\ t = a % v1 + b % v2 + c % v3}`,
 REPEAT GEN_TAC THEN 
REWRITE_TAC[v1_in_convex3] THEN CONJ_TAC THEN
REWRITE_TAC[ SET_RULE ` {t | ?a b c. &0 <= a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 /\
 t = a % v1 + b % v2 + c % v3}
  = {t | ?b a c. &0 <= b /\ &0 <= a /\ &0 <= c /\ a + b + c = &1 /\ t = a % v1 + b % v2 +   c % v3} `]
THEN PURE_ONCE_REWRITE_TAC[VECTOR_ARITH` a % v1 + b % v2 + c % v3 = b % v2 + a % v1 + c % v3 `] THEN 
PURE_ONCE_REWRITE_TAC[REAL_RING ` a + b + c = b + a + c`] THEN 
REWRITE_TAC[v1_in_convex3] THEN PURE_ONCE_REWRITE_TAC [ VECTOR_ARITH ` a % v1 + b % v2 + c % v3 =
 c % v3 + a % v1 + b % v2`]
 THEN REWRITE_TAC[ SET_RULE ` {t | ?a b c. &0 <= a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 /\ t = c % v3 + a % v1 + b % v2} =
  {t | ? c a b. &0 <= c /\ &0 <= a /\ &0 <= b /\ a + b + c = &1 /\ t = c % v3 + a % v1 + b % v2}`]
THEN ONCE_REWRITE_TAC [ REAL_FIELD ` a + b + c = c + a + b ` ] THEN REWRITE_TAC[v1_in_convex3]);;
let convex3 = new_axiom ` convex {t | ?a b c.
              &0 <= a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 /\ t = a % v1 + b % v2 + c % v3}`;;

let INTERS_SUBSET = SET_RULE `! P t0. P t0 ==> INTERS { t| P t } SUBSET t0`;;





let minconvex3 = prove (`! t v1 v2 v3. convex t /\
     {v1, v2, v3} SUBSET t 
  ==> ( ! a b c. &0 <= a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 ==>
 a % v1 + b % v2 + c % v3 IN t )`, 
REPEAT GEN_TAC THEN REWRITE_TAC[convex] THEN REWRITE_TAC [ TAUT ` a/\b ==> c <=>
a==> b ==> c `] THEN 
REWRITE_TAC [SET_RULE ` {v1, v2, v3} SUBSET a <=> v1 IN a /\ v2 IN a /\ v3 IN a`] THEN 
REPEAT DISCH_TAC THEN 
REPEAT GEN_TAC THEN 
REWRITE_TAC[ REAL_ARITH ` &0 <= a <=> &0 = a \/ &0 < a`] THEN 
MATCH_MP_TAC (MESON[]` (a ==> c )/\(b ==> c ) ==> ( a\/b ==> c)`) THEN CONJ_TAC THEN 
SIMP_TAC [] THEN 
SIMP_TAC[ REAL_ARITH ` &0 = a <=> a = &0 `] THEN 
REWRITE_TAC[REAL_ARITH ` b = &0 \/ &0 < b <=> &0 <= b`] THEN
REWRITE_TAC [ REAL_ARITH ` &0 + a = a `; VECTOR_ARITH ` &0 % x + y = y `] THEN 
DISCH_TAC THEN 
REPLICATE_TAC 2 (FIRST_X_ASSUM MP_TAC) THEN 
REWRITE_TAC [ TAUT ` e /\ f /\ t ==> a ==> c <=> a /\ e ==> f ==> t ==> c`] THEN 
DISCH_TAC THEN
ASM_REWRITE_TAC[] THEN 
(* one goal solved *)
FIRST_X_ASSUM MP_TAC THEN 
REWRITE_TAC[MESON[]` &0 < a /\ v1 IN t
 ==> v2 IN t
 ==> v3 IN t
 ==> &0 <= b
 ==> &0 <= c
 ==> a + b + c = &1
 ==> a % v1 + b % v2 + c % v3 IN t 
  <=>
   v1 IN t
 /\ v2 IN t
 /\ v3 IN t ==> &0 < a 
 ==> &0 <= b
 ==> &0 <= c
 ==> a + b + c = &1
 ==> a % v1 + b % v2 + c % v3 IN t `] THEN 
REWRITE_TAC[ MESON[]`v1 IN t /\ v2 IN t /\ v3 IN t
 ==> &0 < a
 ==> &0 <= b
 ==> &0 <= c
 ==> a + b + c = &1
 ==> a % v1 + b % v2 + c % v3 IN t
  <=>
  v1 IN t /\ v2 IN t /\ v3 IN t ==>
   &0 < a
 /\ &0 <= b
 /\ &0 <= c
 /\ a + b + c = &1
 ==> a % v1 + b % v2 + c % v3 IN t `] THEN 

REWRITE_TAC[ REAL_FIELD ` &0 < a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 <=>
     &0 < a /\
     &0 <= b /\ &0 <= a /\
     a = (a + b) * a / (a + b) /\
     b = (a + b) * b / (a + b) /\
     &0 <= a + b /\
     &0 <= c /\
     (a + b) + c = &1`] THEN 
REWRITE_TAC[ MESON[REAL_LE_DIV] ` &0 < a /\
 &0 <= b /\
 &0 <= a /\
 a = (a + b) * a / (a + b) /\
 b = (a + b) * b / (a + b) /\
 &0 <= a + b /\
 &0 <= c /\
 (a + b) + c = &1
  <=>
  &0 < a /\ &0 <= a / ( a + b ) /\ &0 <= b / ( a+ b) /\
 &0 <= b /\
 &0 <= a /\
 a = (a + b) * a / (a + b) /\
 b = (a + b) * b / (a + b) /\
 &0 <= a + b /\
 &0 <= c /\
 (a + b) + c = &1`] THEN 
REWRITE_TAC[ REAL_FIELD ` &0 < a /\
     &0 <= a / (a + b) /\
     &0 <= b / (a + b) /\
     &0 <= b /\
     &0 <= a /\
     a = (a + b) * a / (a + b) /\
     b = (a + b) * b / (a + b) /\
     &0 <= a + b /\
     &0 <= c /\
     (a + b) + c = &1 <=>
     &0 < a /\
     &0 <= a / (a + b) /\
     &0 <= b / (a + b) /\
     a / (a + b) + b / (a + b) = &1 /\
     &0 <= b /\
     &0 <= a /\
     a = (a + b) * a / (a + b) /\
     b = (a + b) * b / (a + b) /\
     &0 <= a + b /\
     &0 <= c /\
     (a + b) + c = &1 `] THEN 
FIRST_X_ASSUM MP_TAC THEN 


REWRITE_TAC[ MESON[]` (!x y u v.
      x IN t
      ==> y IN t
      ==> &0 <= u
      ==> &0 <= v
      ==> u + v = &1
      ==> u % x + v % y IN t)
 ==> v1 IN t /\ v2 IN t /\ v3 IN t
 ==> &0 < a /\
     &0 <= a / (a + b) /\
     &0 <= b / (a + b) /\
     a / (a + b) + b / (a + b) = &1 /\ 
     &0 <= b /\
     &0 <= a /\
     a = (a + b) * a / (a + b) /\
     b = (a + b) * b / (a + b) /\
     &0 <= a + b /\
     &0 <= c /\
     (a + b) + c = &1
 ==> bbb 
  <=> (!x y u v.
      x IN t
      ==> y IN t
      ==> &0 <= u
      ==> &0 <= v
      ==> u + v = &1
      ==> u % x + v % y IN t)
 ==> v1 IN t /\ v2 IN t /\ v3 IN t
 ==> &0 < a /\
     &0 <= a / (a + b) /\
     &0 <= b / (a + b) /\
     a / (a + b) + b / (a + b) = &1 /\ (a / ( a+ b) ) % v1 + ( b / ( a + b))% v2 IN t /\
     &0 <= b /\
     &0 <= a /\
     a = (a + b) * a / (a + b) /\
     b = (a + b) * b / (a + b) /\
     &0 <= a + b /\
     &0 <= c /\
     (a + b) + c = &1
 ==> bbb `] THEN 
REWRITE_TAC[ MESON[VECTOR_MUL_RCANCEL] ` &0 < a /\
     &0 <= a / (a + b) /\
     &0 <= b / (a + b) /\
     a / (a + b) + b / (a + b) = &1 /\
     a / (a + b) % v1 + b / (a + b) % v2 IN t /\
     &0 <= b /\
     &0 <= a /\
     a = (a + b) * a / (a + b) /\
     b = (a + b) * b / (a + b) /\
     &0 <= a + b /\
     &0 <= c /\
     (a + b) + c = &1
 ==> a % v1 + b % v2 + c % v3 IN t 
  <=>
  &0 < a /\
     &0 <= a / (a + b) /\
     &0 <= b / (a + b) /\
     a / (a + b) + b / (a + b) = &1 /\
     a / (a + b) % v1 + b / (a + b) % v2 IN t /\
     &0 <= b /\
     &0 <= a /\
     a = (a + b) * a / (a + b) /\
     b = (a + b) * b / (a + b) /\
     &0 <= a + b /\
     &0 <= c /\
     (a + b) + c = &1
 ==> ((a + b) * a / (a + b)) % v1 + ((a + b) * b / (a + b)) % v2 + c % v3 IN t `] THEN 
REWRITE_TAC[VECTOR_ARITH ` ((a + b) * a / (a + b)) % v1 + ((a + b) * b / (a + b)) % v2 + c % v3 = (a + b) % ( a / (a + b) % v1 +  b / (a + b) % v2 ) + c % v3 `] THEN 
MESON_TAC[]);;

let convex3_in_inters = prove (` ! v1 v2 v3. {t | ?a b c.
          &0 <= a /\
          &0 <= b /\
          &0 <= c /\
          a + b + c = &1 /\
          t = a % v1 + b % v2 + c % v3} SUBSET
 INTERS {t | convex t /\ {v1, v2, v3} SUBSET t} `, 
REPEAT GEN_TAC THEN 
MATCH_MP_TAC (SET_RULE ` ( ! x. x IN A ==> x IN B ) ==> A SUBSET B`) THEN 
REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[IN_INTERS] THEN 
REWRITE_TAC[MESON[] `( !x. (?a b c.
          &0 <= a /\
          &0 <= b /\
          &0 <= c /\
          a + b + c = &1 /\
          x = a % v1 + b % v2 + c % v3)
     ==> (!t. convex t /\ {v1, v2, v3} SUBSET t ==> x IN t))
  <=>( !x. (?a b c.
          &0 <= a /\
          &0 <= b /\
          &0 <= c /\
          a + b + c = &1 /\
          x = a % v1 + b % v2 + c % v3)
     ==> (!t. convex t /\ {v1, v2, v3} SUBSET t /\ (?a b c.
          &0 <= a /\
          &0 <= b /\
          &0 <= c /\
          a + b + c = &1 /\
          x = a % v1 + b % v2 + c % v3) ==> x IN t)) `] THEN 
GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN FIRST_X_ASSUM MP_TAC THEN 
REWRITE_TAC[ IN_ELIM_THM ; TAUT ` a ==> b ==> c <=> a /\ b ==> c `] THEN 
MESON_TAC[minconvex3]);;




(*
let simpl_conv3 = prove (` ! v1 v2 v3. conv_trg {v1 , v2 ,v3} = {t | ?a b c. &0 <= a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 
/\ t = a % v1 + b % v2 + c % v3}`,
REPEAT GEN_TAC THEN
REWRITE_TAC[conv; hull] THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[ SET_RULE` a = b <=> a SUBSET b /\ b SUBSET a `] THEN CONJ_TAC THEN
REWRITE_TAC[conv_trg; hull] THEN 
MATCH_MP_TAC INTERS_SUBSET THEN 
 REWRITE_TAC[convex3] THEN REWRITE_TAC[ SET_RULE `{v1 , v2, v3} SUBSET a <=>
  v1 IN a /\ v2 IN a /\ v3 IN a`] THEN REWRITE_TAC [ v1v2v3_in_convex3] THEN 
 REWRITE_TAC[convex3_in_inters]);;
*)

g ` ! v1 v2 v3. conv_trg {v1 , v2 ,v3} = {t | ?a b c. &0 <= a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 
/\ t = a % v1 + b % v2 + c % v3}`;;
e ( REPEAT GEN_TAC THEN
REWRITE_TAC[conv; hull] THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[ SET_RULE` a = b <=> a SUBSET b /\ b SUBSET a `] THEN CONJ_TAC THEN
REWRITE_TAC[conv_trg; hull]);;
e ( MATCH_MP_TAC INTERS_SUBSET );;
e ( REWRITE_TAC[convex3] THEN REWRITE_TAC[ SET_RULE `{v1 , v2, v3} SUBSET a <=>
  v1 IN a /\ v2 IN a /\ v3 IN a`] THEN REWRITE_TAC [ v1v2v3_in_convex3]);;
e (REWRITE_TAC[convex3_in_inters]);;

let simpl_conv3 = top_thm();;


let chuachungminh = prove (`! bar. bar IN barrier s /\
            ~(conv0_2 {v0, x} INTER conv_trg bar = {}) /\
            ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) 
  ==> ~ (v0 IN bar ) `, 
GEN_TAC THEN REWRITE_TAC[ MESON[]` a /\ b /\ ~ c ==> ~ d <=> a /\ b /\ d ==> c `] THEN 
REWRITE_TAC[ barrier; IN_ELIM_THM] THEN 
MATCH_MP_TAC (MESON[ MESON[] ` (?v1 v2 v3.
          (quasi_tri {v1, v2, v3} s \/
           (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
          bar = {v1, v2, v3}) /\
     ~(conv0_2 {v0, x} INTER conv_trg bar = {}) /\
     v0 IN bar
     ==> (?v1 v2 v3.
              (quasi_tri {v1, v2, v3} s \/
               (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
              ~(conv0_2 {v0, x} INTER conv_trg {v1, v2, v3} = {}) /\
              v0 IN {v1, v2, v3}) /\
         ~(conv0_2 {v0, x} INTER conv_trg bar = {}) /\
         v0 IN bar ` ] ` ( (?v1 v2 v3.
              (quasi_tri {v1, v2, v3} s \/
               (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
              ~(conv0_2 {v0, x} INTER conv_trg {v1, v2, v3} = {}) /\
              v0 IN {v1, v2, v3}) /\
         ~(conv0_2 {v0, x} INTER conv_trg bar = {}) /\
         v0 IN bar 
  ==> x IN
     UNIONS
     {aff_ge {v0} {v1, v2} | ?v1' v2' v3.
                                 (quasi_tri {v1', v2', v3} s \/
                                  (?v4. {v1', v2', v3} UNION {v4} IN Q_SYS s)) /\
                                 {v0, v1, v2} = {v1', v2', v3}} )
  ==> ((?v1 v2 v3.
      (quasi_tri {v1, v2, v3} s \/ (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
      bar = {v1, v2, v3}) /\
 ~(conv0_2 {v0, x} INTER conv_trg bar = {}) /\
 v0 IN bar
 ==> x IN
     UNIONS
     {aff_ge {v0} {v1, v2} | ?v1' v2' v3.
                                 (quasi_tri {v1', v2', v3} s \/
                                  (?v4. {v1', v2', v3} UNION {v4} IN Q_SYS s)) /\
                                 {v0, v1, v2} = {v1', v2', v3}})`) THEN 
REWRITE_TAC[SET_RULE` v0 IN {v1, v2, v3} <=> v0 = v1 \/ v0 = v2 \/ v0 = v3`] THEN 
REWRITE_TAC[ MESON[] ` (quasi_tri {v1, v2, v3} s \/ (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
      ~(conv0_2 {v0, x} INTER conv_trg {v1, v2, v3} = {}) /\
      (v0 = v1 \/ v0 = v2 \/ v0 = v3) <=>
  ((quasi_tri {v1, v2, v3} s \/ (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
      ~(conv0_2 {v0, x} INTER conv_trg {v1, v2, v3} = {}) ) /\
      (v0 = v1 \/ v0 = v2 \/ v0 = v3)`] THEN 
MATCH_MP_TAC (MESON[]`! P. (! (a:real^3) (b:real^3) (c:real^3). P a b c <=> P b a c ) /\ (
  (? (a:real^3) (b:real^3) (c:real^3). P a b c /\ (v = a \/ v = c )) /\ cc ==> last )
  ==> ( (?(a:real^3) (b:real^3) (c:real^3). P a b c /\ ( v = a \/ v= b \/ v = c )) /\ cc ==> last )`) THEN 
REWRITE_TAC[MESON[ SET_RULE ` ! (a:real^3) (b:real^3) (c:real^3). {a, b, c} = { b, a, c}`]`
  (!v1 v2 v3.
      (quasi_tri {v1, v2, v3} s \/ (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
      ~(conv0_2 {v0, x} INTER conv_trg {v1, v2, v3} = {}) <=>
      (quasi_tri {v2, v1, v3} s \/ (?v4. {v2, v1, v3} UNION {v4} IN Q_SYS s)) /\
      ~(conv0_2 {v0, x} INTER conv_trg {v2, v1, v3} = {}))`] THEN 
MATCH_MP_TAC (MESON[]` !P. (!(a:real^3) (b:real^3) (c:real^3). P a b c <=> P c b a) /\
         ((?(a:real^3) (b:real^3) (c:real^3). P a b c /\ v = a) /\ cc ==> last)
         ==> (?(a:real^3) (b:real^3) (c:real^3). P a b c /\ (v = a \/ v = c)) /\ cc
         ==> last `) THEN 
REWRITE_TAC[MESON[ SET_RULE ` ! (a:real^3) (b:real^3) (c:real^3). { a, b , c } = { c, b , a }`]`
  (!v1 v2 v3.
      (quasi_tri {v1, v2, v3} s \/ (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
      ~(conv0_2 {v0, x} INTER conv_trg {v1, v2, v3} = {}) <=>
      (quasi_tri {v3, v2, v1} s \/ (?v4. {v3, v2, v1} UNION {v4} IN Q_SYS s)) /\
      ~(conv0_2 {v0, x} INTER conv_trg {v3, v2, v1} = {})) `] THEN 
REWRITE_TAC[ SET_RULE ` ~ ( a INTER b = {} ) <=> ( ? i j. i IN a/\ j IN b /\ i = j )`] THEN 
REWRITE_TAC[simpl_conv3; simp_def; IN_ELIM_THM] THEN 
REWRITE_TAC[ MESON[]` (?i j.
            (?t. &0 < t /\ t < &1 /\ i = t % v0 + (&1 - t) % x) /\
            (?a b c.
                 &0 <= a /\
                 &0 <= b /\
                 &0 <= c /\
                 a + b + c = &1 /\
                 j = a % v1 + b % v2 + c % v3) /\
            i = j)
  <=> ( ? a b c t. &0 < t /\ t < &1 /\ &0 <= a /\
                 &0 <= b /\
                 &0 <= c /\
                 a + b + c = &1 /\ t % v0 + (&1 - t) % x = a % v1 + b % v2 + c % v3 )`] THEN 
REWRITE_TAC[ MESON[] ` ((quasi_tri {v1, v2, v3} s \/
        (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
       (?a b c t.
            &0 < t /\
            t < &1 /\
            &0 <= a /\
            &0 <= b /\
            &0 <= c /\
            a + b + c = &1 /\
            t % v0 + (&1 - t) % x = a % v1 + b % v2 + c % v3)) /\
      v0 = v1 
  <=>  ((quasi_tri {v1, v2, v3} s \/
        (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
       (?a b c t.
            &0 < t /\
            t < &1 /\
            &0 <= a /\
            &0 <= b /\
            &0 <= c /\
            a + b + c = &1 /\
            t % v1 + (&1 - t) % x = a % v1 + b % v2 + c % v3)) /\
      v0 = v1 `] THEN 
REWRITE_TAC [ VECTOR_ARITH ` t % v1 + (&1 - t) % x = a % v1 + b % v2 + c % v3 <=>
     (&1 - t) % x = --t % v1 + a % v1 + b % v2 + c % v3`] THEN 
REWRITE_TAC[ MESON[REAL_FIELD` (! t.  t < &1 <=> &0 < &1 - t ) /\ (! a b. &0 < a ==> b = a * ( b / a )) ` ] `
  (?a b c t.
          &0 < t /\
          t < &1 /\
          &0 <= a /\
          &0 <= b /\
          &0 <= c /\
          a + b + c = &1 /\
          (&1 - t) % x = --t % v1 + a % v1 + b % v2 + c % v3) <=>
     (?a b c t.
          &0 < t /\
          t < &1 /\
          &0 <= a /\
          &0 <= b /\
          &0 <= c /\
          a + b + c = &1 /\
          --t = (&1 - t) * --t / (&1 - t) /\
          a = (&1 - t) * a / (&1 - t) /\
          b = (&1 - t) * b / (&1 - t) /\
          c = (&1 - t) * c / (&1 - t) /\
          (&1 - t) % x = --t % v1 + a % v1 + b % v2 + c % v3) `] THEN 
REWRITE_TAC[MESON[]` --t = (&1 - t) * --t / (&1 - t) /\
     a = (&1 - t) * a / (&1 - t) /\
     b = (&1 - t) * b / (&1 - t) /\
     c = (&1 - t) * c / (&1 - t) /\
     (&1 - t) % x = --t % v1 + a % v1 + b % v2 + c % v3 <=>
     --t = (&1 - t) * --t / (&1 - t) /\
     a = (&1 - t) * a / (&1 - t) /\
     b = (&1 - t) * b / (&1 - t) /\
     c = (&1 - t) * c / (&1 - t) /\
     (&1 - t) % x =
     ((&1 - t) * --t / (&1 - t)) % v1 +
     ((&1 - t) * a / (&1 - t)) % v1 +
     ((&1 - t) * b / (&1 - t)) % v2 +
     ((&1 - t) * c / (&1 - t)) % v3 `] THEN 
REWRITE_TAC[ VECTOR_ARITH ` ( a * b ) % w = a % ( b % w ) /\ a % v + a % w = a % ( v + w )`] THEN 
REWRITE_TAC[ MESON[REAL_ARITH ` t < &1 ==> ~ ( &1 - t = &0 )`; VECTOR_MUL_LCANCEL_IMP ]`
  &0 < t /\
     t < &1 /\
     &0 <= a /\
     &0 <= b /\
     &0 <= c /\
     a + b + c = &1 /\
     --t = (&1 - t) * --t / (&1 - t) /\
     a = (&1 - t) * a / (&1 - t) /\
     b = (&1 - t) * b / (&1 - t) /\
     c = (&1 - t) * c / (&1 - t) /\
     (&1 - t) % x =
     (&1 - t) %
     (--t / (&1 - t) % v1 +
      a / (&1 - t) % v1 +
      b / (&1 - t) % v2 +
      c / (&1 - t) % v3) <=>
     &0 < t /\
     t < &1 /\
     &0 <= a /\
     &0 <= b /\
     &0 <= c /\
     a + b + c = &1 /\
     --t = (&1 - t) * --t / (&1 - t) /\
     a = (&1 - t) * a / (&1 - t) /\
     b = (&1 - t) * b / (&1 - t) /\
     c = (&1 - t) * c / (&1 - t) /\
     x =
     --t / (&1 - t) % v1 +
     a / (&1 - t) % v1 +
     b / (&1 - t) % v2 +
     c / (&1 - t) % v3 `] THEN 
REWRITE_TAC[ VECTOR_ARITH ` a % v1 + b % v1 + c % v2 + d % v3 = ( a + b ) % v1 + c % v2 + d % v3 `] THEN 
ONCE_REWRITE_TAC[ REAL_ARITH ` t < &1 <=> t < &1 /\ &0 <= &1 - t `] THEN 
REWRITE_TAC[ MESON[REAL_LE_DIV; REAL_FIELD ` a + b + c = &1 /\ t < &1 ==> (--t / (&1 - t) + a / (&1 - t)) +
  b / (&1 - t) + c / (&1 - t) = &1 ` ]` (?a b c t.
          &0 < t /\
          (t < &1 /\ &0 <= &1 - t) /\
          &0 <= a /\
          &0 <= b /\
          &0 <= c /\
          a + b + c = &1 /\
          --t = (&1 - t) * --t / (&1 - t) /\
          a = (&1 - t) * a / (&1 - t) /\
          b = (&1 - t) * b / (&1 - t) /\
          c = (&1 - t) * c / (&1 - t) /\
          x =
          (--t / (&1 - t) + a / (&1 - t)) % v1 +
          b / (&1 - t) % v2 +
          c / (&1 - t) % v3) <=>
     (?a b c t.
          &0 < t /\
          (t < &1 /\ &0 <= &1 - t) /\
          &0 <= a /\
          &0 <= b /\
          &0 <= c /\
          a + b + c = &1 /\
          --t = (&1 - t) * --t / (&1 - t) /\
          a = (&1 - t) * a / (&1 - t) /\
          b = (&1 - t) * b / (&1 - t) /\
          c = (&1 - t) * c / (&1 - t) /\
          &0 <= b / (&1 - t) /\
          &0 <= c / (&1 - t) /\
          (--t / (&1 - t) + a / (&1 - t)) + b / (&1 - t) + c / (&1 - t) = &1 /\
          x =
          (--t / (&1 - t) + a / (&1 - t)) % v1 +
          b / (&1 - t) % v2 +
          c / (&1 - t) % v3) `] THEN 
ONCE_REWRITE_TAC[ MESON[] ` ( ?v1' v2' v3.
         (quasi_tri {v1', v2', v3} s \/
          (?v4. {v1', v2', v3} UNION {v4} IN Q_SYS s)) /\
         {v0, v1, v2} = {v1', v2', v3} ) <=>
         quasi_tri {v0, v1, v2} s \/
         (?v4. {v0, v1, v2} UNION {v4} IN Q_SYS s)`] THEN  (* needs recheck *) 
REWRITE_TAC[ IN_UNIONS; IN_ELIM_THM] THEN 

REWRITE_TAC[ MESON[] ` (?t. (?v0 v1 v2.
               (quasi_tri {v0, v1, v2} s \/
                (?v4. {v0, v1, v2} UNION {v4} IN Q_SYS s)) /\
               t =
               {t | ?u v w.
                        &0 <= v /\
                        &0 <= w /\
                        u + v + w = &1 /\
                        t = u % v0 + v % v1 + w % v2}) /\
          x IN t)
  <=> (?v0 v1 v2.
               (quasi_tri {v0, v1, v2} s \/
                (?v4. {v0, v1, v2} UNION {v4} IN Q_SYS s)) /\
            x IN {t | ?u v w.
                        &0 <= v /\
                        &0 <= w /\
                        u + v + w = &1 /\
                        t = u % v0 + v % v1 + w % v2}) `] THEN 
SET_TAC[]);;







g ` ( center_pac s v0 /\
  Z = UNIONS { aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s} /\
  X = UNIONS {aff_gt {v0} {v1, v2, v3} INTER
       aff_le {v1, v2, v3} {v0} INTER
       voronoi2 v0 s | {v0, v1, v2, v3} IN Q_SYS s} )
  ==> ( voronoi2 v0 s SUBSET X UNION Z UNION VC_trg v0 s )`;;

e (DISCH_TAC THEN SIMP_TAC[trg_sub_se] THEN SIMP_TAC [ trg_in_union ] 
 THEN REWRITE_TAC[ MESON[] `( !x. x IN voronoi2 v0 s ==> x IN X \/ x IN Z \/ x IN VC_trg v0 s )
   <=> ( !x. x IN voronoi2 v0 s ==> x IN Z \/ x IN VC_trg v0 s \/ x IN X )`] THEN
SIMP_TAC [ MESON[] ` A ==> B \/ C <=> A /\ ~ B ==> C`] THEN 
ASM_REWRITE_TAC[voronoi2 ; VC_trg ] THEN REWRITE_TAC[ not_in_set3] THEN REWRITE_TAC [IN_ELIM_THM] THEN
 REWRITE_TAC[trg_d3_sym]THEN REWRITE_TAC[ MESON[] ` (( A /\ B ) /\ C ) /\ ( ~B \/ D \/ E ) <=>
  (( A /\ B ) /\ C ) /\ ( D \/ E )`] THEN SIMP_TAC[ MESON[] ` ((A/\B) /\ C) <=> A /\ B /\ C`]
THEN REWRITE_TAC [d3 ; voronoi_trg;IN_ELIM_THM] THEN 
 REWRITE_TAC [ MESON[ IN ; EQ_SYM_EQ ; DIST_SYM] `(!w. s w /\ ~(w = v0) ==> dist (x,v0) < dist (x,w))
                   <=> (!y. y IN s /\ ~(v0 = y) ==> dist (v0,x) < dist (x,y)) ` ] THEN
REWRITE_TAC[ MESON[] ` A /\ B /\ C /\ ( D \/ ~A) <=> A /\ B /\ C /\ D` ; DIST_SYM ; EQ_SYM_EQ ]
 THEN REWRITE_TAC[obstructed] THEN REWRITE_TAC[ MESON[] ` a /\ b /\c/\( d \/ e ) <=> a /\ b /\ c /\ d \/ a /\ b /\ c /\ e `]
THEN SIMP_TAC[MESON[]` (!y. y IN s /\ ~(v0 = y) ==> dist (v0,x) < dist (x,y)) /\
     dist (v0,x) < &2 /\
     ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
     ~(!y. y IN s /\
           ~(v0 = y) /\
           ~(?bar. bar IN barrier s /\
                   ~(conv0_2 {x, y} INTER conv_trg bar = {}))
           ==> dist (v0,x) < dist (x,y)) <=> F `] THEN 
REWRITE_TAC[MESON[] ` 
     ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
     (?bar. bar IN barrier s /\ ~(conv0_2 {v0, x} INTER conv_trg bar = {})) 
  <=> (?bar. bar IN barrier s /\ ~(conv0_2 {v0, x} INTER conv_trg bar = {}) /\
  ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}))`]
THEN GEN_TAC THEN REWRITE_TAC[TAUT `( a /\ b /\ c ==> d) = ( c ==> ( a /\ b) ==> d )`] 
THEN MP_TAC chuachungminh THEN REWRITE_TAC[usefull] THEN 
UNDISCH_TAC `center_pac s v0 /\
      Z = UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s} /\
      X =
      UNIONS
      {aff_gt {v0} {v1, v2, v3} INTER
       aff_le {v1, v2, v3} {v0} INTER
       voronoi2 v0 s | {v0, v1, v2, v3} IN Q_SYS s}` THEN
 REWRITE_TAC[ TAUT ` a ==> b ==> c ==> d ==> e <=> 
  b ==> a ==> c ==> d ==> e `] THEN DISCH_TAC THEN POP_ASSUM_LIST REWRITE_TAC 
THEN DISCH_TAC THEN REWRITE_TAC[ MESON[] ` a ==> b ==> c <=> a /\ b ==> c `]
THEN REWRITE_TAC[ MESON[] ` ( ? x . p x ) /\ ng <=> ( ? x. p x /\ ng )`] THEN 
REWRITE_TAC[MESON [IN ; EQ_SYM_EQ ; DIST_SYM ] ` ( !y. (y IN s /\ ~(v0 = y) ==> dist (v0,x) < dist (x,y))) <=>
  ( !y. ( s y /\ ~(y = v0) ==> dist (x,v0) < dist (x,y)) ) `] THEN 
PURE_ONCE_REWRITE_TAC[SET_RULE ` (!y. s y /\ ~(y = v0) ==> dist (x,v0) < dist (x,y)) <=>   ( x IN { x | !y. s y /\ ~(y = v0) ==> dist (x,v0) < dist (x,y)} )`]
THEN REWRITE_TAC [ MESON[voronoi_trg] ` ( x IN {x | !y. s y /\ ~(y = v0) ==> dist (x,v0) < dist (x,y)} )
  <=> x IN voronoi_trg v0 s `] THEN REWRITE_TAC [ GSYM d3 ] THEN 
PURE_ONCE_REWRITE_TAC[ SET_RULE ` x IN voronoi_trg v0 s /\
        d3 v0 x < &2 <=> x IN { x | x IN voronoi_trg v0 s /\ d3 v0 x < &2 } `] THEN
PURE_ONCE_REWRITE_TAC[ MESON[ trg_d3_sym] ` d3 v0 x = d3 x v0`] THEN 
PURE_ONCE_REWRITE_TAC[ MESON[voronoi2] `{x | x IN voronoi_trg v0 s /\ d3 x v0 < &2} = voronoi2 v0 s `]
 THEN REWRITE_TAC [ TAUT ` (( a /\ b /\ c)/\d)/\e <=>  a /\ b /\ c/\d/\e `] THEN 
PURE_ONCE_REWRITE_TAC [ TAUT `( bar IN barrier s /\
        ~(conv0_2 {v0, x} INTER conv_trg bar = {}) /\
        ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
        ~(v0 IN bar) /\
        x IN voronoi2 v0 s )
  =
  (      bar IN barrier s /\
         ~(conv0_2 {v0, x} INTER conv_trg bar = {}) /\
          ~(v0 IN bar) /\
           x IN voronoi2 v0 s /\ 
         ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) 
  )`] THEN MP_TAC tarski_arith THEN
PURE_ONCE_REWRITE_TAC[ SET_RULE ` conv_trg bar INTER conv0_2 {v0, x} = {} <=> 
  conv0_2 {v0, x} INTER  conv_trg bar = {} `] THEN 
ASM_REWRITE_TAC[ MESON[] ` (! x. p x ==> q x ) ==> ( ? x. p x ) ==> e 
  <=> (! x. p x ==> q x ) ==> ( ? x. p x /\ q x ) ==> e `]
(* have done *)
 THEN
REWRITE_TAC[ MESON[barrier] `  (bar IN barrier s /\
             ~(conv0_2 {v0, x} INTER conv_trg bar = {}) /\
             ~(v0 IN bar) /\
             x IN voronoi2 v0 s /\
             ~(x IN
               UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s})) /\
            {v0} UNION bar IN Q_SYS s
  <=>    bar IN {{v1, v2, v3} | quasi_tri {v1, v2, v3} s \/
                     (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)} /\
             ~(conv0_2 {v0, x} INTER conv_trg bar = {}) /\
             ~(v0 IN bar) /\
             x IN voronoi2 v0 s /\
             ~(x IN
               UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
            {v0} UNION bar IN Q_SYS s `] THEN 
REWRITE_TAC[IN_ELIM_THM] THEN 
REWRITE_TAC[ MESON[] `(?v1 v2 v3.
          (quasi_tri {v1, v2, v3} s \/
           (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
          bar = {v1, v2, v3}) /\
     ~(conv0_2 {v0, x} INTER conv_trg bar = {}) /\
     ~(v0 IN bar) /\
     x IN voronoi2 v0 s /\
     ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
     {v0} UNION bar IN Q_SYS s <=>
     (?v1 v2 v3.
          (quasi_tri {v1, v2, v3} s \/
           (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
          bar = {v1, v2, v3} /\
          ~(conv0_2 {v0, x} INTER conv_trg {v1, v2, v3} = {}) /\
          ~(v0 IN {v1, v2, v3}) /\
          x IN voronoi2 v0 s /\
          ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
          {v0} UNION {v1, v2, v3} IN Q_SYS s) `] THEN 
REWRITE_TAC[MESON [] `(?bar v1 v2 v3.
          (quasi_tri {v1, v2, v3} s \/
           (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
          bar = {v1, v2, v3} /\
          ~(conv0_2 {v0, x} INTER conv_trg {v1, v2, v3} = {}) /\
          ~(v0 IN {v1, v2, v3}) /\
          x IN voronoi2 v0 s /\
          ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
          {v0} UNION {v1, v2, v3} IN Q_SYS s) <=>
     (?v1 v2 v3.
          (quasi_tri {v1, v2, v3} s \/
           (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
          ~(conv0_2 {v0, x} INTER conv_trg {v1, v2, v3} = {}) /\
          ~(v0 IN {v1, v2, v3}) /\
          x IN voronoi2 v0 s /\
          ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
          {v0} UNION {v1, v2, v3} IN Q_SYS s) `] THEN 
REWRITE_TAC[ SET_RULE` ~ (a INTER b ={}) <=> (? i j. i IN a /\ j IN b /\ i = j)`] THEN 






PURE_ONCE_REWRITE_TAC[SET_RULE ` ~ ( a INTER b = {}) <=> ( ? x y. x IN a /\ y IN b /\ x = y)`] THEN
REWRITE_TAC[simp_def; simpl_conv3] THEN
REWRITE_TAC[IN_ELIM_THM] THEN 
REWRITE_TAC[MESON[] `(?i j.
          (?t. &0 < t /\ t < &1 /\ i = t % v0 + (&1 - t) % x) /\
          (?a b c.
               &0 <= a /\
               &0 <= b /\
               &0 <= c /\
               a + b + c = &1 /\
               j = a % v1 + b % v2 + c % v3) /\
          i = j) <=>
     (?t a b c.
          &0 < t /\
          t < &1 /\
          &0 <= a /\
          &0 <= b /\
          &0 <= c /\
          a + b + c = &1 /\
          t % v0 + (&1 - t) % x = a % v1 + b % v2 + c % v3) `] THEN 
REWRITE_TAC[ VECTOR_ARITH ` t % v0 + (&1 - t) % x = a % v1 + b % v2 + c % v3
  <=> (&1 - t ) % x = -- ( t % v0 ) + a % v1 + b % v2 + c % v3 `] THEN 
REWRITE_TAC[ VECTOR_ARITH ` --( t % v0 ) = ( -- t) % v0 `] THEN 
REWRITE_TAC [ REAL_ARITH ` t < &1 <=> &0 < &1 - t `] THEN 
PURE_ONCE_REWRITE_TAC[MESON[ REAL_FIELD ` &0 < &1 - t ==> ( ! a . a = (&1 - t ) * ( a / ( &1 - t )))`]`
  &0 < &1 - t <=> &0 < &1 - t /\ --t = (&1 - t) * ( --t ) / (&1 - t) /\  a = (&1 - t) * a / (&1 - t) 
  /\  b = (&1 - t) * b / (&1 - t) /\  c = (&1 - t) * c / (&1 - t)`] THEN 
REWRITE_TAC[MESON[]` (?t a b c.
               &0 < t /\
               (&0 < &1 - t /\
                --t = (&1 - t) * --t / (&1 - t) /\
                a = (&1 - t) * a / (&1 - t) /\
                b = (&1 - t) * b / (&1 - t) /\
                c = (&1 - t) * c / (&1 - t)) /\
               &0 <= a /\
               &0 <= b /\
               &0 <= c /\
               a + b + c = &1 /\
               (&1 - t) % x = --t % v0 + a % v1 + b % v2 + c % v3)
  <=> (?t a b c.
               &0 < t /\
               (&0 < &1 - t /\
                --t = (&1 - t) * --t / (&1 - t) /\
                a = (&1 - t) * a / (&1 - t) /\
                b = (&1 - t) * b / (&1 - t) /\
                c = (&1 - t) * c / (&1 - t)) /\
               &0 <= a /\
               &0 <= b /\
               &0 <= c /\
               a + b + c = &1 /\
               (&1 - t) % x = ((&1 - t) * --t / (&1 - t)) % v0 + ((&1 - t) * a / (&1 - t)) % v1 + ((&1 - t) * b / (&1 - t)) % v2 +((&1 - t) * c / (&1 - t)) % v3)`] THEN 
REWRITE_TAC[VECTOR_ARITH` ((&1 - t) * --t / (&1 - t)) % v0 +
               ((&1 - t) * a / (&1 - t)) % v1 +
               ((&1 - t) * b / (&1 - t)) % v2 +
               ((&1 - t) * c / (&1 - t)) % v3 
   =          (&1 - t ) % ( (--t / (&1 - t)) % v0 + (a / (&1 - t)) % v1 + (b / (&1 - t)) % v2 + (c / (&1 - t)) % v3)`] THEN 
PURE_ONCE_REWRITE_TAC[REAL_ARITH` &0 < a <=> &0 < a /\ ~ ( a = &0 )`] THEN 
REWRITE_TAC[MESON[MESON[VECTOR_MUL_LCANCEL_IMP]` ~ (( &1 - t) = &0 ) /\ (&1 - t) % x =
               (&1 - t) %
               (--t / (&1 - t) % v0 +
                a / (&1 - t) % v1 +
                b / (&1 - t) % v2 +
                c / (&1 - t) % v3) <=> ~ (( &1 - t) = &0 ) /\ (&1 - t) % x =
               (&1 - t) %
               (--t / (&1 - t) % v0 +
                a / (&1 - t) % v1 +
                b / (&1 - t) % v2 +
                c / (&1 - t) % v3)/\ x =
               (--t / (&1 - t) % v0 +
                a / (&1 - t) % v1 +
                b / (&1 - t) % v2 +
                c / (&1 - t) % v3) `] ` (&0 < t /\ ~(t = &0)) /\
               ((&0 < &1 - t /\ ~(&1 - t = &0)) /\
                --t = (&1 - t) * --t / (&1 - t) /\
                a = (&1 - t) * a / (&1 - t) /\
                b = (&1 - t) * b / (&1 - t) /\
                c = (&1 - t) * c / (&1 - t)) /\
               &0 <= a /\
               &0 <= b /\
               &0 <= c /\
               a + b + c = &1 /\
               (&1 - t) % x =
               (&1 - t) %
               (--t / (&1 - t) % v0 +
                a / (&1 - t) % v1 +
                b / (&1 - t) % v2 +
                c / (&1 - t) % v3)
  <=> (&0 < t /\ ~(t = &0)) /\
               ((&0 < &1 - t /\ ~(&1 - t = &0)) /\
                --t = (&1 - t) * --t / (&1 - t) /\
                a = (&1 - t) * a / (&1 - t) /\
                b = (&1 - t) * b / (&1 - t) /\
                c = (&1 - t) * c / (&1 - t)) /\
               &0 <= a /\
               &0 <= b /\
               &0 <= c /\
               a + b + c = &1 /\
               (&1 - t) % x =
               (&1 - t) %
               (--t / (&1 - t) % v0 +
                a / (&1 - t) % v1 +
                b / (&1 - t) % v2 +
                c / (&1 - t) % v3) /\
     x =
     --t / (&1 - t) % v0 +
     a / (&1 - t) % v1 +
     b / (&1 - t) % v2 +
     c / (&1 - t) % v3 `] THEN 
REWRITE_TAC[ REAL_ARITH `(&0 < t /\ ~(t = &0)) <=> ( &0 < t )`] THEN 
REWRITE_TAC[ MESON[REAL_LT_IMP_NZ ; REAL_FIELD ` ~ ( a = &0 ) ==> ( ! b. b = a * b / a )`]`(&0 < &1 - t /\
                --t = (&1 - t) * --t / (&1 - t) /\
                a = (&1 - t) * a / (&1 - t) /\
                b = (&1 - t) * b / (&1 - t) /\
                c = (&1 - t) * c / (&1 - t)) <=> (&0 < &1 - t )`] THEN 
PURE_ONCE_REWRITE_TAC [ MESON[REAL_ARITH ` (! a . &0 < a ==> &0 <= a)` ; REAL_LE_DIV ] `
   &0 < t /\ &0 < &1 - t /\ &0 <= a /\ &0 <= b /\ &0 <= c /\ vc <=>
     &0 < t /\
     &0 < &1 - t /\
     &0 <= a /\
     &0 <= b /\
     &0 <= c /\
     &0 <= t / (&1 - t) /\
     &0 <= a / (&1 - t) /\
     &0 <= b / (&1 - t) /\
     &0 <= c / (&1 - t) /\
     vc `] THEN 
REWRITE_TAC[REAL_ARITH` &0 <= t / (&1 - t) <=> --t /(&1 - t ) <= &0 `] THEN 
PURE_ONCE_REWRITE_TAC[ MESON[ REAL_FIELD ` a + b + c = &1 /\ &0 < &1 - t ==> --t / (&1 - t) +
               a / (&1 - t) +
               b / (&1 - t) +
               c / (&1 - t) = &1 `]
  ` &0 < t /\
               &0 < &1 - t /\
               &0 <= a /\
               &0 <= b /\
               &0 <= c /\
               --t / (&1 - t) <= &0 /\
               &0 <= a / (&1 - t) /\
               &0 <= b / (&1 - t) /\
               &0 <= c / (&1 - t) /\
               a + b + c = &1 /\ vc  <=>
  &0 < t /\
               &0 < &1 - t /\
               &0 <= a /\
               &0 <= b /\
               &0 <= c /\
               --t / (&1 - t) <= &0 /\
               &0 <= a / (&1 - t) /\
               &0 <= b / (&1 - t) /\
               &0 <= c / (&1 - t) /\
               a + b + c = &1 /\ --t / (&1 - t) +
               a / (&1 - t) +
               b / (&1 - t) +
               c / (&1 - t) = &1 /\ vc`] THEN REWRITE_TAC[ GSYM simp_def] THEN 
PURE_ONCE_REWRITE_TAC[MESON[]` (?v1 v2 v3.
          (quasi_tri {v1, v2, v3} s \/
           (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
          (?t a b c.
               &0 < t /\
               &0 < &1 - t /\
               &0 <= a /\
               &0 <= b /\
               &0 <= c /\
               --t / (&1 - t) <= &0 /\
               &0 <= a / (&1 - t) /\
               &0 <= b / (&1 - t) /\
               &0 <= c / (&1 - t) /\
               a + b + c = &1 /\
               --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) =
               &1 /\
               (&1 - t) % x =
               (&1 - t) %
               (--t / (&1 - t) % v0 +
                a / (&1 - t) % v1 +
                b / (&1 - t) % v2 +
                c / (&1 - t) % v3) /\
               x =
               --t / (&1 - t) % v0 +
               a / (&1 - t) % v1 +
               b / (&1 - t) % v2 +
               c / (&1 - t) % v3) /\
          ~(v0 IN {v1, v2, v3}) /\
          x IN voronoi2 v0 s /\
          ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
          {v0} UNION {v1, v2, v3} IN Q_SYS s)
  <=> (? a b v1 v2. (?v3 t c.
          (quasi_tri {v1, v2, v3} s \/
           (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
         
               &0 < t /\
               &0 < &1 - t /\
               &0 <= a /\
               &0 <= b /\
               &0 <= c /\
               --t / (&1 - t) <= &0 /\
               &0 <= a / (&1 - t) /\
               &0 <= b / (&1 - t) /\
               &0 <= c / (&1 - t) /\
               a + b + c = &1 /\
               --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) =
               &1 /\
               (&1 - t) % x =
               (&1 - t) %
               (--t / (&1 - t) % v0 +
                a / (&1 - t) % v1 +
                b / (&1 - t) % v2 +
                c / (&1 - t) % v3) /\
               x =
               --t / (&1 - t) % v0 +
               a / (&1 - t) % v1 +
               b / (&1 - t) % v2 +
               c / (&1 - t) % v3 /\
          ~(v0 IN {v1, v2, v3}) /\
          x IN voronoi2 v0 s /\
          ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
          {v0} UNION {v1, v2, v3} IN Q_SYS s))`] THEN 
DISCH_TAC THEN 
MATCH_MP_TAC (MESON[REAL_ARITH ` ! a b. a <= b \/ b <= a `] ` ( ! (a:real) b (v1:real^3) (v2:real^3). Q a b v1 v2 = Q b a v2 v1 ) /\
  ((? (a:real) (b:real) (v1:real^3) (v2:real^3). Q a b v1 v2 ) /\ (? (a:real) b (v1:real^3) (v2:real^3). a <= b /\ Q a b v1 v2) ==> c) ==> ((? a b (v1:real^3) (v2:real^3). Q a b v1 v2) ==> c ) `) THEN 
CONJ_TAC THEN REPEAT GEN_TAC THEN 
REWRITE_TAC [ MESON[]` (quasi_tri {v2, v1, v3} s \/ (?v4. {v2, v1, v3} UNION {v4} IN Q_SYS s)) /\
      &0 < t /\
      &0 < &1 - t /\
      &0 <= b /\
      &0 <= a /\
      &0 <= c /\
      --t / (&1 - t) <= &0 /\
      &0 <= b / (&1 - t) /\
      &0 <= a / (&1 - t) /\
      &0 <= c / (&1 - t) /\
      b + a + c = &1 /\
      --t / (&1 - t) + b / (&1 - t) + a / (&1 - t) + c / (&1 - t) = &1 /\ nnn
  <=> (quasi_tri {v2, v1, v3} s \/ (?v4. {v2, v1, v3} UNION {v4} IN Q_SYS s)) /\
      &0 < t /\
      &0 < &1 - t /\
      &0 <= b /\
      &0 <= a /\
      &0 <= c /\
      --t / (&1 - t) <= &0 /\
      &0 <= b / (&1 - t) /\
      &0 <= a / (&1 - t) /\
      &0 <= c / (&1 - t) /\
     ( b + a + c = &1 /\
      --t / (&1 - t) + b / (&1 - t) + a / (&1 - t) + c / (&1 - t) = &1 )/\ nnn` ] THEN 
REWRITE_TAC[ MESON[]` ( a <=> b ) <=> ( a ==> b ) /\ ( b==> a )`] THEN REWRITE_TAC[]);;
e (CONJ_TAC );; (*truong *)
e (DISCH_TAC THEN 
ONCE_REWRITE_TAC[ REAL_ARITH ` (b + a + c = &1 /\
      --t / (&1 - t) + b / (&1 - t) + a / (&1 - t) + c / (&1 - t) = &1) 
  <=> (a + b + c = &1 /\
           --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1) `] THEN 
REWRITE_TAC [VECTOR_ARITH ` (&1 - t) % x =
     (&1 - t) %
     (--t / (&1 - t) % v0 +
      b / (&1 - t) % v2 +
      a / (&1 - t) % v1 +
      c / (&1 - t) % v3) <=> (&1 - t) % x =
          (&1 - t) %
          (--t / (&1 - t) % v0 +
           a / (&1 - t) % v1 +
           b / (&1 - t) % v2 +
           c / (&1 - t) % v3) `] THEN 
REWRITE_TAC[ VECTOR_ARITH ` x =
     --t / (&1 - t) % v0 +
     b / (&1 - t) % v2 +
     a / (&1 - t) % v1 +
     c / (&1 - t) % v3 <=> x =
          --t / (&1 - t) % v0 +
          a / (&1 - t) % v1 +
          b / (&1 - t) % v2 +
          c / (&1 - t) % v3 `] THEN 
REWRITE_TAC [ SET_RULE ` ! v1 v2 (v3:real^3 ). { v1, v2 , v3} = { v2 , v1 , v3}`] THEN 
FIRST_X_ASSUM MP_TAC THEN MESON_TAC[] THEN 
DISCH_TAC THEN ONCE_REWRITE_TAC[  REAL_ARITH ` ! a b (c:real). (a + b + c = &1 /\
      --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1)
  
  <=> (b + a + c = &1 /\
           --t / (&1 - t) + b / (&1 - t) + a / (&1 - t) + c / (&1 - t) = &1) `] THEN 
ONCE_REWRITE_TAC [VECTOR_ARITH ` (&1 - t) % x =
          (&1 - t) %
          (--t / (&1 - t) % v0 +
           a / (&1 - t) % v1 +
           b / (&1 - t) % v2 +
           c / (&1 - t) % v3)  <=> (&1 - t) % x =
     (&1 - t) %
     (--t / (&1 - t) % v0 +
      b / (&1 - t) % v2 +
      a / (&1 - t) % v1 +
      c / (&1 - t) % v3)` ] THEN 
ONCE_REWRITE_TAC [VECTOR_ARITH ` x =
     --t / (&1 - t) % v0 +
     a / (&1 - t) % v1 +
     b / (&1 - t) % v2 +
     c / (&1 - t) % v3  <=> x =
          --t / (&1 - t) % v0 +
          b / (&1 - t) % v2 +
          a / (&1 - t) % v1 +
          c / (&1 - t) % v3` ] THEN 
ONCE_REWRITE_TAC [ SET_RULE ` ! v1 v2 (v3:real^3). {v1 , v2 ,v3} = { v2, v1, v3}`] THEN 
REWRITE_TAC[ MESON[ SET_RULE ` { a , b, c} = { b, a , c}`]` {v1, v0, v2} IN barrier s
  <=> {v0, v1, v2} IN barrier s `] THEN 
FIRST_X_ASSUM MP_TAC THEN MESON_TAC[]);;  (* TRUONG TRI *)



e (DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_ARITH ` !a b c.
         a + b + c = &1 /\
         --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1 <=>
         b + a + c = &1 /\
         --t / (&1 - t) + b / (&1 - t) + a / (&1 - t) + c / (&1 - t) = &1 `;
  VECTOR_ARITH ` (&1 - t) % x =
 (&1 - t) %
 (--t / (&1 - t) % v0 +
  a / (&1 - t) % v1 +
  b / (&1 - t) % v2 +
  c / (&1 - t) % v3) <=> (&1 - t) % x 
  = ( &1 - t ) % (--t / (&1 - t) % v0  +
      b / (&1 - t) % v2 +
      a / (&1 - t) % v1 +
      c / (&1 - t) % v3 ) `; VECTOR_ARITH ` x =
 --t / (&1 - t) % v0 +
 a / (&1 - t) % v1 +
 b / (&1 - t) % v2 +
 c / (&1 - t) % v3 <=> x =
     --t / (&1 - t) % v0  +
     b / (&1 - t) % v2 +
     a / (&1 - t) % v1 +
     c / (&1 - t) % v3 `] THEN 
ONCE_REWRITE_TAC[  SET_RULE `! v1 v2 (v3:real^3). { v1, v2, v3} = {v2, v1 ,v3} `] THEN 
ONCE_REWRITE_TAC[MESON [SET_RULE ` ! a b c. { a, b, c} = {b, a, c}` ]`( ! a b c s. {a, b, c} IN
    barrier s <=> {b, a, c } IN barrier s) `] THEN FIRST_X_ASSUM MP_TAC THEN MESON_TAC[] );; 
e (MATCH_MP_TAC (MESON[]` ( b ==> c ) ==> ( a /\ b ==> c ) ` ) THEN 
REWRITE_TAC[ MESON[]` (?a b v1 v2. a <= b /\(?v3 t c. Q a b c v1 v2 v3 t )) <=>
  (? a b c v1 v2 v3 t. a <= b /\ Q a b c v1 v2 v3 t )`] THEN 


MATCH_MP_TAC (MESON[ REAL_ARITH ` ! a (b:real). a <= b \/ b <= a `; REAL_ARITH`! a b c:real. a <= b /\ b <= c ==> a <= c`] ` ( !(a:real) b (c:real) (v1:real^3) (v2:real^3) (v3:real^3) t.
  Q a b c v1 v2 v3 t <=> Q c b a v3 v2 v1 t ) /\ ((? (a:real) b (c:real) (v1:real^3) (v2:real^3) (v3:real^3) t.
  a <= b /\ a <= c /\ Q a b c v1 v2 v3 t ) ==> last )  ==> ((? (a:real) b (c:real) (v1:real^3) (v2:real^3) (v3:real^3) t.
  a <= b /\  Q a b c v1 v2 v3 t ) ==> last ) `));;


(* THE RESULT IS:
Warning: inventing type variables
0..0..0..0..3..12..23..66..118..194..350..solved at 384
val it : goalstack = 1 subgoal (1 total)

  0 [`center_pac s v0 /\
      Z = UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s} /\
      X =
      UNIONS
      {aff_gt {v0} {v1, v2, v3} INTER
       aff_le {v1, v2, v3} {v0} INTER
       voronoi2 v0 s | {v0, v1, v2, v3} IN Q_SYS s}`]
  1 [`!bar. bar IN barrier s /\
            (?i j.
                 (?t. &0 < t /\ &0 < &1 - t /\ i = t % v0 + (&1 - t) % x) /\
                 j IN conv_trg bar /\
                 i = j) /\
            ~(v0 IN bar) /\
            x IN voronoi2 v0 s /\
            ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s})
            ==> {v0} UNION bar IN Q_SYS s`]

`(!a b c v1 v2 v3 t.
      (quasi_tri {v1, v2, v3} s \/ (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
      &0 < t /\
      &0 < &1 - t /\
      &0 <= a /\
      &0 <= b /\
      &0 <= c /\
      --t / (&1 - t) <= &0 /\
      &0 <= a / (&1 - t) /\
      &0 <= b / (&1 - t) /\
      &0 <= c / (&1 - t) /\
      (a + b + c = &1 /\
       --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1) /\
      (&1 - t) % x =
      (&1 - t) %
      (--t / (&1 - t) % v0 +
       a / (&1 - t) % v1 +
       b / (&1 - t) % v2 +
       c / (&1 - t) % v3) /\
      x =
      --t / (&1 - t) % v0 +
      a / (&1 - t) % v1 +
      b / (&1 - t) % v2 +
      c / (&1 - t) % v3 /\
      ~(v0 IN {v1, v2, v3}) /\
      x IN voronoi2 v0 s /\
      ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
      {v0} UNION {v1, v2, v3} IN Q_SYS s <=>
      (quasi_tri {v3, v2, v1} s \/ (?v4. {v3, v2, v1} UNION {v4} IN Q_SYS s)) /\
      &0 < t /\
      &0 < &1 - t /\
      &0 <= c /\
      &0 <= b /\
      &0 <= a /\
      --t / (&1 - t) <= &0 /\
      &0 <= c / (&1 - t) /\
      &0 <= b / (&1 - t) /\
      &0 <= a / (&1 - t) /\
      (c + b + a = &1 /\
       --t / (&1 - t) + c / (&1 - t) + b / (&1 - t) + a / (&1 - t) = &1) /\
      (&1 - t) % x =
      (&1 - t) %
      (--t / (&1 - t) % v0 +
       c / (&1 - t) % v3 +
       b / (&1 - t) % v2 +
       a / (&1 - t) % v1) /\
      x =
      --t / (&1 - t) % v0 +
      c / (&1 - t) % v3 +
      b / (&1 - t) % v2 +
      a / (&1 - t) % v1 /\
      ~(v0 IN {v3, v2, v1}) /\
      x IN voronoi2 v0 s /\
      ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
      {v0} UNION {v3, v2, v1} IN Q_SYS s) /\
 ((?a b c v1 v2 v3 t.
       a <= b /\
       a <= c /\
       (quasi_tri {v1, v2, v3} s \/
        (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
       &0 < t /\
       &0 < &1 - t /\
       &0 <= a /\
       &0 <= b /\
       &0 <= c /\
       --t / (&1 - t) <= &0 /\
       &0 <= a / (&1 - t) /\
       &0 <= b / (&1 - t) /\
       &0 <= c / (&1 - t) /\
       (a + b + c = &1 /\
        --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1) /\
       (&1 - t) % x =
       (&1 - t) %
       (--t / (&1 - t) % v0 +
        a / (&1 - t) % v1 +
        b / (&1 - t) % v2 +
        c / (&1 - t) % v3) /\
       x =
       --t / (&1 - t) % v0 +
       a / (&1 - t) % v1 +
       b / (&1 - t) % v2 +
       c / (&1 - t) % v3 /\
       ~(v0 IN {v1, v2, v3}) /\
       x IN voronoi2 v0 s /\
       ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
       {v0} UNION {v1, v2, v3} IN Q_SYS s)
  ==> x IN
      UNIONS
      {aff_gt {v0} {v1, v2, v3} INTER
       aff_le {v1, v2, v3} {v0} INTER
       {x | x IN voronoi2 v0 s} | {v0, v1, v2, v3} IN Q_SYS s})`


*)
e (CONJ_TAC THEN REPEAT GEN_TAC);;
e (MESON_TAC[REAL_ARITH ` !a b c.
         a + b + c = &1 /\
         --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1 <=>
         c + b + a = &1 /\
         --t / (&1 - t) + c / (&1 - t) + b / (&1 - t) + a / (&1 - t) = &1 `;
  VECTOR_ARITH ` (&1 - t) % x =
 (&1 - t) %
 (--t / (&1 - t) % v0 +
  a / (&1 - t) % v1 +
  b / (&1 - t) % v2 +
  c / (&1 - t) % v3) <=> (&1 - t) % x 
  = ( &1 - t ) % (--t / (&1 - t) % v0 +
      c / (&1 - t) % v3 +
      b / (&1 - t) % v2 +
      a / (&1 - t) % v1) `; VECTOR_ARITH ` x =
 --t / (&1 - t) % v0 +
 a / (&1 - t) % v1 +
 b / (&1 - t) % v2 +
 c / (&1 - t) % v3 <=> x =
     --t / (&1 - t) % v0 +
     c / (&1 - t) % v3 +
     b / (&1 - t) % v2 +
     a / (&1 - t) % v1 ` ;MESON[SET_RULE ` ! a b c. { a, b, c} = {c, b, a}` ]`( ! a b c s. {a, b, c} IN
    barrier s <=> {c, b, a } IN barrier s) ` ;  SET_RULE `! v1 v2 (v3:real^3). { v1, v2, v3} = {v3, v2 ,v1} `]);;
e (REWRITE_TAC[ MESON[ REAL_ARITH ` ! a. &0 <= a <=> &0 = a \/ &0 < a `] ` 
  a <= b /\
     a <= c /\
     (quasi_tri {v1, v2, v3} s \/ (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
     &0 < t /\
     &0 < &1 - t /\
     &0 <= a /\
     ccc <=>
     &0 = a /\
     a <= b /\
     a <= c /\
     (quasi_tri {v1, v2, v3} s \/ (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
     &0 < t /\
     &0 < &1 - t /\
     ccc \/
     &0 < a /\
     a <= b /\
     a <= c /\
     (quasi_tri {v1, v2, v3} s \/ (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
     &0 < t /\
     &0 < &1 - t /\
     ccc `]);;
e (REWRITE_TAC[ MESON[REAL_FIELD ` &0 = a ==> a / b = &0 `; VECTOR_ARITH`! v w. &0 % v + w = w `] `
  &0 = a /\
     a <= b /\
     a <= c /\
     (quasi_tri {v1, v2, v3} s \/ (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
     &0 < t /\
     &0 < &1 - t /\
     &0 <= b /\
     &0 <= c /\
     --t / (&1 - t) <= &0 /\
     &0 <= a / (&1 - t) /\
     &0 <= b / (&1 - t) /\
     &0 <= c / (&1 - t) /\
     (a + b + c = &1 /\
      --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1) /\
     (&1 - t) % x =
     (&1 - t) %
     (--t / (&1 - t) % v0 +
      a / (&1 - t) % v1 +
      b / (&1 - t) % v2 +
      c / (&1 - t) % v3) /\
     x =
     --t / (&1 - t) % v0 +
     a / (&1 - t) % v1 +
     b / (&1 - t) % v2 +
     c / (&1 - t) % v3 /\
     last <=>
     a <= b /\
     a <= c /\
     (quasi_tri {v1, v2, v3} s \/ (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)) /\
     &0 < t /\
     &0 < &1 - t /\
     &0 <= b /\
     &0 <= c /\
     --t / (&1 - t) <= &0 /\
     &0 <= a / (&1 - t) /\
     &0 <= b / (&1 - t) /\
     &0 <= c / (&1 - t) /\
     (a + b + c = &1 /\
      --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1) /\
     (&1 - t) % x =
     (&1 - t) %
     (--t / (&1 - t) % v0 +
      a / (&1 - t) % v1 +
      b / (&1 - t) % v2 +
      c / (&1 - t) % v3) /\
     (&0 = a /\
      x =
      --t / (&1 - t) % v0 + &0 % v1 + b / (&1 - t) % v2 + c / (&1 - t) % v3) /\
     last `]);;
e (REWRITE_TAC[ MESON[REAL_FIELD ` &0 = a ==> a / b = &0 `; VECTOR_ARITH`! v w. &0 % v + w = w `] `
  x =
       --t / (&1 - t) % v0 + &0 % v1 + b / (&1 - t) % v2 + c / (&1 - t) % v3
  <=> x = --t / (&1 - t) % v0 + b / (&1 - t) % v2 + c / (&1 - t) % v3 `]);;
e (REWRITE_TAC[ MESON[ SET_RULE ` {v0} UNION {v1, v2, v3} = {v0, v2, v3} UNION {v1 } ` ; 
  barrier ] ` (&0 = a /\
       x = --t / (&1 - t) % v0 + b / (&1 - t) % v2 + c / (&1 - t) % v3) /\
      ~(v0 IN {v1, v2, v3}) /\
      x IN voronoi2 v0 s /\
      ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
      {v0} UNION {v1, v2, v3} IN Q_SYS s
  <=> (&0 = a /\
       x = --t / (&1 - t) % v0 + b / (&1 - t) % v2 + c / (&1 - t) % v3) /\
      ~(v0 IN {v1, v2, v3}) /\
      x IN voronoi2 v0 s /\ {v0, v2, v3} UNION {v1} IN Q_SYS s /\ 
      ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
      {v0} UNION {v1, v2, v3} IN Q_SYS s`]);;

e (ONCE_REWRITE_TAC[ MESON[ MESON[barrier; SET_RULE ` {v0, v2, v3} UNION {v1} IN Q_SYS s ==> {v0, v2, v3} IN {{v1, v2, v3} | quasi_tri {v1, v2, v3} s \/
                         (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s)} `]` {v0, v2, v3} UNION {v1} IN Q_SYS s ==> {v0, v2, v3} IN barrier s `]
  ` {v0, v2, v3} UNION {v1} IN Q_SYS s <=>{v0, v2, v3} UNION {v1} IN Q_SYS s  /\ {v0, v2, v3} IN barrier s `]);;

e (REWRITE_TAC[MESON[] ` --t / (&1 - t) <= &0 /\
     &0 <= a / (&1 - t) /\
     &0 <= b / (&1 - t) /\
     &0 <= c / (&1 - t) /\
     (a + b + c = &1 /\
      --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1) /\
     (&1 - t) % x =
     (&1 - t) %
     (--t / (&1 - t) % v0 +
      a / (&1 - t) % v1 +
      b / (&1 - t) % v2 +
      c / (&1 - t) % v3) /\
     (&0 = a /\
      x = --t / (&1 - t) % v0 + b / (&1 - t) % v2 + c / (&1 - t) % v3) /\
     ~(v0 IN {v1, v2, v3}) /\
     x IN voronoi2 v0 s /\
     ({v0, v2, v3} UNION {v1} IN Q_SYS s /\ {v0, v2, v3} IN barrier s) /\
     ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
     {v0} UNION {v1, v2, v3} IN Q_SYS s <=>
     &0 <= a / (&1 - t) /\
     {v0, v2, v3} UNION {v1} IN Q_SYS s /\
     {v0} UNION {v1, v2, v3} IN Q_SYS s /\
     ~(v0 IN {v1, v2, v3}) /\
     x IN voronoi2 v0 s /\
     (a + b + c = &1 /\
      --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1) /\
     (&1 - t) % x =
     (&1 - t) %
     (--t / (&1 - t) % v0 +
      a / (&1 - t) % v1 +
      b / (&1 - t) % v2 +
      c / (&1 - t) % v3) /\
     (&0 = a /\
      &0 <= b / (&1 - t) /\
      &0 <= c / (&1 - t) /\
      --t / (&1 - t) <= &0 /\
      {v0, v2, v3} IN barrier s /\
      x = --t / (&1 - t) % v0 + b / (&1 - t) % v2 + c / (&1 - t) % v3) /\
     ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) `]);;


(* RESULT: goalstack = 1 subgoal (1 total)

  0 [`center_pac s v0 /\
      Z = UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s} /\
      X =
      UNIONS
      {aff_gt {v0} {v1, v2, v3} INTER
       aff_le {v1, v2, v3} {v0} INTER
       voronoi2 v0 s | {v0, v1, v2, v3} IN Q_SYS s}`]
  1 [`!bar. bar IN barrier s /\
            (?i j.
                 (?t. &0 < t /\ &0 < &1 - t /\ i = t % v0 + (&1 - t) % x) /\
                 j IN conv_trg bar /\
                 i = j) /\
            ~(v0 IN bar) /\
            x IN voronoi2 v0 s /\
            ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s})
            ==> {v0} UNION bar IN Q_SYS s`]

`(?a b c v1 v2 v3 t.
      a <= b /\
      a <= c /\
      (quasi_tri {v1, v2, v3} s \/
       (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s /\ {v1, v2, v3} IN barrier s)) /\
      &0 < t /\
      &0 < &1 - t /\
      &0 <= b /\
      &0 <= c /\
      &0 <= a / (&1 - t) /\
      {v0, v2, v3} UNION {v1} IN Q_SYS s /\
      {v0} UNION {v1, v2, v3} IN Q_SYS s /\
      ~(v0 IN {v1, v2, v3}) /\
      x IN voronoi2 v0 s /\
      (a + b + c = &1 /\
       --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1) /\
      (&1 - t) % x =
      (&1 - t) %
      (--t / (&1 - t) % v0 +
       a / (&1 - t) % v1 +
       b / (&1 - t) % v2 +
       c / (&1 - t) % v3) /\
      (&0 = a /\
       &0 <= b / (&1 - t) /\
       &0 <= c / (&1 - t) /\
       --t / (&1 - t) <= &0 /\
       {v0, v2, v3} IN barrier s /\
       x = --t / (&1 - t) % v0 + b / (&1 - t) % v2 + c / (&1 - t) % v3) /\
      ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) \/
      &0 < a /\
      a <= b /\
      a <= c /\
      (quasi_tri {v1, v2, v3} s \/
       (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s /\ {v1, v2, v3} IN barrier s)) /\
      &0 < t /\
      &0 < &1 - t /\
      &0 <= b /\
      &0 <= c /\
      --t / (&1 - t) <= &0 /\
      &0 <= a / (&1 - t) /\
      &0 <= b / (&1 - t) /\
      &0 <= c / (&1 - t) /\
      (a + b + c = &1 /\
       --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1) /\
      (&1 - t) % x =
      (&1 - t) %
      (--t / (&1 - t) % v0 +
       a / (&1 - t) % v1 +
       b / (&1 - t) % v2 +
       c / (&1 - t) % v3) /\
      x =
      --t / (&1 - t) % v0 +
      a / (&1 - t) % v1 +
      b / (&1 - t) % v2 +
      c / (&1 - t) % v3 /\
      ~(v0 IN {v1, v2, v3}) /\
      x IN voronoi2 v0 s /\
      ~(x IN UNIONS {aff_ge {v0} {v1, v2} | {v0, v1, v2} IN barrier s}) /\
      {v0} UNION {v1, v2, v3} IN Q_SYS s)
 ==> x IN
     UNIONS
     {aff_gt {v0} {v1, v2, v3} INTER
      aff_le {v1, v2, v3} {v0} INTER
      {x | x IN voronoi2 v0 s} | {v0, v1, v2, v3} IN Q_SYS s}` *)

e (REWRITE_TAC[ IN_UNIONS; IN_ELIM_THM]);;
e (REWRITE_TAC[MESON[]` (?t. (?v0 v1 v2. {v0, v1, v2} IN barrier s /\ t = aff_ge {v0} {v1, v2}) /\
          x IN t) <=>
     (?v0 v1 v2. {v0, v1, v2} IN barrier s /\ x IN aff_ge {v0} {v1, v2}) `]);;
e (REWRITE_TAC[simp_def; IN_ELIM_THM]);;
e (REWRITE_TAC[ MESON[]`
  (a + b + c = &1 /\
      --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1) /\
     (&1 - t) % x =
     (&1 - t) %
     (--t / (&1 - t) % v0 +
      a / (&1 - t) % v1 +
      b / (&1 - t) % v2 +
      c / (&1 - t) % v3) /\
     ( &0 = a /\
     &0 <= b / (&1 - t) /\
     &0 <= c / (&1 - t) /\
     --t / (&1 - t) <= &0 /\
     {v0, v2, v3} IN barrier s /\
     x = --t / (&1 - t) % v0 + b / (&1 - t) % v2 + c / (&1 - t) % v3 ) /\ last  <=>
     (&0 = a /\
      a + b + c = &1 /\
      --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1) /\
     (&1 - t) % x =
     (&1 - t) %
     (--t / (&1 - t) % v0 +
      a / (&1 - t) % v1 +
      b / (&1 - t) % v2 +
      c / (&1 - t) % v3) /\
     &0 <= b / (&1 - t) /\
     &0 <= c / (&1 - t) /\
     --t / (&1 - t) <= &0 /\
     {v0, v2, v3} IN barrier s /\
     x = --t / (&1 - t) % v0 + b / (&1 - t) % v2 + c / (&1 - t) % v3 /\ last `]);;
e (REWRITE_TAC[ REAL_FIELD ` (&0 = a /\
       a + b + c = &1 /\
       --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1)
  <=> (&0 = a /\
       b + c = &1 /\
       --t / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1) `]);;

e (SIMP_TAC[MESON[] ` a <= b /\
      a <= c /\
      (quasi_tri {v1, v2, v3} s \/
       (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s /\ {v1, v2, v3} IN barrier s)) /\
      &0 < t /\
      &0 < &1 - t /\
      &0 <= b /\
      &0 <= c /\
      &0 <= a / (&1 - t) /\
      {v0, v2, v3} UNION {v1} IN Q_SYS s /\
      {v0} UNION {v1, v2, v3} IN Q_SYS s /\
      ~(v0 IN {v1, v2, v3}) /\
      x IN voronoi2 v0 s /\
      (&0 = a /\
       b + c = &1 /\
       --t / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1) /\
      (&1 - t) % x =
      (&1 - t) %
      (--t / (&1 - t) % v0 +
       a / (&1 - t) % v1 +
       b / (&1 - t) % v2 +
       c / (&1 - t) % v3) /\
      &0 <= b / (&1 - t) /\
      &0 <= c / (&1 - t) /\
      --t / (&1 - t) <= &0 /\
      {v0, v2, v3} IN barrier s /\
      x = --t / (&1 - t) % v0 + b / (&1 - t) % v2 + c / (&1 - t) % v3 /\
      ~(?v0 v1 v2.
            {v0, v1, v2} IN barrier s /\
            (?u v w.
                 &0 <= v /\
                 &0 <= w /\
                 u + v + w = &1 /\
                 x = u % v0 + v % v1 + w % v2))  <=> F `]);; 






 e (REWRITE_TAC[ MESON []`&0 < a /\ a <= b /\ a <= c /\ last <=> ( &0 < a /\ a <= b /\ a <= c ) /\ last`;
  REAL_ARITH ` &0 < a /\ a <= b /\ a <= c <=> a <= b /\ a <= c /\ &0 < a /\ &0 < b /\ &0 < c `]);;
e (REWRITE_TAC[ MESON[] ` (a <= b /\ a <= c /\ &0 < a /\ &0 < b /\ &0 < c) /\
      (quasi_tri {v1, v2, v3} s \/
       (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s /\ {v1, v2, v3} IN barrier s)) /\
      &0 < t /\
      &0 < &1 - t /\ last 
  <=> a <= b /\ a <= c /\
      (quasi_tri {v1, v2, v3} s \/
       (?v4. {v1, v2, v3} UNION {v4} IN Q_SYS s /\ {v1, v2, v3} IN barrier s)) /\
     ( &0 < t /\  &0 < a /\ &0 < b /\ &0 < c /\
      &0 < &1 - t ) /\ last `]);;
e (REWRITE_TAC[ MESON[REAL_LT_DIV] ` (&0 < t /\ &0 < a /\ &0 < b /\ &0 < c /\ &0 < &1 - t)
  <=> (&0 < t /\ &0 < a /\ &0 < b /\ &0 < c /\ &0 < &1 - t /\
  &0 < a / ( &1 - t ) /\
  &0 < b / ( &1 - t ) /\
  &0 < c / ( &1 - t ) )`]);;
e (ONCE_REWRITE_TAC [ VECTOR_ARITH `  x =
      --t / (&1 - t) % v0 +
      a / (&1 - t) % v1 +
      b / (&1 - t) % v2 +
      c / (&1 - t) % v3 <=>  x =
      --t / (&1 - t) % v0 +
      a / (&1 - t) % v1 +
      b / (&1 - t) % v2 +
      c / (&1 - t) % v3 /\  x =
     
      a / (&1 - t) % v1 +
      b / (&1 - t) % v2 +
      c / (&1 - t) % v3 +  --t / (&1 - t) % v0 `; 
  REAL_ARITH `  --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1 <=> 
  --t / (&1 - t) + a / (&1 - t) + b / (&1 - t) + c / (&1 - t) = &1 /\ 
  a / (&1 - t) + b / (&1 - t) + c / (&1 - t) + ( --t / (&1 - t)) = &1 `]);;
e (ONCE_REWRITE_TAC[ MESON[] `(?t. (?v1 v2 v3 v0 s.
               {v0, v1, v2, v3} IN Q_SYS s /\
               t =
               {t | ?x y z w.
                        &0 < y /\
                        &0 < z /\
                        &0 < w /\
                        x + y + z + w = &1 /\
                        t = x % v0 + y % v1 + z % v2 + w % v3} INTER
               {t | ?a b c d.
                        d <= &0 /\
                        a + b + c + d = &1 /\
                        t = a % v1 + b % v2 + c % v3 + d % v0} INTER
               {x | x IN voronoi2 v0 s}) /\
          x IN t)
  <=> (?v1 v2 v3 v0 s.
               {v0, v1, v2, v3} IN Q_SYS s /\
              x IN {t | ?x y z w.
                        &0 < y /\
                        &0 < z /\
                        &0 < w /\
                        x + y + z + w = &1 /\
                        t = x % v0 + y % v1 + z % v2 + w % v3} INTER
               {t | ?a b c d.
                        d <= &0 /\
                        a + b + c + d = &1 /\
                        t = a % v1 + b % v2 + c % v3 + d % v0} INTER
               {x | x IN voronoi2 v0 s}) `]);;
e (REWRITE_TAC[ MESON[SET_RULE` { a } UNION { f, b , c } = {a, f, b, c}`] 
  ` {v0} UNION {v1, v2, v3} IN Q_SYS s <=> {v0, v1, v2, v3} IN Q_SYS s `]);;
e (SET_TAC[]);; 
let lemma8_1 = top_thm();;  (* no sub goal *)
