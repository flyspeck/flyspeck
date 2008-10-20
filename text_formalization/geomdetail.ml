
(* NGUYEN QUANG TRUONG *)
(* ------------------------------------------------------------------------- *)
(* A few bits of general derived syntax.                                     *)
(* ------------------------------------------------------------------------- *)
needs "definitions_kepler.ml";;
needs "Multivariate/convex.ml";;
(* sua anchor do do sua anchor_points *)


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
 
	   



let packing_trg = new_definition `packing_trg (s:real^3 -> bool) = (! x y.  s x /\ s y /\ ( ~(x=y))
  ==> dist ( x, y) >= &2 ) `;;

let center_pac = new_definition ` center_pac s v = ( packing_trg s /\ s v )`;;

let centered_pac = new_definition ` centered_pac s v = ( packing s /\ v IN s )`;;

let d3 = new_definition ` d3 x y = dist (x,y)`;;

let voronoi2 = new_definition ` voronoi2 v S = {x| x IN voronoi_trg v S /\ d3 x v < &2 }`;;

let t0 = new_definition ` t0 = #1.255`;;


let quasi_tri = new_definition ` quasi_tri tri s = ( packing s /\ 
  tri SUBSET s /\
  (? a b c. ~( a=b \/ b=c\/ c=a) /\  { a, b, c } = tri ) /\
  (! x y.  ( x IN tri /\ y IN tri /\ (~(x=y)) ) ==> ( d3 x y <= &2 * t0 )))`;;


let simplex = new_definition ` simplex (d:real^3 -> bool) s = ( packing s /\
  d SUBSET s /\ 
( ? v1 v2 v3 v4. ~( v1 = v2 \/ v3 = v4 ) /\ {v1, v2 } INTER {v3, v4 } = {}/\ {v1,v2,v3,v4} = d )
 )`;;

let quasi_reg_tet = new_definition ` quasi_reg_tet x s = ( simplex x s /\
   (! v w. ( v IN x /\ w IN x /\ 
    ( ~ ( v = w))) 
  ==> ( d3 v w <= &2 * t0 )) )`;;

let quarter = new_definition ` quarter (q:real^3 -> bool) s =
  ( packing s /\
         simplex q s /\
         (?v w.
              v IN q /\
              w IN q /\
              &2 * t0 <= d3 v w /\
              d3 v w <= sqrt (&8) /\
              (!x y.
                   x IN q /\ y IN q /\ ~({x, y} = {v, w})
                   ==> d3 x y <= &2 * t0)))`;;
let diagonal = new_definition ` diagonal dgcheo d s = ( quarter d s /\
  ( ? x y. x IN d /\ y IN d /\ { x, y } = dgcheo /\ d3 x y >= &2 * t0 ))`;;

let strict_qua = new_definition ` strict_qua d s = ( quarter d s /\ 
  ( ? x y. x IN d /\ y IN d /\ &2 * t0 < d3 x y /\ d3 x y < sqrt( &8 ) ))`;;

let strict_qua2 = new_definition ` strict_qua2 d (ch:real^3 -> bool ) s = ( quarter d s /\ ch SUBSET d 
  /\ ( ? x y. ~( x = y ) /\ ch = {x,y} /\ &2 * t0 < d3 x y /\ d3 x y < sqrt ( &8 ) ) )`;;



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
  /\ ~( conv0 { v1, v3 } INTER conv0 { v , v2 , v4 } = {} ))`;;

let isolated_qua = new_definition ` isolated_qua q s = ( quarter q s /\ ~( ? v v1 v2 v3 v4. q = 
  {v, v1, v2, v3} /\ adjacent_pai v v1 v2 v3 v4 s))`;;

let isolated_pai = new_definition ` isolated_pai q1 q2 s = ( isolated_qua q1 s /\ isolated_qua q2 s /\
  ~ (conv0 q1 INTER conv0 q2 = {}))`;;


let anchor = new_definition ` anchor (v:real^3) v1 v2 s = ( {v, v1, v2} SUBSET s /\ d3 v1 v2 <= sqrt ( &8 ) /\
  d3 v1 v2 >= &2 * t0 /\ d3 v v1 <= &2 * t0 /\ d3 v v2 <= &2 * t0 )`;;

let anchor_points = new_definition ` anchor_points v w s = { t | &2 * t0 <= d3 v w /\
  anchor t v w s }`;;


let Q_SYS = new_definition ` Q_SYS s = {q | quasi_reg_tet q s \/
              strict_qua q s /\
              (?c d.
                   !qq. c IN q /\
                        d IN q /\
                        d3 c d > &2 * t0 /\
                        (quasi_reg_tet qq s \/ strict_qua qq s) /\
                        conv0 {c, d} INTER conv0 qq = {}) \/
              strict_qua q s /\
              (CARD
               {t | ?v w.
                        v IN q /\ w IN q /\ &2 * t0 < d3 v w /\ anchor t v w s} >
               4 \/
               CARD
               {t | ?v w.
                        v IN q /\ w IN q /\ &2 * t0 < d3 v w /\ anchor t v w s} =
               4 /\
               ~(?v1 v2 v3 v4 v w. v IN q /\
                     w IN q /\
                     {v1, v2, v3, v4} SUBSET anchor_points v w s
                      /\
                     
                     &2 * t0 < d3 v w /\
                     quartered_oct v w v1 v2 v3 v4 s))
  \/ (? v w v1 v2 v3 v4. q = { v, w, v1, v2} /\ quartered_oct v w v1 v2 v3 v4 s )
  \/ (? v v1 v3 v2 v4. ( q = {v, v1, v2, v3} \/ q = {v, v1, v3, v4} ) /\
  interior_pos v v1 v3 v2 v4 s /\ anchor_points v1 v3 s = { v, v2, v4} /\
  anchor_points v2 v4 s = { v, v1, v3 } )}`;; 

let barrier = new_definition ` barrier s = { { (v1 : real^3 ) , ( v2 :real^3 ) , (v3 :real^3) } |
  quasi_tri { v1 , v2 , v3 } s \/ 
  (? v4. ( { v1 , v2 , v3 } UNION { v4 }) IN Q_SYS s ) } `;;

let obstructed = new_definition ` obstructed x y s = ( ? bar. bar IN barrier s /\
  ( ~ (conv0 { x , y } INTER conv_trg bar = {})))`;;

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

let affine_hull_e = prove (`affine hull {} = {}`, 
REWRITE_TAC[AFFINE_EMPTY; AFFINE_HULL_EQ]);;

let wlog = MESON[]` (! a b. ( P a b = P b a ) /\ ( Q a b \/ Q b a ) ) ==> ((? a b . P a b ) <=> ( ? a b. P a b 
  /\ Q a b ))`;;
let wlog_real = MESON[REAL_ARITH `( ! a b:real. a <= b \/ b <= a )`] ` 
(! a:real b:real . P a b = P b a ) ==> ((? a:real b . P a b ) <=> ( ? a b. P a b 
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



let conv0_3_trg = new_definition ` conv0_3_trg s = { x | ?a b c t z r. ~( a = b ) /\
 ~( b = c) /\ ~(c = a )
   /\ a IN s /\ b IN s /\ c IN s
   /\ &0 < t /\ t < &1 /\ &0 < z /\ z < &1 /\ &0 < r /\ r < &1 
   /\ t + z + r = &1 /\ x = t % a + z % b + r % c}`;;
(*This definition only correct with s with CARD s = 3*)

let AFFINE_HULL_SINGLE = prove(`!x. affine hull {x} = {x}`,
  SIMP_TAC[AFFINE_SING; AFFINE_HULL_EQ]);;

let usefull = MESON[] ` (!x. a x ==> b x ) ==>(?x. a x ) ==> c ==> d <=>
 (!x. a x ==> b x) ==> (?x. a x /\ b x ) ==> c ==> d `;;

let v1_in_convex3 = prove (` ! v1 v2 v3. v1 IN {t | ?a b c.
              &0 <= a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 /\
 t = a % v1 + b % v2 + c % v3}`, REPEAT GEN_TAC THEN REWRITE_TAC[ IN_ELIM_THM] THEN 
EXISTS_TAC ` &1 ` THEN EXISTS_TAC ` &0 ` THEN EXISTS_TAC ` &0 ` THEN 
REWRITE_TAC[ VECTOR_ARITH ` &1 % v1 + &0 % v2 + &0 % v3 = v1 `] THEN REAL_ARITH_TAC);;
(* truong 
let v3_in_convex3 = prove (`! v1 v2 v3. v3 IN
 {t | ?a b c. &0 <= a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 /\
 t = a % v1 + b % v2 + c % v3}`, 
PURE_ONCE_REWRITE_TAC [ VECTOR_ARITH ` a % v1 + b % v2 + c % v3 = c % v3 + a % v1 + b % v2`]
 THEN REWRITE_TAC[ SET_RULE ` {t | ?a b c. &0 <= a /\ &0 <= b /\ &0 <= c /\ 
t = c % v3 + a % v1 + b % v2} =
  {t | ? c a b. &0 <= c /\ &0 <= a /\ &0 <= b /\ t = c % v3 + a % v1 + b % v2}`] THEN
 REWRITE_TAC[v1_in_convex3]
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
 THEN REWRITE_TAC[ SET_RULE ` {t | ?a b c. &0 <= a /\ &0 <= b /\ &0 <= c /\ a + b + c = &1 /\ 
t = c % v3 + a % v1 + b % v2} =
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
let lemma8_1 = top_thm();; 

truong *)




















(* BEGIN PROVING LEMMA 8.2 *)




let near = new_definition ` near (v0:real^N) (r:real) s = { x | x IN s /\
  dist(x,v0) < r } `;;

let near2t0 = new_definition ` near2t0 v0 s = { x | x IN s /\ dist(v0,x) < &2 * t0 }`;;

let e_plane = new_definition ` e_plane (a:real^N) (b:real^N) x = ( ~( a=b) /\ dist(a,x) = dist(b,x))`;;

let min_dist = new_definition ` min_dist (x:real^3) s = ((?u. u IN s /\
                  (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
             (?u v.
                  u IN s /\
                  v IN s /\
                  ~(u = v) /\
                  dist (u,x) = dist (v,x) /\
                  (!w. w IN s ==> dist (u,x) <= dist (w,x)))) `;;

let PHA = REWRITE_TAC[ MESON[] ` (a/\b)/\c <=> a/\ b /\ c `];;

let NGOAC = REWRITE_TAC[ MESON[] ` a/\b/\c <=> (a/\b)/\c `];;

let PHAT = REWRITE_TAC[ MESON[] ` (a\/b)\/c <=> a\/b\/c `];;

let NGOACT =  REWRITE_TAC[ GSYM (MESON[] ` (a\/b)\/c <=> a\/b\/c `)];;

let KHANANG = PHA THEN REWRITE_TAC[ MESON[]` ( a\/ b ) /\ c <=> a /\ c \/ b /\ c `] THEN 
 REWRITE_TAC[ MESON[]` a /\ ( b \/ c ) <=> a /\ b \/ a /\ c `];;




(* lemma 8.2 *) 
(* this fact is going to be proved *)
let import_le = new_axiom ` ! (x:real^3) y (s:real^3 -> bool). 
  x IN s /\
         dist (x,y) < t0 /\
         ~(y IN
           UNIONS {aff_ge {x} {w1, w2} | w1,w2 | {x, w1, w2} IN barrier s})
         ==> ~obstructed x y s `;;




(* ====================== proving import_le ===============================*)




let strict_qua_in_oct = prove (`! (q:real^3 -> bool) (s:real^3 -> bool ). (?v w v1 v2 v3 v4.
                   q = {v, w, v1, v2} /\ quartered_oct v w v1 v2 v3 v4 s)
  ==> strict_qua q s `, 

REWRITE_TAC[ quartered_oct; strict_qua; quarter] THEN 
ONCE_REWRITE_TAC[ GSYM (MESON[ DIST_TRIANGLE]` dist (v,w) <= dist (v,v1) + dist (v1,w) /\
     dist (v,w) <= dist (v,v2) + dist (v2,w) /\
     q = {v, w, v1, v2} <=>
     q = {v, w, v1, v2} `)] THEN 


ONCE_REWRITE_TAC[SET_RULE ` (!x. x IN {v1, v2, v3, v4}
          ==> dist (x,v) <= &2 * t0 /\ dist (x,w) <= &2 * t0) <=>
     (!x. x IN {v1, v2, v3, v4}
          ==> dist (x,v) <= &2 * t0 /\ dist (x,w) <= &2 * t0) /\
     dist (v1,v) <= &2 * t0 /\
     dist (v1,w) <= &2 * t0 /\ 
  dist (v2,v) <= &2 * t0 /\
     dist (v2,w) <= &2 * t0 `]  THEN 
PHA THEN REWRITE_TAC[ GSYM d3 ] THEN 
ONCE_REWRITE_TAC[ SET_RULE ` q = {v, w, v1, v2} <=> q = {v, w, v1, v2} /\
  v IN q /\ w IN q `] THEN 
REWRITE_TAC[ MESON[]` d3 v w <= d3 v v1 + d3 v1 w /\
          d3 v w <= d3 v v2 + d3 v2 w /\
          (q = {v, w, v1, v2} /\ v IN q /\ w IN q) /\
          packing s /\
          &2 * t0 < d3 v w /\
          d3 v w < sqrt (&8) /\ last <=> ((q = {v, w, v1, v2} /\ v IN q /\ w IN q) /\
          packing s /\
          &2 * t0 < d3 v w /\
          d3 v w < sqrt (&8) ) /\ d3 v w <= d3 v v1 + d3 v1 w /\
          d3 v w <= d3 v v2 + d3 v2 w /\ last ` ] THEN 
REWRITE_TAC[ MESON[]` (?v w v1 v2 v3 v4.
          ((q = {v, w, v1, v2} /\ v IN q /\ w IN q) /\
           packing s /\
           &2 * t0 < d3 v w /\
           d3 v w < sqrt (&8)) /\
          last v w v1 v2 v3 v4 )
     ==> aa /\ bb /\ cc /\
         (?x y. x IN q /\ y IN q /\ &2 * t0 < d3 x y /\ d3 x y < sqrt (&8)) <=>
     (?v w v1 v2 v3 v4.
          ((q = {v, w, v1, v2} /\ v IN q /\ w IN q) /\
           packing s /\
           &2 * t0 < d3 v w /\
           d3 v w < sqrt (&8)) /\
          last v w v1 v2 v3 v4)
     ==> aa /\ bb /\ cc  `] THEN 


REWRITE_TAC[ simplex] THEN PHA THEN SIMP_TAC[] THEN REWRITE_TAC[ d3 ] THEN 




ONCE_REWRITE_TAC[ MESON[ prove(
                         `dist (v,w) <= dist (v,v1) + dist (v1,w) /\
                           dist (v1,v) <= &2 * t0 /\
                           dist (v1,w) <= &2 * t0 /\
                              &2 * t0 < dist (v,w) /\
                              dist (v,w) < sqrt (&8)
                            ==> &0 < dist (v,v1) /\ &0 < dist (v1,w)`, SIMP_TAC[ DIST_SYM; t0] THEN 
                          REAL_ARITH_TAC)] `
          &2 * t0 < dist (v,w) /\
     dist (v,w) < sqrt (&8) /\
     dist (v,w) <= dist (v,v1) + dist (v1,w) /\
     dist (v,w) <= dist (v,v2) + dist (v2,w) /\
     (!x. x IN {v1, v2, v3, v4}
          ==> dist (x,v) <= &2 * t0 /\ dist (x,w) <= &2 * t0) /\
     dist (v1,v) <= &2 * t0 /\
     dist (v1,w) <= &2 * t0 /\
     dist (v2,v) <= &2 * t0 /\
     dist (v2,w) <= &2 * t0 /\
     last <=>
     &2 * t0 < dist (v,w) /\
     dist (v,w) < sqrt (&8) /\
     dist (v,w) <= dist (v,v1) + dist (v1,w) /\
     dist (v,w) <= dist (v,v2) + dist (v2,w) /\
     (!x. x IN {v1, v2, v3, v4}
          ==> dist (x,v) <= &2 * t0 /\ dist (x,w) <= &2 * t0) /\
     dist (v1,v) <= &2 * t0 /\
     dist (v1,w) <= &2 * t0 /\
     dist (v2,v) <= &2 * t0 /\
     dist (v2,w) <= &2 * t0 /\
     &0 < dist (v,v1) /\
     &0 < dist (v1,w) /\ &0 < dist (v,v2) /\
     &0 < dist (v2,w) /\
     last `] THEN 
REWRITE_TAC[ t0] THEN 
ONCE_REWRITE_TAC[ REAL_ARITH ` &2 <= dist (v1,v2) <=> &2 <= dist (v1,v2) /\ 
  &0 < dist(v1,v2) `] THEN 
REWRITE_TAC[ MESON[] ` &0 < dist ( a, b ) /\ sau <=> sau /\ &0 < dist ( a,b) `] THEN PHA THEN 
ONCE_REWRITE_TAC[ MESON[ DIST_NZ]` &0 < dist(a,b) <=> &0 < dist(a,b) /\ ~(a=b) `] THEN 
PHA THEN  
REWRITE_TAC[ MESON[]` ~(a=b) /\ last <=> last /\ ~( a=b) `] THEN PHA THEN 
REWRITE_TAC[ MESON[] ` q = {v, w, v1, v2} /\
          v IN q /\
          w IN q /\
          packing s /\ last <=> packing s /\ q = {v, w, v1, v2} /\
          v IN q /\
          w IN q /\
           last `] THEN 
REWRITE_TAC[ MESON[] `  (?v w v1 v2 v3 v4.
          packing s /\ last v w v1 v2 v3 v4 ) <=> packing s /\ (?v w v1 v2 v3 v4.
         last v w v1 v2 v3 v4 ) `] THEN SIMP_TAC[] THEN 
REWRITE_TAC[ MESON[] ` q = {v, w, v1, v2}  /\ last <=> last /\  q = {v, w, v1, v2} `] THEN 
ONCE_REWRITE_TAC[ SET_RULE `  {v, w, v1, v2, v3, v4} SUBSET s /\
          q = {v, w, v1, v2} <=> {v, w, v1, v2, v3, v4} SUBSET s /\
          q = {v, w, v1, v2} /\ q SUBSET s `] THEN 
REWRITE_TAC[ MESON[] `  ~(v = v1) /\
          ~(v1 = w) /\
          ~(v = v2) /\
          ~(v2 = w) /\
          ~(v4 = v1) /\
          ~(v3 = v4) /\
          ~(v2 = v3) /\
          ~(v1 = v2) /\
          {v, w, v1, v2, v3, v4} SUBSET s /\
          q = {v, w, v1, v2} /\
          q SUBSET s <=> {v, w, v1, v2, v3, v4} SUBSET s /\ 
  q SUBSET s /\ (  ~(v = v1) /\
          ~(v1 = w) /\
          ~(v = v2) /\
          ~(v2 = w) /\
          ~(v4 = v1) /\
          ~(v3 = v4) /\
          ~(v2 = v3) /\
          ~(v1 = v2) /\ q = {v, w, v1, v2}  )  `] THEN 
REWRITE_TAC[ MESON[] ` a /\ b/\ c <=> ( a/\ b) /\ c `] THEN 
REWRITE_TAC[ MESON[]` a /\ b <=> b /\ a `] THEN 
REWRITE_TAC[ MESON[] ` (?v w v1 v2 v3 v4.
          q = {v, w, v1, v2} /\
          ~(v1 = v2) /\
          ~(v2 = v3) /\
          ~(v3 = v4) /\
          ~(v4 = v1) /\
          ~(v2 = w) /\
          ~(v = v2) /\
          ~(v1 = w) /\
          ~(v = v1) /\
          q SUBSET s /\ la v w v1 v2 v3 v4 ) <=> 
  q SUBSET s /\ (?v w v1 v2 v3 v4.
          q = {v, w, v1, v2} /\
          ~(v1 = v2) /\
          ~(v2 = v3) /\
          ~(v3 = v4) /\
          ~(v4 = v1) /\
          ~(v2 = w) /\
          ~(v = v2) /\
          ~(v1 = w) /\
          ~(v = v1) /\
          la v w v1 v2 v3 v4 ) `] THEN SIMP_TAC[] THEN 
ONCE_REWRITE_TAC[ MESON[ REAL_ARITH ` &0 < &2 * #1.255 /\ 
( ! a b c. a < b /\ b < c ==> a < c )`; DIST_NZ ] ` &2 * #1.255 < dist (v,w)
 <=> ~(v=w) /\ &2 * #1.255 < dist (v,w) ` ] THEN PHA THEN 
REWRITE_TAC[ MESON[] ` (~(v = w) /\ &2 * #1.255 < dist (v,w) /\ v IN q /\ w IN q <=>
      &2 * #1.255 < dist (v,w) /\ v IN q /\ w IN q /\ ~(v = w)) /\
     (a /\ b /\ c <=> (a /\ b) /\ c) `] THEN 
REWRITE_TAC[ MESON[] ` ~(v = w) /\ &2 * #1.255 < dist (v,w) /\ v IN q /\ w IN q <=>
      &2 * #1.255 < dist (v,w) /\ v IN q /\ w IN q /\ ~(v = w)
     `] THEN 
REWRITE_TAC[ MESON[] ` a /\ b /\ c <=> (a/\b) /\ c `] THEN 
REWRITE_TAC [MESON[] ` aa /\  ~(v = w) <=> ~(v=w) /\ aa `] THEN PHA  THEN 



REWRITE_TAC[ MESON[]` ~(v = w) /\
          ~(v = v1) /\
          ~(v1 = w) /\
          ~(v = v2) /\
          ~(v2 = w) /\
          ~(v4 = v1) /\
          ~(v3 = v4) /\
          ~(v2 = v3) /\
          ~(v1 = v2) /\
          q = {v, w, v1, v2} /\ last <=> (~(v = w) /\
          ~(v = v1) /\
          ~(v1 = w) /\
          ~(v = v2) /\
          ~(v2 = w) /\
          ~(v4 = v1) /\
          ~(v3 = v4) /\
          ~(v2 = v3) /\
          ~(v1 = v2) /\
          q = {v, w, v1, v2}) /\ last `] THEN 
SIMP_TAC[ SET_RULE ` {v1, v2, v3, v4} = q <=> q = {v1, v2, v3, v4}`] THEN 
ONCE_REWRITE_TAC[ MESON[ SET_RULE ` ~(v = w) /\
           ~(v = v1) /\
           ~(v1 = w) /\
           ~(v = v2) /\
           ~(v2 = w) /\
           ~(v4 = v1) /\
           ~(v3 = v4) /\
           ~(v2 = v3) /\
           ~(v1 = v2) ==>
   ( {v, w} INTER {v1, v2 } = {} /\ ~(v = w \/ v1 = v2 ) )` ] `
  ~(v = w) /\
     ~(v = v1) /\
     ~(v1 = w) /\
     ~(v = v2) /\
     ~(v2 = w) /\
     ~(v4 = v1) /\
     ~(v3 = v4) /\
     ~(v2 = v3) /\
     ~(v1 = v2) /\
     q = {v, w, v1, v2} <=>
     (q = {v, w, v1, v2} /\
      {v, w} INTER {v1, v2} = {} /\
      ~(v = w \/ v1 = v2)) /\
     ~(v = w) /\
     ~(v = v1) /\
     ~(v1 = w) /\
     ~(v = v2) /\
     ~(v2 = w) /\
     ~(v4 = v1) /\
     ~(v3 = v4) /\
     ~(v2 = v3) /\
     ~(v1 = v2) `] THEN 
PHA THEN ONCE_REWRITE_TAC[MESON[]` (?v w v1 v2 v3 v4.
          q = {v, w, v1, v2} /\
          {v, w} INTER {v1, v2} = {} /\
          ~(v = w \/ v1 = v2) /\
          last v w v1 v2 v3 v4) <=>
     (?v w v1 v2.
          q = {v, w, v1, v2} /\
          {v, w} INTER {v1, v2} = {} /\
          ~(v = w \/ v1 = v2)) /\
     (?v w v1 v2 v3 v4.
          q = {v, w, v1, v2} /\
          {v, w} INTER {v1, v2} = {} /\
          ~(v = w \/ v1 = v2) /\
          last v w v1 v2 v3 v4) `] THEN SIMP_TAC[] THEN PHA THEN 
MATCH_MP_TAC (MESON[] `(! q s. gi q s ==> cc q s ) ==> 
   ( ! q s. a q /\ gi q s /\ b s ==> cc q s ) `) THEN 




REWRITE_TAC[ MESON[] ` {v, w, v1, v2, v3, v4} SUBSET s /\ a <=> a /\
 {v, w, v1, v2, v3, v4} SUBSET s `] THEN 
REWRITE_TAC[ MESON[]` q = {v, w, v1, v2} /\ a <=> a /\ q = {v, w, v1, v2} `] THEN PHA THEN 
ONCE_REWRITE_TAC[SET_RULE ` {v, w, v1, v2, v3, v4} SUBSET s /\ q = {v, w, v1, v2} <=>
     {v, w, v1, v2, v3, v4} SUBSET s /\ q = {v, w, v1, v2} /\ q SUBSET s `] THEN 
NGOAC THEN ONCE_REWRITE_TAC[MESON[] ` (?v w v1 v2 v3 v4. aaa v w v1 v2 v3 v4 /\ 
  q SUBSET s ) <=> q SUBSET s /\ (?v w v1 v2 v3 v4. aaa v w v1 v2 v3 v4)`] THEN PHA THEN 
SIMP_TAC[] THEN 
REWRITE_TAC[ MESON[]` dist (v1,v2) <= &2 * #1.255 /\
     &0 < dist (v1,v2) /\
     &2 <= dist (v1,v2) /\
     dist (v2,w) <= &2 * #1.255 /\
     dist (v2,v) <= &2 * #1.255 /\
     dist (v1,w) <= &2 * #1.255 /\
     dist (v1,v) <= &2 * #1.255 /\
     last <=>
     &0 < dist (v1,v2) /\
     &2 <= dist (v1,v2) /\
     last /\
     dist (v1,v2) <= &2 * #1.255 /\
     dist (v2,w) <= &2 * #1.255 /\
     dist (v2,v) <= &2 * #1.255 /\
     dist (v1,w) <= &2 * #1.255 /\
     dist (v1,v) <= &2 * #1.255 `] THEN PHA  THEN 
ONCE_REWRITE_TAC[ SET_RULE ` q = {v, w, v1, v2} <=>
     q = {v, w, v1, v2} /\
     (!x y.
          ~({x, y} = {v, w}) /\ x IN q /\ y IN q
          ==> (x = v \/ x = w \/ x = v1 \/ x = v2) /\
              (y = v \/ y = w \/ y = v1 \/ y = v2) /\
              ~(x = v /\ y = w \/ x = w /\ y = v)) `] THEN 
REWRITE_TAC[ MESON[] ` ~( a\/ b ) <=> ~ a /\ ~ b `] THEN 
NGOAC THEN REWRITE_TAC[ MESON[] ` a /\ ( b \/ c ) <=> a /\ b \/ a /\ c `] THEN 

PHA THEN REWRITE_TAC[ MESON[]` day /\ ~(x = v /\ y = w) /\
                   ~(x = w /\ y = v) <=> 
  ~(x = v /\ y = w) /\
                   ~(x = w /\ y = v) /\ day `] THEN 
PHA THEN REWRITE_TAC[ MESON[] ` ( a \/ b ) /\c <=> a /\ c \/ b /\ c `] THEN PHA THEN 
REWRITE_TAC[ MESON[] ` (a\/b) \/ c <=> a \/ b\/ c`] THEN 

REWRITE_TAC[ MESON[] ` ~(x = v /\ y = w) /\
     ~(x = w /\ y = v) /\
     (x = v /\ y = v \/
      x = w /\ y = v \/
      x = v1 /\ y = v \/
      x = v2 /\ y = v \/
      x = v /\ y = w \/
      last) <=>
     ~(x = v /\ y = w) /\
     ~(x = w /\ y = v) /\
     (x = v /\ y = v \/ x = v1 /\ y = v \/ x = v2 /\ y = v \/ last) `] THEN 
REWRITE_TAC[ MESON[ SET_RULE ` ~({x, y} = {v, w}) <=> ~(x = v /\ y = w) /\ ~(x = w /\ y = v)`]
  ` (!x y.
          ~({x, y} = {v, w}) /\ x IN q /\ y IN q
          ==> ~(x = v /\ y = w) /\ ~(x = w /\ y = v) /\ last x y)
     <=> (!x y. ~({x, y} = {v, w}) /\ x IN q /\ y IN q ==> last x y) `] THEN 
ONCE_REWRITE_TAC[ MESON[DIST_REFL; REAL_ARITH ` a = &0 ==> a <= &2 * #1.255 `]
 ` x = v /\ y = v <=> x = v /\ y = v /\ dist(x,y) <= &2 * #1.255 `] THEN 
REWRITE_TAC[ MESON[]` ( ! x y. P x y ) /\ last <=> last /\ ( ! x y. P x y)`] THEN PHA THEN 
ONCE_REWRITE_TAC[MESON[]` dist (v1,v2) <= &2 * #1.255 /\
     dist (v2,w) <= &2 * #1.255 /\
     dist (v2,v) <= &2 * #1.255 /\
     dist (v1,w) <= &2 * #1.255 /\
     dist (v1,v) <= &2 * #1.255 /\
     (!x y. ~({x, y} = {v, w}) /\ x IN q /\ y IN q ==> last x y) <=>
     dist (v1,v2) <= &2 * #1.255 /\
     dist (v2,w) <= &2 * #1.255 /\
     dist (v2,v) <= &2 * #1.255 /\
     dist (v1,w) <= &2 * #1.255 /\
     dist (v1,v) <= &2 * #1.255 /\
     (!x y.
          ~({x, y} = {v, w}) /\ x IN q /\ y IN q
          ==> 
              dist (v1,v2) <= &2 * #1.255 /\
              dist (v2,w) <= &2 * #1.255 /\
              dist (v2,v) <= &2 * #1.255 /\
              dist (v1,w) <= &2 * #1.255 /\
              dist (v1,v) <= &2 * #1.255 /\ last x y) `] THEN 
REWRITE_TAC[ MESON[ DIST_SYM]`dist (v1,v2) <= &2 * #1.255 /\
     dist (v2,w) <= &2 * #1.255 /\
     dist (v2,v) <= &2 * #1.255 /\
     dist (v1,w) <= &2 * #1.255 /\
     dist (v1,v) <= &2 * #1.255 /\
     (x = v /\ y = v /\ dist (x,y) <= &2 * #1.255 \/
      x = v1 /\ y = v \/
      x = v2 /\ y = v \/
      last) <=>
     dist (v1,v2) <= &2 * #1.255 /\
     dist (v2,w) <= &2 * #1.255 /\
     dist (v2,v) <= &2 * #1.255 /\
     dist (v1,w) <= &2 * #1.255 /\
     dist (v1,v) <= &2 * #1.255 /\
     (x = v /\ y = v /\ dist (x,y) <= &2 * #1.255 \/
      x = v1 /\ y = v /\ dist (x,y) <= &2 * #1.255 \/
      x = v2 /\ y = v /\ dist (x,y) <= &2 * #1.255 \/
      last) `] THEN 
REWRITE_TAC[ MESON[]` a \/ b \/ c <=> (a \/ b ) \/ c `] THEN 
REWRITE_TAC[ MESON[] ` ((((a \/ x = v2 /\ y = v1) \/ x = v /\ y = v2) \/ x = w /\ y = v2) \/
      x = v1 /\ y = v2) \/
     x = v2 /\ y = v2 /\ dist (x,y) <= &2 * #1.255 <=>
     (((x = v2 /\ y = v1 \/ x = v /\ y = v2) \/ x = w /\ y = v2) \/
      x = v1 /\ y = v2) \/
     x = v2 /\ y = v2 /\ dist (x,y) <= &2 * #1.255 \/
     a `] THEN 
REWRITE_TAC[ GSYM (MESON[]` a \/ b \/ c <=> (a \/ b ) \/ c `)] THEN 




REWRITE_TAC[MESON[DIST_SYM ]` dist (v1,v2) <= &2 * #1.255 /\
                   dist (v2,w) <= &2 * #1.255 /\
                   dist (v2,v) <= &2 * #1.255 /\
                   dist (v1,w) <= &2 * #1.255 /\
                   dist (v1,v) <= &2 * #1.255 /\
                   (x = v2 /\ y = v1 \/
                    x = v /\ y = v2 \/
                    x = w /\ y = v2 \/
                    x = v1 /\ y = v2 \/ last ) 
  <=> dist (v1,v2) <= &2 * #1.255 /\
                   dist (v2,w) <= &2 * #1.255 /\
                   dist (v2,v) <= &2 * #1.255 /\
                   dist (v1,w) <= &2 * #1.255 /\
                   dist (v1,v) <= &2 * #1.255 /\
                   ((x = v2 /\ y = v1 \/ 
                    x = v /\ y = v2 \/
                    x = w /\ y = v2 \/
                    x = v1 /\ y = v2 ) /\ dist( x,y) <= &2 * #1.255 \/ last ) `] THEN 
REWRITE_TAC[ MESON[]` a \/ b \/ c <=> (a \/ b ) \/ c `] THEN 
REWRITE_TAC[ MESON[]` ((((a \/ x = v1 /\ y = w) \/
                       x = v2 /\ y = w) \/
                      x = v /\ y = v1) \/
                     x = w /\ y = v1) \/
                    x = v1 /\ y = v1 /\ dist (x,y) <= &2 * #1.255 <=>
  (((x = v1 /\ y = w \/
                       x = v2 /\ y = w) \/
                      x = v /\ y = v1) \/
                     x = w /\ y = v1) \/
                    x = v1 /\ y = v1 /\ dist (x,y) <= &2 * #1.255 \/ a `] THEN 
REWRITE_TAC[ GSYM (MESON[]` a \/ b \/ c <=> (a \/ b ) \/ c `)] THEN 

REWRITE_TAC[ MESON[ DIST_SYM ] ` 
  dist (v1,v2) <= &2 * #1.255 /\
     dist (v2,w) <= &2 * #1.255 /\
     dist (v2,v) <= &2 * #1.255 /\
     dist (v1,w) <= &2 * #1.255 /\
     dist (v1,v) <= &2 * #1.255 /\
     (x = v1 /\ y = w \/
      x = v2 /\ y = w \/
      x = v /\ y = v1 \/
      x = w /\ y = v1 \/
      last) <=>
     dist (v1,v2) <= &2 * #1.255 /\
     dist (v2,w) <= &2 * #1.255 /\
     dist (v2,v) <= &2 * #1.255 /\
     dist (v1,w) <= &2 * #1.255 /\
     dist (v1,v) <= &2 * #1.255 /\
     ((x = v1 /\ y = w \/
       x = v2 /\ y = w \/
       x = v /\ y = v1 \/
       x = w /\ y = v1) /\
      dist (x,y) <= &2 * #1.255 \/
      last) `] THEN 
REWRITE_TAC[ MESON[] ` x = v1 /\ y = v2 /\ dist (x,y) <= &2 * #1.255 
  <=> (x = v1 /\ y = v2) /\ dist (x,y) <= &2 * #1.255 `] THEN 
REWRITE_TAC[ GSYM (MESON[]` a \/ b \/ c <=> (a \/ b ) \/ c `)] THEN 
REWRITE_TAC[ MESON[]` a /\ c \/ b /\ c <=> ( a\/ b) /\ c `] THEN NGOAC THEN 
ONCE_REWRITE_TAC[ MESON[] ` ( ! x y. P x y ==> L x y /\ TT x y ) <=>
  ( ! x y. P x y ==> L x y /\ TT x y ) /\ ( ! x y. P x y ==> TT x y ) `] THEN 
NGOAC THEN 
REWRITE_TAC[ MESON[]` a /\ (!x y.
               (~({x, y} = {v, w}) /\ x IN q) /\ y IN q
               ==> dist (x,y) <= &2 * #1.255) <=> (!x y.
               (~({x, y} = {v, w}) /\ x IN q) /\ y IN q
               ==> dist (x,y) <= &2 * #1.255) /\ a `] THEN 
REWRITE_TAC[ MESON[]` ((( a /\dist (v,w) < sqrt (&8)) /\
                    &2 * #1.255 < dist (v,w)) /\
                   v IN q) /\
                  w IN q
  <=> (((dist (v,w) < sqrt (&8)) /\
                    &2 * #1.255 < dist (v,w)) /\
                   v IN q) /\
                  w IN q /\ a `] THEN PHA THEN 
ONCE_REWRITE_TAC[MESON[ REAL_ARITH ` a < b ==> a <= b `]` (?v w v1 v2 v3 v4.
          (!x y.
               ~({x, y} = {v, w}) /\ x IN q /\ y IN q
               ==> dist (x,y) <= &2 * #1.255) /\
          dist (v,w) < sqrt (&8) /\
          &2 * #1.255 < dist (v,w) /\
          v IN q /\
          w IN q /\ last v w v1 v2 v3 v4 )
  <=> (?v w.
              (!x y.
                   ~({x, y} = {v, w}) /\ x IN q /\ y IN q
                   ==> dist (x,y) <= &2 * #1.255) /\
              dist (v,w) <= sqrt (&8) /\
              &2 * #1.255 <= dist (v,w) /\
              v IN q /\
              w IN q) /\ (?v w v1 v2 v3 v4.
          (!x y.
               ~({x, y} = {v, w}) /\ x IN q /\ y IN q
               ==> dist (x,y) <= &2 * #1.255) /\
          dist (v,w) < sqrt (&8) /\
          &2 * #1.255 < dist (v,w) /\
          v IN q /\
          w IN q /\ last v w v1 v2 v3 v4 )`] THEN PHA THEN 
REPEAT GEN_TAC THEN MATCH_MP_TAC (MESON[] ` ( b ==> d ) ==> (a /\ b /\ c ==> d) `) THEN 
MESON_TAC[]);;




let set_3elements = prove(`(?a b c. ~(a = b \/ b = c \/ c = a) /\ {a, b, c} = {v1, v2, v3}) <=>
 ~(v1 = v2 \/ v2 = v3 \/ v3 = v1)`,
ONCE_REWRITE_TAC[ SET_RULE`{a, b, c} = {v1, v2, v3} <=>
  {a, b, c} = {v1, v2, v3} /\ v1 IN {a, b, c} `] THEN 
REWRITE_TAC[ SET_RULE` x IN { a, b, c} <=> x = a \/ x = b \/ x = c `] THEN NGOAC THEN 
MATCH_MP_TAC (MESON[]`(!a b c. P a b c <=> P b a c) /\
     ((?a b c. P a b c /\ (v = a \/ v = c)) <=> last)
     ==> ((?a b c. P a b c /\ (v = a \/ v = b \/ v = c)) <=> last)`) THEN 
REWRITE_TAC[MESON[SET_RULE ` ! a b c. {a, b, c} = {b, a, c}`]`(!a b c.
      ~(a = b \/ b = c \/ c = a) /\ {a, b, c} = {v1, v2, v3} <=>
      ~(b = a \/ a = c \/ c = b) /\ {b, a, c} = {v1, v2, v3}) <=> T `] THEN 
MATCH_MP_TAC (MESON[]` (!a c b. P a c b <=> P b c a) /\ ((?a c b. P a c b /\ v = a) <=> last)
     ==> ((?a c b. P a c b /\ (v = a \/ v = b)) <=> last)`) THEN 
REWRITE_TAC[ MESON[ SET_RULE` ! a b c. { a, b, c} = { c, b, a } `]`
  (!a b c.
      ~(a = b \/ b = c \/ c = a) /\ {a, b, c} = {v1, v2, v3} <=>
      ~(c = b \/ b = a \/ a = c) /\ {c, b, a} = {v1, v2, v3}) <=> T `] THEN PHA THEN
REWRITE_TAC[ SET_RULE ` ~(a = b \/ b = c \/ c = a) /\ {a, b, c} = {v1, v2, v3} /\ v1 = a <=>
     ~(a = b \/ b = c \/ c = a) /\
     {a, b, c} = {v1, v2, v3} /\
     v1 = a /\
     ~(v1 = v2 \/ v2 = v3 \/ v3 = v1)`] THEN 
MESON_TAC[]);;



let quasi_tri_case = prove( ` ! s x y. (?v1 v2 v3.
      ~(x IN {v1, v2, v3}) /\
      quasi_tri {v1, v2, v3} s /\
      ~(conv0 {x, y} INTER conv_trg {v1, v2, v3} = {}) /\
      dist (x,y) < t0)
 ==> (?v1 v2 v3.
          packing s /\
          ~(v1 = v2 \/ v2 = v3 \/ v3 = v1) /\
          dist (v1,v2) <= #2.51 /\
          dist (v2,v3) <= #2.51 /\
          dist (v3,v1) < sqrt (&8) /\
          {v1, v2, v3} SUBSET s /\
          ~(x IN {v1, v2, v3}) /\
          ~(conv0 {x, y} INTER conv_trg {v1, v2, v3} = {}) /\
          dist (x,y) < t0)`,
REWRITE_TAC[ quasi_tri; set_3elements] THEN PHA THEN 
 REWRITE_TAC[ d3; MESON[t0; REAL_ARITH ` &2 * #1.255 = #2.51 `] ` &2 * t0 = #2.51 `] THEN 
REWRITE_TAC[ MESON[]` a /\ b /\ c /\ d /\e /\ f <=> a /\ b /\ c /\ (d /\e) /\ f`] THEN 
ONCE_REWRITE_TAC[ SET_RULE ` ~(v1 = v2 \/ v2 = v3 \/ v3 = v1) /\
          (!x y.
               x IN {v1, v2, v3} /\ y IN {v1, v2, v3} /\ ~(x = y)
               ==> dist (x,y) <= #2.51)
  <=> ~(v1 = v2 \/ v2 = v3 \/ v3 = v1) /\
          (!x y.
               x IN {v1, v2, v3} /\ y IN {v1, v2, v3} /\ ~(x = y)
               ==> dist (x,y) <= #2.51) /\
   dist (v1,v2) <= #2.51 /\
              dist (v2,v3) <= #2.51 /\
              dist (v3,v1) <= #2.51 `] THEN 
ONCE_REWRITE_TAC[MESON[ REAL_ARITH ` &2 * #1.255 = #2.51 `; MATCH_MP REAL_LT_RSQRT (REAL_ARITH `(&2 * #1.255) pow 2 < &8`); 
  REAL_ARITH` a <= b /\ b < c ==> a < c `] `
  a /\ dist (v3,v1) <= #2.51 <=> a /\ dist (v3,v1) < sqrt ( &8 ) /\ dist (v3,v1) <= #2.51`] THEN 
 MESON_TAC[]);;







(* ========================= proving import_le ================================ *)






let exists_min_dist = new_axiom ` ! (x :real^3) (s:real^3 -> bool).
  ~(s = {}) /\ packing s
         ==> min_dist x s`;;

let tarski_FFSXOWD = new_axiom ` !v0 v1 v2 v3 s.
         packing s /\
         ~(v1 = v2 \/ v2 = v3 \/ v3 = v1) /\
         dist (v1,v2) <= #2.51 /\
         dist (v2,v3) <= #2.51 /\
         dist (v3,v1) < sqrt (&8) /\
         {v1, v2, v3} SUBSET s /\
         ~(v0 IN {v1, v2, v3})
         ==> normball v0 #1.255 INTER conv {v1, v2, v3} = {} `;; (* tarski for lemma82 *)



let VC_DISJOINT = prove ( `! s a b. ~( a = b ) ==> VC a s INTER VC b s = {} `, 
REWRITE_TAC[ VC; lambda_x ] THEN 
REWRITE_TAC[ SET_RULE` a INTER b = {} <=> (! x. ~( x IN a /\ x IN b ))`] THEN 
REWRITE_TAC[ SET_RULE ` x IN { x | p x } <=> p x `] THEN 
REWRITE_TAC[ MESON[] ` ! a P. a ==> (!x. ~P x) <=> a ==> (!x. ~a \/ ~P x) `] THEN 
REWRITE_TAC[ MESON[] ` a = b \/
     ~(((a IN s /\ d3 a x < &2 /\ ~obstructed a x s) /\
        (!w. (w IN s /\ d3 w x < &2 /\ ~obstructed w x s) /\ ~(w = a)
             ==> d3 x a < d3 x w)) /\
       (b IN s /\ d3 b x < &2 /\ ~obstructed b x s) /\
       (!w. (w IN s /\ d3 w x < &2 /\ ~obstructed w x s) /\ ~(w = b)
            ==> d3 x b < d3 x w)) <=>
     ~(~(a = b) /\
       ((a IN s /\ d3 a x < &2 /\ ~obstructed a x s) /\
        (!w. (w IN s /\ d3 w x < &2 /\ ~obstructed w x s) /\ ~(w = a)
             ==> d3 x a < d3 x w)) /\
       (b IN s /\ d3 b x < &2 /\ ~obstructed b x s) /\
       (!w. (w IN s /\ d3 w x < &2 /\ ~obstructed w x s) /\ ~(w = b)
            ==> d3 x b < d3 x w)) `] THEN PHA THEN 
MESON_TAC[ REAL_ARITH ` ! a b. ~( a < b /\ b < a ) `]);;




let lemma_of_lemma82 = prove (` ! (x:real^3) (v0:real^3) s Z. centered_pac s v0 /\ Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
 x IN normball v0 t0 DIFF Z
 ==> (?w. w IN near2t0 v0 s /\ x IN voronoi w s)`, REPEAT GEN_TAC THEN REWRITE_TAC[centered_pac] THEN 
REWRITE_TAC[ SET_RULE `packing s /\ v0 IN s <=> packing s /\ v0 IN s /\ ~(s={})`] THEN 
REWRITE_TAC[MESON[exists_min_dist] ` (packing s /\ v0 IN s /\ ~(s = {})) /\
 Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
 x IN normball v0 t0 DIFF Z  <=>(packing s /\ v0 IN s /\ ~(s = {})) /\
 Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
 x IN normball v0 t0 DIFF Z /\ min_dist x s `] THEN 
SIMP_TAC[normball; min_dist] THEN 
REWRITE_TAC[SET_RULE` x IN a DIFF b <=> x IN a /\ ~( x IN b )`] THEN 
REWRITE_TAC[SET_RULE ` x IN { x | P x } <=> P x `] THEN PHA THEN 
REWRITE_TAC[MESON[]` dist (x,v0) < t0 /\
 ~(x IN Z) /\
 ((?u. u IN s /\ (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
  (?u v.
       u IN s /\
       v IN s /\
       ~(u = v) /\
       dist (u,x) = dist (v,x) /\
       (!w. w IN s ==> dist (u,x) <= dist (w,x)))) <=>
  dist (x,v0) < t0 /\
 ~(x IN Z) /\
 ((?u. u IN s /\ (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
  ( ~(x IN Z) /\ (?u v.
       u IN s /\
       v IN s /\
       ~(u = v) /\
       dist (u,x) = dist (v,x) /\
       (!w. w IN s ==> dist (u,x) <= dist (w,x)) /\ dist (x,v0) < t0 ))) `] THEN 
REWRITE_TAC[MESON[DIST_TRIANGLE] ` v0 IN s /\
     ~(s = {}) /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
     dist (x,v0) < t0 /\
     ~(x IN Z) /\
     ((?u. u IN s /\ (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
      ~(x IN Z) /\
      (?u v.
           u IN s /\
           v IN s /\
           ~(u = v) /\
           dist (u,x) = dist (v,x) /\
           (!w. w IN s ==> dist (u,x) <= dist (w,x)) /\
           dist (x,v0) < t0)) <=>
     v0 IN s /\
     ~(s = {}) /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
     dist (x,v0) < t0 /\
     ~(x IN Z) /\
     ((?u. u IN s /\ (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
      ~(x IN Z) /\
      (?u v.
           u IN s /\
           dist (u,v0) <= dist (u,x) + dist (x,v0) /\
           dist (u,x) <= dist (v0,x) /\
           v IN s /\
           dist (v,v0) <= dist (v,x) + dist (x,v0) /\
           dist (v,x) <= dist (v0,x) /\
           ~(u = v) /\
           dist (u,x) = dist (v,x) /\
           (!w. w IN s ==> dist (u,x) <= dist (w,x)) /\
           dist (x,v0) < t0)) `] THEN 
REWRITE_TAC[MESON[] ` u IN s /\
     dist (u,v0) <= dist (u,x) + dist (x,v0) /\
     dist (u,x) <= dist (v0,x) /\
     v IN s /\
     dist (v,v0) <= dist (v,x) + dist (x,v0) /\
     dist (v,x) <= dist (v0,x) /\
     ~(u = v) /\
     dist (u,x) = dist (v,x) /\
     (!w. w IN s ==> dist (u,x) <= dist (w,x)) /\
     dist (x,v0) < t0 <=>
     u IN s /\
     (dist (u,v0) <= dist (u,x) + dist (x,v0) /\
      dist (u,x) <= dist (v0,x) /\
      dist (x,v0) < t0) /\
     v IN s /\
     (dist (v,v0) <= dist (v,x) + dist (x,v0) /\
      dist (v,x) <= dist (v0,x) /\
      dist (x,v0) < t0) /\
     ~(u = v) /\
     dist (u,x) = dist (v,x) /\
     (!w. w IN s ==> dist (u,x) <= dist (w,x))`] THEN 
SIMP_TAC[DIST_SYM] THEN 
REWRITE_TAC[REAL_ARITH ` dist (u,v0) <= dist (u,x) + dist (v0,x) /\
        dist (u,x) <= dist (v0,x) /\
        dist (v0,x) < t0
  <=> dist (u,v0) <= dist (u,x) + dist (v0,x) /\
        dist (u,x) <= dist (v0,x) /\
        dist (v0,x) < t0 /\ dist(u, v0) < &2 * t0 `] THEN 
REWRITE_TAC[ MESON[] ` a /\ b /\c/\ d /\ e ==> f <=> a/\b/\c/\d ==> e ==> f `] THEN SIMP_TAC[] THEN 
REWRITE_TAC[ IN_UNIONS; e_plane; near2t0] THEN 
REWRITE_TAC[SET_RULE ` x IN { x | P x } <=> P x `] THEN 
REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[ MESON[] ` (?t. (?u v.
                 ((u IN s /\ dist (v0,u) < &2 * t0) /\
                  v IN s /\
                  dist (v0,v) < &2 * t0) /\
                 t = e_plane u v) /\
            x IN t ) 
  <=> (?u v.
                 ((u IN s /\ dist (v0,u) < &2 * t0) /\
                  v IN s /\
                  dist (v0,v) < &2 * t0) /\
                 x IN e_plane u v) `] THEN 
REWRITE_TAC[ SET_RULE ` x IN e_plane u v <=> e_plane u v x `; e_plane] THEN 
PHA THEN SIMP_TAC[ MESON[DIST_SYM] ` ~(?u v.
            u IN s /\
            dist (v0,u) < &2 * t0 /\
            v IN s /\
            dist (v0,v) < &2 * t0 /\
            ~(u = v) /\
            dist (u,x) = dist (v,x)) /\
      (?u v.
           u IN s /\
           dist (u,v0) <= dist (u,x) + dist (v0,x) /\
           dist (u,x) <= dist (v0,x) /\
           dist (v0,x) < t0 /\
           dist (u,v0) < &2 * t0 /\
           v IN s /\
           dist (v,v0) <= dist (v,x) + dist (v0,x) /\
           dist (v,x) <= dist (v0,x) /\
           dist (v0,x) < t0 /\
           dist (v,v0) < &2 * t0 /\
           ~(u = v) /\
           dist (u,x) = dist (v,x) /\
           (!w. w IN s ==> dist (u,x) <= dist (w,x))) <=> F `] THEN 
REWRITE_TAC[voronoi] THEN REWRITE_TAC[ SET_RULE ` x IN { x | P x } <=> P x `] THEN 
REWRITE_TAC[ MESON[] ` dist (v0,x) < t0 /\
     ~(?u v.
           u IN s /\
           dist (v0,u) < &2 * t0 /\
           v IN s /\
           dist (v0,v) < &2 * t0 /\
           ~(u = v) /\
           dist (u,x) = dist (v,x)) /\
     (?u. u IN s /\ (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)))
  <=> dist (v0,x) < t0 /\
     ~(?u v.
           u IN s /\
           dist (v0,u) < &2 * t0 /\
           v IN s /\
           dist (v0,v) < &2 * t0 /\
           ~(u = v) /\
           dist (u,x) = dist (v,x)) /\
     (?u. u IN s /\dist (v0,x) < t0  /\  (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)))`] THEN 
REWRITE_TAC[ MESON[DIST_TRIANGLE] `(?u. u IN s /\
          dist (v0,x) < t0 /\
          (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) <=>
     (?u. u IN s /\
          dist (v0,x) < t0 /\
          dist (u,v0) <= dist (u,x) + dist (x,v0) /\
          (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) `] THEN 
REWRITE_TAC[ MESON[] ` ( a ==> b==> c <=> a/\b ==> c ) `] THEN PHA THEN 
ONCE_REWRITE_TAC[ MESON[] ` a /\ b /\ c ==> d <=> a/\c /\b ==> d `] THEN PHA THEN 
ONCE_REWRITE_TAC[MESON[] ` !P. (?u. P u) /\ v0 IN s <=>
         ((?u. u = v0 /\ P u) \/ (?u. ~(u = v0) /\ P u)) /\ v0 IN s`] THEN 
REWRITE_TAC[t0] THEN ONCE_REWRITE_TAC[MESON[ DIST_REFL; REAL_ARITH ` &0 < &2 * #1.255 ` ] ` u = v0 /\ las  <=> u = v0  /\ dist(u,v0 ) < &2 * #1.255 /\ las `] THEN 
REWRITE_TAC[ MESON[] ` ((?u. u = v0 /\
           dist (u,v0) < &2 * #1.255 /\
           u IN s /\
           dist (v0,x) < #1.255 /\
           dist (u,v0) <= dist (u,x) + dist (x,v0) /\
           (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
      (?u. ~(u = v0) /\
           u IN s /\
           dist (v0,x) < #1.255 /\
           dist (u,v0) <= dist (u,x) + dist (x,v0) /\
           (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)))) /\
     v0 IN s <=>
     ((?u. u = v0 /\
           dist (u,v0) < &2 * #1.255 /\
           u IN s /\
           v0 IN s /\
           dist (v0,x) < #1.255 /\
           dist (u,v0) <= dist (u,x) + dist (x,v0) /\
           (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
      (?u. ~(u = v0) /\
           u IN s /\
           v0 IN s /\
           dist (v0,x) < #1.255 /\
           dist (u,v0) <= dist (u,x) + dist (x,v0) /\
           (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)))) /\
     v0 IN s `] THEN REWRITE_TAC[ MESON[] ` ~(u = v0) /\
     u IN s /\
     v0 IN s /\
     dist (v0,x) < #1.255 /\
     dist (u,v0) <= dist (u,x) + dist (x,v0) /\
     (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)) <=>
     ~(u = v0) /\
    
     u IN s /\
     v0 IN s /\ (  dist (u,x) < dist (v0,x) /\
     dist (v0,x) < #1.255 /\
     dist (u,v0) <= dist (u,x) + dist (x,v0) ) /\
     (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)) `] THEN SIMP_TAC[DIST_SYM] THEN 
PURE_ONCE_REWRITE_TAC[ REAL_ARITH `  ( dist (u,x) < dist (v0,x) /\
     dist (v0,x) < #1.255 /\
     dist (u,v0) <= dist (u,x) + dist (v0,x))  <=>
     (dist (u,x) < dist (v0,x) /\
      dist (v0,x) < #1.255 /\
      dist (u,v0) <= dist (u,x) + dist (v0,x)) /\
     dist (u,v0) < &2 * #1.255 ` ] THEN 
MATCH_MP_TAC (MESON[] `((?u. u = v0 /\
           dist (u,v0) < &2 * #1.255 /\
           u IN s /\
           v0 IN s /\
           dist (v0,x) < #1.255 /\
           dist (u,v0) <= dist (u,x) + dist (v0,x) /\
           (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
      (?u. ~(u = v0) /\
           u IN s /\
           v0 IN s /\
           ((dist (u,x) < dist (v0,x) /\
             dist (v0,x) < #1.255 /\
             dist (u,v0) <= dist (u,x) + dist (v0,x)) /\
            dist (u,v0) < &2 * #1.255) /\
           (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)))
      ==> (?w. w IN s /\
               dist (v0,w) < &2 * #1.255 /\
               (!w'. s w' /\ ~(w' = w) ==> dist (w,x) < dist (w',x))))
     ==> packing s /\
         ~(s = {}) /\
         Z =
         UNIONS
         {e_plane u v | u IN s /\
                        dist (u,v0) < &2 * #1.255 /\
                        v IN s /\
                        dist (v,v0) < &2 * #1.255} /\
         dist (v0,x) < #1.255 /\
         ~(?u v.
               u IN s /\
               dist (u,v0) < &2 * #1.255 /\
               v IN s /\
               dist (v,v0) < &2 * #1.255 /\
               ~(u = v) /\
               dist (u,x) = dist (v,x)) /\
         ((?u. u = v0 /\
               dist (u,v0) < &2 * #1.255 /\
               u IN s /\
               v0 IN s /\
               dist (v0,x) < #1.255 /\
               dist (u,v0) <= dist (u,x) + dist (v0,x) /\
               (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
          (?u. ~(u = v0) /\
               u IN s /\
               v0 IN s /\
               ((dist (u,x) < dist (v0,x) /\
                 dist (v0,x) < #1.255 /\
                 dist (u,v0) <= dist (u,x) + dist (v0,x)) /\
                dist (u,v0) < &2 * #1.255) /\
               (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)))) /\
         v0 IN s
     ==> (?w. w IN s /\
              dist (v0,w) < &2 * #1.255 /\
              (!w'. s w' /\ ~(w' = w) ==> dist (w,x) < dist (w',x))) `) THEN 
MESON_TAC [DIST_SYM; SET_RULE ` ! x s. s x <=> x IN s ` ]);;





(* lemma of lemma 8.2 *) 
(* OK g ` ! (x:real^3) (v0:real^3) s Z. centered_pac s v0 /\ Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
 x IN normball v0 t0 DIFF Z
 ==> (?w. w IN near2t0 v0 s /\ x IN voronoi w s)`;;
e (REPEAT GEN_TAC THEN REWRITE_TAC[centered_pac]);;
e (REWRITE_TAC[ SET_RULE `packing s /\ v0 IN s <=> packing s /\ v0 IN s /\ ~(s={})`]);;
e (REWRITE_TAC[MESON[exists_min_dist] ` (packing s /\ v0 IN s /\ ~(s = {})) /\
 Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
 x IN normball v0 t0 DIFF Z  <=>(packing s /\ v0 IN s /\ ~(s = {})) /\
 Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
 x IN normball v0 t0 DIFF Z /\ min_dist x s `]);;
e (SIMP_TAC[normball; min_dist]);;
e (REWRITE_TAC[SET_RULE` x IN a DIFF b <=> x IN a /\ ~( x IN b )`]);;
e (REWRITE_TAC[SET_RULE ` x IN { x | P x } <=> P x `] THEN PHA );;
e (REWRITE_TAC[MESON[]` dist (x,v0) < t0 /\
 ~(x IN Z) /\
 ((?u. u IN s /\ (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
  (?u v.
       u IN s /\
       v IN s /\
       ~(u = v) /\
       dist (u,x) = dist (v,x) /\
       (!w. w IN s ==> dist (u,x) <= dist (w,x)))) <=>
  dist (x,v0) < t0 /\
 ~(x IN Z) /\
 ((?u. u IN s /\ (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
  ( ~(x IN Z) /\ (?u v.
       u IN s /\
       v IN s /\
       ~(u = v) /\
       dist (u,x) = dist (v,x) /\
       (!w. w IN s ==> dist (u,x) <= dist (w,x)) /\ dist (x,v0) < t0 ))) `]);;
e (REWRITE_TAC[MESON[DIST_TRIANGLE] ` v0 IN s /\
     ~(s = {}) /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
     dist (x,v0) < t0 /\
     ~(x IN Z) /\
     ((?u. u IN s /\ (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
      ~(x IN Z) /\
      (?u v.
           u IN s /\
           v IN s /\
           ~(u = v) /\
           dist (u,x) = dist (v,x) /\
           (!w. w IN s ==> dist (u,x) <= dist (w,x)) /\
           dist (x,v0) < t0)) <=>
     v0 IN s /\
     ~(s = {}) /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
     dist (x,v0) < t0 /\
     ~(x IN Z) /\
     ((?u. u IN s /\ (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
      ~(x IN Z) /\
      (?u v.
           u IN s /\
           dist (u,v0) <= dist (u,x) + dist (x,v0) /\
           dist (u,x) <= dist (v0,x) /\
           v IN s /\
           dist (v,v0) <= dist (v,x) + dist (x,v0) /\
           dist (v,x) <= dist (v0,x) /\
           ~(u = v) /\
           dist (u,x) = dist (v,x) /\
           (!w. w IN s ==> dist (u,x) <= dist (w,x)) /\
           dist (x,v0) < t0)) `]);;
e (REWRITE_TAC[MESON[] ` u IN s /\
     dist (u,v0) <= dist (u,x) + dist (x,v0) /\
     dist (u,x) <= dist (v0,x) /\
     v IN s /\
     dist (v,v0) <= dist (v,x) + dist (x,v0) /\
     dist (v,x) <= dist (v0,x) /\
     ~(u = v) /\
     dist (u,x) = dist (v,x) /\
     (!w. w IN s ==> dist (u,x) <= dist (w,x)) /\
     dist (x,v0) < t0 <=>
     u IN s /\
     (dist (u,v0) <= dist (u,x) + dist (x,v0) /\
      dist (u,x) <= dist (v0,x) /\
      dist (x,v0) < t0) /\
     v IN s /\
     (dist (v,v0) <= dist (v,x) + dist (x,v0) /\
      dist (v,x) <= dist (v0,x) /\
      dist (x,v0) < t0) /\
     ~(u = v) /\
     dist (u,x) = dist (v,x) /\
     (!w. w IN s ==> dist (u,x) <= dist (w,x))`]);;
e (SIMP_TAC[DIST_SYM]);;
e (REWRITE_TAC[REAL_ARITH ` dist (u,v0) <= dist (u,x) + dist (v0,x) /\
        dist (u,x) <= dist (v0,x) /\
        dist (v0,x) < t0
  <=> dist (u,v0) <= dist (u,x) + dist (v0,x) /\
        dist (u,x) <= dist (v0,x) /\
        dist (v0,x) < t0 /\ dist(u, v0) < &2 * t0 `]);;
e (REWRITE_TAC[ MESON[] ` a /\ b /\c/\ d /\ e ==> f <=> a/\b/\c/\d ==> e ==> f `] THEN SIMP_TAC[]);;
e (REWRITE_TAC[ IN_UNIONS; e_plane; near2t0]);;
e (REWRITE_TAC[SET_RULE ` x IN { x | P x } <=> P x `]);;
e (REWRITE_TAC[IN_ELIM_THM]);;
e (REWRITE_TAC[ MESON[] ` (?t. (?u v.
                 ((u IN s /\ dist (v0,u) < &2 * t0) /\
                  v IN s /\
                  dist (v0,v) < &2 * t0) /\
                 t = e_plane u v) /\
            x IN t ) 
  <=> (?u v.
                 ((u IN s /\ dist (v0,u) < &2 * t0) /\
                  v IN s /\
                  dist (v0,v) < &2 * t0) /\
                 x IN e_plane u v) `]);;
e (REWRITE_TAC[ SET_RULE ` x IN e_plane u v <=> e_plane u v x `; e_plane]);;
e (PHA THEN SIMP_TAC[ MESON[DIST_SYM] ` ~(?u v.
            u IN s /\
            dist (v0,u) < &2 * t0 /\
            v IN s /\
            dist (v0,v) < &2 * t0 /\
            ~(u = v) /\
            dist (u,x) = dist (v,x)) /\
      (?u v.
           u IN s /\
           dist (u,v0) <= dist (u,x) + dist (v0,x) /\
           dist (u,x) <= dist (v0,x) /\
           dist (v0,x) < t0 /\
           dist (u,v0) < &2 * t0 /\
           v IN s /\
           dist (v,v0) <= dist (v,x) + dist (v0,x) /\
           dist (v,x) <= dist (v0,x) /\
           dist (v0,x) < t0 /\
           dist (v,v0) < &2 * t0 /\
           ~(u = v) /\
           dist (u,x) = dist (v,x) /\
           (!w. w IN s ==> dist (u,x) <= dist (w,x))) <=> F `]);;
e (REWRITE_TAC[voronoi]);;
(* doing *) 
e (REWRITE_TAC[ SET_RULE ` x IN { x | P x } <=> P x `]);;
e (REWRITE_TAC[ MESON[] ` dist (v0,x) < t0 /\
     ~(?u v.
           u IN s /\
           dist (v0,u) < &2 * t0 /\
           v IN s /\
           dist (v0,v) < &2 * t0 /\
           ~(u = v) /\
           dist (u,x) = dist (v,x)) /\
     (?u. u IN s /\ (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)))
  <=> dist (v0,x) < t0 /\
     ~(?u v.
           u IN s /\
           dist (v0,u) < &2 * t0 /\
           v IN s /\
           dist (v0,v) < &2 * t0 /\
           ~(u = v) /\
           dist (u,x) = dist (v,x)) /\
     (?u. u IN s /\dist (v0,x) < t0  /\  (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)))`]);;
e (REWRITE_TAC[ MESON[DIST_TRIANGLE] `(?u. u IN s /\
          dist (v0,x) < t0 /\
          (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) <=>
     (?u. u IN s /\
          dist (v0,x) < t0 /\
          dist (u,v0) <= dist (u,x) + dist (x,v0) /\
          (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) `]);;
e (REWRITE_TAC[ MESON[] ` ( a ==> b==> c <=> a/\b ==> c ) `] THEN PHA);;
e (ONCE_REWRITE_TAC[ MESON[] ` a /\ b /\ c ==> d <=> a/\c /\b ==> d `] THEN PHA);;
e (ONCE_REWRITE_TAC[MESON[] ` !P. (?u. P u) /\ v0 IN s <=>
         ((?u. u = v0 /\ P u) \/ (?u. ~(u = v0) /\ P u)) /\ v0 IN s`]);;
e (REWRITE_TAC[t0]);;
e (ONCE_REWRITE_TAC[MESON[ DIST_REFL; REAL_ARITH ` &0 < &2 * #1.255 ` ] ` u = v0 /\ las  <=> u = v0  /\ dist(u,v0 ) < &2 * #1.255 /\ las `]);;
e (REWRITE_TAC[ MESON[] ` ((?u. u = v0 /\
           dist (u,v0) < &2 * #1.255 /\
           u IN s /\
           dist (v0,x) < #1.255 /\
           dist (u,v0) <= dist (u,x) + dist (x,v0) /\
           (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
      (?u. ~(u = v0) /\
           u IN s /\
           dist (v0,x) < #1.255 /\
           dist (u,v0) <= dist (u,x) + dist (x,v0) /\
           (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)))) /\
     v0 IN s <=>
     ((?u. u = v0 /\
           dist (u,v0) < &2 * #1.255 /\
           u IN s /\
           v0 IN s /\
           dist (v0,x) < #1.255 /\
           dist (u,v0) <= dist (u,x) + dist (x,v0) /\
           (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
      (?u. ~(u = v0) /\
           u IN s /\
           v0 IN s /\
           dist (v0,x) < #1.255 /\
           dist (u,v0) <= dist (u,x) + dist (x,v0) /\
           (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)))) /\
     v0 IN s `]);;
e (REWRITE_TAC[ MESON[] ` ~(u = v0) /\
     u IN s /\
     v0 IN s /\
     dist (v0,x) < #1.255 /\
     dist (u,v0) <= dist (u,x) + dist (x,v0) /\
     (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)) <=>
     ~(u = v0) /\
    
     u IN s /\
     v0 IN s /\ (  dist (u,x) < dist (v0,x) /\
     dist (v0,x) < #1.255 /\
     dist (u,v0) <= dist (u,x) + dist (x,v0) ) /\
     (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)) `] THEN SIMP_TAC[DIST_SYM] );;
e (PURE_ONCE_REWRITE_TAC[ REAL_ARITH `  ( dist (u,x) < dist (v0,x) /\
     dist (v0,x) < #1.255 /\
     dist (u,v0) <= dist (u,x) + dist (v0,x))  <=>
     (dist (u,x) < dist (v0,x) /\
      dist (v0,x) < #1.255 /\
      dist (u,v0) <= dist (u,x) + dist (v0,x)) /\
     dist (u,v0) < &2 * #1.255 ` ]);;
e (MATCH_MP_TAC (MESON[] `((?u. u = v0 /\
           dist (u,v0) < &2 * #1.255 /\
           u IN s /\
           v0 IN s /\
           dist (v0,x) < #1.255 /\
           dist (u,v0) <= dist (u,x) + dist (v0,x) /\
           (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
      (?u. ~(u = v0) /\
           u IN s /\
           v0 IN s /\
           ((dist (u,x) < dist (v0,x) /\
             dist (v0,x) < #1.255 /\
             dist (u,v0) <= dist (u,x) + dist (v0,x)) /\
            dist (u,v0) < &2 * #1.255) /\
           (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)))
      ==> (?w. w IN s /\
               dist (v0,w) < &2 * #1.255 /\
               (!w'. s w' /\ ~(w' = w) ==> dist (w,x) < dist (w',x))))
     ==> packing s /\
         ~(s = {}) /\
         Z =
         UNIONS
         {e_plane u v | u IN s /\
                        dist (u,v0) < &2 * #1.255 /\
                        v IN s /\
                        dist (v,v0) < &2 * #1.255} /\
         dist (v0,x) < #1.255 /\
         ~(?u v.
               u IN s /\
               dist (u,v0) < &2 * #1.255 /\
               v IN s /\
               dist (v,v0) < &2 * #1.255 /\
               ~(u = v) /\
               dist (u,x) = dist (v,x)) /\
         ((?u. u = v0 /\
               dist (u,v0) < &2 * #1.255 /\
               u IN s /\
               v0 IN s /\
               dist (v0,x) < #1.255 /\
               dist (u,v0) <= dist (u,x) + dist (v0,x) /\
               (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x))) \/
          (?u. ~(u = v0) /\
               u IN s /\
               v0 IN s /\
               ((dist (u,x) < dist (v0,x) /\
                 dist (v0,x) < #1.255 /\
                 dist (u,v0) <= dist (u,x) + dist (v0,x)) /\
                dist (u,v0) < &2 * #1.255) /\
               (!w. w IN s /\ ~(u = w) ==> dist (u,x) < dist (w,x)))) /\
         v0 IN s
     ==> (?w. w IN s /\
              dist (v0,w) < &2 * #1.255 /\
              (!w'. s w' /\ ~(w' = w) ==> dist (w,x) < dist (w',x))) `));;
e (MESON_TAC [DIST_SYM; SET_RULE ` ! x s. s x <=> x IN s ` ]);;
let lemma_of_lemma82 = top_thm();; OK *) 

(* lemma 8.2 *)





let le1_82 = prove (`!s v0 Y.
     centered_pac s v0 /\
     w IN near2t0 v0 s /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s}
     ==> UNIONS {aff_ge {w} {w1, w2} | w1,w2 | {w, w1, w2} IN barrier s} SUBSET
         Y`, SIMP_TAC[] THEN SET_TAC[]);;





let v_near2t0_v = MESON[near2t0; t0; DIST_REFL; SET_RULE ` x IN { x | P x} <=> P x ` ;
 REAL_ARITH ` &0 < &2 * #1.255 `] ` w IN s  ==>  w IN near2t0 w s  `;;


(* haven't added to database_more *)
let in_VC = prove( 
`!w s x.
     w IN s /\
     dist (w,x) < &2 /\
     (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
     ~obstructed w x s
     ==> x IN VC w s`, REWRITE_TAC[ VC; lambda_x ; d3; IN_ELIM_THM] THEN 
  MESON_TAC[ DIST_SYM; SET_RULE ` i IN x <=> x i `]);;







let rhand_subset_lhand = prove (` ! (s:real^3 -> bool) (v0:real^3) Z Y.
     centered_pac s v0 /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s}
     ==> 
         normball v0 t0 INTER voronoi v0 s DIFF (Y UNION Z) SUBSET 
 normball v0 t0 INTER VC v0 s DIFF (Y UNION Z)`, REWRITE_TAC[ SET_RULE ` a INTER b DIFF c SUBSET a INTER d DIFF c <=>
     (!x. x IN a INTER b DIFF c ==> x IN d) ` ] THEN 
REWRITE_TAC[ GSYM (     MESON[centered_pac; le1_82; prove (` ! x s. centered_pac s x ==> x IN near2t0 x s `, REWRITE_TAC[ 
  centered_pac; near2t0] THEN REWRITE_TAC[ MESON [DIST_REFL; t0; REAL_ARITH ` &0 < &2 * #1.255 `] `
  packing s /\ v0 IN s <=> packing s /\ v0 IN s /\ dist (v0,v0) < &2 * t0`] THEN 
  SET_TAC[] ) ] ` !s v0 Z Y.
   centered_pac s v0 /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
     UNIONS {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s} SUBSET
     Y
     ==> last <=>
     centered_pac s v0 /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s}
     ==> last `)] THEN 
REWRITE_TAC[SET_RULE ` x IN a INTER b DIFF c <=> x IN a /\ x IN b /\ ~( x IN c )`] THEN 
REWRITE_TAC[ MESON[] ` centered_pac s v0 /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
     UNIONS {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s} SUBSET
     Y
     ==> (!x. x IN normball v0 t0 /\ x IN voronoi v0 s /\ ~(x IN Y UNION Z)
              ==> x IN VC v0 s) <=>
     centered_pac s v0 /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
     UNIONS {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s} SUBSET
     Y
     ==> (!x. x IN normball v0 t0 /\
              x IN voronoi v0 s /\
              ~(x IN Y UNION Z) /\
              UNIONS
              {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s} SUBSET
              Y
              ==> x IN VC v0 s) `] THEN 
ONCE_REWRITE_TAC[ SET_RULE ` ~(x IN Y UNION Z) /\
     UNIONS {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s} SUBSET
     Y <=>
     ~(x IN
       UNIONS {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s}) /\
     ~(x IN Y UNION Z) /\
     UNIONS {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s} SUBSET
     Y `] THEN REWRITE_TAC[ centered_pac ] THEN 
REWRITE_TAC[ MESON[] ` (packing s /\ v0 IN s) /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
     UNIONS {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s} SUBSET
     Y
     ==> (!x. x IN normball v0 t0 /\
              x IN voronoi v0 s /\
              ~(x IN
                UNIONS
                {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s}) /\
              ~(x IN Y UNION Z) /\
              UNIONS
              {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s} SUBSET
              Y
              ==> x IN VC v0 s) <=>
     (packing s /\ v0 IN s) /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s} /\
     UNIONS {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s} SUBSET
     Y
     ==> (!x. v0 IN s /\
              x IN normball v0 t0 /\
              x IN voronoi v0 s /\
              ~(x IN
                UNIONS
                {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s}) /\
              ~(x IN Y UNION Z) /\
              UNIONS
              {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s} SUBSET
              Y
              ==> x IN VC v0 s) `] THEN 
REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[normball] THEN 
REWRITE_TAC[ SET_RULE ` z IN { x | P x } <=> P z `] THEN 
REWRITE_TAC[ voronoi; VC; lambda_x; d3 ] THEN 
REWRITE_TAC[ SET_RULE ` x IN { x | P x } <=> P x `] THEN 
REWRITE_TAC[MESON[DIST_SYM ; import_le ] ` v0 IN s /\
     dist (x,v0) < t0 /\
     (!w. s w /\ ~(w = v0) ==> dist (x,v0) < dist (x,w)) /\
     ~(x IN
       UNIONS {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s}) /\
     ~(x IN Y UNION Z) /\
     UNIONS {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s} SUBSET
     Y <=>
     v0 IN s /\
     dist (x,v0) < t0 /\
     (!w. s w /\ ~(w = v0) ==> dist (x,v0) < dist (x,w)) /\
     ~(x IN
       UNIONS {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s}) /\
     ~(x IN Y UNION Z) /\
     UNIONS {aff_ge {v0} {w1, w2} | w1,w2 | {v0, w1, w2} IN barrier s} SUBSET
     Y /\
     ~obstructed v0 x s `] THEN 
ONCE_REWRITE_TAC[MESON[t0; REAL_ARITH ` #1.255 < &2 /\ (! a b (c:real). a < b 
/\ b < c ==> a < c ) `; DIST_SYM ]` dist ( x, v0 ) < t0 <=> dist ( x, v0 ) < t0 /\
 dist ( v0, x) < &2 `] THEN 
SIMP_TAC[ DIST_SYM ] THEN 
MESON_TAC[ SET_RULE ` ! s x. s x <=> x IN s `]);;






let lhand_subset_rhand = prove(`  ! (s:real^3 -> bool) (v0:real^3) Z Y.
     centered_pac s v0 /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s}
     ==> normball v0 t0 INTER VC v0 s DIFF (Y UNION Z) SUBSET 
         normball v0 t0 INTER voronoi v0 s DIFF (Y UNION Z)`,
REWRITE_TAC[ SET_RULE ` a INTER b DIFF c SUBSET a INTER d DIFF c <=>
     a INTER b DIFF c DIFF d = {} `] THEN 
REWRITE_TAC[ SET_RULE ` a = {} <=> (! x. ~ (x IN a))`] THEN 
REWRITE_TAC[ SET_RULE` x IN a DIFF b <=> x IN a /\ ~( x IN b ) `] THEN 
REWRITE_TAC[ SET_RULE ` x IN a INTER b <=> x IN a /\ x IN b `] THEN PHA THEN 
REWRITE_TAC[ SET_RULE ` x IN normball v0 t0 /\ x IN VC v0 s /\ ~(x IN Y UNION Z) /\ P x  <=>
     x IN normball v0 t0 DIFF Z /\ x IN VC v0 s /\ ~(x IN Y UNION Z) /\ P x  `] THEN 
REWRITE_TAC[MESON[lemma_of_lemma82]`
  centered_pac s v0 /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s}
     ==> (!x. ~(x IN normball v0 t0 DIFF Z /\
                x IN VC v0 s /\
                ~(x IN Y UNION Z) /\
                ~(x IN voronoi v0 s))) <=>
     centered_pac s v0 /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s}
     ==> (!x. ~(x IN normball v0 t0 DIFF Z /\
                (?w. w IN near2t0 v0 s /\ x IN voronoi w s) /\
                x IN VC v0 s /\
                ~(x IN Y UNION Z) /\
                ~(x IN voronoi v0 s))) `] THEN 
REWRITE_TAC[ MESON[] ` 
  (?w. w IN near2t0 v0 s /\ x IN voronoi w s) /\
     x IN VC v0 s /\
     ~(x IN Y UNION Z) /\
     ~(x IN voronoi v0 s) <=>
     (?w. w IN near2t0 v0 s /\ x IN voronoi w s /\ ~(w = v0)) /\
     x IN VC v0 s /\
     ~(x IN Y UNION Z) /\
     ~(x IN voronoi v0 s) `] THEN 
REWRITE_TAC[ MESON[near2t0] ` 
  (?w. w IN near2t0 v0 s /\ x IN voronoi w s /\ ~(w = v0)) <=>
     (?w. w IN {x | x IN s /\ dist (v0,x) < &2 * t0} /\
          x IN voronoi w s /\
          ~(w = v0)) `] THEN 
REWRITE_TAC[ SET_RULE` a IN { a | p a } <=> p a `] THEN 
REWRITE_TAC[ voronoi; lambda_x] THEN 
REWRITE_TAC[ SET_RULE ` x IN { v | P v } <=> P x `] THEN PHA THEN 
REWRITE_TAC[ MESON[] ` a /\ b /\ d ==> c <=> b /\ d ==> a ==> c `] THEN 
REPEAT GEN_TAC THEN DISCH_TAC THEN 
REWRITE_TAC[centered_pac] THEN 
MATCH_MP_TAC (MESON[]` (a /\ b ==> (!x. ~b \/ P x)) ==> a /\ b ==> (!x. P x)`) THEN 
REWRITE_TAC[ MESON[] ` ~(v0 IN s) \/ ~(x IN normball v0 t0 DIFF Z /\ last) <=>
     ~(v0 IN s /\ x IN normball v0 t0 DIFF Z /\ last)`] THEN 
REWRITE_TAC[ MESON[]` 
  v0 IN s /\
     x IN normball v0 t0 DIFF Z /\
     (?w. w IN s /\
          dist (v0,w) < &2 * t0 /\
          (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
          ~(w = v0)) /\
     last <=>
     x IN normball v0 t0 DIFF Z /\
     (?w. w IN s /\
          v0 IN s /\
          dist (v0,w) < &2 * t0 /\
          (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
          ~(w = v0)) /\
     last`] THEN 
REWRITE_TAC[ MESON[ SET_RULE` x IN s <=> s x `] `
  (?w. w IN s /\
          v0 IN s /\
          dist (v0,w) < &2 * t0 /\
          (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
          ~(w = v0)) <=>
     (?w. w IN s /\
          v0 IN s /\
          dist (x,w) < dist (x,v0) /\
          dist (v0,w) < &2 * t0 /\
          (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
          ~(w = v0)) `] THEN 
REWRITE_TAC[ SET_RULE ` x IN a DIFF b <=> x IN a /\ ~ ( x IN b ) `] THEN 
REWRITE_TAC[ MESON[normball ; SET_RULE `x IN { x | p x } <=> p x `] ` x IN normball v0 t0 
  <=> dist (x,v0) < t0 `] THEN 
REWRITE_TAC[ MESON[REAL_ARITH ` a < b /\ b < c ==> a < c `]`
  (dist (x,v0) < t0 /\ ~(x IN Z)) /\
            (?w. w IN s /\
                 v0 IN s /\
                 dist (x,w) < dist (x,v0) /\
                 dist (v0,w) < &2 * t0 /\
                 (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
                 ~(w = v0)) /\ las 
  <=> (dist (x,v0) < t0 /\ ~(x IN Z)) /\
            (?w. w IN s /\
                 v0 IN s /\ dist(x,w) < t0 /\
                 dist (x,w) < dist (x,v0) /\
                 dist (v0,w) < &2 * t0 /\
                 (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
                 ~(w = v0)) /\ las  `] THEN 


ASM_SIMP_TAC[] THEN PHA THEN 
REWRITE_TAC[ MESON[] ` a /\ b /\ c /\ d /\ las <=> (a /\ d ) /\ b /\ c /\ las `] THEN 
ONCE_REWRITE_TAC[ MESON[near2t0; SET_RULE ` x IN { x | p x } <=> p x ` ]` (w IN s /\ dist (v0,w) < &2 * t0) <=>
  w IN near2t0 v0 s /\ (w IN s /\ dist (v0,w) < &2 * t0) `] THEN 
REWRITE_TAC[ SET_RULE ` ~ ( x IN a UNION b) <=> ~( x IN a ) /\ ~ (x IN b)`] THEN PHA THEN 
 SIMP_TAC[MESON[] ` a /\ a /\ b <=> a /\ b `] THEN 
REWRITE_TAC[ MESON[] ` a/\ b /\ ( ? w. P w ) /\ la <=> b /\ ( ? w. a /\ P w ) /\ la `] THEN 
ONCE_REWRITE_TAC[  MESON[ SET_RULE ` w IN near2t0 v0 s
     ==> UNIONS {aff_ge {w} {w1, w2} | w1,w2 | {w, w1, w2} IN barrier s} SUBSET
         UNIONS
         {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} `]
  `  w IN near2t0 v0 s /\
                 w IN s /\ last 
  <=> UNIONS {aff_ge {w} {w1, w2} | w1,w2 | {w, w1, w2} IN barrier s} SUBSET
         UNIONS
         {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} /\
  w IN near2t0 v0 s /\
                 w IN s /\ last `] THEN 
REWRITE_TAC[ MESON[] ` a /\ b /\ c /\ d /\ last <=> a /\ b /\ ( c/\ d ) /\ last `] THEN 
REWRITE_TAC[ SET_RULE ` ~ ( x IN a ) /\ b SUBSET a <=> ~ ( x IN a )/\ ~( x IN b ) /\ b SUBSET a`] THEN PHA THEN 
REWRITE_TAC[ MESON[DIST_SYM; import_le ] ` dist (x,v0) < t0 /\
                 x IN VC v0 s /\
                 ~(x IN
                   UNIONS
                   {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\
                                          {w, w1, w2} IN barrier s}) /\
                 ~(x IN
                   UNIONS
                   {aff_ge {w} {w1, w2} | w1,w2 | {w, w1, w2} IN barrier s}) /\
                 UNIONS
                 {aff_ge {w} {w1, w2} | w1,w2 | {w, w1, w2} IN barrier s} SUBSET
                 UNIONS
                 {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\
                                        {w, w1, w2} IN barrier s} /\
                 w IN near2t0 v0 s /\
                 w IN s /\
                 dist (v0,w) < &2 * t0 /\
                 (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
                 dist (x,w) < t0 /\
                 dist (x,w) < dist (x,v0) /\
                 ~(w = v0)
  <=> dist (x,v0) < t0 /\
                 x IN VC v0 s /\
                 ~(x IN
                   UNIONS
                   {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\
                                          {w, w1, w2} IN barrier s}) /\
                 ~(x IN
                   UNIONS
                   {aff_ge {w} {w1, w2} | w1,w2 | {w, w1, w2} IN barrier s}) /\
                 UNIONS
                 {aff_ge {w} {w1, w2} | w1,w2 | {w, w1, w2} IN barrier s} SUBSET
                 UNIONS
                 {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\
                                        {w, w1, w2} IN barrier s} /\
                 w IN near2t0 v0 s /\
                 w IN s /\
                 dist (v0,w) < &2 * t0 /\
                 (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
                 dist (x,w) < t0 /\
                 dist (x,w) < dist (x,v0) /\
                 ~(w = v0) /\ ~obstructed w x s `] THEN 
ONCE_REWRITE_TAC[ MESON[t0; REAL_ARITH ` #1.255 < &2 /\ (! a b c. a < b /\ b < c ==> a < c )` ] `
  dist (x,w) < t0 /\ dist (x,w) < dist (x,v0) /\ last <=>
     dist (x,w) < &2 /\ dist (x,w) < t0 /\ dist (x,w) < dist (x,v0) /\ last`] THEN 
REWRITE_TAC[ MESON[ in_VC; DIST_SYM ] `w IN s /\
     dist (v0,w) < &2 * t0 /\
     (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
     dist (x,w) < &2 /\
     dist (x,w) < t0 /\
     dist (x,w) < dist (x,v0) /\
     ~(w = v0) /\
     ~obstructed w x s <=>
     dist (v0,w) < &2 * t0 /\
     dist (x,w) < t0 /\
     ~(w = v0) /\
     dist (x,w) < dist (x,v0) /\
     w IN s /\
     (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
     dist (x,w) < &2 /\
     ~obstructed w x s` ]  THEN 
REWRITE_TAC[ MESON[DIST_SYM] ` dist(x,w) < &2 <=> dist (w,x) < &2 `] THEN 
REWRITE_TAC[MESON[in_VC]` w IN s /\
                 (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
                 dist (w,x) < &2 /\
                 ~obstructed w x s
  <=> w IN s /\
                 (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
                 dist (w,x) < &2 /\
                 ~obstructed w x s /\ x IN VC w s ` ] THEN 
REWRITE_TAC[ MESON[]`  ~(w = v0) /\
                 dist (x,w) < dist (x,v0) /\
                 w IN s /\
                 (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
                 dist (w,x) < &2 /\
                 ~obstructed w x s /\
                 x IN VC w s <=> 
   
                 dist (x,w) < dist (x,v0) /\
                 w IN s /\
                 (!w'. s w' /\ ~(w' = w) ==> dist (x,w) < dist (x,w')) /\
                 dist (w,x) < &2 /\
                 ~obstructed w x s /\
               ~(w = v0) /\  x IN VC w s `] THEN 
ONCE_REWRITE_TAC[ MESON[]` dist (x,v0) < t0 /\
                 x IN VC v0 s /\ last <=> dist (x,v0) < t0  /\ last /\ x IN VC v0 s `]
THEN PHA THEN
ONCE_REWRITE_TAC[SET_RULE ` x IN a /\ x IN b <=> ~ ( a INTER b = {} ) /\ x IN a /\ x IN b `] THEN 
SIMP_TAC[ MESON[VC_DISJOINT ] `  ~(w = v0) /\
                 ~(VC w s INTER VC v0 s = {}) /\
                 x IN VC w s /\
                 x IN VC v0 s <=> F `]);;

let lemma_8_2 = prove (`! (s:real^3 -> bool) (v0:real^3) Z Y.
     centered_pac s v0 /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s}
     ==> normball v0 t0 INTER VC v0 s DIFF (Y UNION Z) =
         normball v0 t0 INTER voronoi v0 s DIFF (Y UNION Z)`,
  REWRITE_TAC[ SET_RULE ` a ==> (b = c) <=> a ==>( b SUBSET c /\ c SUBSET b ) `]
  THEN MESON_TAC[ lhand_subset_rhand; rhand_subset_lhand] );;
