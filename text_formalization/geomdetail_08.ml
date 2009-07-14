
(* tchales, This does not run in Multivariate *)


let TRIANGLE_IN_BARRIER = prove(` ! s v0 v1 v2 . {v0, v1, v2} IN barrier s
 ==> (!xx yy.
          ~(xx = yy) /\ {xx, yy} SUBSET {v1, v2, v0}
          ==> &2 <= dist (xx,yy) /\ dist (xx,yy) <= sqrt (&8)) /\
     ((!aa bb.
           aa IN {v1, v2, v0} /\ bb IN {v1, v2, v0} ==> dist (aa,bb) <= #2.51) \/
      (?aa bb.
           {aa, bb} SUBSET {v1, v2, v0} /\
           #2.51 < dist (aa,bb) /\
           (!x y.
                ~({x, y} = {aa, bb}) /\ {x, y} SUBSET {v1, v2, v0}
                ==> dist (x,y) <= #2.51)))`,
REWRITE_TAC[ barrier; IN_ELIM_THM] THEN 
REWRITE_TAC[ GSYM (MESON[]` P {x, y, z} <=> 
       (?a b c. P {a, b, c} /\ {x, y, z} = {a, b, c})`)] THEN 
MP_TAC A_LEMMA THEN 
REWRITE_TAC[ MESON[]` (! a b c d. P a b c d ==> las a b c d ) ==> (! a b c d .
  P a b c d \/ Q a b c d ==> las a b c d) <=> 
  (! a b c d. P a b c d ==> las a b c d ) ==> (! a b c d .
  Q a b c d ==> las a b c d)`] THEN DISCH_TAC THEN 
NHANH (CUTHE2 CASES_OF_Q_SYS) THEN 
REPEAT GEN_TAC THEN 
MATCH_MP_TAC (MESON[]` ((? a. Q a) ==> l) /\ ((?a. R a ) ==> l) ==> 
  (? a. P a /\ ( Q a \/ R a )) ==> l `) THEN 
REWRITE_TAC[ NOV1] THEN 
NHANH (CUTHE4 TRIANGLE_IN_STRICT_QUA) THEN 
MATCH_MP_TAC (MESON[]` (b ==> l) /\ ( a /\ c ==> l) ==> a /\ ( b \/ c ) ==> l`) THEN 
ASM_REWRITE_TAC[] THEN 
REWRITE_TAC[ strict_qua; quarter; SET_RULE `{a,b,c} UNION {d} = {a,b,c,d}`;  def_simplex] THEN 
PHA THEN 
REWRITE_TAC[ MESON[]` a /\ a /\ l <=> a /\ l `; packing ] THEN 
MATCH_MP_TAC (MESON[] `(a ==> aa) /\ (b ==> bb) ==> a /\ b ==> aa /\ (cc \/ bb)`) THEN 
SIMP_TAC[ SET_RULE `{a,b,c} = {c,a,b} `] THEN 
NHANH (SET_RULE `  {v0, v1, v2, v4} SUBSET s ==> {v0,v1,v2} SUBSET s `) THEN 
NHANH ( MESON[SET_RULE ` x IN a /\ a SUBSET s ==> s x `]`(!u v. s u /\ s v /\ ~(u = v) ==> &2 <= dist (u,v)) /\
       ({v0, v1, v2, v4} SUBSET s /\ {v0, v1, v2} SUBSET s) /\ l ==>
  (!u v. u IN {v0,v1,v2} /\ v IN {v0,v1,v2} /\ ~(u = v) ==> &2 <= dist (u,v))`) THEN 
REWRITE_TAC[t0] THEN 
NHANH ( MESON[PAIR_D3] ` d3 v w <= sqrt (&8) ==> (! x y. x IN {v0, v1, v2, v4} /\
                  y IN {v0, v1, v2, v4} /\ {x,y} = {v,w} ==> d3 x y <= sqrt (&8) )`) THEN 
REWRITE_TAC[ SET_RULE ` {a,b} SUBSET s <=> a IN s /\ b IN s `] THEN 
SIMP_TAC[ SET_RULE ` {a,b,c} = {c,a,b} `] THEN 
REWRITE_TAC[ GSYM d3 ] THEN 
MESON_TAC[ MATCH_MP REAL_LE_RSQRT (REAL_ARITH ` (&2 * #1.255 ) pow 2 <= &8 `);
  SET_RULE ` x IN {a,b,c} ==> x IN {a,b,c,d} `; REAL_ARITH ` a <= b /\ b <= c ==> a <= c `]);;

(* ============== *)



(* lemma 8.2 *)





let le1_82 = prove (`!s v0 Y.
     centered_pac s v0 /\
     w IN near2t0 v0 s /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s}
     ==> UNIONS {aff_ge {w} {w1, w2} | w1,w2 | {w, w1, w2} IN barrier s} SUBSET
         Y`, SIMP_TAC[] THEN SET_TAC[]);;



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



(* ++++++++++++++++++++++++++++ *)




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


(* +++++++++++++++++++++++++ *)

let lemma82_FOCUDTG = prove (`! (s:real^3 -> bool) (v0:real^3) Z Y.
     centered_pac s v0 /\
     Y =
     UNIONS
     {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} /\
     Z = UNIONS {e_plane u v | u IN near2t0 v0 s /\ v IN near2t0 v0 s}
     ==> normball v0 t0 INTER VC v0 s DIFF (Y UNION Z) =
         normball v0 t0 INTER voronoi v0 s DIFF (Y UNION Z)`,
  REWRITE_TAC[ SET_RULE ` a ==> (b = c) <=> a ==>( b SUBSET c /\ c SUBSET b ) `]
  THEN MESON_TAC[ lhand_subset_rhand; rhand_subset_lhand] );;

(* ========= END LEMMA 8.2 ======== *)

let a_le_sub = SET_RULE ` w IN near2t0 v0 s
     ==> UNIONS {aff_ge {w} {w1, w2} | w1,w2 | {w, w1, w2} IN barrier s} SUBSET
         UNIONS
         {aff_ge {w} {w1, w2} | w IN near2t0 v0 s /\ {w, w1, w2} IN barrier s} `;;






















(* ============= BEGIN LEMMA 8.3 =========== *)


let barrier' = new_definition ` barrier' v0 s =
         {{a, b, c} | {a, b, c} IN barrier s /\ v0 IN {a, b, c} \/
                      (?q. diagonal a b q s /\ q IN Q_SYS s /\ c IN anchor_points a b s)} `;;


let lemma7_7_CXRHOVG = new_axiom `!s q1 q2 v w.
         {v, w} SUBSET q1 INTER q2 /\ quarter q2 s /\  diagonal v w q1 s /\ q1 IN Q_SYS s
         ==> q2 IN Q_SYS s `;;


let tarski_UMMNOJN = new_axiom` !x w v0 v1 v2.
         ~(conv {x, w} INTER cone v0 {v1, v2} = {}) /\
         dist (x,v0) < dist (x,v1) /\
         dist (x,v0) < dist (x,v2) /\
         dist (x,w) < dist (x,v0) /\
         (!xx yy.
              ~(xx = yy) /\ {xx, yy} SUBSET {v1, v2, v0}
              ==> &2 <= dist (xx,yy) /\ dist (xx,yy) <= sqrt (&8)) /\
         ((!aa bb.
               aa IN {v1, v2, v0} /\ bb IN {v1, v2, v0}
               ==> dist (aa,bb) <= #2.51) \/
          (?aa bb.
               {aa, bb} SUBSET {v1, v2, v0} /\
               #2.51 < dist (aa,bb) /\
               (!x y.
                    ~({x, y} = {aa, bb}) /\ {x, y} SUBSET {v1, v2, v0}
                    ==> dist (x,y) <= #2.51)))
         ==> (!a. a IN {v1, v2, v0} ==> dist (w,a) <= #2.51) /\
             ~(conv {v0, v1, v2} INTER conv0 {x, w} = {}) `;;

(* ================ *)

let TRIANGLE_IN_BARRIER' = prove( 
`!s v0 v1 v2.
     {v0, v1, v2} IN barrier' v0 s
     ==> (!xx yy.
              ~(xx = yy) /\ {xx, yy} SUBSET {v1, v2, v0}
              ==> &2 <= dist (xx,yy) /\ dist (xx,yy) <= sqrt (&8)) /\
  ((!aa bb.
               aa IN {v1, v2, v0} /\ bb IN {v1, v2, v0}
               ==> dist (aa,bb) <= #2.51) \/
          (?aa bb.
               {aa, bb} SUBSET {v1, v2, v0} /\
               #2.51 < dist (aa,bb) /\
               (!x y.
                    ~({x, y} = {aa, bb}) /\ {x, y} SUBSET {v1, v2, v0}
                    ==> dist (x,y) <= #2.51))) `,
REWRITE_TAC[ barrier'; IN_ELIM_THM] THEN MATCH_MP_TAC (MESON[] ` (!s v0 v1 v2.
          (?a b c.
               ({a, b, c} IN barrier s /\ v0 IN {a, b, c} \/
                (?q. diagonal a b q s /\ c IN anchor_points a b s)) /\
               {v0, v1, v2} = {a, b, c})
          ==> las s v0 v1 v2 )
     ==> (!s v0 v1 v2.
              (?a b c.
                   ({a, b, c} IN barrier s /\ v0 IN {a, b, c} \/
                    (?q. diagonal a b q s /\
                         q IN Q_SYS s /\
                         c IN anchor_points a b s)) /\
                   {v0, v1, v2} = {a, b, c})
              ==> las s v0 v1 v2 )`) THEN 
REWRITE_TAC[ MESON[]` ( ? a b c. ( P {a,b,c} \/ Q a b c ) /\ {v0, v1, v2} = {a, b, c} ) <=>
  P {v0, v1, v2} \/ ( ? a b c. Q a b c  /\ {v0, v1, v2} = {a, b, c} ) `] THEN 
REPEAT GEN_TAC THEN 
MATCH_MP_TAC (MESON[]` (a ==> l) /\ (c ==> l) ==> a /\ b \/ c ==> l`) THEN 
REWRITE_TAC[ TRIANGLE_IN_BARRIER] THEN 
NHANH (CUTHE4 DIA_OF_QUARTER) THEN 
REWRITE_TAC[ anchor_points; IN_ELIM_THM; anchor] THEN 
NHANH (MESON[diagonal; quarter] ` diagonal a b q s ==> packing s `) THEN PHA THEN 
REWRITE_TAC[ MESON[] ` packing s /\ aa /\ bb /\ cc /\ {c, a, b} SUBSET s /\ l 
  <=> ( packing s /\ {c, a, b} SUBSET s ) /\ aa /\ bb /\ cc /\ l `] THEN 
NHANH (CUTHE2 SUB_PACKING ) THEN 
REWRITE_TAC[GSYM d3] THEN 
REWRITE_TAC[ REAL_ARITH ` &2 * t0 <= d3 a b <=> d3 a b <= &2 * t0 /\ &2 * t0 = d3 a b  \/ &2 * t0 
  < d3 a b `; t0; REAL_ARITH ` &2 * #1.255 = #2.51 ` ] THEN 
REWRITE_TAC[ SET_RULE ` {x,y} SUBSET s <=> x IN s /\ y IN s`] THEN 
SIMP_TAC[ SET_RULE `!a b c.  {c, a, b} = {a, b, c}`] THEN PHA THEN 
REWRITE_TAC[ MESON[]` a /\ b /\ a /\ l <=> a /\ b /\ l `] THEN 
KHANANG THEN 
REWRITE_TAC[ MESON[]` (?q. P q /\ l1 \/ P q /\ l2) <=> (?q. P q) /\ (l1 \/ l2)`] THEN 
PHA THEN 
MATCH_MP_TAC (MESON[] ` ((? a b c. Q a b c) ==> l) ==> (? a b c. P a b c /\ Q a b c ) ==> l `) THEN 
REWRITE_TAC[ MESON[]` ( a \/ b ) /\ c <=> a /\ c \/ b /\ c `] THEN 
ONCE_REWRITE_TAC[ MESON[]` (d3 a b <= #2.51 /\ l <=> l /\ d3 a b <= #2.51) /\
  (#2.51 < d3 a b /\ l <=> l /\ #2.51 < d3 a b) `] THEN PHA THEN 
REWRITE_TAC[ MESON[]` d3 c a <= #2.51 /\
      d3 c b <= #2.51 /\
      d3 a b <= #2.51 /\ l <=> ( d3 a b <= #2.51 /\
      d3 c a <= #2.51 /\
      d3 c b <= #2.51 ) /\ l `] THEN  
NHANH ( CUTHE3 (
prove(`! a b c. d3 a b <= #2.51 /\ d3 c a <= #2.51 /\
       d3 c b <= #2.51 ==> (!aa bb. aa IN {a,b,c} /\ bb IN {a,b,c} ==> d3 aa bb <= #2.51)`,
REWRITE_TAC[ SET_RULE ` x IN {a,b,c} <=> x = a \/ x= b \/  x= c `] THEN 
MESON_TAC[ D3_REFL; trg_d3_sym; REAL_ARITH ` &0 <= #2.51 `]))) THEN 
REWRITE_TAC[ MESON[] ` d3 a b <= sqrt (&8) /\
     d3 a b >= #2.51 /\
     d3 c a <= #2.51 /\
     d3 c b <= #2.51 /\
     #2.51 < d3 a b /\
     l <=>
     d3 a b >= #2.51 /\
     l /\
     #2.51 < d3 a b /\
     d3 a b <= sqrt (&8) /\
     d3 c a <= #2.51 /\
     d3 c b <= #2.51 `] THEN 
NHANH (CUTHE3 (
prove(`!a b c.
     #2.51 < d3 a b /\
     d3 a b <= sqrt (&8) /\
     d3 c a <= #2.51 /\
     d3 c b <= #2.51
     ==> (?aa bb.
              aa IN {a, b, c} /\
              bb IN {a, b, c} /\
              #2.51 < d3 aa bb /\
              (!x y.
                   ~({x, y} = {aa, bb}) /\ x IN {a, b, c} /\ y IN {a, b, c}
                   ==> d3 x y <= #2.51)) /\
         (!xx yy.
              ~(xx = yy) /\ xx IN {a,b,c} /\ yy IN {a,b,c}
              ==> d3 xx yy <= sqrt (&8))`,
REWRITE_TAC[ MESON[]` (? a b. P a b ) /\ l <=> (? a b. P a b /\ l ) `] THEN 
REWRITE_TAC[ SET_RULE ` x IN {a,b,c} <=> x = a \/ x = b \/ x = c `] THEN 
REPEAT GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `a:real^3` THEN EXISTS_TAC `b:real^3`
THEN FIRST_X_ASSUM MP_TAC THEN 
REWRITE_TAC[ SET_RULE `{a,b} ={x,y} <=> a = x /\ b = y \/ a = y /\ b = x `] THEN 
MESON_TAC[trg_d3_sym; db_t0_sq8; D3_REFL; REAL_ARITH ` &0 <= #2.51 /\ (! a b c. a <= b /\ b < c ==> a <= c )`]))) THEN 
PHA THEN 
ONCE_REWRITE_TAC[ MESON[] `(! x y. P x y ) /\ l <=> l /\ (! x y. P x y) `] THEN 
PHA THEN 
ONCE_REWRITE_TAC[ SET_RULE ` {v0, v1, v2} = {a, b, c} <=> {v1, v2, v0} = {a, b, c}`] THEN 
NHANH ( MESON[db_t0_sq8 ; REAL_ARITH ` a <= b /\ b < c ==> a <= c `]` (!aa bb. aa IN {a, b, c} /\ bb IN {a, b, c} ==> d3 aa bb <= #2.51) /\
      {v1, v2, v0} = {a, b, c} /\
      (!x y. x IN {a, b, c} /\ y IN {a, b, c} /\ ~(x = y) ==> &2 <= d3 x y)
  ==> (! x y. ~(x=y) /\ x IN {v1,v2,v0} /\ y IN {v1,v2,v0}==> &2 <= d3 x y /\
  d3 x y <= sqrt (&8)) `) THEN 
PHA THEN REWRITE_TAC[ MESON[]` {v1, v2, v0} = {a, b, c} /\ l <=> l /\ {v1, v2, v0} = {a, b, c}`] THEN PHA THEN 
PURE_ONCE_REWRITE_TAC[ MESON[]` P {a,b,c} /\ Q {a,b,c} /\ R {a,b,c} /\ {v1,v2,v0} = {a,b,c} <=> P {v1,v2,v0} /\
  Q {v1,v2,v0} /\ R {v1,v2,v0} /\ {v1,v2,v0} = {a,b,c} ` ] THEN 
MESON_TAC[]);;


(* -----------
-------------- *) 


let NOV6 = prove(` ! s v0 v1 v2 w. packing s /\ 
  CARD {v0, v1, v2, w} = 4 /\
 (!a. a IN {v1, v2, v0} ==> dist (w,a) <= #2.51) /\
 {v0, v1, v2, w} SUBSET s /\
 (?a b c.
      {a, b, c} = {v0, v1, v2} /\
      &2 * t0 <= d3 a b /\
      d3 a b <= sqrt (&8) /\
      c IN anchor_points a b s)
 ==> quarter {v0, v1, v2, w} s`,
REWRITE_TAC[ quarter; def_simplex] THEN 
REWRITE_TAC[ prove(`! v0 v1 v2 w. CARD {v0, v1, v2, w} = 4  <=> ~(v0 = v1 \/ v0 = v2 \/ v0 = w \/ v1 = v2 \/ v1 = w \/ v2 = w)`,
  REWRITE_TAC[ CARD4] THEN SET_TAC[])] THEN 
SIMP_TAC[] THEN 
NHANH ( SET_RULE ` {a, b, c} = {v0, v1, v2} ==> a IN {v0,v1,v2,w} /\
  b IN {v0,v1,v2,w} `) THEN 
REWRITE_TAC[ MESON[]` (!a . P a ) /\ a /\ (? a b c. Q a b c) <=>
  a /\ (?a b c. Q a b c /\ (!a . P a ))`] THEN 
REWRITE_TAC[ anchor_points; anchor; IN_ELIM_THM] THEN PHA THEN 
SIMP_TAC[ SET_RULE ` {v1, v2, v0} = {v0, v1, v2}`] THEN 
PURE_ONCE_REWRITE_TAC[ MESON []`  {a, b, c} = {v0, v1, v2} /\ P {v0, v1, v2}
  <=> {a, b, c} = {v0, v1, v2} /\ P {a, b, c}`] THEN 
ONCE_REWRITE_TAC[ DIST_SYM] THEN 
REWRITE_TAC[ GSYM d3 ] THEN 
REWRITE_TAC[ MESON[t0; REAL_ARITH ` #2.51 = &2 * #1.255 `] ` #2.51 = &2 * t0 `] THEN 
NHANH (CUTHE4 SHORT_EDGES) THEN 
PURE_ONCE_REWRITE_TAC[ SET_RULE ` {a, b, c, w} = w INSERT {a,b,c} `] THEN 
PURE_ONCE_REWRITE_TAC[ GSYM (MESON []`  {a, b, c} = {v0, v1, v2} /\ P {v0, v1, v2}
  <=> {a, b, c} = {v0, v1, v2} /\ P {a, b, c}`)] THEN MESON_TAC[]);;

(* ============ *)

let NOV7 = prove(`!s v0 v1 v2 w x . CARD {v0, v1, v2, w, x} = 5 /\ 
     (!a. a IN {v1, v2, v0} ==> dist (w,a) <= #2.51) /\
     {v0, v1, v2, w} SUBSET s /\
     (?a b c.
          (?q. diagonal a b q s /\ q IN Q_SYS s /\ c IN anchor_points a b s) /\
          {v0, v1, v2} = {a, b, c})
     ==> {v0, v1, v2, w} IN Q_SYS s`, 
ONCE_REWRITE_TAC[ SET_RULE ` {v0, v1, v2, w, x} = {x,v0, v1, v2, w}`] THEN 
REWRITE_TAC[CARD5; GSYM CARD4] THEN 
NHANH (CUTHE4 DIA_OF_QUARTER) THEN 
NHANH (MESON[diagonal; quarter] `diagonal a b q s ==> packing s `) THEN 
PHA THEN REWRITE_TAC[ MESON[]` (?q. diagonal a b q s /\ a1 /\ a2 /\ a3 /\ q IN Q_SYS s /\ a4) <=>
     a1 /\ a2 /\ a3 /\ a4 /\ (?q. diagonal a b q s /\ q IN Q_SYS s) `] THEN 
NHANH ( MESON[NOV6]` CARD {v0, v1, v2, w} = 4 /\
     (!a. a IN {v1, v2, v0} ==> dist (w,a) <= #2.51) /\
     {v0, v1, v2, w} SUBSET s /\
     (?a b c.
          (packing s /\
           &2 * t0 <= d3 a b /\
           d3 a b <= sqrt (&8) /\
           c IN anchor_points a b s /\
           (?q. diagonal a b q s /\ q IN Q_SYS s)) /\
          {v0, v1, v2} = {a, b, c})
     ==> quarter {v0, v1, v2, w} s`) THEN 
PHA THEN REWRITE_TAC[ MESON[]` (? a. P a) /\ aa <=> (? a . P a /\ aa )`] THEN 
NHANH (MESON[diagonal] ` diagonal a b q s ==> {a,b} SUBSET q `) THEN 
PHA THEN REWRITE_TAC[ MESON[]` (? a. P a) /\ aa <=> (? a . P a /\ aa )`] THEN 
NHANH (SET_RULE ` {v0, v1, v2} = {a, b, c} ==> {a,b} SUBSET {v0,v1,v2,w} `) THEN 
REWRITE_TAC[ SET_RULE ` {a, b} SUBSET q /\ aa /\ bb /\ {a, b} SUBSET {v0, v1, v2, w} <=>
     {a, b} SUBSET q INTER {v0, v1, v2, w} /\ aa /\ bb`] THEN 
MESON_TAC[lemma7_7_CXRHOVG]);;


let lemma8_3_OVOAHCG =prove(`!s v0 v1 v2 w x. {v0, v1, v2, w} SUBSET s /\ CARD {v0,v1,v2,w,x} = 5  /\
     centered_pac s v0 /\
     ~(conv {x, w} INTER aff_ge {v0} {v1, v2} = {}) /\
     {v0, v1, v2} IN barrier' v0 s /\
     unobstructed v0 x s /\
     dist (x,v0) < dist (x,v1) /\
     dist (x,v0) < dist (x,v2)
     ==> ~(x IN VC w s)`,
REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ MESON[] ` a ==> ~b <=> a /\ b ==> ~b`] THEN 
REWRITE_TAC[IN_ELIM_THM] THEN 
NHANH (MESON[CARD5] ` CARD {x, w, v0, v1, v2} = 5 ==> ~(x IN {w,v0,v1,v2})`) THEN 
NHANH ( SET_RULE ` ~(x IN {w,v0,v1,v2}) ==> ~( x = w ) `) THEN 
PHA THEN  REWRITE_TAC[  MESON[]` unobstructed v0 x s /\ a <=> a /\ 
  unobstructed v0 x s `] THEN REWRITE_TAC[ MESON[]` ~(x = w) /\ a <=> a /\ ~(x = w) `]
   THEN PHA THEN 
NHANH (SET_RULE ` ~(v0 IN {v1, v2, w, x}) ==> ~( v0 = w )`) THEN 
NGOAC THEN MATCH_MP_TAC (MESON[] ` (a ==> c) ==> ( a /\ b ==> c ) `) THEN PHA THEN 
REWRITE_TAC[ unobstructed] THEN 
REWRITE_TAC[ MESON[] ` ~(v0 = w) /\ centered_pac s v0 /\ aa /\ bb /\ cc /\
  x IN VC w s /\  ~obstructed v0 x s /\ las <=>
  aa /\ bb /\ cc /\ las /\ ( centered_pac s v0 /\ ~(v0 = w) /\
  ~obstructed v0 x s  /\ x IN VC w s   )`] THEN 
NHANH (CUTHE4 (prove(` ! s v0 w x . centered_pac s v0 /\ ~(v0 = w) /\ ~obstructed v0 x s /\ x IN VC w s 
==> d3 w x < d3 v0 x`, REWRITE_TAC[ VC; lambda_x; IN_ELIM_THM] THEN PURE_ONCE_REWRITE_TAC
[ MESON[] `( !s v0 w x. a v0 x s w ==> b v0 x w ) <=> ( ! s v0 w x. ( d3 v0 x < &2 \/ 
~(d3 v0 x < &2)) /\ a v0 x s w ==> b v0 x w) `] THEN MESON_TAC[centered_pac; trg_d3_sym;
  REAL_ARITH` ~(d3 v0 x < &2) /\ d3 w x < &2 ==> d3 w x < d3 v0 x`]))) THEN 
NHANH (CUTHE4 TRIANGLE_IN_BARRIER') THEN 
PHA THEN 
ONCE_REWRITE_TAC[MESON[] ` a1 /\ a2 /\ a3 /\  a4 /\
~(conv {x, w} INTER aff_ge {v0} {v1, v2} = {}) /\ aa /\  bb /\  cc /\  dd /\  a5 <=> aa /\
     bb /\  cc /\   dd /\   ~(conv {x, w} INTER aff_ge {v0} {v1, v2} = {}) /\  a3 /\ a4 /\
  a5 /\   a1 /\  a2`] THEN ONCE_REWRITE_TAC[ trg_d3_sym] THEN REWRITE_TAC[d3] THEN 
REWRITE_TAC[MESON[aff_ge_def; cone]` aff_ge {v0} {v1, v2} = cone v0 {v1,v2}`] THEN 
ONCE_REWRITE_TAC[ MESON[] ` CARD {v0, v1, v2, w, x} = 5 /\ a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6 /\ l <=>
     a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6 /\ CARD {v0, v1, v2, w, x} = 5 /\ l`] THEN 
NHANH (CUTHE5 tarski_UMMNOJN) THEN 
PHA THEN REWRITE_TAC[ MESON[] ` ( a \/ b ) /\ c <=> c /\ ( a \/ b ) `] THEN 
REWRITE_TAC[ MESON[] `{v0, v1, v2} IN barrier' v0 s /\ a <=>  
  a /\ {v0, v1, v2} IN barrier' v0 s`] THEN 
REWRITE_TAC[ barrier'; IN_ELIM_THM] THEN 
PURE_ONCE_REWRITE_TAC[ MESON[]` (?a b c.
      ( P  {a, b, c} \/
       Q a b c ) /\
      {v0, v1, v2} = {a, b, c})
  <=> P {v0, v1, v2} \/  (? a b c. Q a b c /\ {v0, v1, v2} = {a, b, c})`] THEN PHA THEN 
ONCE_REWRITE_TAC[ MESON[] ` ~(conv {v0, v1, v2} INTER conv0 {x, w} = {}) /\ aa /\ (b \/ bb) <=>
     ~(conv {v0, v1, v2} INTER conv0 {x, w} = {}) /\
     aa /\
     (~(conv {v0, v1, v2} INTER conv0 {x, w} = {}) /\ b \/ bb)`] THEN 
REWRITE_TAC[ SET_RULE ` conv {v0, v1, v2} INTER conv0 {x, w} = 
          conv0 {x, w} INTER conv {v0, v1, v2}`] THEN 
NHANH (MESON[ def_obstructed] ` ~(conv0 {x, w} INTER conv {v0, v1, v2} = {}) /\
  {v0, v1, v2} IN barrier s /\ l ==> obstructed x w s `) THEN 
PHA THEN REWRITE_TAC[ MESON[] ` {v0, v1, v2, w} SUBSET s /\ a <=> a /\ {v0, v1, v2, w} 
   SUBSET s`] THEN 
REWRITE_TAC[ MESON[] ` (!a. a IN {v1, v2, v0} ==> dist (w,a) <= #2.51) /\ a <=> 
   a /\ (!a. a IN {v1, v2, v0} ==> dist (w,a) <= #2.51)`] THEN 
REWRITE_TAC[ MESON[]` CARD {v0, v1, v2, w, x} = 5 /\ a <=>
    a /\ CARD {v0, v1, v2, w, x} = 5 `] THEN 
PHA THEN 
ONCE_REWRITE_TAC[ MESON[] ` ( a \/ b) /\ a1 /\ a2 /\ {v0, v1, v2, w} SUBSET s <=> ( a \/ 
  a2 /\ a1 /\ {v0, v1, v2, w} SUBSET s /\ b) /\ a1 /\ a2 /\ {v0, v1, v2, w} SUBSET s`] THEN 
NHANH (CUTHE6 NOV7) THEN 
NHANH (prove(` {v0, v1, v2, w} IN Q_SYS s ==> {v0,v1,v2} IN barrier s `, 
  REWRITE_TAC[ barrier; SET_RULE` {a,b,c} UNION {d} = {a,b,c,d} `; IN_ELIM_THM]
   THEN MESON_TAC[])) THEN 
ONCE_REWRITE_TAC[ MESON[] ` ~(conv0 {x, w} INTER conv {v0, v1, v2} = {}) /\ a1 
  /\ ( a \/ b ) /\ l <=>  ~(conv0 {x, w} INTER conv {v0, v1, v2} = {}) /\ a1 
  /\ ( a \/ b /\ ~(conv0 {x, w} INTER conv {v0, v1, v2} = {}) ) /\ l`] THEN 
PHA THEN NHANH (MESON[def_obstructed] ` {v0, v1, v2} IN barrier s /\
  ~(conv0 {x, w} INTER conv {v0, v1, v2} = {}) ==> obstructed x w s`) THEN 
REWRITE_TAC[ MESON[]` (a /\ b \/ a /\ c ) <=> a /\ ( b \/ c ) `] THEN 
DAO THEN 
REWRITE_TAC[ MESON[] `( obstructed x w s /\ b \/ obstructed x w s
  /\ c ) <=>  obstructed x w s /\ ( b \/ c ) `] THEN PHA THEN 
REWRITE_TAC[MESON[ OBS_IMP_NOT_IN_VC] ` a1/\a2/\a3 /\ obstructed x w s /\ l 
  ==> ~(x IN VC w s)`]);;

let lambda_x = prove(` ! x s. lambda_x x s ={w | w IN s /\ d3 w x < &2 /\ ~obstruct w x s}`,
REWRITE_TAC[lambda_x; OBSTRUCT_EQ]);;

(* ==== end repare VC === *)


(* LEMMA 8.1 *)



let TCQPONA = new_axiom ` ! s v v1 v2 v3.
  packing s /\
 CARD {v, v1, v2, v3} = 4 /\
 {v, v1, v2, v3} SUBSET s /\
 d3 v1 v2 <= &2 * t0 /\
 d3 v2 v3 <= &2 * t0 /\
 d3 v3 v1 <= &2 * t0 /\
 ~(conv {v1, v2, v3} INTER voronoi v s = {})
 ==> (!x. x IN {v1, v2, v3} ==> &2 <= d3 x v /\ d3 x v <= &2 * t0)`;;



let CEWWWDQ = new_axiom ` !s v v1 v2 v3.
     packing s /\
     CARD {v, v1, v2, v3}  = 4 /\
     {v, v1, v2, v3}  SUBSET s /\
     d3 v1 v2 <= &2 * t0 /\
     d3 v2 v3 <= &2 * t0 /\
     d3 v1 v3 <= sqrt (&8) /\
     ~(conv {v1, v2, v3} INTER voronoi v s = {})
     ==> (!x. x IN {v1, v2, v3} ==> &2 <= d3 x v /\ d3 x v <= &2 * t0)`;;




let QHSEWMI = new_axiom ` !v1 v2 v3 w1 w2.
         ~(conv {w1, w2} INTER conv {v1, v2, v3} = {}) /\
         ~(w1 IN conv {v1,v2,v3})
         ==> w2 IN cone w1 {v1, v2, v3}`;;




(* =================== *)

let BAR_TRI = prove(` ! b s. b IN barrier s <=> (? x y z . b = {x,y,z} /\ {x,y,z} IN barrier s)`,
REWRITE_TAC[ barrier ; IN_ELIM_THM] THEN MESON_TAC[]);;





let NOV20 = prove(` ! v0 x' y z. v0 IN {x', y, z} <=> (?yy zz. {v0, yy, zz} = {x', y, z})`, 
REPEAT GEN_TAC THEN 
REWRITE_TAC[EQ_EXPAND] THEN 
REWRITE_TAC[SET_RULE `((?yy zz. {v0, yy, zz} = {x', y, z}) 
   ==> v0 IN {x', y, z})`] THEN 
REWRITE_TAC[IN_SET3] THEN 
MESON_TAC[SET_RULE ` x = a
     ==> {x, b, c} = {a, b, c} /\
         {x, b, c} = {b, a, c} /\
         {x, b, c} = {b, c, a}`]);;



let X_IN_VOR_X = prove(` ! x:real^A s. x IN voronoi x s `,
REWRITE_TAC[voronoi; IN_ELIM_THM; DIST_REFL; DIST_POS_LT] THEN 
MESON_TAC[DIST_POS_LT]);;

let IN_VO2_EQ = prove(` ! s v0 x . x IN voro2 v0 s <=>
 (!w. s w /\ ~(w = v0) ==> d3 x v0 < d3 x w) /\ d3 x v0 < &2`,
REWRITE_TAC[voro2; voronoi; IN_ELIM_THM; d3]);;

let IN_VO_EQ = prove(`! x s v0 . x IN voronoi v0 s <=> (!w. s w /\
   ~(w = v0) ==> dist(x,v0) < dist(x,w))`, REWRITE_TAC[voronoi; IN_ELIM_THM]);;


let IN_BAR_DISTINCT = prove(` ! a b c s. {a,b,c} IN barrier s ==> 
   ~( a = b\/ b= c \/ c = a)`,
REWRITE_TAC[barrier; IN_ELIM_THM; quasi_tri;set_3elements] THEN 
KHANANG THEN REWRITE_TAC[EXISTS_OR_THM] THEN NHANH ( MESON[]` (?v1 v2 v3.
          (a1  /\  a2 v1 v2 v3  /\
           ~(v1 = v2 \/ v2 = v3 \/ v3 = v1) /\
           a3 v1 v2 v3 ) /\
          {a, b, c} = {v1, v2, v3}) ==> (?v1 v2 v3.
           ~(v1 = v2 \/ v2 = v3 \/ v3 = v1) /\
          {a, b, c} = {v1, v2, v3})`) THEN 
ONCE_REWRITE_TAC[MESON[EQ_SYM_EQ]` {a,b,c} = {x,y,z} <=> {x,y,z} = {a,b,c}` ] THEN 
REWRITE_TAC[ set_3elements] THEN MESON_TAC[OCT23]);;


let FOUR_POINTS = prove(`!a b c d s.
     {a, b, c} IN barrier s /\ ~(d IN {a, b, c}) ==> CARD {a, b, c, d} = 4`,
NHANH (CUTHE4 IN_BAR_DISTINCT) THEN ONCE_REWRITE_TAC[ 
SET_RULE ` {a,b,c,d} = {d,a,b,c} `] THEN MESON_TAC[CARD4]);;


(* ========= *)


let IN_Q_SYS_IMP4 = prove(`!q s. q IN Q_SYS s ==> 
  (?a b c d. {a, b, c} UNION {d} = q)`,
NHANH (SPEC_ALL CASES_OF_Q_SYS) THEN 
REWRITE_TAC[quasi_reg_tet; strict_qua; quarter; simplex] THEN 
REWRITE_TAC[SET_RULE` {a,b,c,d} = {a,b,c} UNION {d} `] THEN 
MESON_TAC[]);;


let SET2_SU_EX = SET_RULE` {(a:A),b} SUBSET s <=> a IN s /\ b IN s `;;
let D3_SYM = MESON[trg_d3_sym]` ! x y. d3 x y = d3 y x `;;


let EXISTS_DIA = prove(`! q s. quarter q s ==> (? a b. diagonal a b q s)`,
REWRITE_TAC[quarter; diagonal] THEN 
REWRITE_TAC[SET2_SU_EX] THEN 
SIMP_TAC[] THEN 
NHANH (MESON[REAL_LE_TRANS]`&2 * t0 <= d3 v w /\ a1 /\ (!x y. P x y ==> d3 x y <= &2 * t0)
     ==> (!x y. P x y ==> d3 x y <= d3 v w)`) THEN 
MP_TAC PAIR_D3 THEN 
REWRITE_TAC[MESON[REAL_ARITH ` a = b ==> a <= b `] ` a ==> b = c:real <=>
  a ==> ( b = c /\ b <= c )`] THEN 
MESON_TAC[]);;


let QUARTER_EQ_EX_DIA = prove(`! q s. quarter q s <=> (? a b. diagonal a b q s)`,
REWRITE_TAC[EQ_EXPAND; EXISTS_DIA; diagonal] THEN MESON_TAC[]);;


let IN_Q_IMP = prove(`!q s.
     q IN Q_SYS s ==>
     quasi_reg_tet q s \/
     (?a b q1.
          {a, b} SUBSET q INTER q1 /\ quarter q s /\ diagonal a b q1 s /\ q1 IN Q_SYS s)`,
REWRITE_TAC[MESON[CASES_OF_Q_SYS]`  (q IN Q_SYS s ==> a ) <=> q IN Q_SYS s
    /\ (quasi_reg_tet q s \/ strict_qua q s) ==> a `] THEN 
KHANANG THEN 
REWRITE_TAC[MESON[]` a \/ b ==> c <=> (a ==> c) /\ ( b==> c) `] THEN 
SIMP_TAC[] THEN 
REWRITE_TAC[strict_qua] THEN 
NHANH (SPEC_ALL EXISTS_DIA) THEN 
NHANH (MESON[diagonal]`  diagonal d1 d2 q s ==>  {d1, d2} SUBSET q `) THEN 
REWRITE_TAC[SUBSET_INTER] THEN 
MESON_TAC[]);;

let NOV21 = prove(` ! q s. quasi_reg_tet q s ==> q IN Q_SYS s`,
REWRITE_TAC[Q_SYS; IN_ELIM_THM] THEN REWRITE_TAC[ MESON[]` a ==> a \/ b `]);;


let NOVE21 = prove(` ! q s. quasi_reg_tet q s \/
     (?a b q1.
          {a, b} SUBSET q1 INTER q /\ quarter q s /\ diagonal a b q1 s /\ q1 IN Q_SYS s)
  ==> q IN Q_SYS s `,
MP_TAC NOV21 THEN REWRITE_TAC[OR_IMP_EX] THEN SIMP_TAC[] THEN 
MP_TAC lemma7_7_CXRHOVG THEN MESON_TAC[]);;


let COND_Q_SYS =prove(`!q s.
     q IN Q_SYS s <=>  quasi_reg_tet q s \/
     (?a b q1. {a, b} SUBSET q INTER q1 /\ quarter q s /\ 
     diagonal a b q1 s /\ q1 IN Q_SYS s)`, REWRITE_TAC[EQ_EXPAND] THEN 
REWRITE_TAC[IN_Q_IMP] THEN MESON_TAC[INTER_COMM; NOVE21]);;

(* ============ *)

let SET4_SUB_EX = SET_RULE ` {a,b,c,d} SUBSET s <=> 
     a IN s /\ b IN s /\ c IN s /\ (d:A) IN s `;;



let IMP_QUA_RE_TE = prove(`!s v0 x y z. v0 IN s /\ packing s /\
     {x, y, z} SUBSET s /\
     (!aa bb. aa IN {y, z, x} /\ bb IN {y, z, x} ==> dist (aa,bb) <= #2.51) /\
     ~(voronoi v0 s INTER conv {x, y, z} = {}) /\
     CARD {x, y, z, v0} = 4 ==> quasi_reg_tet {v0,x,y,z} s `,
NHANH (SET_RULE ` (! aa bb. aa IN {y, z, x} /\ bb IN {y, z, x} ==> P aa bb ) 
  ==> P x y /\ P y z /\ P z x `) THEN 
ONCE_REWRITE_TAC[ SET_RULE `{a,b,c,d} = {d,a,b,c}`] THEN 
REWRITE_TAC[ SET_RULE ` v0 IN s /\ packing s /\
     {x, y, z} SUBSET s /\ l <=> packing s /\ {v0,x,y,z} SUBSET s /\ l `] THEN 
REWRITE_TAC[ MESON[]` a /\ b/\ ( c1 /\ c2 ) /\ d /\ e <=> c1 /\ a /\ e 
   /\ b /\ c2 /\d `] THEN 
ONCE_REWRITE_TAC[INTER_COMM] THEN 
REWRITE_TAC[ GSYM db_t0; GSYM d3] THEN PHA THEN 
NHANH (SPEC_ALL TCQPONA) THEN 
REWRITE_TAC[quasi_reg_tet; def_simplex; CARD4;IN_SET3; IN_SET4; 
   DE_MORGAN_THM; SET4_SUB_EX; db_t0] THEN 
SIMP_TAC[] THEN PHA THEN DAO THEN 
REWRITE_TAC[ MESON[D3_SYM]` (!x'. x' = x \/ x' = y \/ x' = z ==> 
  d3 x' v0 <= #2.51 /\ &2 <= d3 x' v0) /\     a1 /\
     d3 z x <= #2.51 /\
     d3 y z <= #2.51 /\
     d3 x y <= #2.51 /\
     l  ==> (!v w. ~(v = w) /\
              (v = z \/ v = v0 \/ v = x \/ v = y) /\
              (w = z \/ w = v0 \/ w = x \/ w = y)
              ==> d3 v w <= #2.51)`]);;

(* =========== *)

let SET3_U_SET1 = SET_RULE ` {a,b,c} UNION {d} = {a,b,c,d} `;;


let IN_BA_IM_PA_SU = prove(`! s x y z. {x, y, z} IN barrier s ==> 
packing s /\ {x, y, z} SUBSET s`,
REWRITE_TAC[barrier; IN_ELIM_THM] THEN 
NHANH (SPEC_ALL CASES_OF_Q_SYS) THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[quasi_tri] THEN KHANANG THEN 
REWRITE_TAC[MESON[]` (?a b c. P a b c \/ Q a b c) ==> l <=> 
       ((?a b c . P a b c ) ==> l) /\ ((?a b c. Q a b c) ==> l)`] THEN 
REWRITE_TAC[MESON[]` (?v1 v2 v3.  (packing s /\
        {v1, v2, v3} SUBSET s /\P v1 v2 v3 ) /\
       {x, y, z} = {v1, v2, v3}) ==> packing s /\ {x, y, z} SUBSET s`] THEN 
REWRITE_TAC[quasi_reg_tet; strict_qua; quarter; SET3_U_SET1; def_simplex] THEN 
REWRITE_TAC[SET_RULE ` {a,b,c,d} SUBSET s <=> {a,b,c} SUBSET s /\ d IN s `] THEN 
MESON_TAC[]);;


let FIRST_NOV22 = prove(` ! s v0 x y z. {x, y, z} IN barrier s /\
 (!xx yy.
      ~(xx = yy) /\ {xx, yy} SUBSET {y, z, x}
      ==> &2 <= dist (xx,yy) /\ dist (xx,yy) <= sqrt (&8)) /\
 (!aa bb. aa IN {y, z, x} /\ bb IN {y, z, x} ==> dist (aa,bb) <= #2.51) /\
 v0 IN s /\
 ~(voronoi v0 s INTER conv {x, y, z} = {}) /\
 CARD {x, y, z, v0} = 4
 ==> {v0, x, y, z} IN Q_SYS s`,
NHANH (SPEC_ALL IN_BA_IM_PA_SU ) THEN 
PHA THEN 
ONCE_REWRITE_TAC[MESON[]` a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6 /\ a7 /\ a8 <=>
  a1 /\ a4 /\ a6 /\ a2 /\ a3 /\ a5 /\ a7 /\ a8 `] THEN 
NHANH (SPEC_ALL IMP_QUA_RE_TE) THEN 
MESON_TAC[COND_Q_SYS]);;



let QUA_TRI_EDGE = prove(` ! q s. quasi_tri q s ==> 
  (! a b. a IN q /\ b IN q ==> d3 a b <= &2 * t0 )`,REWRITE_TAC[quasi_tri; db_t0]
THEN MP_TAC D3_REFL THEN MP_TAC (REAL_ARITH ` &0 <= #2.51 `) THEN MESON_TAC[]);;


let BAR_WI_LONG_ED = prove(`!bar s.
     bar IN barrier s /\ (?a b. #2.51 < d3 a b /\ a IN bar /\ b IN bar)
     ==> (?w. w INSERT bar IN Q_SYS s /\ strict_qua (w INSERT bar) s)`,
REWRITE_TAC[barrier; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THENL 
[REPEAT (FIRST_X_ASSUM MP_TAC);REPEAT (FIRST_X_ASSUM MP_TAC)]
 THENL [NHANH (SPEC_ALL QUA_TRI_EDGE); 
ABBREV_TAC ` an w s = (w:real^3 INSERT (bar:real^3 -> bool) IN Q_SYS s)`] THENL 
[REWRITE_TAC[ GSYM db_t0]; NHANH (SPEC_ALL CASES_OF_Q_SYS)] THENL 
[MESON_TAC[REAL_ARITH ` a <= b <=> ~( b < a )`]; 
NHANH (MESON[QUA_TET_IMPLY_QUA_TRI]`quasi_reg_tet ({v0, v1, v2} UNION {v4}) s ==>
  quasi_tri {v0, v1, v2} s`)] THEN NHANH (SPEC_ALL QUA_TRI_EDGE) THEN 
STRIP_TAC THENL [ASM_MESON_TAC[db_t0; REAL_ARITH` a <= b <=> ~( b < a ) `];
ASM_MESON_TAC[SET_RULE ` s UNION {a} = a INSERT s `]]);;

(* ======= *)

let PER_SET3 = SET_RULE ` {a,b,c} = {a,c,b} /\ {a,b,c} = {b,a,c} /\
  {a,b,c} = {c,a,b} /\ {a,b,c} = {b,c,a} /\ {a,b,c} = {c,b,a} `;;

let EXI_THIRD_PO =prove( ` ! a b c x y: A. {x,y} SUBSET {a,b,c} /\ ~(x=y) 
  ==> (? z. {x,y,z} = {a,b,c} ) `, REPEAT GEN_TAC THEN 
REWRITE_TAC[SET2_SU_EX] THEN REWRITE_TAC[SET2_SU_EX; IN_SET3] THEN 
KHANANG THEN REWRITE_TAC[MESON[]`x = a /\ y = a /\ ~(x = y) <=> F`] THEN 
MESON_TAC[ PER_SET3]);;




let IMP_QUA = prove(` ! a b c s v0. packing s /\
 CARD {v0, a, b, c} = 4 /\
 {v0, a, b, c} SUBSET s /\
 d3 a b <= &2 * t0 /\
 d3 b c <= &2 * t0 /\ &2 * t0 <= d3 a c /\
 d3 a c <= sqrt (&8) /\
 (!x. x IN {a, b, c} ==> &2 <= d3 x v0 /\ d3 x v0 <= &2 * t0)
==> quarter {v0, a, b, c} s `,
REWRITE_TAC[quarter; def_simplex; CARD4; IN_SET3; DE_MORGAN_THM] THEN 
SIMP_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN 
EXISTS_TAC `a:real^3` THEN EXISTS_TAC `c:real^3` THEN 
ASM_SIMP_TAC[FOUR_IN] THEN REWRITE_TAC[IN_SET4; PAIR_EQ_EXPAND] THEN 
MP_TAC (MESON[REAL_ARITH ` &0 <= #2.51`; db_t0]` &0 <= &2*t0 `) THEN 
ASM_MESON_TAC[D3_SYM; D3_REFL]);;


let QUA_RE_TE_EDGE = prove(`! a b q s. quasi_reg_tet q s /\ a IN q /\ b IN q
 ==> d3 a b <= &2 * t0 `, REWRITE_TAC[quasi_reg_tet] THEN MP_TAC D3_REFL THEN 
REWRITE_TAC[db_t0] THEN MESON_TAC[REAL_ARITH `&0 <= #2.51 `]);;

(* ========= *)


let CONSI_OF_LE77 = prove(`!s v0 v4 w x y z.
     quarter ({x, y, z} UNION {v0}) s /\
     aa IN {x, y, z} /\
     bb IN {x, y, z} /\
     {x, y, z} UNION {v4} IN Q_SYS s /\
     diagonal aa bb ({x, y, z} UNION {v4}) s
     ==> {x, y, z} UNION {v0} IN Q_SYS s`,
REWRITE_TAC[MESON[]` quarter q s /\ a <=>a/\quarter q s `] THEN 
PHA THEN NHANH (SET_RULE `  aa IN {x, y, z} /\ bb IN {x, y, z} /\ l
     ==> (!v0 v4.
              {aa, bb} SUBSET
              ({x, y, z} UNION {v4}) INTER ({x, y, z} UNION {v0}))`) THEN 
PHA THEN NHANH (MESON[]` diagonal aa bb ({x, y, z} UNION {v4}) s /\
     quarter ({x, y, z} UNION {v0}) s /\
     (!v0 v4. P v0 v4) ==> P v0 v4 `) THEN MESON_TAC[lemma7_7_CXRHOVG]);;









let IMP_IN_Q_SYS = prove( ` ! s v0 x y z . {x, y, z} IN barrier s /\ v0 IN s /\ 
 ~(voronoi v0 s INTER conv {x, y, z} = {}) /\
 CARD {x, y, z, v0} = 4
 ==> {v0, x, y, z} IN Q_SYS s`,
NHANH (CUTHE4 TRIANGLE_IN_BARRIER) THEN 
KHANANG THEN 
REWRITE_TAC[OR_IMP_EX] THEN 
REWRITE_TAC[FIRST_NOV22] THEN 
REPEAT GEN_TAC THEN 
MATCH_MP_TAC (MESON[]`(a /\ c ==> d ) ==> a /\ b /\ c ==> d `) THEN 
NHANH (SPEC_ALL IN_BA_IM_PA_SU) THEN 
REWRITE_TAC[MESON[]` a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`] THEN 
NHANH (MESON[DIST_NZ; REAL_ARITH ` &0 < #2.51 /\ ( a < b /\ b < c ==> a < c )`]`
  #2.51 < dist (aa,bb) ==> ~( aa = bb ) `) THEN 
REWRITE_TAC[ MESON[]` a /\ ( b /\ c ) /\ l <=> (a /\ c ) /\ b /\ l`] THEN 
NHANH (SPEC_ALL EXI_THIRD_PO) THEN 
REWRITE_TAC[MESON[]` a/\ b/\ c/\ d <=> c /\ a/\b/\d`] THEN 
STRIP_TAC THEN REPEAT (FIRST_X_ASSUM MP_TAC) THEN 
ONCE_REWRITE_TAC[ EQ_SYM_EQ] THEN 
REWRITE_TAC[MESON[]` a = b ==> P a <=> a = b ==> P b `] THEN 
ONCE_REWRITE_TAC[ EQ_SYM_EQ] THEN 
ONCE_REWRITE_TAC[ SET_RULE ` {x, y, z, v0} = {v0,y,z,x} `] THEN 
REWRITE_TAC[CARD4; GSYM CARD3] THEN 
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN 
REWRITE_TAC[MESON[]` a = b ==> P a <=> a = b ==> P b `] THEN 
REWRITE_TAC[IMP_IMP] THEN PHA THEN 
REWRITE_TAC[MESON[]` (! a b. P a b ) /\l <=> l/\(!a b. P a b)`] THEN 
PHA THEN 
ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN 
REWRITE_TAC[CARD3] THEN 
NHANH (SET_RULE ` ~(aa = bb \/ bb = z' \/ z' = aa) /\
 (!x' y'.
      ~({x', y'} = {aa, bb}) /\ {x', y'} SUBSET {aa, bb, z'}
      ==> P x' y') ==>
  P bb z' /\ P z' aa `) THEN 
PHA THEN 
REWRITE_TAC[MESON[CARD4]` ~(v0 IN {aa, bb, z'}) /\
 ~(aa = bb \/ bb = z' \/ z' = aa) /\ l <=> CARD {v0,aa,bb,z'} = 4 /\ l `] THEN 
ONCE_REWRITE_TAC[ SET_RULE ` {v0, aa, bb, z'} = {v0,bb,z',aa}`] THEN 
SIMP_TAC[SET_RULE ` {y,z,x} = {x,y,z} `] THEN 
REWRITE_TAC[ GSYM d3; GSYM db_t0] THEN 
REWRITE_TAC[ GSYM d3; GSYM db_t0; SET2_SU_EX] THEN 
REWRITE_TAC[MESON[]` (aa IN {x, y, z} /\ bb IN {x, y, z}) /\a1 /\a2 /\
 &2 * t0 < d3 aa bb /\a3 /\ a4  /\ a5 /\ l <=> (aa IN {x, y, z} /\ bb IN {x, y, z}
  /\ a5 /\ &2 * t0 < d3 aa bb) /\ a1 /\ a2 /\ a3 /\ a4 /\ l `] THEN 
NHANH (SPEC_ALL DIAGONAL_BARRIER) THEN 
NHANH (SPEC_ALL DIA_OF_QUARTER) THEN 
REWRITE_TAC[ GSYM LEFT_AND_EXISTS_THM] THEN 
PHA THEN 
REWRITE_TAC[MESON[]` d3 aa bb <= sqrt (&8) /\ l <=>l/\d3 aa bb <= sqrt (&8)`] THEN 
REWRITE_TAC[MESON[]` a = b /\ P b <=> a = b /\ P a`] THEN 
PHA THEN REWRITE_TAC[MESON[]` ~ ( a INTER b = {}) /\ l <=> l/\ ~ ( a INTER b = {})`]
  THEN PHA THEN 
REWRITE_TAC[SET_RULE` v0 IN s /\
     a1 /\
     {aa, bb, z'} SUBSET s /\
     CARD {v0, aa, bb, z'} = 4 /\
     l /\
     las <=>
     l /\ a1 /\ CARD {v0, aa, bb, z'} = 4 /\ {v0, bb, z', aa} SUBSET s /\ las`] THEN 
ONCE_REWRITE_TAC[MESON[SET_RULE ` {v0, aa, bb, z'} = {v0,bb,z',aa}`]` CARD {v0, aa, bb, z'} =4
  <=> CARD {v0,bb,z',aa} = 4 `] THEN 
ONCE_REWRITE_TAC[INTER_COMM] THEN 
ONCE_REWRITE_TAC[MESON[SET_RULE ` {a,b,c} = {b,c,a}`]`
   conv {a,b,c} = conv {b,c,a} `] THEN 
ONCE_REWRITE_TAC[MESON[D3_SYM]` d3 aa bb <= sqrt (&8) <=> d3 bb aa <= sqrt (&8)`] THEN 
NHANH (SPEC_ALL CEWWWDQ) THEN 
NHANH (REAL_ARITH ` a < b ==> a <= b `) THEN 
ONCE_REWRITE_TAC[MESON[]` ( a/\ b ) /\ c <=> c /\ b /\ a `] THEN 
PHA THEN 
NHANH (MESON[IMP_QUA; D3_SYM]` packing s /\
 CARD {v0, bb, z', aa} = 4 /\
 {v0, bb, z', aa} SUBSET s /\
 d3 bb z' <= &2 * t0 /\
 d3 z' aa <= &2 * t0 /\
 d3 bb aa <= sqrt (&8) /\ a2 /\
 (!x. x IN {bb, z', aa} ==> &2 <= d3 x v0 /\ d3 x v0 <= &2 * t0) /\
 &2 * t0 <= d3 aa bb /\ a1 ==> quarter {v0, bb, z', aa} s`) THEN 
REWRITE_TAC[MESON[]`( ? a. P a ) /\ l <=> l /\ (?a. P a) `] THEN 
REWRITE_TAC[barrier; IN_ELIM_THM] THEN 
REWRITE_TAC[MESON[]` P b /\ a = b <=> a = b /\ P a `] THEN 
REWRITE_TAC[GSYM LEFT_AND_EXISTS_THM] THEN 
PHA THEN 
REWRITE_TAC[MESON[]`( a < b /\ l <=> l /\ a < b ) /\ 
       ( ( x \/ y ) /\ z <=> z /\ ( x \/ y ))`] THEN 
REWRITE_TAC[ MESON[]` a IN s /\ b /\ c <=> c /\ a IN s /\ b `] THEN 
NHANH (SPEC_ALL QUA_TRI_EDGE) THEN 
PHA THEN 
REWRITE_TAC[MESON[real_lt]`&2 * t0 < d3 aa bb /\
     (a1 /\ (!a b. a IN s /\ b IN s ==> d3 a b <= &2 * t0) \/ a2) /\
     aa IN s /\
     bb IN s <=>
     &2 * t0 < d3 aa bb /\ a2 /\ aa IN s /\ bb IN s`] THEN 
NHANH (SPEC_ALL CASES_OF_Q_SYS) THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN 
KHANANG THEN 
NHANH (MESON[SET_RULE ` a IN s ==> a IN ( s UNION t )`; QUA_RE_TE_EDGE]`
  quasi_reg_tet ({x, y, z} UNION {v4}) s /\
                 aa IN {x, y, z} /\
                 bb IN {x, y, z} ==> d3 aa bb <= &2 * t0 `) THEN 
DAO THEN 
REWRITE_TAC [REAL_ARITH ` a <= b <=> ~( b < a ) `] THEN 
REWRITE_TAC[MESON[]`(?v4. ~(&2 * t0 < d3 aa bb) /\ P v4 \/ Q v4) /\ a1 /\ &2 * t0 < d3 aa bb <=>
     (?v4. Q v4) /\ a1 /\ &2 * t0 < d3 aa bb`] THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN 
PHA THEN 
NHANH (MESON[SET_RULE` a IN s ==> a IN ( s UNION t ) `; DIAGONAL_STRICT_QUA]` 
  bb IN {x, y, z} /\
      aa IN {x, y, z} /\ a1 /\
      strict_qua ({x, y, z} UNION {v4}) s /\
      a2  /\
      &2 * t0 < d3 aa bb /\ l ==> diagonal aa bb ({x, y, z} UNION {v4}) s  `) THEN 
NHANH (MESON[strict_qua]` strict_qua q s /\ l ==> quarter q s `) THEN 
PHA THEN 
REWRITE_TAC[SET_RULE ` {v0, bb, z', aa} = {aa,bb,z'} UNION {v0}`] THEN 
DAO THEN 
REWRITE_TAC[MESON[]` a = b /\ l <=> l/\ a= b `] THEN 
REWRITE_TAC[MESON[]`  quarter q s /\
         &2 * t0 < d3 aa bb /\l <=> &2 * t0 < d3 aa bb /\l /\ quarter q s`] THEN 
PHA THEN 
REWRITE_TAC[MESON[]` quarter ({aa, bb, z'} UNION {v0}) s /\
     a1 /\
      {aa, bb, z'} = {x, y, z} /\ l <=> l /\ a1 /\  {aa, bb, z'} = {x, y, z}
   /\ quarter ({x, y, z} UNION {v0}) s`] THEN 
REWRITE_TAC[MESON[]` a IN Q_SYS s /\ l <=> l /\ a IN Q_SYS s`] THEN 
REWRITE_TAC[MESON[]` a IN s /\ b /\ l <=>l /\ a IN s /\b `] THEN 
REWRITE_TAC[ MESON[]` diagonal aa bb ({x, y, z} UNION {v4}) s /\ l <=>
  l /\ diagonal aa bb ({x, y, z} UNION {v4}) s`] THEN 
PHA THEN 
NHANH (MESON[CONSI_OF_LE77]` quarter ({x, y, z} UNION {v0}) s /\
      aa IN {x, y, z} /\
      bb IN {x, y, z} /\
      {x, y, z} UNION {v4} IN Q_SYS s /\a1/\
      diagonal aa bb ({x, y, z} UNION {v4}) s
  ==> {x, y, z} UNION {v0} IN Q_SYS s`) THEN 
DAO THEN 
REWRITE_TAC[GSYM RIGHT_AND_EXISTS_THM] THEN 
REWRITE_TAC[MESON[SET_RULE ` {x, y, z} UNION {v0}  =  {y, v0, x} UNION {z} `;CASES_OF_Q_SYS]`
  {x, y, z} UNION {v0} IN Q_SYS s /\ last
     ==> {y, v0, x} UNION {z} IN Q_SYS s /\
         quasi_reg_tet ({y, v0, x} UNION {z}) s \/
         {y, v0, x} UNION {z} IN Q_SYS s /\
         strict_qua ({y, v0, x} UNION {z}) s`]);;

(* ========= *)


let POS_EQ_INV_POS = prove(`!x. &0 < x <=> &0 < &1 / x`, GEN_TAC THEN EQ_TAC
THENL [REWRITE_TAC[MESON[REAL_LT_RDIV_0; REAL_ARITH ` &0 < &1 `]`! b.  &0 < b 
   ==> &0 < &1 / b `];REWRITE_TAC[] THEN 
MESON_TAC[MESON[REAL_LT_RDIV_0; REAL_ARITH ` &0 < &1 `]` &0 < b
    ==> &0 < &1 / b `; REAL_FIELD ` &1 / ( &1 / x ) = x ` ]]);;


let STRIP_TR = REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM MP_TAC)
      THEN REWRITE_TAC[IMP_IMP] THEN PHA;;

let INTER_DIF_EM_EX = SET_RULE `! a b. ~(a INTER b = {}) <=> (? x. x IN a /\ x IN b ) `;;




let AFF_LE_CONE =prove(` ! a b x y z. ~( conv0 {a,b} INTER conv {x,y,z} = {}) 
  ==> ( b IN aff_le {x,y,z} {a}) /\ ( b IN cone a {x,y,z}) `,
REWRITE_TAC[CONV_SET3; CONV0_SET2; INTER_DIF_EM_EX; IN_ELIM_THM] THEN 
REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (FIRST_X_ASSUM MP_TAC) THEN 
REWRITE_TAC[IMP_IMP] THEN PHA THEN REWRITE_TAC[MESON[]` x' = aa /\a1
 /\a2 /\a3/\a4 /\ x' = bb <=> x' = aa /\a1 /\a2 /\a3/\a4 /\ aa = bb `] 
THEN REWRITE_TAC[ VECTOR_ARITH ` a + b:real^N = c <=> b = c - a`] THEN 
NHANH (MESON[VECTOR_MUL_LCANCEL]`  b' % b = a ==> (&1 / b') % (b' % b)
  = (&1 / b') % a `) THEN REWRITE_TAC[VECTOR_MUL_ASSOC;
 VECTOR_SUB_LDISTRIB; VECTOR_ADD_LDISTRIB; simp_def] THEN 
NHANH (MESON[POS_EQ_INV_POS]` &0 < a ==> &0 < &1 / a `) THEN 
REWRITE_TAC[VECTOR_ARITH ` a - b % x = a + ( -- b ) % x `] THEN 
MP_TAC (REAL_FIELD `! b.  &0 < b ==>  &1 / b * b = &1 `) THEN 
REWRITE_TAC[IMP_IMP] THEN PHA THEN REWRITE_TAC[REAL_ARITH ` a / b * c 
= (a * c) / b`; REAL_MUL_LID; VECTOR_ARITH ` a - b % x = a + (--b) % x `] THEN 
REWRITE_TAC[REAL_ARITH ` -- ( a / b ) = ( -- a ) / b `] THEN 
NHANH (MESON[REAL_ARITH ` a / m + b / m + c / m + d / m = ( a + b + c + d ) / m `]`
  b' / b' % b = (a'' / b' % x + b'' / b' % y + c / b' % z) + --a' / b' % a
  ==> a'' / b' + b'' / b' + c / b' + -- a' / b' = ( a'' + b'' + c + -- a' ) / b' `)
 THEN NHANH (MESON[REAL_ARITH ` a' + b' = &1 /\  a'' + b'' + c = &1
  ==> a'' + b'' + c + --a' = b' `]` a' + b' = &1 /\a1 /\a2 /\a3 /\a4 /\
   a'' + b'' + c = &1 /\ l  ==> a'' + b'' + c + --a' = b'`) THEN 
MP_TAC (REAL_ARITH ` ! a. a < &0 ==> a <= &0 `) THEN REWRITE_TAC[ IN_ELIM_THM]
 THEN NHANH (MESON[]`(!b. &0 < b ==> b / b = &1) /\ --a' / b' < &0 /\
     &0 < a' /\ &0 < &1 / a' /\ &0 < b' /\ l ==>  b' / b' = &1 `) THEN 
REWRITE_TAC[MESON[] ` a /\ b' / b' = &1 ==> l <=> b' / b' = &1 ==> a ==> l`] THEN 
SIMP_TAC[VECTOR_MUL_LID] THEN PHA THEN NHANH (MESON[REAL_LT_DIV]
` &0 < a' /\ &0 < &1 / a' /\ &0 < b' /\ l ==> &0 < a' / b' `) THEN 
REWRITE_TAC[REAL_ARITH ` &0 < a' / b' <=> --a' / b' < &0 `] THEN 
REWRITE_TAC[ MESON[]` a = x / y /\ x = y <=> a = y/ y /\ x = y `] THEN 
REWRITE_TAC[ VECTOR_ARITH ` ((a:real^N) + b ) + c = a + b + c `] THEN 
STRIP_TR THENL [MESON_TAC[VECTOR_MUL_LID];
REWRITE_TAC[cone; GSYM aff_ge_def; simp_def; IN_ELIM_THM]] THEN 
MP_TAC VECTOR_MUL_LID THEN SIMP_TAC[VECTOR_ARITH ` a + b + c + (d:real^N)
 = b + c + d + a `] THEN REWRITE_TAC[MESON[]` &0 <= a /\ l <=> l /\ &0 <= a `]
 THEN SIMP_TAC[ REAL_ARITH ` a + b + c + d = b + c + d + a `] THEN 
REWRITE_TAC[ MESON[]` &0 < a /\ l <=> l /\ &0 < a `] THEN PHA THEN 
NHANH (MESON[REAL_ARITH ` &0 < b ==> &0 <= b `; REAL_LE_DIV]` &0 <= c /\
     &0 <= b'' /\ &0 <= a'' /\ &0 < b' /\ &0 < a' ==> 
&0 <= a'' / b' /\ &0 <= b''/ b' /\ &0 <= c/ b' `) THEN 
NHANH (MESON[REAL_FIELD `  &0 < b' ==> b' / b' = &1 `]`(&0 <= c /\ &0 
<= b'' /\ &0 <= a'' /\ &0 < b' /\ &0 < a') ==> b' / b' = &1 `) THEN 
REWRITE_TAC[ MESON[]` a / a = &1 /\ l <=> l /\ a / a = &1 `] THEN DAO THEN 
REWRITE_TAC[IMP_IMP] THEN  REWRITE_TAC[ MESON[]`b' / b' = &1 /\ &0 < a' /\
 &0 < b' /\ l <=> &0 < a' /\ l /\ &0 < b' /\ b' / b' = &1  `] THEN 
REWRITE_TAC[ MESON[]` a = (b:real^N) /\ l <=> l /\ b = a `] THEN 
PHA THEN REWRITE_TAC[ MESON[]` aaa = b' / b' % b /\ &0 < b' /\
     b' / b' = &1 <=> &0 < b' /\ b' / b' = &1 /\ aaa = &1 % b `] 
THEN REWRITE_TAC[ VECTOR_MUL_LID] THEN MESON_TAC[]);;


let NOVE30 = prove(`! P l. ( ! x y z i j k s. ( P x y z i j k s <=> P y x z j i k s)
 /\ ( l x y z <=> l y x z ) ) /\ (! x y z i j k s. i <= j /\ P x y z i j k s ==> 
l x y z )   ==> (! x y z i j k s. P x y z i j k s ==> l x y z ) `, 
ONCE_REWRITE_TAC[ MESON[]` a ==> (!x y z i j k s. P x y z i j k s ==> l x y z) <=>
     (a ==> (!x y z i j k s. i <= j /\ P x y z i j k s ==> l x y z)) /\(a ==>
 (!x y z i j k s. ~(i <= j) /\ P x y z i j k s ==> l x y z)) `] THEN REPEAT
GEN_TAC THEN 
CONJ_TAC THENL [MESON_TAC[]; MESON_TAC[REAL_ARITH ` ~( a <= b ) ==> b <= a `]]);;



let NOVE31 = prove(`! P l. ( ! x y z i j k s. ( P x y z i j k s <=> P z y x k j i s )
 /\ ( l x y z <=> l z y x ) ) /\ (! x y z i j k s. i <= j /\ i <= k /\ P x y z i j k s
 ==> l x y z )   ==> (! x y z i j k s. i <= j /\ P x y z i j k s ==> l x y z ) `, 
ONCE_REWRITE_TAC[ MESON[]` a ==> (!x y z i j k s. P x y z i j k s ==> l x y z) <=>
     (a ==> (!x y z i j k s. i <= k /\ P x y z i j k s ==> l x y z)) /\(a ==>
 (!x y z i j k s. ~(i <= k) /\ P x y z i j k s ==> l x y z)) `] THEN REPEAT
GEN_TAC THEN CONJ_TAC THENL [MESON_TAC[];   MESON_TAC[REAL_LE_TRANS; 
REAL_ARITH ` ~( a <= b ) ==> b <= a `]]);;




let IMP_IN_BA = prove(`! x y z a s. {x,y,z} UNION {a} IN Q_SYS s ==> {x,y,z} IN barrier s `,
REWRITE_TAC[barrier; IN_ELIM_THM] THEN MESON_TAC[]);;



let IMP_IN_AFF4  = prove(` ! s v0 xx x y z. xx IN cone v0 {x, y, z} /\
 ~(xx IN UNIONS {aff_ge {v0} {v1, v2} | v1,v2 | barrier s {v0, v1, v2}}) /\
 {v0, x, y, z} IN Q_SYS s ==> xx IN aff_gt {v0} {x, y, z}`, 
REWRITE_TAC[cone; GSYM aff_ge_def; simp_def; IN_ELIM_THM] THEN 
REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[MESON[]` ( ! x y z. (? s i j k.
 P s i j k x y z ) /\ Q x y z ==> l x y z) <=> ( ! x y z i j k s. 
P s i j k x y z /\ Q x y z ==> l x y z ) `] THEN MATCH_MP_TAC NOVE30 THEN 
CONJ_TAC THENL [MESON_TAC[PER_SET3; REAL_ARITH ` a + b + c = b + a + c ` ;
  VECTOR_ARITH `(a:real^N ) + b + c = b + a + c `]; MATCH_MP_TAC NOVE31 THEN 
CONJ_TAC]THENL [MESON_TAC[PER_SET3; REAL_ARITH ` a + b + c = c + b + a ` ;
 VECTOR_ARITH `(a:real^N ) + b + c = c + b + a `]; PHA] THEN 
REWRITE_TAC[MESON[REAL_ARITH ` &0 <= i <=> i = &0 \/ &0 < i `]`
  &0 <= i /\ &0 <= j /\ &0 <= k /\ l <=> ( i = &0 \/ &0 < i ) /\ &0 <= j /\
   &0 <= k /\ l `] THEN KHANANG THEN REPEAT GEN_TAC THEN 
STRIP_TAC THENL [REPEAT (FIRST_X_ASSUM MP_TAC) THEN REPLICATE_TAC 3 DISCH_TAC
 THEN REWRITE_TAC[IMP_IMP] THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[VECTOR_MUL_LZERO; 
VECTOR_ADD_LID; REAL_ADD_LID] THEN REWRITE_TAC[SET_RULE ` {v0, x, y, z} = {v0,y,z}
 UNION {x} `] THEN NHANH (SPEC_ALL IMP_IN_BA) THEN REWRITE_TAC[IN_UNIONS; 
IN_ELIM_THM] THEN REWRITE_TAC[MESON[IN]` barrier s a /\ l <=> a IN barrier s /\ 
l`] THEN PHA THEN REWRITE_TAC[MESON[]` (? t. (? v1 v2 . P v1 v2 /\ t = Q v1 v2 ) 
/\ xx IN t )  <=> (? v1 v2. P v1 v2 /\ xx IN Q v1 v2 ) `] THEN REWRITE_TAC[IN_ELIM_THM]
 THEN MESON_TAC[]; STRIP_TR THEN REWRITE_TAC[MESON[REAL_ARITH ` i <= j /\ &0 < i 
==> &0 < j `]`  i <= j /\ i <= k /\ &0 < i /\l  <=> i <= j /\ i <= k /\ &0 < j /\
 &0 < k /\ &0 < i /\ l`] THEN MESON_TAC[]]);;





let VORO2_EX =prove(`! v0 s. voro2 v0 s = {x | (!w. s w /\ ~(w = v0) ==>
  d3 x v0 < d3 x w) /\ d3 x v0 < &2} `, REWRITE_TAC[voro2; voronoi; d3 ] 
 THEN SET_TAC[]);;



let LEMMA81 = prove(`!(X:real^3 -> bool) Z s v0:real^3 .
     centered_pac s v0 /\
     Z = UNIONS {aff_ge {v0} {v1, v2} | v1,v2 | {v0, v1, v2} IN barrier s} /\
     X = UNIONS
     {aff_gt {v0} {v1, v2, v3} INTER
      aff_le {v1, v2, v3} {v0} INTER
      voro2 v0 s | v1,v2,v3 | {v0, v1, v2, v3} IN Q_SYS s}
     ==> voro2 v0 s SUBSET X UNION Z UNION VC v0 s`,
REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[SET_RULE ` as SUBSET a UNION b UNION c <=> 
( as DIFF (b UNION c))   SUBSET a`] THEN REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION;
 VC; lambda_x; IN_ELIM_THM; voro2;voronoi; GSYM d3;  DE_MORGAN_THM; centered_pac]
 THEN ABBREV_TAC ` ketluan x  = ((x:real^3) IN (X:real^3 -> bool))` THEN SIMP_TAC[]
 THEN PHA THEN REWRITE_TAC[MESON[]` a /\b/\e/\c==>d <=> c ==> a/\b/\e==>d`] THEN
 DISCH_TAC THEN REWRITE_TAC[GSYM (MESON[]` a /\b/\e/\c==>d <=> c ==> a/\b/\e==>d`)] 
THEN REWRITE_TAC[MESON[trg_d3_sym]` d3 x v0 < &2 /\ aa/\
          ((~(d3 v0 x < &2) \/ l) \/ l') <=> d3 x v0 < &2 /\ aa/\ (l\/ l')`; IN] THEN 
PHA THEN REWRITE_TAC[MESON[]` (!w. s w /\ ~(w = v0) ==> d3 x v0 < d3 x w) /\
 aa /\ bb /\ (cc \/ ~(!w. s w /\ dd w /\ ee w /\ ~(w = v0) ==> d3 x v0 < d3 x w)) <=>
     (!w. s w /\ ~(w = v0) ==> d3 x v0 < d3 x w) /\ aa /\ bb /\ cc`] THEN 
REWRITE_TAC[obstruct] THEN ONCE_REWRITE_TAC[BAR_TRI] THEN 
REWRITE_TAC[ MESON[]`(?bar. (?x y z. bar = {x, y, z} /\ P {x, y, z}) /\ Q bar) <=>
     (?x y z. P {x, y, z} /\ Q {x, y, z})`] THEN NHANH (MESON[]` ~(conv0 {v0, x} INTER 
conv {x', y, z} = {}) ==>  v0 IN {x' ,y,z} \/ ~( v0 IN {x', y,z})`) THEN KHANANG THEN 
NHANH (MESON[IN_SET3; SET_RULE` x = a ==> {x,b,c} = {a,b,c} /\ {x,b,c} = {b,c,a} /\
 {x,b,c} = {b,a,c}  `]`  x IN {a,b,c} ==> (? yy zz. {x,yy,zz} = {a,b,c})`) THEN 
REWRITE_TAC[EXISTS_OR_THM] THEN NGOAC THEN REWRITE_TAC[MESON[]`(?x' y z. P {x', y, z} 
/\ (?yy zz. {x, yy, zz} = {x', y, z})) <=> (?y z. P {x, y, z})`] THEN 
NHANH (CUTHE4 IN_AFF_GE_CON) THEN PHA THEN 
REWRITE_TAC[SET_RULE`  ~UNIONS {aff_ge {v0} {v1, v2} | v1,v2 | barrier s {v0, v1, v2}} x /\
((?y z. {v0, y, z} IN barrier s /\ aaa y z /\ x IN aff_ge {v0} {y, z} /\
 bbb y z) \/  last) <=> ~UNIONS {aff_ge {v0} {v1, v2} | v1,v2 | barrier s {v0, v1, v2}} x /\
     last`] THEN REWRITE_TAC[DE_MORGAN_THM] THEN SIMP_TAC[GSYM NOV20] THEN 
REWRITE_TAC[d3; GSYM IN_VO_EQ] THEN NHANH (MESON[X_IN_VOR_X; VORONOI_CONV]` x IN voronoi v0 s 
   ==> v0 IN voronoi v0 s /\ convex (voronoi v0 s )`) THEN 
NHANH (MESON[CONVEX_IM_CONV02_SU ]` x IN voronoi v0 s /\    v0 IN voronoi v0 s /\
 convex (voronoi v0 s) ==> conv0 {v0,x} SUBSET voronoi v0 s `) THEN PHA THEN 
DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THENL [REPEAT (FIRST_X_ASSUM MP_TAC) THEN 
REWRITE_TAC[ IMP_IMP] THEN PHA THEN NHANH (SET_RULE` conv0 {v0, x} SUBSET voronoi v0 s 
/\a1  /\a2  /\a3  /\ ~(conv0 {v0, x} INTER conv {x', y, z} = {}) /\ l ==>
  ~( voronoi v0 s INTER conv {x', y, z} = {})`) THEN NHANH (MESON[FOUR_POINTS]
` {x', y, z} IN barrier s /\ a1 /\   ~(v0 IN {x', y, z}) ==> CARD {x',y,z, v0} = 4 `)
 THEN PHA THEN NHANH (SET_RULE `  conv0 {v0, x} SUBSET s /\ a1 /\a2 /\a3 /\
 ~(conv0 {v0, x} INTER s1  = {}) /\ l ==> ~( s INTER s1 = {}) `) THEN PHA THEN 
REWRITE_TAC[MESON[]`( s x /\ l <=>l/\ s x)/\ (a IN barrier s /\ l <=>
   l /\ a IN barrier s) `] THEN NHANH (SPEC_ALL (REWRITE_RULE[CONV3_EQ] IN_AFF_GE_CON))
 THEN PHA THEN REWRITE_TAC[SET_RULE ` ~UNIONS {aff_ge {v0} {v1, v2} | v1,v2 | 
  barrier s {v0, v1, v2}} x /\  a1 /\ x IN aff_ge {v0} {y, z} /\
   a2 /\ a3/\ {v0, y, z} IN barrier s /\ a4 <=> F `] ; REPEAT (FIRST_X_ASSUM MP_TAC)]
 THEN REWRITE_TAC[ IMP_IMP] THEN PHA THEN 
NHANH (SET_RULE` conv0 {v0, x} SUBSET voronoi v0 s /\a1  /\a2  /\a3  /\
 ~(conv0 {v0, x} INTER conv {x', y, z} = {}) /\ l ==>
  ~( voronoi v0 s INTER conv {x', y, z} = {})`) THEN 
NHANH (MESON[FOUR_POINTS]` {x', y, z} IN barrier s /\ a1 /\ 
  ~(v0 IN {x', y, z}) ==> CARD {x',y,z, v0} = 4 `) THEN PHA THEN NHANH (SET_RULE ` 
 conv0 {v0, x} SUBSET s /\ a1 /\a2 /\a3 /\ ~(conv0 {v0, x} INTER s1  = {}) /\ l 
==> ~( s INTER s1 = {}) `) THEN PHA THEN REWRITE_TAC[MESON[]`( s x /\ l <=>l/\
 s x)/\ (a IN barrier s /\ l <=>   l /\ a IN barrier s) `] THEN PHA THEN 
NHANH (MESON[IMP_IN_Q_SYS; IN]` CARD {x', y, z, v0} = 4 /\
 ~(voronoi v0 s INTER conv {x', y, z} = {}) /\ {x', y, z} IN barrier s /\
 s v0 ==> {v0,x',y,z} IN Q_SYS s `) THEN NHANH (SPEC_ALL AFF_LE_CONE) THEN PHA THEN 
ONCE_REWRITE_TAC[MESON[IN] ` ~ UNIONS s x <=> ~ ( x IN UNIONS s ) `] THEN 
ONCE_REWRITE_TAC[MESON[]` a1 /\a /\ b /\ x IN cone v0 {x', y, z} /\ l <=>a /\ b /\ l /\
  x IN cone v0 {x', y, z} /\ a1 `] THEN PHA THEN REWRITE_TAC[MESON[]` a IN Q_SYS s /\
 b /\ c <=> b /\ c /\ a IN Q_SYS s`] THEN NHANH (SPEC_ALL IMP_IN_AFF4) THEN 
NGOAC THEN REWRITE_TAC[MESON[]` (a /\ b ) /\ x IN aff_gt {v0} {x', y, z} <=> 
  x IN aff_gt {v0} {x', y, z}/\ b/\ a `] THEN PHA THEN DAO THEN 
REWRITE_TAC[GSYM VORO2_EX] THEN REWRITE_TAC[prove(`dist (x,v0) < &2 /\a1/\a2/\a3 /\
x IN voronoi v0 s /\ l  <=> a1/\a2/\a3 /\ l /\ x IN voro2 v0 s`, REWRITE_TAC[GSYM d3; 
  voro2; IN_ELIM_THM] THEN MESON_TAC[])] THEN REWRITE_TAC[MESON[]`x IN aff_le a s /\
 l <=> l /\ x IN aff_le a s `] THEN DAO THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN 
SIMP_TAC[] THEN ONCE_REWRITE_TAC[MESON[]` (! x. P x ) /\ a = b /\ l <=> b = a /\ l /\ 
  (! x . P x )`] THEN SIMP_TAC[] THEN MATCH_MP_TAC (MESON[]` ( a1 /\a2/\a3/\a4 ==> l ) 
==> ( a1/\a2/\a3/\a4/\a5 ==> l ) `) THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN 
REWRITE_TAC[ MESON[]` (?t. (? a b c. P a b c /\ t = Q a b c ) /\ x IN t )
  <=> (? a b c. P a b c /\ x IN Q a b c ) `] THEN REWRITE_TAC[IN_INTER] THEN 
SET_TAC[]);;
