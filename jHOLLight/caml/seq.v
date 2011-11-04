(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

"needs \"caml/ssrnat.hl\"".
"#use \"/mnt/HOL Light/update_database.ml\"".


(* The seq type is the ssreflect type for sequences; it is an alias for the   *)
(* standard Coq list type. The ssreflect library equips it with many          *)
(* operations, as well as eqType and predType (and, later, choiceType)        *)
(* structures. The operations are geared towards reflection: they generally   *)
(* expect and provide boolean predicates, e.g., the membership predicate      *)
(* expects an eqType. To avoid any confusion we do not Import the Coq List    *)
(* module.                                                                    *)
(*   As there is no true subtyping in Coq, we don't use a type for non-empty  *)
(* sequences; rather, we pass explicitly the head and tail of the sequence.   *)
(*   The empty sequence is especially bothersome for subscripting, since it   *)
(* forces us to pass a default value. This default value can often be hidden  *)
(* by a notation.                                                             *)
(*   Here is the list of seq operations:                                      *)
(*  ** constructors:                                                          *)
(*                        seq T == the type of sequences with items of type T *)
(*                       bitseq == seq bool                                   *)
(*             [::], nil, Nil T == the empty sequence (of type T)             *)
(* x :: s, cons x s, Cons T x s == the sequence x followed by s (of type T)   *)
(*                       [:: x] == the singleton sequence                     *)
(*           [:: x_0; ...; x_n] == the explicit sequence of the x_i           *)
(*       [:: x_0, ..., x_n & s] == the sequence of the x_i, followed by s     *)
(*                    rcons s x == the sequence s, followed by x              *)
(*  All of the above, except rcons, can be used in patterns. We define a view *)
(* lastP and and induction principle last_ind that can be used to decompose   *)
(* or traverse a sequence in a right to left order. The view lemma lastP has  *)
(* a dependent family type, so the ssreflect tactic case/lastP: p => [|p' x]  *)
(* will generate two subgoals in which p has been replaced by [::] and by     *)
(* rcons p' x, respectively.                                                  *)
(*  ** factories:                                                             *)
(*             nseq n x == a sequence of n x's                                *)
(*          ncons n x s == a sequence of n x's, followed by s                 *)
(* seqn n x_0 ... x_n-1 == the sequence of the x_i (can be partially applied) *)
(*             iota m n == the sequence m, m + 1, ..., m + n - 1              *)
(*            mkseq f n == the sequence f 0, f 1, ..., f (n - 1)              *)
(*  ** sequential access:                                                     *)
(*      head x0 s == the head (zero'th item) of s if s is non-empty, else x0  *)
(*        ohead s == None if s is empty, else Some x where x is the head of s *)
(*       behead s == s minus its head, i.e., s' if s = x :: s', else [::]     *)
(*       last x s == the last element of x :: s (which is non-empty)          *)
(*     belast x s == x :: s minus its last item                               *)
(*  ** dimensions:                                                            *)
(*         size s == the number of items (length) in s                        *)
(*       shape ss == the sequence of sizes of the items of the sequence of    *)
(*                   sequences ss                                             *)
(*  ** random access:                                                         *)
(*         nth x0 s i == the item i of s (numbered from 0), or x0 if s does   *)
(*                       not have at least i+1 items (i.e., size x <= i)      *)
(*               s`_i == standard notation for nth x0 s i for a default x0,   *)
(*                       e.g., 0 for rings.                                   *)
(*   set_nth x0 s i y == s where item i has been changed to y; if s does not  *)
(*                       have an item i it is first padded with copieds of x0 *)
(*                       to size i+1.                                         *)
(*       incr_nth s i == the nat sequence s with item i incremented (s is     *)
(*                       first padded with 0's to size i+1, if needed).       *)
(*  ** predicates:                                                            *)
(*          nilp s == s is [::]                                               *)
(*                 := (size s == 0)                                           *)
(*         x \in s == x appears in s (this requires an eqType for T)          *)
(*       index x s == the first index at which x appears in s, or size s if   *)
(*                    x \notin s                                              *)
(*         has p s == the (applicative, boolean) predicate p holds for some   *)
(*                    item in s                                               *)
(*         all p s == p holds for all items in s                              *)
(*        find p s == the number of items of s for which p holds              *)
(*      constant s == all items in s are identical (trivial if s = [::])      *)
(*          uniq s == all the items in s are pairwise different               *)
(*    subseq s1 s2 == s1 is a subsequence of s2, i.e., s1 = mask m s2 for     *)
(*                    some m : bitseq (see below).                            *)
(*   perm_eq s1 s2 == s2 is a permutation of s1, i.e., s1 and s2 have the     *)
(*                    items (with the same repetitions), but possibly in a    *)
(*                    different order.                                        *)
(*  perm_eql s1 s2 <-> s1 and s2 behave identically on the left of perm_eq    *)
(*  perm_eqr s1 s2 <-> s1 and s2 behave identically on the rightt of perm_eq  *)
(*    These left/right transitive versions of perm_eq make it easier to chain *)
(* a sequence of equivalences.                                                *)
(*  ** filtering:                                                             *)
(*           filter p s == the subsequence of s consisting of all the items   *)
(*                         for which the (boolean) predicate p holds          *)
(* subfilter s : seq sT == when sT has a subType p structure, the sequence    *)
(*                         of items of type sT corresponding to items of s    *)
(*                         for which p holds                                  *)
(*              undup s == the subsequence of s containing only the first     *)
(*                         occurrence of each item in s, i.e., s with all     *)
(*                         duplicates removed.                                *)
(*             mask m s == the subsequence of s selected by m : bitseq, with  *)
(*                         item i of s selected by bit i in m (extra items or *)
(*                         bits are ignored.                                  *)
(*  ** surgery:                                                               *)
(* s1 ++ s2, cat s1 s2 == the concatenation of s1 and s2                      *)
(*            take n s == the sequence containing only the first n items of s *)
(*                        (or all of s if size s <= n)                        *)
(*            drop n s == s minus its first n items ([::] if size s <= n)     *)
(*             rot n s == s rotated left n times (or s if size s <= n)        *)
(*                     := drop n s ++ take n s                                *)
(*            rotr n s == s rotated right n times (or s if size s <= n)       *)
(*               rev s == the (linear time) reversal of s                     *)
(*        catrev s1 s2 == the reversal of s1 followed by s2 (this is the      *)
(*                        recursive form of rev)                              *)
(*  ** iterators: for s == [:: x_1, ..., x_n], t == [:: y_1, ..., y_m],       *)
(*        map f s == the sequence [:: f x_1, ..., f x_n]                      *)
(*     [seq E | i <- s] := map (fun i => E) s                                 *)
(*  [seq E | i <- s, C] := map (fun i => E) (filter (fun i => C) s)           *)
(*      pmap pf s == the sequence [:: y_i1, ..., y_ik] where i1 < ... < ik,   *)
(*                   pf x_i = Some y_i, and pf x_j = None iff j is not in     *)
(*                   {i1, ..., ik}.                                           *)
(*   foldr f a s == the right fold of s by f (i.e., the natural iterator)     *)
(*               := f x_1 (f x_2 ... (f x_n a))                               *)
(*        sumn s == x_1 + (x_2 + ... + (x_n + 0)) (when s : seq nat)          *)
(*   foldl f a s == the left fold of s by f                                   *)
(*               := f (f ... (f a x_1) ... x_n-1) x_n                         *)
(*   scanl f a s == the sequence of partial accumulators of foldl f a s       *)
(*               := [:: f a x_1; ...; foldl f a s]                            *)
(* pairmap f a s == the sequence of f applied to consecutie items in a :: s   *)
(*               := [:: f a x_1; f x_1 x_2; ...; f x_n-1 x_n]                 *)
(*       zip s t == itemwise pairing of s and t (dropping any extra items)    *)
(*               := [:: (x_1, y_1); ...; (x_mn, y_mn)] with mn = minn n m.    *)
(*      unzip1 s == [:: (x_1).1; ...; (x_n).1] when s : seq (S * T)           *)
(*      unzip2 s == [:: (x_1).2; ...; (x_n).2] when s : seq (S * T)           *)
(*     flatten s == x_1 ++ ... ++ x_n ++ [::] when s : seq (seq T)            *)
(*   reshape r s == s reshaped into a sequence of sequences whose sizes are   *)
(*                  given by r (trucating if s is too long or too short)      *)
(*               := [:: [:: x_1; ...; x_r1];                                  *)
(*                      [:: x_(r1 + 1); ...; x_(r0 + r1)];                    *)
(*                      ...;                                                  *)
(*                      [:: x_(r1 + ... + r(k-1) + 1); ...; x_(r0 + ... rk)]] *)
(* allpairs f s t == the sequence of all the f x y, with x and y drawn from   *)
(*                  s and t, respectievly, in row-major order:                *)
(*               := [:: f x_1 y_1; ...; f x_1 y_m; f x_2 y_1; ...; f x_n y_m] *)
(*  [seq E | i <- s, j <- t] := allpairs (fun i j => E) s t                   *)
(*   We are quite systematic in providing lemmas to rewrite any composition   *)
(* of two operations. "rev", whose simplifications are not natural, is        *)
(* protected with nosimpl.                                                    *)


Section Sequences.

Variable n0 : `:num`.  (* numerical parameter for take, drop et al *)
--Variable T : Type.  (* must come before the implicit Type     *)
Variable x0 : `:A`.    (* default for head/nth *)

Implicit Types x y z : `:A`.
Implicit Types m n : `:num`.
Implicit Type s : `:(A)list`.

--Fixpoint size s := if s is _ :: s' then (size s').+1 else 0.
"let size = new_definition `sizel = LENGTH`".

Lemma size0nil s: `sizel s = 0 ==> s = []`.
by case: s => [->|[h [t] ->]]; move => //; rewr size LENGTH; arith. Qed.

--Definition nilp s := size s == 0.
"let nilp = new_definition `!(s:(A)list). nilp s <=> (sizel s = 0)`".

Lemma nilP s : `s = [] <=> nilp s`.
by case: s => [->|[h [t ->]]]; rewrite nilp size; rewr LENGTH // NOT_CONS_NIL; arith. Qed.

--Definition ohead s := if s is x :: _ then Some x else None.
--Definition head s := if s is x :: _ then x else x0.
"let head = define `!(x0:A) h t. headl x0 [] = x0 /\ headl x0 (CONS h t) = h`".

--Definition behead s := if s is _ :: s' then s' else [::].
"let behead = define `!(h:A) t. behead [] = [] /\ behead (CONS h t) = t`".

Lemma size_behead s : `sizel (behead s) = (sizel s) - 1`.
by case: s => [->|[h [t ->]]]; rewr behead size LENGTH SUC_SUB1 sub0n. Qed.

(* Factories *)

--Definition ncons n x := iter n (cons x).
--Definition nseq n x := ncons n x [::].
"let ncons = new_definition `!n (x:A). ncons n x = iter n (CONS x)`".
"let nseq = new_definition `!n (x:A). nseq n x = ncons n x []`".

Lemma size_nil : `sizel ([]:(A)list) = 0`. by rewr size LENGTH. Qed.
Lemma size_cons h t: `sizel (CONS (h:A) t) = SUC (sizel t)`. by rewr size LENGTH. Qed.

Lemma size_ncons n x s : `sizel (ncons n x s) = n + sizel s`.
--Proof. by elim: n => //= n ->. Qed.
elim: n; rewrite !ncons; rewr iter; rewrite ?add0n // => n IH.
by rewrite size_cons IH addSn.
Qed.

Lemma size_nseq n x : `sizel (nseq n (x:A)) = n`.
--Proof. by rewrite size_ncons addn0. Qed.
by rewrite nseq size_ncons size_nil addn0. Qed.

(* n-ary, dependently typed constructor. *)

--Fixpoint seqn_type n := if n is n'.+1 then T -> seqn_type n' else seq T.

--Fixpoint seqn_rec f n : seqn_type n :=
--  if n is n'.+1 return seqn_type n then
--    fun x => seqn_rec (fun s => f (x :: s)) n'
--  else f [::].
--Definition seqn := seqn_rec id.

(* Sequence catenation "cat".                                               *)

--Fixpoint cat s1 s2 := if s1 is x :: s1' then x :: s1' ++ s2 else s2
--where "s1 ++ s2" := (cat s1 s2) : seq_scope.

"parse_as_infix (\"::\", (12, \"right\"))".
"override_interface (\"::\", `CONS`)".
"make_overloadable \"++\" `:A -> A -> A`".

"let cat = define `!(x:A) t s2. cat [] s2 = s2 /\ cat (CONS x t) s2 = x :: cat t s2`".
"overload_interface (\"++\", `cat`)".

Lemma cat0s s : `[] ++ (s:(A)list) = s`. by rewr cat. Qed.
Lemma cat1s x s : `[x:A] ++ s = x :: s`. by rewr !cat. Qed.
Lemma cat_cons x s1 s2 : `(x :: s1) ++ s2 = x :: s1 ++ s2`. by rewr cat. Qed.

Lemma cat_nseq n x s : `nseq n (x:A) ++ s = ncons n x s`.
--Proof. by elim: n => //= n ->. Qed.
by elim: n; rewr nseq ncons iter cat // => n ->. Qed.

Lemma cats0 s : `s ++ [] = (s:(A)list)`.
--Proof. by elim: s => //= x s ->. Qed.
by elim: s => [| x s]; rewr cat // => ->. Qed.

Lemma catA s1 s2 s3 : `s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3:(A)list`.
--Proof. by elim: s1 => //= x s1 ->. Qed.
by elim: s1 => [| x s1]; rewr !cat // => ->. Qed.

Lemma size_cat s1 s2 : `sizel (s1 ++ s2) = sizel s1 + sizel (s2:(A)list)`.
--Proof. by elim: s1 => //= x s1 ->. Qed.
by elim: s1 => [| x s1]; rewr !cat size_nil size_cons add0n // addSn => ->. Qed.

(* last, belast, rcons, and last induction. *)

--Fixpoint rcons s z := if s is x :: s' then x :: rcons s' z else [:: z].
"let rcons = define `!x t (z:A). rcons [] z = [z] /\ rcons (x :: t) z = x :: rcons t z`".

Lemma rcons_cons x s z : `rcons (x :: s) z = x:A :: rcons s z`. by rewr rcons. Qed.

Lemma cats1 s z : `s ++ [z:A] = rcons s z`.
--Proof. by elim: s => //= x s ->. Qed.
by elim: s => [| x s]; rewr cat rcons // => ->. Qed.

--Fixpoint last x s := if s is x' :: s' then last x' s' else x.
--Fixpoint belast x s := if s is x' :: s' then x :: (belast x' s') else [::].
"let last = define `!(x:A) h t. last x [] = x /\ last x (h :: t) = last h t`".
"let belast = define `!(x:A) h t. belast x [] = [] /\ belast x (h :: t) = x :: (belast h t)`".

Lemma lastI x s : `(x:A :: s) = rcons (belast x s) (last x s)`.
--Proof. by elim: s x => [|y s IHs] x //=; rewrite IHs. Qed.
by elim: s x => [|y s IHs]; move => x; rewr belast last rcons. Qed.

Lemma last_cons x y s : `last x (y:A :: s) = last y s`. by rewr last. Qed.

Lemma size_rcons s x : `sizel (rcons s (x:A)) = SUC (sizel s)`.
--Proof. by rewrite -cats1 size_cat addnC. Qed.
by rewrite -cats1 size_cat size_cons size_nil addnS addn0. Qed.

Lemma size_belast x s : `sizel (belast (x:A) s) = sizel s`.
--Proof. by elim: s x => [|y s IHs] x //=; rewrite IHs. Qed.
by elim: s x => [|y s IHs]; move => x; rewr belast // size_cons. Qed.

Lemma last_cat x s1 s2 : `last (x:A) (s1 ++ s2) = last (last x s1) s2`.
--Proof. by elim: s1 x => [|y s1 IHs] x //=; rewrite IHs. Qed.
by elim: s1 x => [|y s1 IHs]; move => x; rewr last cat // last. Qed.

Lemma last_rcons x s z : `last x (rcons s z) = z:A`.
--Proof. by rewrite -cats1 last_cat. Qed.
by rewrite -cats1 last_cat; rewr !last. Qed.

Lemma belast_cat x s1 s2 :
  `belast x (s1 ++ s2) = belast x s1 ++ belast (last (x:A) s1) s2`.
--Proof. by elim: s1 x => [|y s1 IHs] x //=; rewrite IHs. Qed.
by elim: s1 x => [|y s1 IHs]; move => x; rewr belast cat last // belast. Qed.

Lemma belast_rcons x s z : `belast x (rcons s z) = x:A :: s`.
Proof. by rewrite lastI -!cats1 belast_cat; rewr !belast. Qed.

Lemma cat_rcons x s1 s2 : `rcons s1 x ++ s2 = s1 ++ (x:A :: s2)`.
--Proof. by rewrite -cats1 -catA. Qed.
by rewrite -cats1 -catA; rewr !cat. Qed.

Lemma rcons_cat x s1 s2 : `rcons (s1 ++ s2) x = s1 ++ rcons s2 (x:A)`.
Proof. by rewrite -!cats1 catA. Qed.

--CoInductive last_spec : seq T -> Type :=
--  | LastNil        : last_spec [::]
--  | LastRcons s x  : last_spec (rcons s x).
--Lemma lastP s : last_spec s.
--Proof. case: s => [|x s]; [left | rewrite lastI; right]. Qed.

Lemma last_ind P :
  `P [] ==> (!s (x : A). P s ==> P (rcons s x)) ==> (!s. P s)`.
--move=> Hnil Hlast s; rewrite -(cat0s s).
--elim: s [::] Hnil => [|x s2 IHs] s1 Hs1; first by rewrite cats0.
--by rewrite -cat_rcons; auto.
move => Hnil Hlast s.
rewrite -(cat0s s).
elim: s `[]` Hnil => [|y s2 IHs]; first by rewrite cats0.
by rewrite -cat_rcons => s1 Ps1; apply: IHs; exact: Hlast.
Qed.


(* Sequence indexing. *)

--Fixpoint nth s n {struct n} :=
--  if s is x :: s' then if n is n'.+1 then @nth s' n' else x else x0.
"let nth = define `!(x0:A) h t n. nth x0 [] n = x0 /\ nth x0 (h :: t) 0 = h /\ nth x0 (h :: t) (SUC n) = nth x0 t n`".

--Fixpoint set_nth s n y {struct n} :=
--  if s is x :: s' then if n is n'.+1 then x :: @set_nth s' n' y else y :: s'
--  else ncons n x0 [:: y].
"let set_nth = define `!(x0:A) h t n y. 
	set_nth x0 [] n y = ncons n x0 [y] /\
	set_nth x0 (h :: t) 0 y = y :: t /\
	set_nth x0 (h :: t) (SUC n) y = h :: set_nth x0 t n y`".

Lemma nth0 s : `nth x0 s 0 = headl x0 s`.
by elim: s => [|h t _]; rewr nth head. Qed.

Lemma nth_default s n : `sizel s <= n ==> nth x0 s n = x0`.
--Proof. by elim: s n => [|x s IHs] [|n]; try exact (IHs n). Qed.
elim: s n => [| x s IHs]; elim => [|n _]; rewr nth size_cons //; first by arith.
by rewrite leqSS; move/IHs. Qed.

Lemma nth_nil n : `nth x0 [] n = x0`.
--Proof. by case: n. Qed.
by elim: n => [|n _]; rewr nth. Qed.

Lemma last_nth x s : `last x s = nth x0 (x :: s) (sizel s)`.
--Proof. by elim: s x => [|y s IHs] x /=. Qed.
elim: s x => [|y s IHs]; move => x; rewr last size_nil nth; first done.
by rewrite IHs size_cons; rewr nth. Qed.

Lemma nth_last s : `nth x0 s (sizel s - 1) = last x0 s`.
--Proof. by case: s => //= x s; rewrite last_nth. Qed.
by elim: s => [|t h _]; rewr nth last // size_cons succnK last_nth. Qed.

Lemma nth_behead s n : `nth x0 (behead s) n = nth x0 s (SUC n)`.
--Proof. by case: s n => [|x s] [|n]. Qed.
by elim: s n => [|x s _]; elim => [|n _]; rewr behead nth. Qed.

Lemma nth_cat s1 s2 n :
  `nth x0 (s1 ++ s2) n = if n < sizel s1 then nth x0 s1 n else nth x0 s2 (n - sizel s1)`.
--Proof. by elim: s1 n => [|x s1 IHs] [|n]; try exact (IHs n). Qed.
elim: s1 n => [|x s1 IHs]; elim => [|n _]; 
	rewr cat sub0n size_nil ltnn /= subn0 nth size_cons; [arith | arith | move].
by rewrite IHs subSS !ltE leqSS. Qed.
  

Lemma nth_rcons s x n :
  `nth x0 (rcons s x) n =
    if n < sizel s then nth x0 s n else if n = sizel s then x else x0`.
--Proof. by elim: s n => [|y s IHs] [|n] //=; rewrite ?nth_nil ?IHs. Qed.
elim: s n => [|y s IHs]; elim => [|n _]; 
	rewr rcons nth size_nil ltnn /= nth size_cons ltn0Sn /=; first by arith.
by rewrite ltE leqSS eqSS IHs ltE.
Qed.

Lemma nth_ncons m x s n :
  `nth x0 (ncons m x s) n = if n < m then x else nth x0 s (n - m)`.
--Proof. by elim: m n => [|m IHm] [|n] //=; exact: IHm. Qed.
elim: m n => [|m IHm]; elim => [|n _]; 
	rewr ncons iter ltnn /= subn0 // -ncons nth; [arith | arith | move].
by rewrite IHm !ltE leqSS subSS.
Qed.

Lemma nth_nseq m x n : `nth x0 (nseq m x) n = (if n < m then x else x0)`.
--Proof. by elim: m n => [|m IHm] [|n] //=; exact: IHm. Qed.
elim: m n => [|m IHm]; elim => [|n _]; rewr nseq ncons iter nth ltnn /=; [arith| arith | move].
by rewrite -ncons -nseq IHm !ltE leqSS.
Qed.

Lemma eq_from_nth s1 s2 :
    `sizel s1 = sizel s2 ==> (!i. i < sizel s1 ==> nth x0 s1 i = nth x0 s2 i) ==>
  s1 = s2`.
--elim: s1 s2 => [|x1 s1 IHs1] [|x2 s2] //= [eq_sz] eq_s12.
--rewrite [x1](eq_s12 0) // (IHs1 s2) // => i; exact: (eq_s12 i.+1).
elim: s1 s2 => [|x1 s1 IHs1]; elim => [|x2 s2 _]; rewr size_cons size_nil NOT_SUC //.
rewrite eqSS => eq_sz eq_s12.
move: (eq_s12 `0`); rewrite ltn0Sn /= (IHs1 s2) //; last by rewr nth => ->.
rewrite -eq_sz /= => i c; move: (eq_s12 `SUC i`).
rewrite ltE leqSS -ltE => h.
by move: (h c); rewr nth.
Qed.

Lemma size_set_nth s n y : `sizel (set_nth x0 s n y) = maxn (SUC n) (sizel s)`.
--elim: s n => [|x s IHs] [|n] //=.
--- by rewrite size_ncons addn1 maxn0.
--- by rewrite -add_sub_maxn subn1.
--by rewrite IHs -add1n addn_maxr.
elim: s n => [|x s IHs]; elim => [|n _]; rewr set_nth.
  by rewr ncons iter size_cons size_nil maxn; arith.
  by rewr size_ncons size_cons size_nil -ONE addn1 maxn; arith.
  by rewrite -add_sub_maxn; rewr size_cons; arith.
by rewrite !size_cons IHs -add1n addn_maxr !add1n.
Qed.


Lemma set_nth_nil n y : `set_nth x0 [] n y = ncons n x0 [y]`.
--Proof. by case: n. Qed.
by elim: n => [|n _]; rewr set_nth. Qed.

Lemma ltS0 n : `SUC n < 0 <=> F`. by arith. Qed.
Lemma eqS0 n : `SUC n = 0 <=> F`. by arith. Qed.
Lemma eq0S n : `0 = SUC n <=> F`. by arith. Qed.
Lemma gtS0 n : `0 < SUC n`. by arith. Qed.
Lemma ltSS m n: `SUC m < SUC n <=> m < n`. by arith. Qed.

Lemma nth_set_nth s n y i: `nth x0 (set_nth x0 s n y) i = if i = n then y else nth x0 s i`.
--elim: s n => [|x s IHs] [|n] [|m] //=; rewrite ?nth_nil ?IHs // nth_ncons eqSS.
--case: ltngtP => // [lt_nm | ->]; last by rewrite subnn.
--by rewrite nth_default // subn_gt0.
elim: s n i => [|x s IHs]; elim => [|n _]; elim => [|m _];
    rewr set_nth nth_nil nth_ncons sub0n ltnn // ltS0 eqS0 eq0S gtS0 subn0 !nth; last first.
  by rewrite eqSS -IHs.
rewrite ltSS subSS eqSS.
case: (ltngtP m n) => [lt_mn | [lt_nm | ->]]; last by rewr subnn ltnn !nth.
  by rewrite lt_mn /= "ARITH_RULE `m < n ==> (m = n <=> F)`".
rewrite nth_default ?if_same; last by rewrite "ARITH_RULE `n < m ==> (m = n <=> F)`".
by rewrite size_cons size_nil -ltE subn_gt0.
Qed.


Lemma set_set_nth s n1 y1 n2 y2 :
  `set_nth x0 (set_nth x0 s n1 y1) n2 y2 = 
	if n1 = n2 then set_nth x0 s n2 y2 else set_nth x0 (set_nth x0 s n2 y2) n1 y1`.
--have [-> | ne_n12] := altP eqP.
--  apply: eq_from_nth => [|i _]; first by rewrite !size_set_nth maxnA maxnn.
--  by do 2!rewrite !nth_set_nth /=; case: eqP.
--apply: eq_from_nth => [|i _]; first by rewrite !size_set_nth maxnCA.
--do 2!rewrite !nth_set_nth /=; case: eqP => // ->.
--by rewrite eq_sym -if_neg ne_n12.
case: (EXCLUDED_MIDDLE `n1 = n2:num`) => [-> /=| ne_n12].
  apply: "REWRITE_RULE[IMP_IMP] eq_from_nth"; split; first by rewrite !size_set_nth maxnA maxnn.
  by move => i _; rewrite !nth_set_nth /=.
apply: "REWRITE_RULE[IMP_IMP] eq_from_nth"; split; first by rewr ne_n12 /=; rewrite !size_set_nth maxnCA.
move => i _; rewrite //= !nth_set_nth /=; rewr ne_n12 /=.
case: (EXCLUDED_MIDDLE `i = n2:num`) => [-> | ne_i2]; rewr /=.
  by rewr nth_set_nth ne_n12 /= nth_set_nth /=.
by rewr ne_i2 /= !nth_set_nth ne_i2 /=.
Qed.


(* find, count, has, all. *)

Section SeqFind.

Variable a : `:A -> bool`.


--Fixpoint find s := if s is x :: s' then if a x then 0 else (find s').+1 else 0.
"let find = define `!a (x:A) s'. find a [] = 0 /\ 
	find a (x :: s') = if a x then 0 else SUC(find a s')`".

--Fixpoint filter s :=
--  if s is x :: s' then if a x then x :: filter s' else filter s' else [::].
"let filter = define `!a (x:A) s'. filter a [] = [] /\
	filter a (x :: s') = if a x then x :: filter a s' else filter a s'`".

--Fixpoint count s := if s is x :: s' then a x + count s' else 0.
"let count = define `!a (x:A) s'. count a [] = 0 /\
	count a (x :: s') = (if a x then 1 else 0) + count a s'`".

--Fixpoint has s := if s is x :: s' then a x || has s' else false.
"let has = define `!a (x:A) s'. has a [] = F /\
	has a (x :: s') = (a x \/ has a s')`".

--Fixpoint all s := if s is x :: s' then a x && all s' else true.
"let all = define `!a (x:A) s'. all a [] = T /\
	all a (x :: s') = (a x /\ all a s')`".

Lemma find_nil : `find a [] = 0`. by rewr find. Qed.
Lemma find_cons x t: `find a (x::t) = if a x then 0 else SUC (find a t)`. by rewr find. Qed.
Lemma filter_nil : `filter a [] = []`. by rewr filter. Qed.
Lemma filter_cons x t: `filter a (x::t) = if a x then x :: filter a t else filter a t`.
by rewr filter. Qed.
Lemma count_nil : `count a [] = 0`. by rewr count. Qed.
Lemma count_cons x t: `count a (x::t) = (if a x then 1 else 0) + count a t`. by rewr count. Qed.
Lemma has_nil : `has a [] = F`. by rewr !has. Qed.
Lemma has_cons x t: `has a (x::t) <=> a x \/ has a t`. by rewr has. Qed.
Lemma all_nil : `all a [] = T`. by rewr !all. Qed.
Lemma all_cons x t: `all a (x::t) <=> a x /\ all a t`. by rewr all. Qed.

Lemma count_filter s : `count a s = sizel (filter a s)`.
--Proof. by elim: s => //= x s ->; case (a x). Qed.
elim: s => [| x s]; rewr count filter size_nil // => ->.
case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => [-> /=| nax]; rewr add1n size_cons /=.
by rewr nax /= add0n.
Qed.

Lemma has_count s : `has a s = (0 < count a s)`.
--Proof. by elim: s => //= x s ->; case (a x). Qed.
elim: s => [| x s]; rewr has !count ltnn // => ->.
by case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => [-> /=|nax //=]; arith.
Qed.

Lemma count_size s : `count a s <= sizel s`.
--Proof. by elim: s => //= x s; case: (a x); last exact: leqW. Qed.
elim: s => [|x s]; rewr count size_nil leqnn.
case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => //= _; rewrite size_cons; arith.
Qed.

Lemma all_count s : `all a s = (count a s = sizel s)`.
--elim: s => //= x s; case: (a x) => _ //=.
--by rewrite add0n eqn_leq andbC ltnNge count_size.
elim: s => [| x s]; rewr all !count size_nil //.
case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => /= _ _; rewr size_cons; first by arith.
by rewrite add0n eqn_leq andbC -ltE ltnNge count_size.
Qed.


Lemma filter_all s : `all a (filter a s)`.
--Proof. by elim: s => //= x s IHs; case: ifP => //= ->. Qed.
elim: s => [|x s IHs]; rewr filter all.
by case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => /=; rewr all. Qed.

Lemma all_filterP s : `(filter a s = s) <=> (all a s)`.
--apply: (iffP idP) => [| <-]; last exact: filter_all.
--by elim: s => //= x s IHs /andP[-> Hs]; rewrite IHs.
"EQ_TAC" => [<-|]; first by rewrite filter_all.
elim: s => [|x s IHs]; rewr filter all // => [] [-> Hs] /=.
by rewrite (IHs Hs).
Qed.


Lemma filter_id s : `filter a (filter a s) = filter a s`.
--Proof. by apply/all_filterP; exact: filter_all. Qed.
by rewrite all_filterP filter_all. Qed.

Lemma has_find s : `has a s <=> (find a s < sizel s)`.
--Proof. by elim: s => //= x s IHs; case (a x); rewrite ?leqnn. Qed.
elim: s => [| x s IHs]; rewr has !find size_nil size_cons ltnn //=.
by case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => /= _; rewrite ?ltSS ?gtS0.
Qed.

Lemma find_size s : `find a s <= sizel s`.
--Proof. by elim: s => //= x s IHs; case (a x). Qed.
elim: s => [|x s IHs]; rewr find size_nil size_cons leqnn.
by case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => /= _; rewrite ?leq0n // leqSS.
Qed.

Lemma find_cat s1 s2 :
  `find a (s1 ++ s2) = if has a s1 then find a s1 else sizel s1 + find a s2`.
--by elim: s1 => //= x s1 IHs; case: (a x) => //; rewrite IHs (fun_if succn).
elim: s1 => [|x s1 IHs]; rewr cat has find size_nil size_cons add0n //.
case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => /= _.
by rewrite IHs [`SUC _1`]fun_if addSn.
Qed.


Lemma has_nil : `has a [] = F`. by rewr !has. Qed.

Lemma has_seq1 x : `has a [x] = a x`. by rewr !has. Qed.

Lemma has_seqb b x : `has a (nseq (if b then 1 else 0) x) <=> (b /\ a x)`.
by case: b => -> /=; rewr nseq ncons ONE !iter has_nil // has_seq1. Qed.

Lemma all_nil : `all a [] = T`. by rewr !all. Qed.

Lemma all_seq1 x : `all a [x] = a x`. by rewr !all. Qed.

Lemma nth_find s : `has a s ==> a (nth x0 s (find a s))`.
--Proof. by elim: s => //= x s IHs; case Hx: (a x). Qed.
elim: s => [|x s IHs]; rewr has // find.
by case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => /=; rewr nth. Qed.

Lemma before_find s i : `i < find a s ==> (a (nth x0 s i) <=> F)`.
--by elim: s i => //= x s IHs; case Hx: (a x) => [|] // [|i] //; exact: (IHs i).
elim: s i => [|x s IHs]; rewr find ltn0 //.
case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => /= ax; first by rewrite ltn0.
elim => [|i _]; rewr nth ax // ltSS.
by move/IHs.
Qed.

Lemma filter_cat s1 s2 : `filter a (s1 ++ s2) = filter a s1 ++ filter a s2`.
--Proof. by elim: s1 => //= x s1 ->; case (a x). Qed.
elim: s1 => [|x s1 Ihs]; rewr cat filter cat //.
by case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => /= _; rewr cat.
Qed.

Lemma filter_rcons s x :
  `filter a (rcons s x) = if a x then rcons (filter a s) x else filter a s`.
--Proof. by rewrite -!cats1 filter_cat /=; case (a x); rewrite /= ?cats0. Qed.
rewrite -!cats1 filter_cat; rewr !filter.
by case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => /= _; rewrite cats0.
Qed.

Lemma count_cat s1 s2 : `count a (s1 ++ s2) = count a s1 + count a s2`.
Proof. by rewrite !count_filter filter_cat size_cat. Qed.

Lemma has_cat s1 s2 : `has a (s1 ++ s2) = (has a s1 \/ has a s2)`.
--Proof. by elim: s1 => [|x s1 IHs] //=; rewrite IHs orbA. Qed.
elim: s1 => [|x s1 IHs]; rewr cat has /=. 
by rewrite IHs orbA. Qed.

Lemma has_rcons s x : `has a (rcons s x) = (a x \/ has a s)`.
Proof. by rewrite -cats1 has_cat has_seq1 orbC. Qed.

Lemma all_cat s1 s2 : `all a (s1 ++ s2) = (all a s1 /\ all a s2)`.
--Proof. by elim: s1 => [|x s1 IHs] //=; rewrite IHs andbA. Qed.
elim: s1 => [|x s1 IHs]; rewr cat all /=. 
by rewrite IHs andbA. 
Qed.

Lemma all_rcons s x : `all a (rcons s x) = (a x /\ all a s)`.
Proof. by rewrite -cats1 all_cat all_seq1 andbC. Qed.

End SeqFind.

"let pred0 = new_basic_definition `pred0 = (\(x:A). F)`".
"let pred1 = new_definition `pred1 (a:A) = (\x. x = a)`".
"let predT = new_basic_definition `predT = (\(x:A). T)`".
"let predI = new_definition `predI p1 p2 = (\(x:A). p1 x /\ p2 x)`".
"let predU = new_definition `predU p1 p2 = (\(x:A). p1 x \/ p2 x)`".
"let predC = new_definition `predC p = (\(x:A). ~(p x))`".
"let predD = new_definition `predD p1 p2 = predI (predC p2) p1`".
"let predD1 = new_definition `predD1 a x = predD a (pred1 x)`".

Lemma eq_find a1 a2 : `(!x:A. a1 x = a2 x) ==> (!s. find a1 s = find a2 s)`.
by move/EQ_EXT => ->. Qed.

Lemma eq_filter a1 a2 : `(!x:A. a1 x = a2 x) ==> (!s. filter a1 s = filter a2 s)`.
by move/EQ_EXT => ->. Qed.

Lemma eq_count a1 a2 : `(!x:A. a1 x = a2 x) ==> (!s. count a1 s = count a2 s)`.
by move/EQ_EXT => ->. Qed.

Lemma eq_has a1 a2 : `(!x. a1 x = a2 x) ==> (!s. has a1 s = has a2 s)`.
by move/EQ_EXT => ->. Qed.

Lemma eq_all a1 a2 : `(!x. a1 x = a2 x) ==> (!s. all a1 s = all a2 s)`.
by move/EQ_EXT => ->. Qed.

Lemma filter_pred0 s : `filter pred0 s = []`.
elim: s => [|x s IHs]; rewr filter // pred0 /=.
by rewrite -IHs pred0. Qed.

Lemma filter_predT s : `filter predT s = s`.
--Proof. by elim: s => //= x s ->. Qed.
elim: s => [|x s IHs]; rewr filter // predT /=.
by rewrite -{2}IHs predT.
Qed.

Lemma filter_predI a1 a2 s : `filter (predI a1 a2) s = filter a1 (filter a2 s)`.
--elim: s => //= x s IHs; rewrite andbC IHs.
--by case: (a2 x) => //=; case (a1 x).
elim: s => [|x s IHs]; rewr !filter //= predI.
case: (EXCLUDED_MIDDLE `(a2:A->bool) x`) => /= _; last by rewrite -IHs predI.
case: (EXCLUDED_MIDDLE `(a1:A->bool) x`) => /= a1x; rewr filter.
	by rewr a1x /= -IHs predI.
by rewr a1x /= -IHs predI.
Qed.

Lemma count_pred0 s : `count pred0 s = 0`.
--Proof. by rewrite count_filter filter_pred0. Qed.
by rewrite count_filter filter_pred0 size_nil. Qed.

Lemma count_predT s : `count predT s = sizel s`.
Proof. by rewrite count_filter filter_predT. Qed.

Lemma count_predUI a1 a2 s :
 `count (predU a1 a2) s + count (predI a1 a2) s = count a1 s + count a2 (s:(A)list)`.
--elim: s => //= x s IHs; rewrite /= addnCA -addnA IHs addnA addnC.
--by rewrite -!addnA; do 2 nat_congr; case (a1 x); case (a2 x).
elim: s => [|x s IHs]; rewr count //= predI predU.
case: (EXCLUDED_MIDDLE `(a1:A->bool) x`) => /= a1x;
case: (EXCLUDED_MIDDLE `(a2:A->bool) x`) => /= a2x; rewrite -predI -predU; move: IHs; arith.
Qed.

Lemma count_predC a s : `count a s + count (predC a) s = sizel (s:(A)list)`.
--by elim: s => //= x s IHs; rewrite addnCA -addnA IHs addnA addn_negb.
elim: s => [|x s IHs]; rewr count size_nil add0n /=.
rewrite addnCA -addnA IHs size_cons predC.
case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => /= ax; arith. Qed.


Lemma has_pred0 s : `has pred0 s = F`.
Proof. by rewrite has_count count_pred0 ltnn. Qed.

Lemma has_predT s : `has predT s = (0 < sizel s)`.
Proof. by rewrite has_count count_predT. Qed.

Lemma has_predC a s : `has (predC a) s = ~ all a s`.
--Proof. by elim: s => //= x s ->; case (a x). Qed.
elim: s => [|x s IHs]; rewr has !all.
by rewrite IHs predC /= negb_and. Qed.


Lemma has_predU a1 a2 s : `has (predU a1 a2) s <=> (has a1 s \/ has a2 s)`.
--Proof. by elim: s => //= x s ->; rewrite -!orbA; do !bool_congr. Qed.
elim: s => [|x s IHs]; rewr has /=.
rewrite IHs predU /= -!orbA.
by rewrite [`has a1 s \/ _ \/ _1`]orbCA.
Qed.

Lemma all_pred0 s : `all pred0 s = (sizel s = 0)`.
Proof. by rewrite all_count count_pred0 [`0 = _`]eq_sym. Qed.

Lemma all_predT s : `all predT s`.
Proof. by rewrite all_count count_predT. Qed.

Lemma all_predC a s : `all (predC a) s = ~ has a s`.
--Proof. by elim: s => //= x s ->; case (a x). Qed.
elim: s => [|x s IHs]; rewr all !has.
by rewrite IHs negb_or predC. Qed.

Lemma can_inj f g : `(!x. g (f x) = x) ==> (!x y. f x = f y ==> x = y)`.
move => h x y f_eq.
by rewrite -h -[`y`]h f_eq.
Qed.

Lemma all_predI a1 a2 s : `all (predI a1 a2) s <=> all a1 s /\ all a2 s`.
--apply: (can_inj negbK); rewrite negb_and -!has_predC -has_predU.
--by apply: eq_has => x; rewrite /= negb_and.
by apply: (can_inj negbK); rewrite negb_and -!has_predC -has_predU predU predI !predC /= negb_and. Qed.


(* Surgery: drop, take, rot, rotr.                                        *)

--Fixpoint drop n s {struct s} :=
--  match s, n with
--  | _ :: s', n'.+1 => drop n' s'
--  | _, _ => s
--  end.
"let drop = define `!n x s. dropl (SUC n) (x :: s) = dropl n s /\ 
	dropl n [] = [] /\ dropl 0 s = s`".

Lemma eq_ext f g: `(!x. f x = g x) <=> f = g`.
"EQ_TAC" => h; first by "MATCH_MP_TAC EQ_EXT".
by rewrite h.
Qed.

Lemma drop_nil n : `dropl n [] = []`. by rewr drop. Qed.
Lemma drop0 : `dropl 0 = I`. by rewr -eq_ext drop I_THM. Qed.
Lemma drop_cons n x s: `dropl (SUC n) (x :: s) = dropl n s`. by rewr drop. Qed.

Lemma drop_behead : `dropl n0 = iter n0 behead`.
--Proof. by elim: n0 => [|n IHn] [|x s] //; rewrite iterSr -IHn. Qed.
elim: n0 => [|n IHn]; rewr -eq_ext drop; first by rewr iter.
by elim => [|x s _]; rewrite iterSr -IHn; rewr behead drop. Qed.

Lemma drop0 s : `dropl 0 s = s`.
by elim: s => [|x s _]; rewr drop. Qed.

Lemma drop1 s : `dropl 1 s = behead s`.
--Proof. by case=> [|x [|y s]]. Qed.
by elim: s => [|x s _]; rewr ONE drop behead // drop0. Qed.

Lemma drop_oversize n s : `sizel s <= n ==> dropl n s = []`.
--Proof. by elim: n s => [|n IHn] [|x s]; try exact (IHn s). Qed.
elim: n s => [|n IHn]; elim => [|x s _]; rewr drop // size_cons -ltE ltn0 //.
by rewrite ltE leqSS; move/IHn.
Qed.

Lemma drop_size s : `dropl (sizel s) s = []`.
Proof. by rewrite drop_oversize // leqnn. Qed.


Lemma size_drop s : `sizel (dropl n0 s) = sizel s - n0`.
--Proof. by elim: s n0 => [|x s IHs] [|n]; try exact (IHs n). Qed.
elim: s n0 => [|x s IHs]; elim => [|n _]; rewr drop size_nil subn0 sub0n //.
by rewrite size_cons subSS.
Qed.

Lemma drop_cat s1 s2 :
  `dropl n0 (s1 ++ s2) =
    if n0 < sizel s1 then dropl n0 s1 ++ s2 else dropl (n0 - sizel s1) s2`.
--Proof. by elim: s1 n0 => [|x s1 IHs] [|n]; try exact (IHs n). Qed.
elim: s1 n0 => [|x s1 IHs]; elim => [|n _]; rewr cat sub0n drop cat size_cons if_same /=;
	rewr size_nil ltn0 /= subn0 gtS0 /=.
by rewrite IHs ltSS subSS.
Qed.

Lemma drop_size_cat n s1 s2 : `sizel s1 = n ==> dropl n (s1 ++ s2) = s2`.
--Proof. by move <-; elim: s1 => //=; rewrite drop0. Qed.
move => <-; elim: s1 => [|x s IHs]; rewr cat size_nil drop0 //.
by rewrite size_cons drop_cons IHs.
Qed.

Lemma nconsK n x s : `dropl n (ncons n x s) = s`.
--Proof. by elim: n => //; case. Qed.
by elim: n => [|n IHn]; rewr drop ncons iter /= drop -ncons. Qed.

--Fixpoint take n s {struct s} :=
--  match s, n with
--  | x :: s', n'.+1 => x :: take n' s'
--  | _, _ => [::]
--  end.
"let take = define `!x s n. take (SUC n) (x :: s) = x :: take n s /\
	take 0 s = [] /\ take n [] = []`".

Lemma take0 s : `take 0 s = []`. by elim: s => [|x s _]; rewr take. Qed.

Lemma take_oversize n s : `sizel s <= n ==> take n s = s`.
--Proof. by elim: n s => [|n IHn] [|x s] Hsn; try (congr cons; apply: IHn). Qed.
elim: n s => [|n IHn]; elim => [|x s IHs]; rewr take /=.
  by rewrite size_cons -ltE ltn0.
by rewrite size_cons leqSS => Hsn; rewrite IHn.
Qed.


Lemma take_size s : `take (sizel s) s = s`.
Proof. by rewrite take_oversize // leqnn. Qed.

--Lemma take_cons x s :
--  take n0 (x :: s) = if n0 is n.+1 then x :: (take n s) else [::].
--Proof. by []. Qed.
Lemma take_cons x s : `take (SUC n0) (x :: s) = x :: (take n0 s)`. by rewr take. Qed.

Lemma drop_rcons s : `n0 <= sizel s ==>
  !x. dropl n0 (rcons s x) = rcons (dropl n0 s) x`.
--Proof. by elim: s n0 => [|y s IHs] [|n]; try exact (IHs n). Qed.
elim: s n0 => [|y s IHs]; elim => [|n _]; rewr drop rcons /= size_nil -ltE ltn0 /=.
by rewrite size_cons ltE leqSS drop_cons; move/IHs => <-.
Qed.

Lemma congr1 f x y: `x = y ==> f x = f y`. by move => ->. Qed.

Lemma cat_take_drop s : `take n0 s ++ dropl n0 s = s`.
--Proof. by elim: s n0 => [|x s IHs] [|n]; try exact (congr1 _ (IHs n)). Qed.
elim: s n0 => [|x s IHs]; elim => [|n _]; rewr take drop cat /=.
by rewrite IHs.
Qed.

Lemma size_takel s : `n0 <= sizel s ==> sizel (take n0 s) = n0`.
--by move/subnKC; rewrite -{2}(cat_take_drop s) size_cat size_drop => /addIn.
by move/subnKC; rewrite -{2}(cat_take_drop s) size_cat size_drop; move/addIn => <-. Qed.

Lemma size_take s : `sizel (take n0 s) = if n0 < sizel s then n0 else sizel s`.
--have [le_sn | lt_ns] := leqP (size s) n0; first by rewrite take_oversize.
--by rewrite size_takel // ltnW.
move: (leqP `sizel (s:(A)list)` n0) => [le_sn | lt_ns].
  by rewrite take_oversize // ltnNge le_sn /=.
by rewrite lt_ns /= size_takel // ltnW.
Qed.

Lemma take_cat s1 s2 :
 `take n0 (s1 ++ s2) =
   if n0 < sizel s1 then take n0 s1 else s1 ++ take (n0 - sizel s1) s2`.
--elim: s1 n0 => [|x s1 IHs] [|n] //=.
--by rewrite ltnS subSS -(fun_if (cons x)) -IHs.
elim: s1 n0 => [|x s1 IHs]; elim => [|n _]; 
	rewr cat take size_nil ltn0 /= subn0 take /= size_cons gtS0 /=.
by rewrite ltSS subSS -fun_if IHs.
Qed.

Lemma take_size_cat n s1 s2 : `sizel s1 = n ==> take n (s1 ++ s2) = s1`.
--Proof. by move <-; elim: s1 => [|x s1 IHs]; rewrite ?take0 //= IHs. Qed.
move => <-; elim: s1 => [|x s1 IHs]; rewr size_nil take /= size_cons cat take.
by rewrite IHs.
Qed.

Lemma takel_cat s1 :
    `n0 <= sizel (s1:(A)list) ==> (!s2. take n0 (s1 ++ s2) = take n0 s1)`.
move=> Hn0 s2.
rewrite take_cat ltn_neqAle Hn0 andbT.
--by case: (n0 =P size s1) => //= ->; rewrite subnn take0 cats0 take_size.
case: (EXCLUDED_MIDDLE `n0 = sizel (s1:(A)list)`) => /= eq.
by rewrite subnn take0 cats0 take_size.
Qed.


Lemma nth_drop s i : `nth x0 (dropl n0 s) i = nth x0 s (n0 + i)`.
--have [lt_n0_s | le_s_n0] := ltnP n0 (size s).
move: (ltnP n0 `sizel (s:(A)list)`) => [lt_n0_s | le_s_n0].
  rewrite -{2}[`s`]cat_take_drop nth_cat size_take lt_n0_s /= addKn.
  by rewrite ltnNge leq_addr.
--rewrite !nth_default //; first exact: leq_trans (leq_addr _ _).
--by rewrite size_drop (eqnP le_s_n0).
rewrite !nth_default //.
  by move: le_s_n0; rewrite size_drop !leqE => ->; rewrite sub0n.
by apply: (leq_trans le_s_n0); rewrite leq_addr.
Qed.

Lemma nth_take i : `i < n0 ==> !s. nth x0 (take n0 s) i = nth x0 s i`.
Proof.
--move=> lt_i_n0 s; case lt_n0_s: (n0 < size s).
move => lt_i_n0 s; case: (EXCLUDED_MIDDLE `n0 < sizel (s:(A)list)`) => lt_n0_s.
  by rewrite -{2}[`s`]cat_take_drop nth_cat size_take lt_n0_s /= lt_i_n0.
by rewrite -{1}[`s`]cats0 take_cat; rewr lt_n0_s /= take cats0.
Qed.

(* drop_nth and take_nth below do NOT use the default n0, because the "n"  *)
(* can be inferred from the condition, whereas the nth default value x0    *)
(* will have to be given explicitly (and this will provide "d" as well).   *)

Lemma drop_nth n s : `n < sizel s ==> dropl n s = nth x0 s n :: dropl (SUC n) s`.
--Proof. by elim: s n => [|x s IHs] [|n] Hn //=; rewrite ?drop0 1?IHs. Qed.
elim: s n => [|x s IHs]; elim => [|n _]; rewr drop size_nil ltn0 /= nth drop /=.
by rewrite size_cons ltSS; move/IHs.
Qed.

Lemma take_nth n s : `n < sizel s ==> take (SUC n) s = rcons (take n s) (nth x0 s n)`.
--Proof. by elim: s n => [|x s IHs] //= [|n] Hn /=; rewrite ?take0 -?IHs. Qed.
elim: s n => [|x s IHs]; elim => [|n _]; rewr size_nil ltn0 /= take rcons nth take /=.
by rewrite size_cons ltSS; move/IHs => ->.
Qed.

(* Rotation *)

--Definition rot n s := drop n s ++ take n s.
"let rot = new_definition `rot n s = dropl n s ++ take n s`".

Lemma rot0 s : `rot 0 s = s`.
Proof. by rewrite rot drop0 take0 cats0. Qed.

Lemma size_rot s : `sizel (rot n0 s) = sizel s`.
Proof. by rewrite -{2}[`s`]cat_take_drop rot !size_cat addnC. Qed.

Lemma rot_oversize n s : `sizel s <= n ==> rot n s = s`.
Proof. by move=> le_s_n; rewrite rot take_oversize ?drop_oversize //; rewr cat. Qed.

Lemma rot_size s : `rot (sizel s) s = s`.
--Proof. exact: rot_oversize. Qed.
by apply: rot_oversize; rewrite leqnn. Qed.

Lemma has_rot s a : `has a (rot n0 s) = has a s`.
--Proof. by rewrite has_cat orbC -has_cat cat_take_drop. Qed.
by rewrite rot has_cat orbC -has_cat cat_take_drop. Qed.

Lemma rot_size_cat s1 s2 : `rot (sizel s1) (s1 ++ s2) = s2 ++ s1`.
Proof. by rewrite rot take_size_cat ?drop_size_cat. Qed.

--Definition rotr n s := rot (size s - n) s.
"let rotr = new_definition `rotr n s = rot (sizel s - n) s`".

Lemma rotK s : `rotr n0 (rot n0 s) = s`.
rewrite rotr size_rot -size_drop [`rot n0 _`]rot.
by rewrite rot_size_cat cat_take_drop.
Qed.

Lemma rot_inj s1 s2: `rot n0 (s1:(A)list) = rot n0 s2 ==> s1 = s2`.
by move: ((can_inj rotK) s1 s2). Qed.

Lemma rot1_cons x s : `rot 1 (x :: s) = rcons s x`.
Proof. by rewrite rot ONE drop_cons take_cons take0 drop0 -cats1. Qed.

(* (efficient) reversal *)

--Fixpoint catrev s1 s2 := if s1 is x :: s1' then catrev s1' (x :: s2) else s2.

End Sequences.

(* rev must be defined outside a Section because Coq's end of section *)
(* "cooking" removes the nosimpl guard.                               *)

--Definition rev T (s : seq T) := nosimpl (catrev s [::]).
"let catrev = define `catrev (x :: s1) s2 = catrev s1 (x :: s2) /\ catrev [] s2 = s2`".
"let rev = new_definition `rev s = catrev s []`".

--Implicit Arguments nilP [T s].
--Implicit Arguments all_filterP [T a s].

--Prenex Implicits size nilP head ohead behead last rcons belast.
--Prenex Implicits cat take drop rev rot rotr.
--Prenex Implicits find count nth all has filter all_filterP.

--Infix "++" := cat : seq_scope.

Section Rev.

--Variable T : Type.
Implicit Types s t: `:(A)list`.

Lemma catrev_catl s t u : `catrev (s ++ t) u = catrev t (catrev s u)`.
--Proof. by elim: s u => /=. Qed.
by elim: s u; rewr cat catrev /=. Qed.

Lemma catrev_catr s t u : `catrev s (t ++ u) = catrev s t ++ u`.
--Proof. by elim: s t => //= x s IHs t; rewrite -IHs. Qed.
elim: s t => [|x s IHs]; move => t; rewr catrev /=.
by rewr -IHs cat.
Qed.

Lemma catrevE s t : `catrev s t = rev s ++ t`.
Proof. by rewrite rev -catrev_catr; rewr cat. Qed.

Lemma rev_cons x s : `rev (x :: s) = rcons (rev s) x`.
Proof. by rewrite -cats1 -catrevE rev; rewr catrev. Qed.

Lemma size_rev s : `sizel (rev s) = sizel s`.
--Proof. by elim: s => // x s IHs; rewrite rev_cons size_rcons IHs. Qed.
elim: s => [|x s IHs]; rewr rev catrev /=.
by rewrite catrevE cats1 size_rcons IHs size_cons.
Qed.

Lemma rev_cat s t : `rev (s ++ t) = rev t ++ rev s`.
Proof. by rewrite !rev -catrev_catr cat0s -catrev_catl. Qed.

Lemma rev_rcons s x : `rev (rcons s x) = x :: rev s`.
Proof. by rewrite -cats1 rev_cat rev; rewr !catrev !cat. Qed.

Lemma revK s : `rev (rev s) = s`.
--Proof. by elim=> //= x s IHs; rewrite rev_cons rev_rcons IHs. Qed.
elim: s => [|x s IHs]; first rewr !rev !catrev /=.
by rewrite rev_cons rev_rcons IHs.
Qed.

Lemma nth_rev x0 n s :
  `n < sizel s ==> nth x0 (rev s) n = nth x0 s (sizel s - SUC n)`.
(*
elim/last_ind: s => // s x IHs in n *.
rewrite rev_rcons size_rcons ltnS subSS -cats1 nth_cat /=.
case: n => [|n] lt_n_s; first by rewrite subn0 ltnn subnn.
by rewrite -{2}(subnK lt_n_s) -addSnnS leq_addr /= -IHs.
*)
move: s n; apply: "REWRITE_RULE[IMP_IMP] last_ind".
rewrite size_nil ltn0 /= => s x IHs n.
rewrite rev_rcons size_rcons ltnS subSS -cats1 nth_cat.
elim: n => [|n _]; first by rewrite subn0 ltnn /= subnn !nth0; rewr head.
move => lt_n_s.
rewrite -{2}(subnK lt_n_s) -addSnnS ltE leq_addr /= -IHs ?ltE //.
by rewr nth.
Qed.

End Rev.

(* Equality and eqType for seq.                                          *)

Section EqSeq.

Variables n0 : `:num`.
Variable x0 : `:A`.
--Notation Local nth := (nth x0).
Implicit Type s : `:(A)list`.
Implicit Types x y z : `:A`.

(*
Fixpoint eqseq s1 s2 {struct s2} :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => (x1 == x2) && eqseq s1' s2'
  | _, _ => false
  end.

Lemma eqseqP : Equality.axiom eqseq.
Proof.
move; elim=> [|x1 s1 IHs] [|x2 s2]; do [by constructor | simpl].
case: (x1 =P x2) => [<-|neqx]; last by right; case.
by apply: (iffP (IHs s2)) => [<-|[]].
Qed.

Canonical seq_eqMixin := EqMixin eqseqP.
Canonical seq_eqType := Eval hnf in EqType (seq T) seq_eqMixin.

Lemma eqseqE : eqseq = eq_op. Proof. by []. Qed.
*)

Lemma eqseq_cons x1 x2 s1 s2 :
  `((x1 :: s1) = x2 :: s2) <=> (x1 = x2 /\ s1 = s2)`.
by rewrite "injectivity \"list\"".
Qed.

Lemma eqseq_cat s1 s2 s3 s4 :
  `sizel s1 = sizel s2 ==> (s1 ++ s3 = s2 ++ s4 <=> (s1 = s2 /\ s3 = s4))`.
--elim: s1 s2 => [|x1 s1 IHs] [|x2 s2] //= [sz12].
--by rewrite !eqseq_cons -andbA IHs.
elim: s1 s2 => [|x1 s1 IHs]; elim => [|x2 s2 _]; rewr !cat size_nil size_cons; 
	[arith | arith | move].
by rewrite eqSS !eqseq_cons -andbA; move/IHs => ->.
Qed.

Lemma eqseq_rcons s1 s2 x1 x2 :
  `(rcons s1 x1 = rcons s2 x2) <=> (s1 = s2 /\ x1 = x2)`.
Proof.
--elim: s1 s2 => [|y1 s1 IHs] [|y2 s2] /=;
--  rewrite ?eqseq_cons ?andbT ?andbF // ?IHs 1?andbA // andbC;
--  by [case s2 | case s1].
elim: s1 s2 => [|y1 s1 IHs]; elim => [|y2 s2 _]; rewr rcons eqseq_cons /=; last first.
  by rewrite IHs andbA.
  by elim: s2 => [|x s2 _]; rewr rcons NOT_CONS_NIL /=.
by elim: s1 => [|xx ss _]; rewr rcons NOT_CONS_NIL /=.
Qed.

Lemma has_filter a s : `has a s <=> ~(filter a s = [])`.
Proof. 
rewrite has_count count_filter.
set l := `filter a s`.
elim: l l_def => [|x l _]; move => _; rewrite ?size_nil /= ?ltnn // size_cons.
by rewr NOT_CONS_NIL gtS0.
Qed.
-- case (filter a s). Qed.

Lemma size_eq0 s : `(sizel s = 0) <=> (s = [])`.
by split => [| ->]; rewrite ?size_nil //; move/size0nil. Qed.

(* mem_seq and index. *)
(* mem_seq defines a predType for seq. *)

--Fixpoint mem_seq (s : seq T) :=
--  if s is y :: s' then xpredU1 y (mem_seq s') else xpred0.
--Definition eqseq_class := seq T.
--Identity Coercion seq_of_eqseq : eqseq_class >-> seq.
--Coercion pred_of_eq_seq (s : eqseq_class) : pred_class := [eta mem_seq s].
--Canonical seq_predType := @mkPredType T (seq T) pred_of_eq_seq.
(* The line below makes mem_seq a canonical instance of topred. *)
--Canonical mem_seq_predType := mkPredType mem_seq.

"parse_as_infix(\"<-\", (11, \"right\"))".
"override_interface(\"<-\", `MEM`)".

Lemma in_cons y s x : `(x <- y :: s) <=> (x = y \/ x <- s)`. by rewr !MEM. Qed.

Lemma in_nil x : `(x <- []) = F`. by rewr !MEM. Qed.

Lemma mem_seq1 x y : `(x <- [y]) <=> (x = y)`.
by rewrite in_cons in_nil orbF. Qed.

 (* to be repeated after the Section discharge. *)
--Let inE := (mem_seq1, in_cons, inE).

Lemma mem_seq2 x y1 y2 : `(x <- [y1; y2]) <=> (x = y1 \/ x = y2)`.
by rewrite !in_cons in_nil orbF. Qed.

Lemma mem_seq3  x y1 y2 y3 : `(x <- [y1; y2; y3]) <=> (x = y1 \/ x = y2 \/ x = y3)`.
--Proof. by rewrite !inE. Qed.
by rewrite !in_cons in_nil orbF. Qed.

Lemma mem_seq4  x y1 y2 y3 y4 :
  `(x <- [y1; y2; y3; y4]) <=> (x = y1 \/ x = y2 \/ x = y3 \/ x = y4)`.
Proof. by rewrite !in_cons in_nil orbF. Qed.

Lemma mem_cat x s1 s2 : `(x <- s1 ++ s2) <=> (x <- s1 \/ x <- s2)`.
--Proof. by elim: s1 => //= y s1 IHs; rewrite !inE /= -orbA -IHs. Qed.
elim: s1 => [|y s1 IHs]; first by rewrite cat0s in_nil orFb.
by rewrite cat_cons !in_cons IHs -orbA. Qed.

Lemma mem_rcons s y : `!x. x <- rcons s y <=> x <- y :: s`.
Proof. by move=> x; rewrite -cats1 /= mem_cat mem_seq1 orbC in_cons. Qed.

Lemma mem_head x s : `x <- x :: s`.
--Proof. exact: predU1l. Qed.
by rewrite in_cons /=. Qed.

Lemma mem_last x s : `last x s <- x :: s`.
Proof. by rewrite lastI mem_rcons mem_head. Qed.

Lemma mem_behead s : `!x. x <- behead s ==> x <- s`.
--Proof. by case: s => // y s x; exact: predU1r. Qed.
by elim: s => [|y s _ x]; rewr behead in_nil // in_cons /=. Qed.

Lemma mem_belast s y : `!x. x <- belast y s ==> x <- y :: s`.
--Proof. by move=> x ys'x; rewrite lastI mem_rcons mem_behead. Qed.
by move => x ys'x; rewrite lastI mem_rcons mem_behead; rewr behead. Qed.

Lemma mem_nth s n : `n < sizel s ==> nth x0 s n <- s`.
--by elim: s n => [|x s IHs] // [_|n sz_s]; rewrite ?mem_head // mem_behead ?IHs.
elim: s n => [|x s IHs]; elim => [|n _]; rewr size_nil ltnn ltS0 /= nth mem_head /=.
rewrite size_cons ltSS => sz_s.
by rewrite mem_behead; rewr behead; rewrite IHs.
Qed.

Lemma mem_take s x : `x <- take n0 s ==> x <- s`.
--Proof. by move=> s0x; rewrite -(cat_take_drop n0 s) mem_cat /= s0x. Qed.
by move => s0x; rewrite -(cat_take_drop n0 s) mem_cat. Qed.

Lemma mem_drop s x : `x <- dropl n0 s ==> x <- s`.
--Proof. by move=> s0'x; rewrite -(cat_take_drop n0 s) mem_cat /= s0'x orbT. Qed.
by move => s0'x; rewrite -(cat_take_drop n0 s) mem_cat. Qed.

Lemma mem_rev s : `!x. x <- rev s <=> x <- s`.
--by move=> y; elim: s => // x s IHs; rewrite rev_cons /= mem_rcons in_cons IHs.
move => y; elim: s => [|x s IHs]; first by rewr rev catrev /=.
by rewrite rev_cons mem_rcons !in_cons IHs. Qed.

Section Filters.

Variable a : `:A -> bool`.

Lemma hasP s : `(?x. x <- s /\ a x) <=> has a s`.
--elim: s => [|y s IHs] /=; first by right; case.
--case ay: (a y); first by left; exists y; rewrite ?mem_head.
--apply: (iffP IHs) => [] [x ysx ax]; exists x => //; first exact: mem_behead.
--by case: (predU1P ysx) ax => [->|//]; rewrite ay.
elim: s => [|y s IHs]; rewr has !in_nil.
case: (EXCLUDED_MIDDLE `(a:A->bool) y`) => /= ay; first by exists y; rewrite mem_head.
rewrite -IHs; split => [] [x [ysx ax]]; last first.
  by exists x; rewrite mem_behead //; rewr behead.
exists x; move: ysx; rewrite in_cons.
case: (EXCLUDED_MIDDLE `x = y:A`) => //= xy.
by move: ax; rewr xy ay.
Qed.

Lemma hasPn s : `(!x. x <- s ==> ~(a x)) <=> ~has a s`.
--apply: (iffP idP) => not_a_s => [x s_x|].
--  by apply: contra not_a_s => a_x; apply/hasP; exists x.
--by apply/hasP=> [[x s_x]]; apply/negP; exact: not_a_s.
split => not_a_s; first last.
  move => x s_x; apply: contra not_a_s => a_x.
  by rewrite -hasP; exists x.
by rewrite -hasP -implybF => [[x [s_x]]]; rewrite implybF; exact: not_a_s.
Qed.

Lemma allP s : `(!x. x <- s ==> a x) <=> (all a s)`.
--elim: s => [|x s IHs]; first by left.
--rewrite /= andbC; case: IHs => IHs /=.
--  apply: (iffP idP) => [Hx y|]; last by apply; exact: mem_head.
--  by case/predU1P=> [->|Hy]; auto.
--by right=> H; case IHs => y Hy; apply H; exact: mem_behead.
elim: s => [|x s IHs]; rewr in_nil all //.
rewrite andbC -IHs in_cons; split; last first.
  move => [h ax] y [-> //|ys].
  exact: h.
move => h.
case: (EXCLUDED_MIDDLE `(a:A->bool) x`) => /=; first move => ax.
  by rewr ax /= => y ys; exact: h.
exact: h.
Qed.


Lemma allPn s : `(?x. x <- s /\ ~a x) <=> ~all a s`.
--elim: s => [|x s IHs]; first by right=> [[x Hx _]].
--rewrite /= andbC negb_and; case: IHs => IHs /=.
--  by left; case: IHs => y Hy Hay; exists y; first exact: mem_behead.
--apply: (iffP idP) => [|[y]]; first by exists x; rewrite ?mem_head.
--by case/predU1P=> [-> // | s_y not_a_y]; case: IHs; exists y.
elim: s => [|x s IHs]; rewr all in_nil // in_cons.
rewrite andbC negb_and -IHs; split.
  move => [y [ay [eq | mem]]].
    by move: ay; rewrite eq /=.
  by right; exists y.
case => [nax |[y [ys nay]]]; first by exists x => /=.
by exists y.
Qed.


Lemma mem_filter x s : `(x <- filter a s) <=> (a x /\ x <- s)`.
--rewrite andbC; elim: s => //= y s IHs.
--rewrite (fun_if (fun s' : seq T => x \in s')) !in_cons {}IHs.
--by case: eqP => [->|_]; case (a y); rewrite /= ?andbF.
rewrite andbC; elim: s => [|y s IHs]; rewr filter MEM //.
rewrite fun_if !in_cons IHs.
by case: (EXCLUDED_MIDDLE `(a:A->bool) y`) => /= ay;
  case: (EXCLUDED_MIDDLE `x = y:A`) => //=.
Qed.

End Filters.

Lemma eq_in_filter a1 a2 s :
  `(!x. x <- s ==> a1 x = a2 x) ==> filter a1 s = filter a2 s`.
--elim: s => //= x s IHs eq_a.
--rewrite eq_a ?mem_head ?IHs // => y s_y; apply: eq_a; exact: mem_behead.
elim: s => [|x s IHs]; rewr filter // => eq_a.
rewrite eq_a ?mem_head ?IHs // => y s_y.
by apply: eq_a; rewrite mem_behead; rewr behead.
Qed.

Lemma eq_has_r s1 s2 : `(!x. x <- s1 <=> x <- s2) ==> (!a. has a s1 <=> has a s2)`.
--move=> Es12 a; apply/(hasP a s1)/(hasP a s2) => [] [x Hx Hax];
-- by exists x; rewrite // ?Es12 // -Es12.
move => Es12 a.
split; rewrite -!hasP => [] [x [Hx Hax]].
  by exists x; rewrite -Es12.
by exists x; rewrite Es12.
Qed.

Lemma eq_all_r s1 s2 : `(!x. x <- s1 <=> x <- s2) ==> (!a. all a s1 = all a s2)`.
--by move=> Es12 a; apply/(allP a s1)/(allP a s2) => Hs x Hx;
--  apply: Hs; rewrite Es12 in Hx *.
move => Es12 a; rewrite -!allP; split => Hs x Hx.
  by apply: Hs; rewrite Es12.
by apply: Hs; rewrite -Es12.
Qed.

Lemma has_sym s1 s2 : `has (\x. x <- s1) s2 = has (\x. x <- s2) s1`.
--Proof. by apply/(hasP _ s2)/(hasP _ s1) => [] [x]; exists x. Qed.
by rewrite -!hasP /= andbC. Qed.

Lemma has_pred1 x s : `has (pred1 x) s <=> x <- s`.
--Proof. by rewrite -(eq_has (mem_seq1^~ x)) (has_sym [:: x]) /= orbF. Qed.
rewrite -hasP pred1 /=; split => [[y [ys <-]] // | xs].
by exists x.
Qed.

(* Constant sequences, i.e., the image of nseq. *)

--Definition constant s := if s is x :: s' then all (pred1 x) s' else true.
"let constant = define `constant [] = T /\ constant (CONS x s') = all (pred1 x) s'`".

Lemma all_pred1P x s : `(s = nseq (sizel s) x) <=> (all (pred1 x) s)`.
--elim: s => [|y s IHs] /=; first by left.
--case: eqP => [->{y} | ne_xy]; last by right=> [] [? _]; case ne_xy.
--by apply: (iffP IHs) => [<- //| []].
elim: s => [| y s IHs]; rewr nseq ncons size_nil size_cons iter all // eqseq_cons.
case: (EXCLUDED_MIDDLE `x = y`) => [<- | ne_xy]; last first.
  by rewrite pred1 /=; rewr ne_xy andFb.
by rewrite {1}pred1 /= -IHs nseq ncons.
Qed.

Lemma all_pred1_constant x s : `all (pred1 x) s ==> constant s`.
--Proof. by case: s => //= y s /andP[/eqP->]. Qed.
by elim: s; rewr constant all pred1 /=. Qed.

Lemma all_pred1_nseq x y n : `all (pred1 x) (nseq n y) <=> (n = 0 \/ x = y)`.
--case: n => //= n; rewrite eq_sym; apply: andb_idr => /eqP->{x}.
--by elim: n => //= n ->; rewrite eqxx.
elim: n => [|n _]; rewr pred1 nseq !ncons iter all //=.
rewrite [`y = x`]eq_sym eqS0 orFb; apply: andb_idr => ->.
by elim: n => [|n IHn]; rewr iter all /=.
Qed.

Lemma constant_nseq n x : `constant (nseq n x)`.
--Proof. by case: n => //= n; rewrite all_pred1_nseq eqxx orbT. Qed.
elim: n => [|n _]; rewr nseq ncons iter constant //.
by rewrite -ncons -nseq all_pred1_nseq.
Qed.

(* Uses x0 *)
Lemma constantP s : `(?x. s = nseq (sizel s) x) <=> (constant s)`.
--apply: (iffP idP) => [| [x ->]]; last exact: constant_nseq.
--case: s => [|x s] /=; first by exists x0.
--by move/all_pred1P=> def_s; exists x; rewrite -def_s.
split => [[x ->]|]; first by rewrite constant_nseq.
elim: s => [|x s _]; rewr constant /=; first by "EXISTS_TAC `x0:A`"; rewr nseq ncons size_nil iter.
rewrite -all_pred1P => def_s; exists x.
by rewrite {1}def_s; rewr nseq ncons size_cons iter.
Qed.


(* Duplicate-freenes. *)

--Fixpoint uniq s := if s is x :: s' then (x \notin s') && uniq s' else true.
"let uniq = define `uniq [] = T /\ (uniq (x :: s') <=> ~(MEM x s') /\ uniq s')`".

Lemma nil_uniq : `uniq ([]:(A)list)`. by rewr uniq. Qed.

Lemma cons_uniq x s : `uniq (x :: s) <=> ~(x <- s) /\ uniq s`.
Proof. by rewr uniq. Qed.

Lemma cat_uniq s1 s2 :
  `uniq (s1 ++ s2) <=> uniq s1 /\ ~ has (\x. x <- s1) s2 /\ uniq s2`.
--elim: s1 => [|x s1 IHs]; first by rewrite /= has_pred0.
--by rewrite has_sym /= mem_cat !negb_or has_sym IHs -!andbA; do !bool_congr.
elim: s1 => [|x s1 IHs]; first by rewrite in_nil -pred0 has_pred0 cat0s nil_uniq.
rewrite has_sym cat_cons cons_uniq mem_cat has_cons !negb_or has_sym IHs cons_uniq !andbA /=.
by rewrite [`_ /\ uniq s1`]andbAC.
Qed.

Lemma uniq_catC s1 s2 : `uniq (s1 ++ s2) = uniq (s2 ++ s1)`.
Proof. by rewrite !cat_uniq has_sym andbCA andbA andbC. Qed.

Lemma uniq_catCA s1 s2 s3 : `uniq (s1 ++ s2 ++ s3) = uniq (s2 ++ s1 ++ s3)`.
--by rewrite !catA -!(uniq_catC s3) !(cat_uniq s3) uniq_catC !has_cat orbC.
rewrite !catA.
by rewrite -![`uniq (cat _ s3)`]uniq_catC ![`uniq (cat s3 _)`]cat_uniq uniq_catC !has_cat orbC.
Qed.

Lemma rcons_uniq s x : `uniq (rcons s x) <=> (~(x <- s) /\ uniq s)`.
by rewrite -cats1 uniq_catC cat_cons cons_uniq cat0s. Qed.
--Proof. by rewrite -cats1 uniq_catC. Qed.

Lemma filter_uniq s a : `uniq s ==> uniq (filter a s)`.
--elim: s => [|x s IHs] //= /andP[Hx Hs]; case (a x); auto.
--by rewrite /= mem_filter /= (negbTE Hx) andbF; auto.
elim: s => [|x s IHs]; rewr filter uniq //.
case: (EXCLUDED_MIDDLE `a x`) => [-> /= | nax]; move => [Hx Hs]; last first.
  by rewr nax /=; exact: IHs.
by rewr uniq; rewrite mem_filter (negbTE Hx) andbF IHs.
Qed.

Lemma rot_uniq s : `uniq (rot n0 s) = uniq s`.
Proof. by rewrite rot uniq_catC cat_take_drop. Qed.

Lemma rev_uniq s : `uniq (rev s) = uniq s`.
--elim: s => // x s IHs.
elim:s => [| x s IHs]; first by rewr rev catrev //.
by rewrite rev_cons -cats1 cat_uniq !cons_uniq has_cons in_nil nil_uniq has_nil negb_or /= andbC IHs mem_rev.
Qed.

Lemma count_uniq_mem s x : `uniq s ==> count (pred1 x) s = if (x <- s) then 1 else 0`.
--elim: s => //= [y s IHs] /andP[/negbTE Hy /IHs-> {IHs}].
--by rewrite in_cons eq_sym; case: eqP => // ->; rewrite Hy.
elim: s => [|y s IHs]; rewr count in_nil /=.
rewrite in_cons cons_uniq => [] [Hy]; move/IHs => ->.
rewrite pred1 /= [`y = x`]eq_sym.
case: (EXCLUDED_MIDDLE `x = y`) => [-> /=| ]; rewr Hy /= addn0 //.
by rewrite add0n.
Qed.

(* Removing duplicates *)

--Fixpoint undup s :=
--  if s is x :: s' then if x \in s' then undup s' else x :: undup s' else [::].
"let undup = define `undup [] = [] /\ 
	undup (x :: s') = if x <- s' then undup s' else x :: undup s'`".

Lemma size_undup s : `sizel (undup s) <= sizel s`.
--Proof. by elim: s => //= x s IHs; case: (x \in s) => //=; exact: ltnW. Qed.
elim: s => [|x s IHs]; rewr undup leqnn //.
by case: (EXCLUDED_MIDDLE `x <- s`) => /=; rewrite !size_cons ?leqSS // ltnW // ltE leqSS.
Qed.

Lemma mem_undup s : `!x. x <- undup s <=> x <- s`.
--move=> x; elim: s => //= y s IHs.
--by case Hy: (y \in s); rewrite in_cons IHs //; case: eqP => // ->.
move => x; elim: s => [|y s IHs]; rewr undup //.
case: (EXCLUDED_MIDDLE `y <- s`) => /= Hy; rewrite in_cons IHs; rewr MEM //.
by case: (EXCLUDED_MIDDLE `x = y`) => /=.
Qed.

Lemma undup_uniq s : `uniq (undup s)`.
--by elim: s => //= x s IHs; case s_x: (x \in s); rewrite //= mem_undup s_x.
elim: s => [|x s IHs]; rewr undup uniq //.
by case: (EXCLUDED_MIDDLE `x <- s`); rewrite //= cons_uniq mem_undup /=.
Qed.

Lemma undup_id s : `uniq s ==> undup s = s`.
--Proof. by elim: s => //= x s IHs /andP[/negbTE-> /IHs->]. Qed.
elim: s => [|x s IHs]; rewr undup uniq //= => [] [Hx Hs].
by rewrite IHs.
Qed.

Lemma ltn_size_undup s : `(sizel (undup s) < sizel s) <=> ~ uniq s`.
--by elim: s => //= x s IHs; case Hx: (x \in s); rewrite //= ltnS size_undup.
elim: s => [|x s IHs]; rewr undup uniq ltnn //.
by case: (EXCLUDED_MIDDLE `x <- s`); rewrite //= !size_cons ?ltSS // ltnS size_undup.
Qed.

(* Lookup *)

--Definition index x := find (pred1 x).
"let index = new_definition `indexl x = find (pred1 x)`".

Lemma index_size x s : `indexl x s <= sizel s`.
Proof. by rewrite index find_size. Qed.

Lemma index_mem x s : `(indexl x s < sizel s) <=> (x <- s)`.
by rewrite -has_pred1 index has_find. Qed.

Lemma nth_index x s : `x <- s ==> nth x0 s (indexl x s) = x`.
--Proof. by rewrite -has_pred1 => /(nth_find x0)/eqP. Qed.
by rewrite -has_pred1; move/(nth_find x0); rewrite index pred1 /=. Qed.

Lemma index_cat x s1 s2 :
 `indexl x (s1 ++ s2) = if x <- s1 then indexl x s1 else sizel s1 + indexl x s2`.
Proof. by rewrite index find_cat has_pred1. Qed.

Lemma index_uniq i s : `i < sizel s ==> uniq s ==> indexl (nth x0 s i) s = i`.
--elim: s i => [|x s IHs] //= [|i]; rewrite /= ?eqxx // ltnS => lt_i_s.
--case/andP=> not_s_x /(IHs i)-> {IHs}//.
--by case: eqP not_s_x => // ->; rewrite mem_nth.
elim: s i => [|x s IHs]; rewr size_nil ltn0 //; elim => [|i _].
  by rewr nth index find pred1 /=.
rewrite size_cons ltnS -ltE cons_uniq => lt_i_s [not_s_x].
move/(IHs i lt_i_s); rewr nth index find pred1 => -> /=.
case: (EXCLUDED_MIDDLE `x = nth x0 s i`) => /= x_eq.
by have := mem_nth lt_i_s; rewrite -x_eq (negbTE not_s_x).
Qed.

Lemma index_head x s : `indexl x (x :: s) = 0`.
Proof. by rewr index find pred1 /=. Qed.

Lemma index_last x s : `uniq (x :: s) ==> indexl (last x s) (x :: s) = sizel s`.
rewrite lastI rcons_uniq -cats1 index_cat size_belast.
--by case: ifP => //=; rewrite eqxx addn0.
case: (EXCLUDED_MIDDLE `last x s <- belast x s`) => /=.
by rewr index find pred1 /= addn0.
Qed.

Lemma nth_uniq s i j :
  `i < sizel s ==> j < sizel s ==> uniq s ==> (nth x0 s i = nth x0 s j) = (i = j)`.
--move=> lt_i_s lt_j_s Us; apply/eqP/eqP=> [eq_sij|-> //].
--by rewrite -(index_uniq lt_i_s Us) eq_sij index_uniq.
move => lt_i_s lt_j_s Us; split => [eq_sij| -> //].
by rewrite -(index_uniq lt_i_s Us) eq_sij index_uniq.
Qed.

Lemma mem_rot s : `!x. x <- rot n0 s <=> x <- s`.
--Proof. by move=> x; rewrite -{2}(cat_take_drop n0 s) !mem_cat /= orbC. Qed.
by move => x; rewrite -{2}[`s`](cat_take_drop n0 s) rot !mem_cat orbC. Qed.

Lemma eqseq_rot s1 s2 : `(rot n0 s1 = rot n0 s2) <=> (s1 = s2)`.
--Proof. by apply: inj_eq; exact: rot_inj. Qed.
by split => [| -> //]; move/rot_inj. Qed.

--CoInductive rot_to_spec s x := RotToSpec i s' of rot i s = x :: s'.
--x \in s -> rot_to_spec s x.

Lemma rot_to s x : `x <- s ==> ?i s'. rot i s = x :: s'`.
--move=> s_x; pose i := index x s; exists i (drop i.+1 s ++ take i s).
--rewrite -cat_cons {}/i; congr cat; elim: s s_x => //= y s IHs.
--by rewrite eq_sym in_cons; case: eqP => // -> _; rewrite drop0.
move => s_x; set i := `indexl (x:A) s`.
exists i `dropl (SUC i) s ++ take i s`.
rewrite -cat_cons rot -i_def; set r := `take _1 _2`.
move: i_def r_def => _ _.
elim: s s_x => [|y s IHs]; rewrite ?in_nil //.
rewrite in_cons; case: (EXCLUDED_MIDDLE `x = y`) => /=.
  rewrite index_head drop0 drop_cons drop0 //.
by rewr index find pred1 /= -pred1 -index drop_cons => _; move/IHs => ->.
Qed.


End EqSeq.

--Definition inE := (mem_seq1, in_cons, inE).

--Prenex Implicits mem_seq1 uniq undup index.

--Implicit Arguments eqseqP [T x y].
--Implicit Arguments hasP [T a s].
--Implicit Arguments hasPn [T a s].
--Implicit Arguments allP [T a s].
--Implicit Arguments allPn [T a s].
--Prenex Implicits eqseqP hasP hasPn allP allPn.

Section NseqthTheory.

Implicit Type s : `:(A)list`.

Lemma nthP s x x0 :
  `(?i. i < sizel s /\ nth x0 s i = x) <=> (x <- s)`.
--apply: (iffP idP) => [|[n Hn <-]]; last by apply mem_nth.
--by exists (index x s); [rewrite index_mem | apply nth_index].
split => [[n [Hn <-]] | Hx]; first by apply: mem_nth.
by exists `indexl x s`; rewrite index_mem Hx andTb; apply: nth_index.
Qed.

Lemma has_nthP a s x0 :
  `(?i. i < sizel s /\ a (nth x0 s i)) <=> (has a s)`.
--elim: s => [|x s IHs] /=; first by right; case.
--case nax: (a x); first by left; exists 0.
--by apply: (iffP IHs) => [[i]|[[|i]]]; [exists i.+1 | rewrite nax | exists i].
elim: s => [|x s IHs]; rewr has !size_nil ltn0 andFb //.
case: (EXCLUDED_MIDDLE `a x`) => /= ax.
  by exists `0`; rewr nth size_cons ltn0Sn.
rewrite -IHs; split => [[] | [i]]; last first.
  by move => [i_s anth]; exists `SUC i`; rewr nth size_cons ltSS.
elim => [|i _]; rewr nth; first by rewr ax.
by rewrite size_cons ltSS => [] [i_s anth]; exists i.
Qed.

Lemma all_nthP a s x0 :
  `(!i. i < sizel s ==> a (nth x0 s i)) <=> (all a s)`.
--rewrite -(eq_all (fun x => negbK (a x))) all_predC.
--case: (has_nthP _ _ x0) => [na_s | a_s]; [right=> a_s | left=> i lti].
--  by case: na_s => i lti; rewrite a_s.
--by apply/idPn=> na_si; case: a_s; exists i.
elim: s => [|x s IHs]; rewr size_nil all !ltn0 //.
case: (EXCLUDED_MIDDLE `a x`) => /= ax; last first.
  by rewrite NOT_FORALL_THM; exists `0`; rewrite size_cons ltn0Sn; rewr !nth.
rewrite -IHs; split => IH i i_s.
  by move: (IH `SUC i`); rewrite size_cons ltSS; rewr nth; exact.
elim: i i_s => [|i _]; rewr nth //.
by rewrite size_cons ltSS; apply: IH.
Qed.


End NseqthTheory.

Lemma set_nth_default s y0 x0 n : `n < sizel s ==> nth (x0:A) s n = nth y0 s n`.
--Proof. by elim: s n => [|y s' IHs] [|n] /=; auto. Qed.
elim: s n => [|y s' IHs]; elim => [|n _]; rewr nth size_nil ltnn ltn0 //.
by rewrite size_cons ltSS; move/IHs.
Qed.

Lemma headI s x : `rcons s x = headl x s :: behead (rcons s (x:A))`.
by elim: s => [|s x _]; rewr rcons head behead. Qed.

--Implicit Arguments nthP [T s x].
--Implicit Arguments has_nthP [T a s].
--Implicit Arguments all_nthP [T a s].
--Prenex Implicits nthP has_nthP all_nthP.

--Definition bitseq := seq bool.
--Canonical bitseq_eqType := Eval hnf in [eqType of bitseq].
--Canonical bitseq_predType := Eval hnf in [predType of bitseq].

(* Incrementing the ith nat in a seq nat, padding with 0's if needed. This  *)
(* allows us to use nat seqs as bags of nats.                               *)

--Fixpoint incr_nth v i {struct i} :=
--  if v is n :: v' then if i is i'.+1 then n :: incr_nth v' i' else n.+1 :: v'
--  else ncons i 0 [:: 1].
"let incr_nth = define `incr_nth (n :: v') (SUC i) = n :: incr_nth v' i /\
	incr_nth (n :: v') 0 = SUC n :: v' /\
	incr_nth [] i = ncons i 0 [1]`".

Lemma nth_incr_nth v i j : `nth 0 (incr_nth v i) j = (if (i = j) then 1 else 0) + nth 0 v j`. 
--elim: v i j => [|n v IHv] [|i] [|j] //=; rewrite ?eqSS ?addn0 //; try by case j.
--elim: i j => [|i IHv] [|j] //=; rewrite ?eqSS //; by case j.
elim: v i j => [|n v IHv]; elim => [|i _]; elim => [|j _];
  rewr incr_nth nth ncons iter !nth addn0 // eqS0 /= add0n add1n //.
  arith.
  elim: i j => [|i IHv]; elim => [|j _]; rewr iter !nth //.
    arith. arith.
  by rewrite IHv !eqSS.
  by rewrite [`0 = SUC j`]eq_sym eqS0 /= add0n.
by rewrite IHv eqSS.
Qed.


Lemma size_incr_nth v i :
  `sizel (incr_nth v i) = if i < sizel v then sizel v else SUC i`.
--elim: v i => [|n v IHv] [|i] //=; first by rewrite size_ncons /= addn1.
--rewrite IHv; exact: fun_if.
elim: v i => [|n v IHv]; elim => [|i _];
	rewr incr_nth size_ncons size_nil ltnn size_cons size_nil add0n // ltS0 /=.
  by rewrite -ONE addn1.
  by rewrite ltn0Sn.
by rewrite IHv ltSS [`SUC _`]fun_if.
Qed.


(* equality up to permutation *)

Section PermSeq.

Implicit Type s s1 : `:(A)list`.

--Definition same_count1 s1 s2 x := count (pred1 x) s1 == count (pred1 x) s2.
--Definition perm_eq s1 s2 := all (same_count1 s1 s2) (s1 ++ s2).

"let same_count1 = new_definition `same_count1 s1 s2 x <=> (count (pred1 x) s1 = count (pred1 x) s2)`".
"let perm_eq = new_definition `perm_eq s1 s2 = all (same_count1 s1 s2) (s1 ++ s2)`".
"let predD = new_definition `predD p1 p2 = predI (predC p2) p1`".
"let predD1 = new_definition `predD1 a x = predD a (pred1 x)`".

Lemma perm_eqP s1 s2 : `perm_eq s1 s2 <=> (!a. count a s1 = count a s2)`.
--reflect (count^~ s1 =1 count^~ s2) (perm_eq s1 s2).
--Proof.
--apply: (iffP allP) => [eq_cnt1 a | eq_cnt x _]; last exact/eqP.
--elim: {a}_.+1 {-2}a (ltnSn (count a (s1 ++ s2))) => // n IHn a le_an.
--case: (posnP (count a (s1 ++ s2))).
--  by move/eqP; rewrite count_cat addn_eq0; do 2!case: eqP => // ->.
--rewrite -has_count => /hasP[x s12x a_x]; pose a' := predD1 a x.
--have cnt_a' s : count a s = count (pred1 x) s + count a' s.
  --rewrite count_filter -(count_predC (pred1 x)) 2!count_filter.
  --rewrite -!filter_predI -!count_filter; congr (_ + _).
--  by apply: eq_count => y /=; case: eqP => // ->.
--rewrite !cnt_a' (eqnP (eq_cnt1 _ s12x)) (IHn a') // -ltnS.
--apply: leq_trans le_an.
--by rewrite ltnS cnt_a' -add1n leq_add2r -has_count has_pred1.

rewrite perm_eq -allP same_count1; split => [eq_cnt1 a | eq_cnt x _]; last exact.
elim: `SUC _` {1 3 4}a (ltnSn `count a (s1 ++ s2)`); rewrite ?ltn0 // => n IHn a le_an.
case: (posnP `count a (s1 ++ s2)`).
  by rewrite count_cat addn_eq0 => [] [] -> ->.
rewrite -has_count -hasP => [] [x] [s12x a_x]; set a' := `predD1 a x`.
have cnt_a' : `!s. count a s = count (pred1 x) s + count a' s`.
  move => s.
  rewrite count_filter -(count_predC `pred1 x`) 2!count_filter.
  rewrite -!filter_predI -!count_filter -predD -predD1 a'_def eqn_addr.
  by apply: eq_count s => y; rewrite predI pred1 /=; split => [[-> //] | -> ].
rewrite !cnt_a' (eq_cnt1 s12x) (IHn a') // ltE -ltnS.
move: le_an; rewrite !ltE; apply: leq_trans.
by rewrite -ltE ltnS cnt_a' -add1n leq_add2r ONE -ltE -has_count has_pred1.
Qed.

Lemma perm_eq_refl s : `perm_eq s s`.
--Proof. exact/perm_eqP. Qed.
by rewrite perm_eqP. Qed.

--Hint Resolve perm_eq_refl.

Lemma perm_eq_sym : `!s1 s2. perm_eq s1 s2 = perm_eq s2 s1`.
--Proof. by move=> s1 s2; apply/perm_eqP/perm_eqP=> ? ?. Qed.
by move => s1 s2; rewrite !perm_eqP [`!a. _ a`]eq_sym. Qed.

Lemma perm_eq_trans : `!s2 s1 s3. perm_eq s1 s2 ==> perm_eq s2 s3 ==> perm_eq s1 s3`.
--transitive perm_eq.
--move=> s2 s1 s3; move/perm_eqP=> eq12; move/perm_eqP=> eq23.
--by apply/perm_eqP=> a; rewrite eq12.
move => s2 s1 s3; rewrite !perm_eqP => eq12 eq23 a.
by rewrite eq12 eq23.
Qed.

--Notation perm_eql s1 s2 := (perm_eq s1 =1 perm_eq s2).
--Notation perm_eqr s1 s2 := (perm_eq^~ s1 =1 perm_eq^~ s2).

Lemma perm_eqlP s1 s2 : 
  `perm_eq s1 s2 <=> (!s. perm_eq s1 s = perm_eq s2 s)`.
--apply: (iffP idP) => [eq12 s3 | -> //].
--apply/idP/idP; last exact: perm_eq_trans.
--by rewrite -!(perm_eq_sym s3); move/perm_eq_trans; apply.
split => [eq12 s3 | -> ]; last by rewrite perm_eq_refl.
split; last exact: perm_eq_trans.
by rewrite -![`perm_eq _ s3`](perm_eq_sym s3); move/perm_eq_trans; apply.
Qed.

Lemma perm_eqrP s1 s2 : `perm_eq s1 s2 <=> (!s. perm_eq s s1 = perm_eq s s2)`.
split => [| <-]; last by rewrite perm_eq_refl.
rewrite perm_eqlP => eq12 s3.
by rewrite ![`perm_eq s3 _`](perm_eq_sym s3) eq12.
Qed.

Lemma perm_catC s1 s2 : `!s. perm_eq (s1 ++ s2) s = perm_eq (s2 ++ s1) s`.
--Proof. by apply/perm_eqlP; apply/perm_eqP=> a; rewrite !count_cat addnC. Qed.
by rewrite -perm_eqlP perm_eqP => a; rewrite !count_cat addnC. Qed.

Lemma perm_cat2l s1 s2 s3 : `perm_eq (s1 ++ s2) (s1 ++ s3) = perm_eq s2 s3`.
Proof.
--apply/perm_eqP/perm_eqP=> eq23 a; apply/eqP;
--  by move/(_ a)/eqP: eq23; rewrite !count_cat eqn_addl.
rewrite !perm_eqP; split => eq23 a.
  by move: (eq23 a); rewrite !count_cat eqn_addl.
by move: (eq23 a); rewrite !count_cat eqn_addl.
Qed.


Lemma perm_cons x s1 s2 : `perm_eq (x :: s1) (x :: s2) = perm_eq s1 s2`.
--Proof. exact: (perm_cat2l [::x]). Qed.
by move: (perm_cat2l `[x]`); rewrite !cat_cons !cat0s => ->. Qed.

Lemma perm_cat2r s1 s2 s3 : `perm_eq (s2 ++ s1) (s3 ++ s1) = perm_eq s2 s3`.
--Proof. by do 2!rewrite perm_eq_sym perm_catC; exact: perm_cat2l. Qed.
by do 2!rewrite perm_eq_sym perm_catC; rewrite perm_cat2l. Qed.

Lemma perm_catAC s1 s2 s3 : `!s. perm_eq ((s1 ++ s2) ++ s3) s = perm_eq ((s1 ++ s3) ++ s2) s`.
Proof. by rewrite -perm_eqlP -!catA perm_cat2l perm_catC perm_eq_refl. Qed.

Lemma perm_catCA s1 s2 s3 : `!s. perm_eq (s1 ++ s2 ++ s3) s = perm_eq (s2 ++ s1 ++ s3) s`.
Proof. by rewrite -perm_eqlP !catA perm_cat2r perm_catC perm_eq_refl. Qed.

Lemma perm_rcons x s : `!s2. perm_eq (rcons s x) s2 = perm_eq (x :: s) s2`.
--Proof. by move=> /= s2; rewrite -cats1 perm_catC. Qed.
by move => s2; rewrite -cats1 perm_catC cat1s. Qed.

Lemma perm_rot n s : `!s2. perm_eq (rot n s) s2 = perm_eq s s2`.
Proof. by move=> s2; rewrite rot perm_catC cat_take_drop. Qed.

Lemma perm_rotr n s : `!s2. perm_eq (rotr n s) s2 = perm_eq s s2`.
--Proof. exact: perm_rot. Qed.
by rewrite rotr perm_rot. Qed.

Lemma perm_filterC a s : `!s2. perm_eq (filter a s ++ filter (predC a) s) s2 = perm_eq s s2`.
--apply/perm_eqlP; elim: s => //= x s IHs.
--by case: (a x); last rewrite /= -cat1s perm_catCA; rewrite perm_cons.
rewrite -perm_eqlP; elim: s => [|x s IHs]; rewr filter cat perm_eq_refl //.
rewrite predC /=.
(* FIXME: implement rewrite which works with negations *)
(* move: `a x`. *)
set r := `a x`.
by case: r r_def => -> _ /=; 
	last rewrite -cat1s perm_catCA; rewrite cat_cons perm_cons -predC ?cat0s.
Qed.

Lemma perm_eq_mem s1 s2 : `perm_eq s1 s2 ==> (!x. x <- s1 <=> x <- s2)`.
--Proof. by move/perm_eqP=> eq12 x; rewrite -!has_pred1 !has_count eq12. Qed.
rewrite perm_eqP => eq12 x; rewrite -!has_pred1 !has_count.
by rewrite eq12.
Qed.

Lemma perm_eq_size s1 s2 : `perm_eq s1 s2 ==> sizel s1 = sizel s2`.
--Proof. by move/perm_eqP=> eq12; rewrite -!count_predT eq12. Qed.
rewrite perm_eqP => eq12.
by rewrite -!count_predT eq12. Qed.

Lemma uniq_leq_size s1 s2 : `uniq s1 ==> (!x. x <- s1 ==> x <- s2) ==> sizel s1 <= sizel s2`.
--elim: s1 => [|x s1 IHs] /= in s2 *; [by case: s2 | case/andP=> Hx Hs1 Hs12].
--have [|i s2' Ds2'] := @rot_to T s2 x; first exact/Hs12/predU1l.
--rewrite -(size_rot i s2) (Ds2'); apply: IHs => // [y /= Hy].
--move: (Hs12 _ (predU1r _ _ Hy)); rewrite /= -(mem_rot i) Ds2'.
--by case/predU1P=> // Dy; rewrite -Dy Hy in Hx.
elim: s1 s2 => [|x s1 IHs]; [by rewrite size_nil leq0n | rewrite cons_uniq => _ [Hx Hs1 Hs12]].
move: (Hs12 x); rewrite mem_head /= => Hxs2.
move: (rot_to Hxs2) => [i] [s2' Ds2'].
rewrite -[`sizel s2`](size_rot i s2) Ds2' !size_cons leqSS IHs Hs1 andTb => y Hy.
move: (Hs12 y); rewrite in_cons Hy /= -(mem_rot i) Ds2' in_cons.
case => // yx; move: Hx Hy.
by rewrite yx /=.
Qed.

Lemma leq_size_uniq s1 s2 :
  `uniq s1 ==> (!x. x <- s1 ==> x <- s2) ==> sizel s2 <= sizel s1 ==> uniq s2`.
--elim: s1 s2 => [|x s1 IHs] s2 Hs1 Hs12; first by case s2.
--case: (@rot_to T s2 x); [ by apply: Hs12; apply: predU1l | move=> i s2' Ds2' ].
--  rewrite -(size_rot i) -(rot_uniq i) Ds2' /=; case Hs2': (x \in s2').
--  rewrite ltnNge /=; case/negP; apply: (uniq_leq_size Hs1) => [y Hy].
--  by move: (Hs12 _ Hy); rewrite /= -(mem_rot i) Ds2'; case/predU1P=> // ->.
--move: Hs1 => /=; case/andP=> Hx Hs1; apply: IHs => // [y /= Hy].
--have:= Hs12 _ (predU1r _ _ Hy); rewrite /= -(mem_rot i) Ds2'.
--by case/predU1P=> // Dx; rewrite -Dx Hy in Hx.
elim: s1 s2 => [s2 Hs1 Hs12 |x s1 IHs s2 Hs1 Hs12].
  by elim: s2 => [|y s _]; rewrite ?nil_uniq // size_cons size_nil -ltE ltn0.
move: (Hs12 x); rewrite mem_head /= => Hxs2.
move: (rot_to Hxs2) => [i] [s2' Ds2'].
rewrite -(size_rot i) -(rot_uniq i) Ds2'; case: (EXCLUDED_MIDDLE `x <- s2'`) => Hs2'.
  rewrite !size_cons -ltE ltnNge cons_uniq Hs2' /= -(size_cons x).
  apply: (uniq_leq_size Hs1) => [y Hy].
  by move: (Hs12 Hy); rewrite -(mem_rot i) Ds2' in_cons; case => // ->.
move: Hs1; rewrite !cons_uniq => [] [Hx Hs1]; rewr Hs2' /= size_cons leqSS.
apply: (IHs Hs1) => [y Hy].
have := Hs12 y; rewrite in_cons Hy /= -(mem_rot i) Ds2' in_cons; case => // yx.
by move: Hy Hx; rewrite yx /=.
Qed.


Lemma uniq_size_uniq s1 s2 :
  `uniq s1 ==> (!x. x <- s1 <=> x <- s2) ==> (uniq s2 = (sizel s2 = sizel s1))`.
Proof.
move=> Us1 Es12.
--rewrite eqn_leq andbC uniq_leq_size //= => [|y]; last by rewrite /= Es12.
--apply/idP/idP => [Hs2|]; first by apply uniq_leq_size => // y; rewrite /= Es12.
--by apply: leq_size_uniq => // y; rewrite /= Es12.
rewrite eqn_leq andbC uniq_leq_size ?Us1 ?Es12 //=.
split => [Hs2|]; first by rewrite uniq_leq_size Es12 /=.
by apply: (leq_size_uniq Us1) => y; rewrite Es12.
Qed.

Lemma leq_size_perm s1 s2 :
    `uniq s1 ==> (!x. x <- s1 ==> x <- s2) ==> sizel s2 <= sizel s1 ==>
  (!x. x <- s1 <=> x <- s2) /\ sizel s1 = sizel s2`.
Proof.
move=> Us1 Hs1 Hs12; have Us2: `uniq s2`.
  by rewrite (leq_size_uniq Us1).
suff: `!x. x <- s1 <=> x <- s2`.
  by move => h; split => //; rewrite -uniq_size_uniq.
move=> x.
--apply/idP/idP=> [|Hxs2]; [exact: Hs1 | apply/idPn=> Hxs1].
split => [|Hxs2]; [by apply: Hs1 | case: (EXCLUDED_MIDDLE `x <- s1`) => // Hxs1].
--suffices: size (x :: s1) <= size s2 by rewrite /= ltnNge Hs12.
--apply: uniq_leq_size => [|y] /=; first by rewrite Hxs1.
--case/predU1P=> [-> //|]; exact: Hs1.
suff: `sizel (x :: s1) <= sizel s2`.
  by rewrite size_cons -ltE ltnNge Hs12.
rewrite uniq_leq_size; split => [|y]; first by rewrite cons_uniq.
by rewrite in_cons; case => [-> //| Hy]; exact: Hs1.
Qed.


Lemma perm_uniq s1 s2 : `(!x. x <- s1 <=> x <- s2) ==> 
	sizel s1 = sizel s2 ==> uniq s1 = uniq s2`.
--by move=> Es12 Hs12; apply/idP/idP => Us;
--  rewrite (uniq_size_uniq Us) ?Hs12 ?eqxx.
move => Es12 Hs12; split => Us.
  by rewrite (uniq_size_uniq Us) ?Hs12.
by rewrite (uniq_size_uniq Us) ?Hs12.
Qed.

Lemma perm_eq_uniq s1 s2 : `perm_eq s1 s2 ==> uniq s1 = uniq s2`.
--move=> eq_s12; apply: perm_uniq; [exact: perm_eq_mem | exact: perm_eq_size].
move => eq_s12; rewrite (perm_uniq s1 s2) //; split; [exact: perm_eq_mem | exact: perm_eq_size].
Qed.

Lemma uniq_perm_eq s1 s2 : `uniq s1 ==> uniq s2 ==> 
	(!x. x <- s1 <=> x <- s2) ==> perm_eq s1 s2`.
--move=> Us1 Us2 eq12; apply/allP=> x _; apply/eqP.
move => Us1 Us2 eq12; rewrite perm_eq -allP same_count1 => x _.
by rewrite !count_uniq_mem ?eq12.
Qed.

Lemma count_mem_uniq s : `(!x. count (pred1 x) s = if (x <- s) then 1 else 0) ==> uniq s`.
Proof.
move=> count1_s; have Uus := undup_uniq s.
suff: `perm_eq s (undup s)`; first by move/perm_eq_uniq => ->.
--by apply/allP=> x _; apply/eqP; rewrite (count_uniq_mem x Uus) mem_undup.
rewrite perm_eq -allP same_count1 => x _.
by rewrite (count_uniq_mem s x Uus) mem_undup.
Qed.

End PermSeq.

--Notation perm_eql s1 s2 := (perm_eq s1 =1 perm_eq s2).
--Notation perm_eqr s1 s2 := (perm_eq^~ s1 =1 perm_eq^~ s2).

--Implicit Arguments perm_eqP [T s1 s2].
--Implicit Arguments perm_eqlP [T s1 s2].
--Implicit Arguments perm_eqrP [T s1 s2].
--Prenex Implicits perm_eq perm_eqP perm_eqlP perm_eqrP.
--Hint Resolve perm_eq_refl.

Section RotrLemmas.

--Variables (n0 : nat) (T : Type) (T' : eqType).
--Implicit Type s : seq T.
Variable n0 : `:num`.
Implicit Type s : `:(A)list`.


Lemma size_rotr s : `sizel (rotr n0 s) = sizel s`.
by rewrite rotr size_rot. Qed.

Lemma mem_rotr s : `!x. x <- rotr n0 s <=> x <- s`.
Proof. by move => x; rewrite rotr mem_rot. Qed.

Lemma rotr_size_cat s1 s2 : `rotr (sizel s2) (s1 ++ s2) = s2 ++ s1`.
Proof. by rewrite rotr size_cat addnK rot_size_cat. Qed.

Lemma rotr1_rcons x s : `rotr 1 (rcons s x) = x :: s`.
Proof. by rewrite -rot1_cons rotK. Qed.

Lemma has_rotr a s : `has a (rotr n0 s) = has a s`.
Proof. by rewrite rotr has_rot. Qed.

Lemma rotr_uniq s : `uniq (rotr n0 s) = uniq s`.
Proof. by rewrite rotr rot_uniq. Qed.

Lemma rotrK : `!s. rot n0 (rotr n0 s) = s`.
Proof.
--move=> s; have [lt_n0s | ge_n0s] := ltnP n0 (size s).
move => s.
have [] [lt_n0s | ge_n0s] := ltnP n0 `sizel s`.
--  by rewrite -{1}(subKn (ltnW lt_n0s)) -{1}[size s]size_rotr; exact: rotK.
  by rewrite -{1}(subKn (ltnW lt_n0s)) -{1}[`sizel s`]size_rotr -rotr [`rotr n0 _`]rotr rotK.
--by rewrite -{2}(rot_oversize ge_n0s) /rotr (eqnP ge_n0s) rot0.
rewrite -{2}(rot_oversize ge_n0s) rotr.
by move: (subn_eq0 `sizel s` n0); rewrite ge_n0s /= rot0.
Qed.

Lemma rotr_inj s1 s2: `rotr n0 (s1:(A)list) = rotr n0 s2 ==> s1 = s2`.
--Proof. exact (can_inj rotrK). Qed.
move => h.
by rewrite -rotrK h rotrK.
Qed.

Lemma rev_rot s : `rev (rot n0 s) = rotr n0 (rev s)`.
Proof.
--rewrite /rotr size_rev -{3}(cat_take_drop n0 s) {1}/rot !rev_cat.
rewrite rotr size_rev -{3}[`s`](cat_take_drop n0 s) rot !rev_cat.
--by rewrite -size_drop -size_rev rot_size_cat.
by rewrite -size_drop -size_rev rot_size_cat.
Qed.

Lemma rev_rotr s : `rev (rotr n0 s) = rot n0 (rev s)`.
--apply: canRL rotrK _; rewrite {1}/rotr size_rev size_rotr /rotr {2}/rot rev_cat.
rewrite -rotrK -[`rot n0 (rev s)`]rotrK; "AP_TERM_TAC"; rewrite rotK.
rewrite rotr size_rev size_rotr rotr.
rewrite [`rot _ s`]rot rev_cat.
--set m := size s - n0; rewrite -{1}(@size_takel m _ _ (leq_subr _ _)).
set m := `sizel s - n0`.
rewrite -{1}(size_takel m s); last first.
  by rewrite -size_rev rot_size_cat -rev_cat cat_take_drop.
by rewrite -m_def leq_subr.
Qed.


End RotrLemmas.

Section RotCompLemmas.

--Variable T : Type.
--Implicit Type s : seq T.
Implicit Type s : `:(A)list`.

Lemma rot_addn m n s : `m + n <= sizel s ==> rot (m + n) s = rot m (rot n s)`.
--move=> sz_s; rewrite {1}/rot -[take _ s](cat_take_drop n).
--rewrite 5!(catA, =^~ rot_size_cat) !cat_take_drop.
--by rewrite size_drop !size_takel ?leq_addl ?addnK.
move => sz_s; rewrite rot -[`take _ s`](cat_take_drop n).
rewrite catA -rot_size_cat catA -rot_size_cat catA !cat_take_drop.
by rewrite size_drop !size_takel ?leq_addl ?addnK.
Qed.


Lemma rotS n s : `n < sizel s ==> rot (SUC n) s = rot 1 (rot n s)`.
--Proof. exact: (@rot_addn 1). Qed.
by rewrite ltE -add1n => /rot_addn. Qed.

Lemma rot_add_mod m n s : `n <= sizel s ==> m <= sizel s ==>
  rot m (rot n s) = rot (if m + n <= sizel s then m + n else (m + n) - sizel s) s`.
--move=> Hn Hm; case: leqP => [/rot_addn // | /ltnW Hmn]; symmetry.
--by rewrite -{2}(rotK n s) /rotr -rot_addn size_rot addn_subA ?subnK ?addnK.
move => Hn Hm; case: (EXCLUDED_MIDDLE `m + n <= sizel s`) => /=; [move/rot_addn => -> //| move].
rewrite -ltnNge => /ltnW Hmn; rewrite eq_sym.
by rewrite -{2}[`s`](rotK n s) rotr -rot_addn size_rot addn_subA ?subnK ?addnK.
Qed.

Lemma rot_rot m n s : `rot m (rot n s) = rot n (rot m s)`.
--case: (ltnP (size s) m) => Hm.
--  by rewrite !(@rot_oversize T m) ?size_rot 1?ltnW.
--case: (ltnP (size s) n) => Hn.
--  by rewrite !(@rot_oversize T n) ?size_rot 1?ltnW.
--by rewrite !rot_add_mod 1?addnC.
case: (ltnP `sizel s` m) => Hm.
  by rewrite ![`rot m _`]rot_oversize ?size_rot 1?ltnW.
case: (ltnP `sizel s` n) => Hn.
  by rewrite ![`rot n _`]rot_oversize ?size_rot 1?ltnW.
by rewrite !rot_add_mod 1?addnC.
Qed.


Lemma rot_rotr m n s : `rot m (rotr n s) = rotr n (rot m s)`.
Proof. by rewrite [`rotr n (rot m s)`]rotr size_rot rot_rot -rotr. Qed.

Lemma rotr_rotr m n s : `rotr m (rotr n s) = rotr n (rotr m s)`.
Proof. by rewrite !rotr !size_rot rot_rot. Qed.

End RotCompLemmas.

Section Mask.

--Variables (n0 : nat) (T : Type).
--Implicit Types (m : bitseq) (s : seq T).
Variable n0 : `:num`.
Implicit Type m : `:(bool)list`.
Implicit Type s s1 : `:(A)list`.


--Fixpoint mask m s {struct m} :=
--  match m, s with
--  | b :: m', x :: s' => if b then x :: mask m' s' else mask m' s'
--  | _, _ => [::]
--  end.
"let mask = define `mask [] s' = [] /\ mask m' [] = [] /\
	mask (b :: m') (x :: s') = if b then x :: mask m' s' else mask m' s'`".


Lemma mask_false s n : `mask (nseq n F) s = []`.
--Proof. by elim: s n => [|x s IHs] [|n] /=. Qed.
by elim: s n => [|x s IHs]; elim => [|n _]; rewr nseq ncons iter mask //= -ncons -nseq. Qed.


Lemma mask_true s n : `sizel s <= n ==> mask (nseq n T) s = s`.
--Proof. by elim: s n => [|x s IHs] [|n] //= Hn; congr (_ :: _); apply: IHs. Qed.
elim: s n => [| x s IHs]; elim => [|n _]; rewr nseq ncons iter mask // size_cons -ltE ltn0 //.
by rewrite ltE leqSS -ncons -nseq => /IHs ->.
Qed.

Lemma mask0 m : `mask m [] = []`.
--Proof. by case: m. Qed.
by elim: m => [|m _]; rewr mask. Qed.

Lemma mask1 b x : `mask [b] [x] = nseq (if b then 1 else 0) x`.
--Proof. by case: b. Qed.
by case: b => -> /=; rewr mask /= nseq ncons ONE !iter mask. Qed.

Lemma mask_cons b m x s : `mask (b :: m) (x :: s) = nseq (if b then 1 else 0) x ++ mask m s`.
--Proof. by case: b. Qed.
by case: b => ->; rewr mask /= nseq ncons ONE !iter cat1s cat0s. Qed.

Lemma size_mask m s : `sizel m = sizel s ==> sizel (mask m s) = count I m`.
--Proof. by elim: m s => [|b m IHm] [|x s] //= [Hs]; case: b; rewrite /= IHm. Qed.
elim: m s => [|b m IHm]; elim => [|x s _]; rewr mask count size_nil // size_cons eqS0 // eqSS.
by rewrite I_THM; case: b => -> /= /IHm <-; rewrite ?size_cons ?add1n // add0n. Qed.

Lemma mask_cat m1 s1 m2 s2 :
    `sizel m1 = sizel s1 ==>
       mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2`.
--move=> Hm1; elim: m1 s1 Hm1 => [|b1 m1 IHm] [|x1 s1] //= [Hm1].
--by rewrite (IHm _ Hm1); case b1.
move => Hm1.
elim: m1 s1 Hm1 => [|b1 m1 IHm]; elim => [|x1 s1 _]; 
	rewrite ?mask0 ?cat0s // ?size_nil ?size_cons ?[`0 = _`]eq_sym ?eqS0 //.
by rewrite eqSS !cat_cons => /IHm; rewr mask => ->; case: b1 => -> /=; rewrite cat_cons. Qed.

Lemma has_mask_cons a b m x s :
  `has a (mask (b :: m) (x :: s)) <=> b /\ a x \/ has a (mask m s)`.
--Proof. by case: b. Qed.
by case: b => ->; rewr mask /= has. Qed.

Lemma mask_rot m s : `sizel m = sizel s ==>
   mask (rot n0 m) (rot n0 s) = rot (count I (take n0 m)) (mask m s)`.
move=> Hs.
have Hsn0: `sizel (take n0 m) = sizel (take n0 s)`; first by rewrite !size_take Hs.
--rewrite -(size_mask Hsn0) {1 2}/rot mask_cat ?size_drop ?Hs //.
rewrite -(size_mask Hsn0) 2!rot mask_cat ?size_drop ?Hs //.
--rewrite -{4}(cat_take_drop n0 m) -{4}(cat_take_drop n0 s) mask_cat //.
rewrite -{4}[`m`](cat_take_drop n0 m) -{4}[`s`](cat_take_drop n0 s) mask_cat //.
--by rewrite rot_size_cat.
by rewrite rot_size_cat.
Qed.

End Mask.

Section EqMask.

--Variables (n0 : nat) (T : eqType).
--Implicit Types (s : seq T) (m : bitseq).
Variable n0 : `:num`.
Implicit Type s : `:(A)list`.
Implicit Type m : `:(bool)list`.


Lemma mem_mask_cons x b m y s :
  `(x <- mask (b :: m) (y :: s)) <=> b /\ (x = y) \/ (x <- mask m s)`.
--Proof. by case: b. Qed.
by case: b => ->; rewr mask /= in_cons. Qed.

Lemma mem_mask x m s : `x <- mask m s ==> x <- s`.
--by elim: s m => [|y p IHs] [|[|] m] //=; rewrite !in_cons;
--  case (x == y) => /=; eauto.
elim: s m => [|y p IHs]; elim => [|m _]; rewr mask in_nil // !in_cons.
by case: m => -> /=; rewrite ?in_cons; case: `x = y` => -> /= _; apply: IHs.
Qed.

Lemma mask_uniq s : `uniq s ==> !m. uniq (mask m s)`.
--elim: s => [|x s IHs] /= Hs [|b m] //.
--move/andP: Hs b => [Hx Hs] [|] /=; rewrite {}IHs // andbT.
--apply/negP => [Hmx]; case/negP: Hx; exact (mem_mask Hmx).
elim: s => [|x s IHs]; rewrite ?mask0 ?nil_uniq // cons_uniq => [] [Hx Hs]; elim => [|b m _].
  by rewr mask nil_uniq.
case: b => ->; rewr mask /= uniq; move: (IHs Hs m) => -> //=.
by move: Hx; apply: contra => /mem_mask.
Qed.

Lemma mem_mask_rot m s : `sizel m = sizel s ==>
  (!x. x <- mask (rot n0 m) (rot n0 s) <=> x <- mask m s)`.
Proof. by move=> Hm x; rewrite mask_rot // mem_rot. Qed.

End EqMask.

Section Subseq.

--Variable T : eqType.
--Implicit Type s : seq T.
Implicit Types s s1 : `:(A)list`.

--Fixpoint subseq s1 s2 :=
--  if s2 is y :: s2' then
--    if s1 is x :: s1' then subseq (if x == y then s1' else s1) s2' else true
--  else s1 == [::].
"let subseq = define `subseq (x :: s1) (y :: s2) = subseq (if x = y then s1 else x :: s1) s2 /\
	subseq [] s2 = T /\ subseq (x :: s1) [] = F`".

Lemma sub0seq s : `subseq [] s`. by rewr subseq. Qed.

Lemma subseq0 s : `subseq s [] = (s = [])`. 
by elim: s => [|x s _]; rewr subseq // !NOT_CONS_NIL. Qed.

Lemma subseqP s1 s2 :
--  reflect (exists2 m, size m = size s2 & s1 = mask m s2) (subseq s1 s2).
`subseq s1 s2 <=> (?m. sizel m = sizel s2 /\ s1 = mask m s2)`.
Proof.
elim: s2 s1 => [|y s2 IHs2]; elim => [|x s1 _]; rewr subseq /=.
-- - by left; exists [::].
-- - by right; do 2!case.
-- - by left; exists (nseq (size s2).+1 false); rewrite ?size_nseq //= mask_false.
  by exists `[]:(bool)list`; rewr mask size_nil /=.
  by rewrite NOT_EXISTS_THM negb_and mask0; rewr NOT_CONS_NIL /=.
  by exists `nseq (SUC (sizel s2)) F`; rewrite size_nseq size_cons mask_false.
--apply: {IHs2}(iffP (IHs2 _)) => [] [m sz_m def_s1].
--  by exists ((x == y) :: m); rewrite /= ?sz_m // -def_s1; case: eqP => // ->.
rewrite IHs2; split => [] [n] [sz_m def_s1]; move: IHs2 => _.
  exists `(x = y) :: n`; rewrite !size_cons sz_m; rewr mask; rewrite -def_s1 /=.
  by case: (EXCLUDED_MIDDLE `x = y`) => /=.
--case: eqP => [_ | ne_xy]; last first.
--  by case: m def_s1 sz_m => [|[] m] // [] // -> [<-]; exists m. 
case: (EXCLUDED_MIDDLE `x = y`) => /=; [move => _ | move => ne_xy]; last first.
  elim: n def_s1 sz_m => [|[] -> m IHm]; rewr mask NOT_CONS_NIL // size_cons eqSS => eq seq.
    by move: eq; rewrite eqseq_cons //.
  by exists m.
--pose i := index true m; have def_m_i: take i m = nseq (size (take i m)) false.
--  apply/all_pred1P; apply/(all_nthP true) => j.
--  rewrite size_take ltnNge leq_minl negb_or -ltnNge; case/andP=> lt_j_i _.
--  rewrite nth_take //= -negb_add addbF -addbT -negb_eqb.
--  by rewrite [_ == _](before_find _ lt_j_i).
set i := `indexl T n`.
have def_m_i: `take i n = nseq (sizel (take i n)) F`.
  rewrite all_pred1P -(all_nthP `pred1 F` `take i n` `T`) => j.
  rewrite size_take ltnNge -minn leq_minl negb_or -ltnNge; case => lt_j_i _.
  rewrite (nth_take lt_j_i); move: lt_j_i; rewrite -i_def index => /before_find /(_ `T`).
  by rewrite !pred1 /=.

--have lt_i_m: i < size m.
--  rewrite ltnNge; apply/negP=> le_m_i; rewrite take_oversize // in def_m_i.
--  by rewrite def_m_i mask_false in def_s1.
have lt_i_m: `i < sizel n`.
  rewrite ltnNge; rewrite -"TAUT `(P ==> F) <=> ~P`" => le_m_i.
  by move: def_m_i def_s1; rewrite take_oversize // => ->; rewrite mask_false; rewr !NOT_CONS_NIL.
--rewrite size_take lt_i_m in def_m_i.
move: def_m_i; rewrite size_take lt_i_m /= => def_m_i.
--exists (take i m ++ drop i.+1 m).
--  rewrite size_cat size_take size_drop lt_i_m.
--  by rewrite sz_m in lt_i_m *; rewrite subnKC.
exists `take i n ++ dropl (SUC i) n`; split.
  rewrite size_cat size_take size_drop lt_i_m /=.
  by move: lt_i_m; rewrite sz_m ltE => /subnKC; rewrite size_cons addSn eqSS.
--rewrite {s1 def_s1}[s1](congr1 behead def_s1).
--rewrite -[s2](cat_take_drop i) -{1}[m](cat_take_drop i) {}def_m_i -cat_cons.
move: (congr1 `behead` def_s1); rewr behead => ->.
rewrite -[`s2`](cat_take_drop i) -{1}[`n`](cat_take_drop i) def_m_i -cat_cons.
--have sz_i_s2: size (take i s2) = i by apply: size_takel; rewrite sz_m in lt_i_m.
have sz_i_s2: `sizel (take i s2) = i`.
  by apply: size_takel; move: lt_i_m; rewrite sz_m ltE size_cons leqSS.
--rewrite lastI cat_rcons !mask_cat ?size_nseq ?size_belast ?mask_false //=.
--by rewrite (drop_nth true) // nth_index -?index_mem.
rewrite lastI cat_rcons !mask_cat ?size_nseq ?size_belast ?mask_false //= !cat0s.
rewrite (drop_nth `T`) // -{1}i_def nth_index -?index_mem ?i_def //.
by rewr mask /= behead.
Qed.

Lemma subseq_trans s1 s2 s3: `subseq s1 s2 ==> subseq s2 s3 ==> subseq s1 s3`.
--move=> _ _ s /subseqP[m2 _ ->] /subseqP[m1 _ ->].
--elim: s => [|x s IHs] in m2 m1 *; first by rewrite !mask0.
--case: m1 => [|[] m1]; first by rewrite mask0.
--  case: m2 => [|[] m2] //; first by rewrite /= eqxx IHs.
--  case/subseqP: (IHs m2 m1) => m sz_m def_s; apply/subseqP.
--  by exists (false :: m); rewrite //= sz_m.
--case/subseqP: (IHs m2 m1) => m sz_m def_s; apply/subseqP.
--by exists (false :: m); rewrite //= sz_m.
rewrite subseqP => [] [m2] [_ ->]; rewrite subseqP => [] [m1] [_ ->].
elim: s3 m2 m1 => [|x s IHs]; first by rewrite !mask0 subseq0.
move => m2 m1.
elim: m1 => [|[] -> m1 _]; rewr mask mask0 subseq //.
  elim: m2 => [|[] -> m2 _]; rewr mask !subseq IHs //.
  move: (IHs m2 m1); rewrite !subseqP => [] [m] [sz_m def_s].
  by exists `F :: m`; rewrite !size_cons sz_m def_s; rewr mask /=.
move: (IHs m2 m1); rewrite !subseqP => [] [m] [sz_m def_s].
by exists `F :: m`; rewrite !size_cons sz_m def_s; rewr mask /=.
Qed.


Lemma subseq_refl s : `subseq s s`.
--Proof. by elim: s => //= x s IHs; rewrite eqxx. Qed.
by elim: s => [|x s IHs]; rewr subseq /=. Qed.

--Hint Resolve subseq_refl.

Lemma subseq_cat s1 s2 s3 s4 :
  `subseq s1 s3 ==> subseq s2 s4 ==> subseq (s1 ++ s2) (s3 ++ s4)`.
--case/subseqP=> m1 sz_m1 ->; case/subseqP=> m2 sz_m2 ->; apply/subseqP.
--by exists (m1 ++ m2); rewrite ?size_cat ?mask_cat ?sz_m1 ?sz_m2.
rewrite !subseqP => [] [m1] [sz_m1 ->] [m2] [sz_m2 ->].
by exists `m1 ++ m2`; rewrite ?size_cat ?mask_cat ?sz_m1 ?sz_m2.
Qed.

Lemma mem_subseq s1 s2 : `subseq s1 s2 ==> (!x. x <- s1 ==> x <- s2)`.
--Proof. by case/subseqP=> m _ -> x; exact: mem_mask. Qed.
by rewrite subseqP => [] [m] [_ ->] x; apply: mem_mask. Qed.

Lemma subseq_seq1 x s : `subseq [x] s <=> x <- s`.
--by elim: s => //= y s; rewrite inE; case: (x == y); rewrite ?sub0seq.
elim: s => [|y s IHs]; rewr subseq !MEM.
by case: (EXCLUDED_MIDDLE `x = y`) => /=; rewr subseq /=.
Qed.

Lemma size_subseq s1 s2 : `subseq s1 s2 ==> sizel s1 <= sizel s2`.
--Proof. by case/subseqP=> m sz_m ->; rewrite size_mask -sz_m ?count_size. Qed.
rewrite subseqP => [] [m] [sz_m ->]. 
by rewrite size_mask -sz_m ?count_size. Qed.

Lemma size_subseq_leqif s1 s2 :
--  subseq s1 s2 ==> sizel s1 <= sizel s2 ?= iff (s1 == s2).
`subseq s1 s2 ==> leqif (sizel s1) (sizel s2) (s1 = s2)`.
--move=> sub12; split; first exact: size_subseq.
--apply/idP/eqP=> [|-> //]; case/subseqP: sub12 => m sz_m ->{s1}.
--rewrite size_mask -sz_m // -all_count -(eq_all eqb_id).
--by move/(@all_pred1P _ true)->; rewrite sz_m mask_true.
move => sub12; rewrite leqif; split; first exact: size_subseq.
split => [|-> //]; move: sub12; rewrite subseqP => [] [m] [sz_m ->].
rewrite size_mask -sz_m // -all_count.
have ->: `all I m = all (pred1 T) m`.
  move: (eq_all `I:bool->bool` `pred1 T`).
  by rewrite pred1 /= I_THM /=.
by rewrite -all_pred1P => ->; rewrite sz_m mask_true ?leqnn.
Qed.

Lemma subseq_cons s x : `subseq s (x :: s)`.
--Proof. by exact: (@subseq_cat [::] s [:: x]). Qed.
move: (subseq_cat `[]` s `[x]` s).
by rewrite subseq_refl cat0s cat1s; rewr subseq /=.
Qed.

Lemma subseq_rcons s x : `subseq s (rcons s x)`.
Proof. by rewrite -{1}[`s`]cats0 -cats1 subseq_cat; rewr subseq !subseq_refl. Qed.

Lemma subseq_uniq s1 s2 : `subseq s1 s2 ==> uniq s2 ==> uniq s1`.
--Proof. by case/subseqP=> m _ -> Us2; exact: mask_uniq. Qed.
rewrite subseqP => [] [m] [_ ->] Us2. 
by move: (mask_uniq Us2 m).
Qed.

End Subseq.

--Prenex Implicits subseq.
--Implicit Arguments subseqP [T s1 s2].

--Hint Resolve subseq_refl.

Section Map.

--Variables (n0 : nat) (T1 : Type) (x1 : T1).
--Variables (T2 : Type) (x2 : T2) (f : T1 -> T2).
Variable n0 : `:num`.
Variable x1 : `:A`.
Variable x2 : `:B`.
Variable f : `:A -> B`.

--Fixpoint map s := if s is x :: s' then f x :: map s' else [::].
"let map = define `map f (x :: s) = f x :: map f s /\ map f [] = []`".

Lemma map_MAP : `map = MAP`.
apply EQ_EXT => f; apply EQ_EXT => s.
by elim: s => [|x s IHs]; rewr map MAP.
Qed.


Lemma map_cons x s : `map f (x :: s) = f x :: map f s`.
--Proof. by []. Qed.
by rewr map. Qed.

Lemma map_nseq x : `map f (nseq n0 x) = nseq n0 (f x)`.
--Proof. by elim: n0 => // *; congr (_ :: _). Qed.
elim: n0 => [|n IHn]; rewr nseq ncons iter map // -ncons -nseq.
by rewrite IHn.
Qed.

Lemma map_cat s1 s2 : `map f (s1 ++ s2) = map f s1 ++ map f s2`.
--Proof. by elim: s1 => [|x s1 IHs] //=; rewrite IHs. Qed.
by elim: s1 => [|x s1 IHs]; rewr cat map cat //. Qed.

Lemma size_map s : `sizel (map f s) = sizel s`.
--Proof. by elim: s => //= x s ->. Qed.
elim: s => [|x s IHs]; rewr map size_nil // size_cons.
by rewrite IHs.
Qed.

Lemma behead_map s : `behead (map f s) = map f (behead s)`.
--Proof. by case: s. Qed.
by elim: s => [|x s IHs]; rewr map behead map. Qed.

Lemma nth_map n s : `n < sizel s ==> nth x2 (map f s) n = f (nth x1 s n)`.
--Proof. by elim: s n => [|x s IHs] [|n]; try exact (IHs n). Qed.
elim: s n => [|x s IHs]; elim => [|n _]; rewr size_nil ltnn ltS0 /= map nth //.
by rewrite size_cons ltSS => /IHs.
Qed.


Lemma map_rcons s x : `map f (rcons s x) = rcons (map f s) (f x)`.
Proof. by rewrite -!cats1 map_cat; rewr !map. Qed.

Lemma last_map s x : `last (f x) (map f s) = f (last x s)`.
--Proof. by elim: s x => /=. Qed.
by elim: s x => [|x s IHs]; rewr map last. Qed.

Lemma belast_map s x : `belast (f x) (map f s) = map f (belast x s)`.
--Proof. by elim: s x => //= y s IHs x; rewrite IHs. Qed.
by elim: s x => [|y s IHs x]; rewr map belast !map. Qed.

"let preim = new_definition `preim (f:A->B) (a:B->bool) = (\x. a (f x))`".

Lemma filter_map a s : `filter a (map f s) = map f (filter (preim f a) s)`.
--Proof. by elim: s => //= x s IHs; rewrite (fun_if map) /= IHs. Qed.
elim: s => [|x s IHs]; rewr filter map filter //.
rewrite IHs preim /=.
by case: (EXCLUDED_MIDDLE `a (f x)`) => /= _; rewr map.
Qed.

Lemma find_map a s : `find a (map f s) = find (preim f a) s`.
--Proof. by elim: s => //= x s ->. Qed.
elim: s => [|x s IHs]; rewr map find //.
by rewrite IHs preim.
Qed.

Lemma has_map a s : `has a (map f s) = has (preim f a) s`.
--Proof. by elim: s => //= x s ->. Qed.
elim: s => [|x s IHs]; rewr map has //.
by rewrite IHs preim.
Qed.

Lemma all_map a s : `all a (map f s) = all (preim f a) s`.
--Proof. by elim: s => //= x s ->. Qed.
elim: s => [|x s IHs]; rewr map all //.
by rewrite IHs preim.
Qed.

Lemma count_map a s : `count a (map f s) = count (preim f a) s`.
--Proof. by elim: s => //= x s ->. Qed.
elim: s => [|x s IHs]; rewr map count //.
by rewrite IHs preim.
Qed.

Lemma map_take s : `map f (take n0 s) = take n0 (map f s)`.
--Proof. by elim: n0 s => [|n IHn] [|x s] //=; rewrite IHn. Qed.
by elim: n0 s => [|n IHn]; elim => [|x s _]; rewr take map take. Qed.

Lemma map_drop s : `map f (dropl n0 s) = dropl n0 (map f s)`.
--Proof. by elim: n0 s => [|n IHn] [|x s] //=; rewrite IHn. Qed.
by elim: n0 s => [|n IHn]; elim => [|x s _]; rewr drop map drop. Qed.

Lemma map_rot s : `map f (rot n0 s) = rot n0 (map f s)`.
Proof. by rewrite !rot map_cat map_take map_drop. Qed.

Lemma map_rotr s : `map f (rotr n0 s) = rotr n0 (map f s)`.
--Proof. by apply: canRL (@rotK n0 T2) _; rewrite -map_rot rotrK. Qed.
by apply (rot_inj n0); rewrite rotrK -map_rot rotrK. Qed.


Lemma map_rev s : `map f (rev s) = rev (map f s)`.
--Proof. by elim: s => //= x s IHs; rewrite !rev_cons -!cats1 map_cat IHs. Qed.
by elim: s => [|x s IHs]; rewr map rev_cons map_rcons // rev catrev map. Qed.

Lemma map_mask m s : `map f (mask m s) = mask m (map f s)`.
--Proof. by elim: m s => [|[|] m IHm] [|x p] //=; rewrite IHm. Qed.
elim: m s => [|[] -> m IHm]; elim => [|x p _]; rewr mask map // mask //.
by rewrite map_cons /= IHm.
Qed.

Lemma inj_map : `(!x y. f x = f y ==> x = y) ==> (!s1 s2. map f s1 = map f s2 ==> s1 = s2)`.
--by move=> injf; elim=> [|y1 s1 IHs] [|y2 s2] //= [/injf-> /IHs->].
move => injf; elim => [|y1 s1 IHs]; elim => [|y2 s2 _]; rewr map //;
  rewrite ?[`[] = CONS _1 _2`]eq_sym; rewr NOT_CONS_NIL //.
by rewrite eqseq_cons => [] [/injf -> /IHs ->].
Qed.

End Map.

Lemma filter_mask a s : `filter (a:A->bool) s = mask (map a s) s`.
--Proof. by elim: s => //= x s <-; case: (a x). Qed.
elim: s => [|x s IHs]; rewr mask filter // map.
by case: (EXCLUDED_MIDDLE `a x`) => /=; rewrite IHs; rewr mask /=.
Qed.

Section FilterSubseq.

--Variable T : eqType.
--Implicit Types (s : seq T) (a : pred T).
Implicit Type s s1 : `:(A)list`.
Implicit Type a : `:A -> bool`.

Lemma filter_subseq a s : `subseq (filter a s) s`.
--Proof. by apply/subseqP; exists (map a s); rewrite ?size_map ?filter_mask. Qed.
by rewrite subseqP; exists `map a s`; rewrite size_map filter_mask. Qed.

Lemma subseq_filter s1 s2 a :
  `subseq s1 (filter a s2) <=> all a s1 /\ subseq s1 s2`.
--elim: s2 s1 => [|x s2 IHs] [|y s1] //=; rewrite ?andbF ?sub0seq //.
--by case a_x: (a x); rewrite /= !IHs /=; case: eqP => // ->; rewrite a_x.
elim: s2 s1 => [|x s2 IHs]; elim => [|y s1 _]; rewr filter subseq !all //.
by case: (EXCLUDED_MIDDLE `a x`) => /= ax; rewr subseq; 
	case: (EXCLUDED_MIDDLE `y = x`) => /= yx; rewrite IHs ?all_cons.
Qed.


Lemma subseq_uniqP s1 s2 :
  `uniq s2 ==> (subseq s1 s2 <=> s1 = filter (\x. x <- s1) s2)`.
--move=> uniq_s2; apply: (iffP idP) => [ss12 | ->]; last exact: filter_subseq.
--apply/eqP; rewrite -size_subseq_leqif ?subseq_filter ?(introT allP) //.
--apply/eqP/esym/perm_eq_size.
--rewrite uniq_perm_eq ?filter_uniq ?(subseq_uniq ss12) // => x.
--by rewrite mem_filter; apply: andb_idr; exact: (mem_subseq ss12).
move => uniq_s2; split => [ss12 | ->]; last by rewrite filter_subseq.
have: `subseq s1 (filter (\x. x <- s1) s2)`.
  by rewrite subseq_filter -allP.
move/size_subseq_leqif; move/leqif_imp_eq => <-.
rewrite eq_sym; apply: perm_eq_size.
rewrite uniq_perm_eq filter_uniq // (subseq_uniq ss12) //.
by rewrite mem_filter /= => x; rewrite andb_idr //; apply: (mem_subseq ss12).
Qed.

End FilterSubseq.

--Implicit Arguments subseq_uniqP [T s1 s2].

Section EqMap.

--Variables (n0 : nat) (T1 : eqType) (x1 : T1).
--Variables (T2 : eqType) (x2 : T2) (f : T1 -> T2).
--Implicit Type s : seq T1.
Variable n0 : `:num`.
Variable x1 : `:A`.
Variable x2 : `:B`.
Variable f : `:A -> B`.
Implicit Type s : `:(A)list`.

Lemma map_f s x : `x <- s ==> f x <- map f s`.
--elim: s => [|y s IHs] //=.
--by case/predU1P=> [->|Hx]; [exact: predU1l | apply: predU1r; auto].
elim: s => [|y s IHs]; rewr map in_nil in_cons //.
by case => [-> //| Hx]; right; apply: IHs.
Qed.

Lemma mapP s y : `(y <- map f s) <=> (?x. x <- s /\ y = f x)`.
--elim: s => [|x s IHs]; first by right; case.
--rewrite /= in_cons eq_sym; case Hxy: (f x == y).
--  by left; exists x; [rewrite mem_head | rewrite (eqP Hxy)].
--apply: (iffP IHs) => [[x' Hx' ->]|[x' Hx' Dy]].
--  by exists x'; first exact: predU1r.
--by case: Dy Hxy => ->; case/predU1P: Hx' => [->|]; [rewrite eqxx | exists x'].
elim: s => [|x s IHs]; rewr map in_nil andFb.
  by rewrite NOT_EXISTS_THM => x.
rewrite !in_cons; case: (EXCLUDED_MIDDLE `y = f x`) => /= Hxy.
  by exists x.
rewrite IHs; split => [[x' [Hx' ->]] | [x' [Hx' Dy]]].
  by exists x'.
case: Hx' => Hx'; [move | exists x' => //].
by move: Hxy; rewrite Dy Hx'.
Qed.


Lemma map_uniq s : `uniq (map f s) ==> uniq s`.
--elim: s => //= x s IHs /andP[not_sfx /IHs->]; rewrite andbT.
--by apply: contra not_sfx => sx; apply/mapP; exists x.
elim: s => [|x s IHs]; rewr map uniq // => [] [not_sfx].
move/IHs => ->; rewrite andbT.
by apply: contra not_sfx => sx; rewrite mapP; exists x.
Qed.

Lemma map_inj_in_uniq s : `(!x y. x <- s ==> y <- s ==> (f x = f y ==> x = y)) ==>
	uniq (map f s) = uniq s`.
--{in s &, injective f} -> uniq (map f s) = uniq s.
Proof.
--elim: s => //= x s IHs //= injf; congr (~~ _ && _).
--  apply/mapP/idP=> [[y sy /injf] | ]; last by exists x.
--  by rewrite mem_head mem_behead // => ->.
--apply: IHs => y z sy sz; apply: injf => //; exact: predU1r.
elim: s => [|x s IHs]; rewr in_nil /= map uniq // => injf.
rewrite IHs.
  move => a b [[Ha Hb] fab].
  by move: (injf a b); rewrite !in_cons Ha Hb fab.
"AP_THM_TAC THEN AP_TERM_TAC".
rewrite mapP NOT_EXISTS_THM negb_and; split.
  by move/(_ x) => /=.
move => Hx y.
case: (EXCLUDED_MIDDLE `y <- s`) => /= Hy.
rewr "TAUT `~A <=> (A ==> F)`" => fxy.
move: (injf x y); rewrite !in_cons Hy fxy /=.
case: (EXCLUDED_MIDDLE `x = y`) => // xy.
by move: Hy Hx; rewrite xy.
Qed.


Lemma map_subseq s1 s2 : `subseq s1 s2 ==> subseq (map f s1) (map f s2)`.
--case/subseqP=> m sz_m ->; apply/subseqP.
--by exists m; rewrite ?size_map ?map_mask.
rewrite !subseqP => [] [m] [sz_m ->].
by exists m; rewrite size_map map_mask.
Qed.

End EqMap.

Section EqMap2.

Variable n0 : `:num`.
Variable x1 : `:A`.
Variable x2 : `:B`.
Variable f : `:A -> B`.
Implicit Type s : `:(A)list`.
Hypothesis Hf : `!x y. f x = f y ==> x = y`.

Lemma inj_eq x y: `(f x = f y <=> x = y)`.
Proof. by split => [/Hf | -> ]. Qed.

Lemma mem_map s x : `(f x <- map f s) = (x <- s)`.
--Proof. by apply/mapP/idP=> [[y Hy /Hf->] //|]; exists x. Qed.
by rewrite mapP; split => [[y [Hy /Hf ->]] // | Hx]; exists x. Qed.

Lemma index_map s x : `indexl (f x) (map f s) = indexl x s`.
--Proof. by rewrite /index; elim: s => //= y s IHs; rewrite (inj_eq Hf) IHs. Qed.
rewrite !index; elim: s => [|y s IHs]; rewr map find // pred1 /=.
by rewrite -[`y = x`]inj_eq -!pred1 IHs.
Qed.


Lemma map_inj_uniq s : `uniq (map f s) = uniq s`.
--Proof. apply: map_inj_in_uniq; exact: in2W. Qed.
by apply: map_inj_in_uniq => x y _ _ /Hf. Qed.

End EqMap2.

--Implicit Arguments mapP [T1 T2 f s y].
--Prenex Implicits mapP.


Section MapComp.

--Variable T1 T2 T3 : Type.

Lemma map_id s : `map I (s:(A)list) = s`.
--Proof. by elim: s => //= x s ->. Qed.
by elim: s => [|x s IHs]; rewr map // I_THM. Qed.

Lemma eq_map f1 f2 : `(!x. (f1:A->B) x = f2 x) ==> map f1 = map f2`.
--Proof. by move=> Ef; elim=> //= x s ->; rewrite Ef. Qed.
by rewrite eq_ext => ->. Qed.

Lemma map_comp f1 f2 s :
  `map (f1 o f2) s = map (f1:B->C) (map (f2:A->B) s)`.
--Proof. by elim: s => //= x s ->. Qed.
elim: s => [|x s IHs]; rewr !map.
by rewrite IHs o_THM.
Qed.

Lemma mapK f1 f2 :
--  cancel f1 f2 -> cancel (map f1) (map f2).
`(!x. (f2:B->A) ((f1:A->B) x) = x) ==> (!s. map f2 (map f1 s) = s)`.
--Proof. by move=> eq_f12; elim=> //= x s ->; rewrite eq_f12. Qed.
by move => eq_f12; elim => [|x s IHs]; rewr !map. Qed.

End MapComp.

Lemma eq_in_map f1 f2 s :
  `(!x. x <- s ==> (f1:A->B) x = f2 x) ==> map f1 s = map f2 s`.
--  {in s, f1 =1 f2} -> map f1 s = map f2 s.
--elim: s => //= x s IHs eqf12.
--rewrite eqf12 ?inE /= (eqxx, IHs) // => y sy.
--by rewrite eqf12 ?inE //= predU1r.
elim: s => [|x s IHs eqf12]; rewr map //.
rewrite eqf12 ?in_cons // IHs // => y sy.
by rewrite eqf12 ?in_cons.
Qed.

Lemma map_id_in f s : `(!x. x <- s ==> f x = (x:A)) ==> map f s = s`.
--Proof. by move/eq_in_map->; exact: map_id. Qed.
move/eq_in_map => ->.
rewrite -{2}[`s`]map_id.
by rewrite (eq_map `(\x. x)` `I`) //= I_THM.
Qed.

(* Map a partial function *)

(*
Section Pmap.

--Variables (aT rT : Type) (f : aT -> option rT) (g : rT -> aT).
Variable f : `

Fixpoint pmap s :=
  if s is x :: s' then oapp (cons^~ (pmap s')) (pmap s') (f x) else [::].

Lemma map_pK : pcancel g f -> cancel (map g) pmap.
Proof. by move=> gK; elim=> //= x s ->; rewrite gK. Qed.

Lemma size_pmap s : size (pmap s) = count [eta f] s.
Proof. by elim: s => //= x s <-; case f. Qed.

Lemma pmapS_filter s : map some (pmap s) = map f (filter [eta f] s).
Proof. by elim: s => //= x s; case fx: (f x) => //= [u] <-; congr (_ :: _). Qed.

Hypothesis fK : ocancel f g.

Lemma pmap_filter s : map g (pmap s) = filter [eta f] s.
Proof. by elim: s => //= x s <-; rewrite -{3}(fK x); case f. Qed.

End Pmap.

Section EqPmap.

Variables (aT rT : eqType) (f : aT -> option rT) (g : rT -> aT).

Lemma eq_pmap (f1 f2 : aT -> option rT) :
 f1 =1 f2 -> pmap f1 =1 pmap f2.
Proof. by move=> Ef; elim=> //= x s ->; rewrite Ef. Qed.

Lemma mem_pmap s u : (u \in pmap f s) = (Some u \in map f s).
Proof. by elim: s => //= x s IHs; rewrite in_cons -IHs; case (f x). Qed.

Hypothesis fK : ocancel f g.

Lemma can2_mem_pmap : pcancel g f -> forall s u, (u \in pmap f s) = (g u \in s).
Proof.
by move=> gK s u; rewrite -(mem_map (pcan_inj gK)) pmap_filter // mem_filter gK.
Qed.

Lemma pmap_uniq s : uniq s -> uniq (pmap f s).
Proof.
by move/(filter_uniq [eta f]); rewrite -(pmap_filter fK); exact: map_uniq.
Qed.

End EqPmap.

Section PmapSub.

Variables (T : Type) (p : pred T) (sT : subType p).

Lemma size_pmap_sub s : size (pmap (insub : T -> option sT) s) = count p s.
Proof. by rewrite size_pmap (eq_count (isSome_insub _)). Qed.

End PmapSub.

Section EqPmapSub.

Variables (T : eqType) (p : pred T) (sT : subType p).

Let insT : T -> option sT := insub.

Lemma mem_pmap_sub s u : (u \in pmap insT s) = (val u \in s).
Proof. apply: (can2_mem_pmap (insubK _)); exact: valK. Qed.

Lemma pmap_sub_uniq s : uniq s -> uniq (pmap insT s).
Proof. exact: (pmap_uniq (insubK _)). Qed.

End EqPmapSub.
*)

(* Index sequence *)

--Fixpoint iota m n := if n is n'.+1 then m :: iota m.+1 n' else [::].
"let iota = define `iota m (SUC n) = m :: iota (SUC m) n /\ iota m 0 = []`".

Lemma size_iota m n : `sizel (iota m n) = n`.
--Proof. by elim: n m => //= n IHn m; rewrite IHn. Qed.
elim: n m => [|n IHn m]; rewr iota !size_nil size_cons.
by rewrite IHn.
Qed.

Lemma iota_add m n1 n2 : `iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2`.
--by elim: n1 m => //= [|n1 IHn1] m; rewrite ?addn0 // -addSnnS -IHn1.
elim: n1 m => [|n1 IHn1]; rewr addn0 add0n iota cat0s //.
by rewr -addSnnS addSn iota IHn1 addSn cat_cons.
Qed.

Lemma iota_addl m1 m2 n : `iota (m1 + m2) n = map ((+) m1) (iota m2 n)`.
--Proof. by elim: n m2 => //= n IHn m2; rewrite -addnS IHn. Qed.
elim: n m2 => [|n IHn m2]; rewr iota !map //.
by rewrite -addnS IHn.
Qed.

Lemma nth_iota m n i : `i < n ==> nth 0 (iota m n) i = m + i`.
--by move/subnKC <-; rewrite addSnnS iota_add nth_cat size_iota ltnn subnn.
rewrite ltE => /subnKC <-; rewrite addSnnS iota_add nth_cat size_iota ltnn /= subnn.
by rewr iota nth.
Qed.

Lemma mem_iota m n i : `(i <- iota m n) <=> (m <= i) /\ (i < m + n)`.
--elim: n m => [|n IHn] /= m; first by rewrite addn0 ltnNge andbN.
--rewrite -addSnnS leq_eqVlt in_cons eq_sym.
--by case: eqP => [->|_]; [rewrite leq_addr | exact: IHn].
elim: n m => [|n IHn] m; rewr iota in_nil.
  by rewrite addn0 ltnNge andbN.
rewrite -addSnnS leq_eqVlt in_cons [`i = m`]eq_sym.
case: (EXCLUDED_MIDDLE `m = i`) => /=.
  by rewrite ltE addSn leqSS leq_addr.
by rewrite IHn -ltE.
Qed.

Lemma iota_uniq m n : `uniq (iota m n)`.
--Proof. by elim: n m => //= n IHn m; rewrite mem_iota ltnn /=. Qed.
elim: n m => [|n IHn m]; rewr iota !uniq //.
by rewrite mem_iota IHn -ltE ltnn andFb.
Qed.

(* Making a sequence of a specific length, using indexes to compute items. *)

Section MakeSeq.

--Variables (T : Type) (x0 : T).
Variable x0 : `:A`.

--Definition mkseq f n : seq T := map f (iota 0 n).
"let mkseq = new_definition `mkseq f n = map f (iota 0 n)`".

Lemma size_mkseq f n : `sizel (mkseq f n) = n`.
Proof. by rewrite mkseq size_map size_iota. Qed.

Lemma eq_mkseq f g : `(!x. f x = g x) ==> mkseq f = mkseq g`.
--Proof. by move=> Efg n; exact: eq_map Efg _. Qed.
by rewrite -eq_ext !mkseq => /eq_map ->. Qed.

Lemma nth_mkseq f n i : `i < n ==> nth x0 (mkseq f n) i = f i`.
--Proof. by move=> Hi; rewrite (nth_map 0) ?nth_iota ?size_iota. Qed.
move => Hi; rewrite mkseq.
rewrite nth_map; exists `0`; rewrite size_iota Hi /= => _.
by rewrite nth_iota ?add0n.
Qed.

Lemma mkseq_nth s : `mkseq (nth x0 s) (sizel s) = s`.
--by apply: (@eq_from_nth _ x0); rewrite size_mkseq // => i Hi; rewrite nth_mkseq.
apply "REWRITE_RULE[IMP_IMP] eq_from_nth".
exists x0; rewrite size_mkseq /= => i Hi.
by rewrite nth_mkseq.
Qed.

End MakeSeq.

Lemma mkseq_uniq f n :
  `(!x y. f x = f y ==> x = y) ==> uniq (mkseq f n)`.
--Proof. by move=> injf; rewrite map_inj_uniq // iota_uniq. Qed.
move/map_inj_uniq => Hs.
by rewrite mkseq Hs iota_uniq.
Qed.

Section FoldRight.

--Variables (T R : Type) (f : T -> R -> R) (z0 : R).
Variable f : `:A -> B -> B`.
Variable z0: `:B`.

--Fixpoint foldr s := if s is x :: s' then f x (foldr s') else z0.
"let foldr = define `foldr f z0 (x :: s) = f x (foldr f z0 s) /\ foldr f z0 [] = z0`".

End FoldRight.

Section FoldRightComp.

--Variables (T1 T2 : Type) (h : T1 -> T2).
--Variables (R : Type) (f : T2 -> R -> R) (z0 : R).
Variable h : `:A->B`.
Variable f : `:B->R->R`.
Variable z0 : `:R`.

Lemma foldr_cat s1 s2 : `foldr f z0 (s1 ++ s2) = foldr f (foldr f z0 s2) s1`.
--Proof. by elim: s1 => //= x s1 ->. Qed.
by elim: s1 => [|x s1 IHs]; rewr cat foldr. Qed.

Lemma foldr_map s : `foldr f z0 (map h s) = foldr (\x z. f (h x) z) z0 s`.
--Proof. by elim: s => //= x s ->. Qed.
by elim: s => [|x s IHs]; rewr map foldr. Qed.

End FoldRightComp.

(* Quick characterization of the null sequence. *)

--Definition sumn := foldr addn 0.
"let sumn = new_definition `sumn = foldr (+) 0`".

Lemma sumn0 : `sumn [] = 0`. by rewr sumn foldr. Qed.

Lemma sumn_nseq x n : `sumn (nseq n x) = x * n`.
--Proof. by rewrite mulnC; elim: n => //= n ->. Qed.
rewrite mulnC; elim: n => [|n IHn]; rewr nseq ncons iter sumn foldr mul0n //.
by rewrite -sumn -ncons -nseq IHn mulSn.
Qed.

Lemma sumn_cat s1 s2 : `sumn (s1 ++ s2) = sumn s1 + sumn s2`.
--Proof. by elim: s1 => //= x s1 ->; rewrite addnA. Qed.
elim: s1 => [|x s1 IHs]; rewr cat sumn0 add0n //.
by rewr sumn foldr -sumn IHs addnA.
Qed.

Lemma natnseq0P s : `sumn s = 0 <=> s = nseq (sizel s) 0`.
--apply: (iffP idP) => [|->]; last by rewrite sumn_nseq.
--by elim: s => //= x s IHs; rewrite addn_eq0 => /andP[/eqP-> /IHs <-].
split => [| ->]; last by rewrite sumn_nseq mul0n.
elim: s => [|x s IHs]; first by rewr size_nil nseq ncons iter.
by rewr sumn foldr -sumn addn_eq0 size_cons nseq ncons iter -ncons -nseq => [] [-> /IHs <-].
Qed.

Section FoldLeft.

--Variables (T R : Type) (f : R -> T -> R).
Variable f : `:R->A->R`.

--Fixpoint foldl z s := if s is x :: s' then foldl (f z x) s' else z.
"let foldl = define `foldl f z (x :: s) = foldl f (f z x) s /\ foldl f z [] = z`".

Lemma foldl_rev z s : `foldl f z (rev s) = foldr (\x z0. f z0 x) z s`.
--elim/last_ind: s z => [|s x IHs] z //=.
--by rewrite rev_rcons -cats1 foldr_cat -IHs.
apply: "REWRITE_RULE[IMP_IMP] last_ind" s z; split => [|s x IHs] z.
  by rewr rev catrev foldl foldr.
rewrite rev_rcons -cats1 foldr_cat -IHs.
by rewr !foldr foldl.
Qed.

Lemma foldl_cat z s1 s2 : `foldl f z (s1 ++ s2) = foldl f (foldl f z s1) s2`.
--by rewrite -(revK (s1 ++ s2)) foldl_rev rev_cat foldr_cat -!foldl_rev !revK.
by rewrite -(revK `s1 ++ s2`) foldl_rev rev_cat foldr_cat -!foldl_rev !revK. Qed.

End FoldLeft.

Section Scan.

--Variables (T1 : Type) (x1 : T1) (T2 : Type) (x2 : T2).
--Variables (f : T1 -> T1 -> T2) (g : T1 -> T2 -> T1).
Variable x1 : `:A`.
Variable x2 : `:B`.
Variable f : `:A -> A -> B`.
Variable g : `:A -> B -> A`.

--Fixpoint pairmap x s := if s is y :: s' then f x y :: pairmap y s' else [::].
"let pairmap = define `pairmap f x (y :: s) = f x y :: pairmap f y s /\ pairmap f x [] = []`".

Lemma size_pairmap x s : `sizel (pairmap f x s) = sizel s`.
--Proof. by elim: s x => //= y s IHs x; rewrite IHs. Qed.
elim: s x => [|y s IHs] x; rewr pairmap size_nil //.
by rewrite !size_cons IHs.
Qed.

Lemma pairmap_cat x s1 s2 :
  `pairmap f x (s1 ++ s2) = pairmap f x s1 ++ pairmap f (last x s1) s2`.
--Proof. by elim: s1 x => //= y s1 IHs1 x; rewrite IHs1. Qed.
elim: s1 x => [|y s1 IHs1] x; rewr pairmap cat last // pairmap.
by rewrite IHs1.
Qed.

Lemma nth_pairmap s n : `n < sizel s ==>
  !x. nth x2 (pairmap f x s) n = f (nth x1 (x :: s) n) (nth x1 s n)`.
--Proof. by elim: s n => [|y s IHs] [|n] //= Hn x; apply: IHs. Qed.
elim: s n => [|y s IHs]; elim => [|n _]; rewr size_nil ltnn ltS0 // pairmap nth //.
by rewrite size_cons ltSS => /IHs Hn x.
Qed.

--Fixpoint scanl x s :=
--  if s is y :: s' then let x' := g x y in x' :: scanl x' s' else [::].
"let scanl = define `scanl g x (y :: s) = g x y :: scanl g (g x y) s /\ scanl g x [] = []`".

Lemma size_scanl x s : `sizel (scanl g x s) = sizel s`.
--Proof. by elim: s x => //= y s IHs x; rewrite IHs. Qed.
elim: s x => [|y s IHs] x; rewr scanl size_nil // size_cons.
by rewrite IHs.
Qed.

Lemma scanl_cat x s1 s2 :
  `scanl g x (s1 ++ s2) = scanl g x s1 ++ scanl g (foldl g x s1) s2`.
--Proof. by elim: s1 x => //= y s1 IHs1 x; rewrite IHs1. Qed.
by elim: s1 x => [|y s1 IHs1] x; rewr cat scanl cat foldl. Qed.

Lemma nth_scanl s n : `n < sizel s ==>
  !x. nth x1 (scanl g x s) n = foldl g x (take (SUC n) s)`.
--Proof. by elim: s n => [|y s IHs] [|n] Hn x //=; rewrite ?take0 ?IHs. Qed.
elim: s n => [|y s IHs]; elim => [|n _]; rewr size_nil ltnn ltS0 // scanl nth !take !foldl //.
by rewrite size_cons ltSS => /IHs Hn.
Qed.

Lemma scanlK :
  --(forall x, cancel (g x) (f x)) -> forall x, cancel (scanl x) (pairmap x).
  `(!x y. f x (g x y) = y) ==> (!x s. pairmap f x (scanl g x s) = s)`.
--Proof. by move=> Hfg x s; elim: s x => //= y s IHs x; rewrite Hfg IHs. Qed.
move => Hfg x s.
by elim: s x => [|y s IHs] x; rewr scanl pairmap.
Qed.

Lemma pairmapK :
  --(forall x, cancel (f x) (g x)) -> forall x, cancel (pairmap x) (scanl x).
  `(!x y. g x (f x y) = y) ==> (!x s. scanl g x (pairmap f x s) = s)`.
--Proof. by move=> Hgf x s; elim: s x => //= y s IHs x; rewrite Hgf IHs. Qed.
move => Hgf x s.
by elim: s x => [|y s IHs] x; rewr pairmap scanl.
Qed.

End Scan.

--Prenex Implicits mask map pmap foldr foldl scanl pairmap.

Section Zip.

--Variables S T : Type.

--Fixpoint zip (s : seq S) (t : seq T) {struct t} :=
--  match s, t with
--  | x :: s', y :: t' => (x, y) :: zip s' t'
--  | _, _ => [::]
--  end.
"let zip = define `zip (x :: s) (y :: t) = (x, y) :: zip s t /\
	zip [] t = [] /\ zip s [] = []`".

--Definition unzip1 := map (@fst S T).
--Definition unzip2 := map (@snd S T).
"let unzip1 = new_definition `unzip1 = map FST`".
"let unzip2 = new_definition `unzip2 = map SND`".

Lemma zip_unzip s : `zip (unzip1 s) (unzip2 s) = s`.
--Proof. by elim: s => [|[x y] s /= ->]. Qed.
elim: s => [|x s IHs]; rewr unzip1 unzip2 map zip // PAIR.
by rewrite -unzip1 -unzip2 IHs.
Qed.

Lemma unzip1_zip s t : `sizel s <= sizel t ==> unzip1 (zip s t) = s`.
--Proof. by elim: s t => [|x s IHs] [|y t] //= le_s_t; rewrite IHs. Qed.
elim: s t => [|x s IHs]; elim => [|y t _]; rewr size_nil size_cons -ltE ltn0 zip unzip1 map //.
by rewrite ltE leqSS /= -unzip1 => /IHs ->.
Qed.

Lemma unzip2_zip s t : `sizel t <= sizel s ==> unzip2 (zip s t) = t`.
--Proof. by elim: s t => [|x s IHs] [|y t] //= le_t_s; rewrite IHs. Qed.
elim: s t => [|x s IHs]; elim => [|y t _]; rewr size_nil size_cons -ltE ltn0 zip unzip2 map //.
by rewrite ltE leqSS /= -unzip2 => /IHs ->.
Qed.

Lemma size1_zip s t : `sizel s <= sizel t ==> sizel (zip s t) = sizel s`.
--Proof. by elim: s t => [|x s IHs] [|y t] //= Hs; rewrite IHs. Qed.
elim: s t => [|x s IHs]; elim => [|y t _]; rewr !size_nil size_cons -ltE ltn0 zip size_nil //.
by rewrite ltE leqSS size_cons => /IHs ->.
Qed.

Lemma size2_zip s t : `sizel t <= sizel s ==> sizel (zip s t) = sizel t`.
--Proof. by elim: s t => [|x s IHs] [|y t] //= Hs; rewrite IHs. Qed.
elim: s t => [|x s IHs]; elim => [|y t _]; rewr size_nil size_cons -ltE ltn0 zip size_nil //.
by rewrite ltE leqSS size_cons => /IHs ->.
Qed.

Lemma size_zip s t : `sizel (zip s t) = minn (sizel s) (sizel t)`.
--by elim: s t => [|x s IHs] [|t2 t] //=; rewrite IHs -add1n addn_minr.
elim: s t => [|x s IHs]; elim => [|t2 t _]; rewr zip size_nil minn ltnn /= size_cons gtS0 ltS0 //.
by rewrite -minn -add1n IHs addn_minr !add1n.
Qed.

Lemma zip_cat s1 s2 t1 t2 :
  `sizel s1 = sizel t1 ==> zip (s1 ++ s2) (t1 ++ t2) = zip s1 t1 ++ zip s2 t2`.
--Proof. by move/eqP; elim: s1 t1 => [|x s IHs] [|y t] //= /IHs->. Qed.
elim: s1 t1 => [|x s IHs]; elim => [|y t _]; rewr cat zip cat // size_nil size_cons;
		rewrite ?[`0 = _`]eq_sym ?eqS0 //.
by rewrite eqSS => /IHs ->.
Qed.

Lemma nth_zip x y s t i :
  `sizel s = sizel t ==> nth (x, y) (zip s t) i = (nth x s i, nth y t i)`.
--Proof. by move/eqP; elim: i s t => [|i IHi] [|y1 s1] [|y2 t] //= /IHi->. Qed.
elim: i s t => [|i IHi]; elim => [|y1 s1 _]; elim => [|y2 t _]; rewr zip nth //; 
	rewrite ?size_nil ?size_cons ?[`0 = _`]eq_sym ?eqS0 //.
by rewrite eqSS => /IHi ->.
Qed.

Lemma nth_zip_cond p s t i :
   `nth p (zip s t) i
     = (if i < sizel (zip s t) then (nth (FST p) s i, nth (SND p) t i) else p)`.
rewrite size_zip ltnNge leq_minl.
--by elim: s t i => [|x s IHs] [|y t] [|i] //=; rewrite ?orbT -?IHs.
elim: s t i => [|x s IHs]; elim => [|y t _]; elim => [|i _]; rewr nth size_nil !leqnn zip nth leq0n // size_cons -ltE ltn0 //.
by rewrite IHs !ltE !leqSS.
Qed.

Lemma zip_rcons s1 s2 z1 z2 :
    `sizel s1 = sizel s2 ==>
  zip (rcons s1 z1) (rcons s2 z2) = rcons (zip s1 s2) (z1, z2)`.
--Proof. by move=> eq_sz; rewrite -!cats1 zip_cat //= eq_sz. Qed.
by move => eq_sz; rewrite -!cats1 zip_cat //; rewr !zip. Qed.

Lemma rev_zip s1 s2 :
  `sizel s1 = sizel s2 ==> rev (zip s1 s2) = zip (rev s1) (rev s2)`.
--elim: s1 s2 => [|x s1 IHs] [|y s2] //= [eq_sz].
--by rewrite !rev_cons zip_rcons ?IHs ?size_rev.
elim: s1 s2 => [|x s1 IHs]; elim => [|y s2 _]; last first.
  rewrite !size_cons eqSS => eq_sz.
  by rewrite !rev_cons zip_rcons ?size_rev //; rewr zip rev_cons; rewrite IHs.
by rewr rev catrev zip catrev.
by rewr rev catrev zip catrev.
by rewr rev catrev zip catrev.
Qed.

End Zip.

--Prenex Implicits zip unzip1 unzip2.

Section Flatten.

--Variable T : Type.
--Implicit Types (s : seq T) (ss : seq (seq T)).
Implicit Type s : `:(A)list`.
Implicit Type ss : `:((A)list)list`.

--Definition flatten := foldr cat (Nil T).
--Definition shape := map (@size T).
--Fixpoint reshape sh s :=
--  if sh is n :: sh' then take n s :: reshape sh' (drop n s) else [::].
"let flatten = new_definition `flatten = foldr cat []`".
"let shape = new_definition `shape = map sizel`".
"let reshape = define `reshape (n :: sh) s = take n s :: reshape sh (dropl n s) /\
	reshape [] s = []`".

Lemma flatten0 : `flatten [] = []`. by rewr flatten foldr. Qed.
Lemma flatten_cons s ss : `flatten (s :: ss) = s ++ flatten ss`.
by rewr flatten foldr. Qed.

Lemma size_flatten ss : `sizel (flatten ss) = sumn (shape ss)`.
--Proof. by elim: ss => //= s ss <-; rewrite size_cat. Qed.
elim: ss => [|s ss IHs]; rewr flatten foldr shape map size_nil sumn0 //.
by rewrite -flatten size_cat IHs -shape; rewr sumn foldr.
Qed.

Lemma flatten_cat ss1 ss2 :
  `flatten (ss1 ++ ss2) = flatten ss1 ++ flatten ss2`.
--Proof. by elim: ss1 => //= s ss1 ->; rewrite catA. Qed.
elim: ss1 => [|s ss1 IHs]; rewr flatten0 cat // flatten_cons.
by rewrite IHs catA.
Qed.

Lemma flattenK ss : `reshape (shape ss) (flatten ss) = ss`.
--by elim: ss => //= s ss IHss; rewrite take_size_cat ?drop_size_cat ?IHss.
elim: ss => [|s ss IHss]; rewr flatten shape foldr map reshape //.
by rewrite take_size_cat // drop_size_cat // -flatten -shape IHss.
Qed.

Lemma reshapeKr sh s : `sizel s <= sumn sh ==> flatten (reshape sh s) = s`.
--elim: sh s => [[]|n sh IHsh] //= s sz_s; rewrite IHsh ?cat_take_drop //.
--by rewrite size_drop leq_sub_add.
elim: sh s => [|n sh IHsh s sz_s].
  by elim => [|x s _]; rewr reshape cat flatten0 // sumn0 size_cons -ltE ltn0.
rewr reshape flatten foldr -flatten.
rewrite IHsh ?cat_take_drop // size_drop leq_sub_add; move: sz_s.
by rewr sumn foldr.
Qed.

Lemma reshapeKl sh s : `sumn sh <= sizel s ==> shape (reshape sh s) = sh`.
--elim: sh s => [[]|n sh IHsh] //= s sz_s.
--rewrite size_takel; last exact: leq_trans (leq_addr _ _) sz_s.
--by rewrite IHsh // -(leq_add2l n) size_drop add_sub_maxn leq_maxr sz_s orbT.
elim: sh s => [|n sh IHsh s sz_s].
  by elim => [|x s _]; rewr reshape shape map.
move: sz_s; rewr sumn foldr -sumn => sz_s.
rewr reshape shape map -shape; rewrite size_takel.
  by apply: leq_trans sz_s; rewrite leq_addr.
by rewrite IHsh // -(leq_add2l n) size_drop add_sub_maxn leq_maxr sz_s orbT.
Qed.

End Flatten.

Section AllPairs.

--Variables (S T R : Type) (f : S -> T -> R).
--Implicit Types (s : seq S) (t : seq T).
Variable f : `:S->T->R`.
Implicit Type s : `:(S)list`.
Implicit Type t : `:(T)list`.

--Definition allpairs s t := foldr (fun x => cat (map (f x) t)) [::] s.
"let allpairs = new_definition `allpairs f s t = foldr (\x. cat (map (f x) t)) [] s`".

Lemma size_allpairs s t : `sizel (allpairs f s t) = sizel s * sizel t`.
--Proof. by elim: s => //= x s IHs; rewrite size_cat size_map IHs. Qed.
elim: s => [|x s IHs]; rewr allpairs foldr size_nil mul0n //.
by rewrite size_cat -allpairs IHs size_map size_cons mulSn.
Qed.

Lemma allpairs_cat s1 s2 t :
  `allpairs f (s1 ++ s2) t = allpairs f s1 t ++ allpairs f s2 t`.
--Proof. by elim: s1 => //= x s1 ->; rewrite catA. Qed.
elim: s1 => [|x s1 IHs]; rewr cat allpairs foldr cat //.
by rewrite -!allpairs IHs catA.
Qed.

End AllPairs.

Section EqAllPairs.

--Variables (S T R : eqType) (f : S -> T -> R).
--Implicit Types (s : seq S) (t : seq T).
Variable f : `:S->T->R`.
Implicit Type s : `:(S)list`.
Implicit Type t : `:(T)list`.

Lemma allpairsP s t z :
--  reflect (exists p, [/\ p.1 \in s, p.2 \in t & z = f p.1 p.2])
--          (z \in allpairs f s t).
`(z <- allpairs f s t) <=> (?p. FST p <- s /\ SND p <- t /\ z = f (FST p) (SND p))`.
--elim: s => [|x s IHs /=]; first by right=> [[p []]].
--rewrite mem_cat; have [fxt_z | not_fxt_z] := altP mapP.
--  by left; have [y t_y ->] := fxt_z; exists (x, y); rewrite mem_head.
--apply: (iffP IHs) => [] [[x' y] /= [s_x' t_y def_z]]; exists (x', y).
--  by rewrite !inE predU1r.
--by have [def_x' | //] := predU1P s_x'; rewrite def_z def_x' map_f in not_fxt_z.
--Qed.
elim: s => [|x s IHs]; rewr allpairs foldr in_nil //.
rewrite -allpairs mem_cat mapP IHs; split.
  case => [[y] [Hy ->]|[p] [p1 [p2 ->]]]; first by exists `(x, y)` => /=; rewrite in_cons.
  by exists p; rewrite in_cons.
rewrite in_cons; move => [p] [[p_s]] [p_t ->].
  by left; exists `SND p`.
by right; exists p.
Qed.

 

Lemma mem_allpairs s1 t1 s2 t2 :
  `(!x. x <- s1 <=> x <- s2) ==> (!y. y <- t1 <=> y <- t2) 
	==> (!p. p <- allpairs f s1 t1 <=> p <- allpairs f s2 t2)`.
move=> eq_s eq_t z.
--by apply/allpairsP/allpairsP=> [] [p fpz]; exists p; rewrite eq_s eq_t in fpz *.
rewrite !allpairsP; split => [] [p]; rewrite eq_s eq_t => fpz.
  by exists p.
by exists p.
Qed.

Lemma allpairs_catr s t1 t2 :
  `!p. p <- allpairs f s (t1 ++ t2) <=> p <- allpairs f s t1 ++ allpairs f s t2`.
move=> z; rewrite mem_cat.
--apply/allpairsP/orP=> [[p [sP1]]|].
--  by rewrite mem_cat; case/orP; [left | right]; apply/allpairsP; exists p.
--by case=> /allpairsP[p [sp1 sp2 ->]]; exists p; rewrite mem_cat sp2 ?orbT.
rewrite allpairsP; split => [[p [sP1]]|].
  by rewrite mem_cat => [] [[H] ->]; [left | right]; rewrite allpairsP; exists p.
case; rewrite allpairsP => [[p]] [sp1] [sp2 ->].
  by exists p; rewrite mem_cat sp2.
by exists p; rewrite mem_cat sp2.
Qed.

End EqAllPairs.

(*
Prenex Implicits flatten shape reshape allpairs.

Notation "[ 'seq' E | i <- s ]" := (map (fun i => E) s)
  (at level 0, i ident,
   format "[ '[hv' 'seq'  E '/ '  |   i  <-  s ] ']'") : form_scope.

Notation "[ 'seq' E | i <- s , j <- t ]" := (allpairs (fun i j => E) s t)
  (at level 0, i ident,
   format "[ '[hv' 'seq'  E '/ '  |   i  <-  s , '/ '  j  <-  t ] ']'")
   : form_scope.

Notation "[ 'seq' E | i <- s , C ]" :=
     (map (fun i => E) (filter (fun i => C) s))
  (at level 0, i ident,
   format "[ '[hv' 'seq'  E '/ '  |   i  <-  s , '/ '  C ] ']'")
   : form_scope.
*)

