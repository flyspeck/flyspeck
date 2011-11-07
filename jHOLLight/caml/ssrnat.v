(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

"needs \"caml/ssrbool.hl\"".

"prioritize_num()".

Lemma succnK n : `SUC n - 1 = n`. by arith. Qed.
Lemma succn_inj n m: `SUC n = SUC m ==> n = m`. by arith. Qed.

Lemma eqSS m n: `(SUC m = SUC n) = (m = n)`. by arith. Qed.

Lemma add0n n : `0 + n = n`. by arith. Qed.
Lemma addSn m n : `SUC m + n = SUC (m + n)`. by arith. Qed.
Lemma add1n n : `1 + n = SUC n`. by arith. Qed.
Lemma addn0 n : `n + 0 = n`. by arith. Qed.
Lemma addnS m n : `m + SUC n = SUC (m + n)`. by arith. Qed.
Lemma addSnnS m n : `SUC m + n = m + SUC n`. by arith. Qed.
Lemma addnCA m n p : `m + (n + p) = n + (m + p)`. by arith. Qed.
Lemma addnC m n : `m + n = n + m`.
by rewrite -{1}(addn0 n) addnCA addn0. Qed.
Lemma addn1 n : `n + 1 = SUC n`. by rewrite addnC add1n. Qed.
Lemma addnA n m p : `n + (m + p) = (n + m) + p`.
by rewrite [`m + p`]addnC addnCA addnC. Qed.
Lemma addnAC m n p: `(n + m) + p = (n + p) + m`.
by rewrite -!addnA [`p + m`]addnC. Qed.
Lemma addn_eq0 m n : `(m + n = 0) <=> (m = 0) /\ (n = 0)`. by arith. Qed.
Lemma eqn_addl p m n: `(p + m = p + n) <=> (m = n)`. by arith. Qed.
Lemma eqn_addr p m n: `(m + p = n + p) = (m = n)`. by arith. Qed.
Lemma addnI m n1 n2: `m + n1 = m + n2 ==> n1 = n2`.
by move => Heq; rewrite -(eqn_addl m). Qed.
Lemma addIn m n1 n2: `n1 + m = n2 + m ==> n1 = n2`.
rewrite -![`_1 + m`]addnC => Heq.
by move: (addnI Heq).
Qed.

Lemma sub0n n: `0 - n = 0`. by arith. Qed.
Lemma subn0 n: `n - 0 = n`. by arith. Qed.
Lemma subnn : `!n. n - n = 0`. by arith. Qed.

Lemma subSS : `!n m. SUC m - SUC n = m - n`. by arith. Qed.
Lemma subn_add2l : `!p m n. (p + m) - (p + n) = m - n`. by arith. Qed.
Lemma subn_add2r : `!p m n. (m + p) - (n + p) = m - n`.
move => p m n.
by rewrite -![`_1 + p`]addnC subn_add2l.
Qed.

Lemma addKn : `!n x. (n + x) - n = x`.
-- Proof. by move=> m; rewrite /= -{2}[n]addn0 subn_add2l subn0. Qed.
move => n m.
by rewrite -{2}[`n`]addn0 subn_add2l subn0.
Qed.

Lemma addnK : `!n x. (x + n) - n = x`.
-- Proof. by move=> m; rewrite /= (addnC m) addKn. Qed.
by move => n m; rewrite addnC addKn. Qed.

Lemma subSnn : `!n. SUC n - n = 1`.
-- Proof. exact (addnK n 1). Qed.
move => n.
by rewrite -add1n addnK. Qed.

Lemma subn_sub m n p: `(n - m) - p = n - (m + p)`.
-- Proof. by elim: m n => [|m IHm] [|n]; try exact (IHm n). Qed.
--move => m n p.
--elim: n m => [|m IHm]; case; arith.
by arith. Qed.

Lemma subnAC : `!m n p. (m - n) - p = (m - p) - n`.
-- Proof. by move=> m n p; rewrite !subn_sub addnC. Qed.
by move => m n p; rewrite !subn_sub addnC. Qed.

Lemma predn_sub : `!m n. (m - n) - 1 = m - SUC n`.
-- Proof. by rewrite -subn1 subn_sub addn1. Qed.
by move => m n; rewrite subn_sub addn1. Qed.

Lemma predn_subS : `!m n. (SUC m - n) - 1 = m - n`.
-- Proof. by rewrite predn_sub. Qed.
by rewrite predn_sub subSS. Qed.


Lemma ltnS : `!m n. (m < SUC n) = (m <= n)`. by arith. Qed.
Lemma leq0n : `!n. 0 <= n`. by arith. Qed.
Lemma ltn0Sn : `!n. 0 < SUC n`. by arith. Qed.
Lemma ltn0 : `!n. n < 0 <=> F`. by arith. Qed.
Lemma leqnn : `!n. n <= n`.
--Proof. by elim: n. Qed.
by arith. Qed.
Lemma ltnSn : `!n. n < SUC n`. by arith. Qed.
Lemma eq_leq : `!m n. m = n ==> m <= n`.
--Proof. by move->. Qed.
by move => m n ->; rewrite leqnn. Qed.
Lemma leqnSn : `!n. n <= SUC n`. by arith. Qed.
Lemma leq_pred : `!n. n - 1 <= n`. by arith. Qed.
Lemma leqSpred : `!n. n <= SUC (n - 1)`. by arith. Qed.

Lemma ltn_predK : `!m n. m < n ==> SUC (n - 1) = n`. by arith. Qed.
Lemma prednK : `!n. 0 < n ==> SUC (n - 1) = n`.
-- Proof. exact: ltn_predK. Qed.
move => n H; exact: (ltn_predK `0`). Qed.

Lemma leqNgt : `!m n. (m <= n) <=> ~(n < m)`.
-- Proof. by elim: m n => [|m IHm] [|n] //; exact: IHm n. Qed.
by arith. Qed.

Lemma ltnNge : `!m n. (m < n) = ~(n <= m)`.
-- Proof. by rewrite leqNgt. Qed.
move => m n; by rewrite leqNgt.
Qed.

Lemma ltnn : `!n. n < n <=> F`.
-- Proof. by rewrite ltnNge leqnn. Qed.
by move => n; rewrite ltnNge leqnn. Qed.

Lemma leqn0 : `!n. (n <= 0) = (n = 0)`. by arith. Qed.
Lemma lt0n : `!n. (0 < n) = ~(n = 0)`. by arith. Qed.
Lemma lt0n_neq0 : `!n. 0 < n ==> ~(n = 0)`. by arith. Qed.
Lemma eqn0Ngt : `!n. (n = 0) = ~(0 < n)`. by arith. Qed.
Lemma neq0_lt0n : `!n. (n = 0) = F ==> 0 < n`. by arith. Qed.

Lemma eqn_leq : `!m n. (m = n) = (m <= n /\ n <= m)`.
--Proof. elim: m n => [|m IHm] [|n] //; exact: IHm n. Qed.
by arith. Qed.

Lemma anti_leq : `!m n. m <= n /\ n <= m ==> m = n`.
-- Proof. by move=> m n; rewrite -eqn_leq => /eqP. Qed.
by move => m n; rewrite -eqn_leq. Qed.

Lemma neq_ltn : `!m n. ~(m = n) <=> (m < n) \/ (n < m)`.
-- Proof. by rewrite eqn_leq negb_and orbC -!ltnNge. Qed.
move => m n.
by rewrite eqn_leq negb_and orbC -!ltnNge. Qed.

Lemma leq_eqVlt m n: `(m <= n) <=> (m = n) \/ (m < n)`.
--Proof. elim: m n => [|m IHm] [|n] //; exact: IHm n. Qed.
by arith. Qed.

Lemma eq_sym : `!x y:A. x = y <=> y = x`. by move: EQ_SYM_EQ. Qed.

Lemma ltn_neqAle : `!m n. (m < n) <=> ~(m = n) /\ (m <= n)`.
--Proof. by rewrite ltnNge leq_eqVlt negb_or -leqNgt eq_sym. Qed.
move => m n.
by rewrite ltnNge leq_eqVlt negb_or -leqNgt [`n = m`]eq_sym.
Qed.

Lemma leq_trans : `!n m p. m <= n ==> n <= p ==> m <= p`.
--Proof. by elim: n m p => [|i IHn] [|m] [|p] //; exact: IHn m p. Qed.
by arith. Qed.

Lemma ltE : `!n m. n < m <=> SUC n <= m`. by arith. Qed.
Lemma leqSS : `!n m. SUC n <= SUC m <=> n <= m`. by arith. Qed.

Lemma leq_ltn_trans : `!n m p. m <= n ==> n < p ==> m < p`.
-- Proof. move=> Hmn; exact: leq_trans. Qed.
move => n m p Hmn.
by rewrite !ltE; apply: leq_trans; by rewrite leqSS.
Qed.

Lemma ltn_leq_trans n m p : `m < n ==> n <= p ==> m < p`. by arith. Qed.

Lemma ltnW : `!m n. m < n ==> m <= n`.
--Proof. exact: leq_trans. Qed.
by move => m n; rewrite ltE; apply: leq_trans; rewrite leqnSn.
Qed.

Lemma leqW : `!m n. m <= n ==> m <= SUC n`.
--Proof. by move=> le_mn; exact: ltnW. Qed.
by move => m n le_mn; apply: ltnW; rewrite ltE leqSS.
Qed.

Lemma ltn_trans : `!n m p. m < n ==> n < p ==> m < p`.
--Proof. by move=> lt_mn /ltnW; exact: leq_trans. Qed.
move => n m p lt_mn.
move/ltnW; rewrite ltE.
by apply: leq_trans; rewrite -ltE.
Qed.


Lemma geqE : `!m n. m >= n <=> n <= m`. by arith. Qed.
Lemma gtE m n: `m > n <=> n < m`. arith. Qed.

Lemma leq_total m n: `(m <= n) \/ (n <= m)`.
--Proof. by rewrite -implyNb -ltnNge; apply/implyP; exact: ltnW. Qed.
by rewrite -implyNb -ltnNge => lt_nm; exact: ltnW. Qed.


Lemma leqP m n: `m <= n \/ n < m`. by arith. Qed.
Lemma ltnP m n: `m < n \/ n <= m`. by arith. Qed.
Lemma posnP n: `n = 0 \/ 0 < n`. by arith. Qed.
Lemma ltngtP m n: `m < n \/ n < m \/ m = n`. by arith. Qed.


--(* Monotonicity lemmas *)

--Definition monotone f := forall m n, (f m <= f n) = (m <= n).

Lemma leq_add2l : `!p m n. (p + m <= p + n) = (m <= n)`. by arith. Qed.

Lemma ltn_add2l : `!p m n. (p + m < p + n) = (m < n)`.
--Proof. by rewrite -addnS; exact: leq_add2l. Qed.
move => p m n.
by rewrite !ltE -addnS leq_add2l.
Qed.

Lemma leq_add2r : `!p m n. (m + p <= n + p) = (m <= n)`.
--Proof. by rewrite -!(addnC p); exact: leq_add2l. Qed.
move => p m n.
by rewrite -![`_1 + p`]addnC leq_add2l.
Qed.

Lemma ltn_add2r : `!p m n. (m + p < n + p) = (m < n)`.
--Proof. exact: leq_add2r p m.+1 n. Qed.
move => p m n.
by rewrite !ltE -addSn leq_add2r.
Qed.

Lemma leq_add : `!m1 m2 n1 n2. m1 <= n1 ==> m2 <= n2 ==> m1 + m2 <= n1 + n2`.
--Proof. by move=> le_mn1 le_mn2; rewrite (@leq_trans (m1 + n2)) ?leq_add2l ?leq_add2r. Qed.
move => m1 m2 n1 n2 le_mn1 le_mn2.
by rewrite (leq_trans `m1 + n2`) leq_add2l leq_add2r. Qed.

Lemma leq_addr : `!m n. n <= n + m`.
--Proof. by rewrite -{1}[n]addn0 leq_add2l. Qed.
move => m n.
by rewrite -{1}[`n`]addn0 leq_add2l leq0n. Qed.

Lemma leq_addl : `!m n. n <= m + n`.
--Proof. by rewrite addnC leq_addr. Qed.
by rewrite addnC leq_addr. Qed.

Lemma ltn_addr m n p: `m < n ==> m < n + p`.
--Proof. by move/leq_trans=> -> //; exact: leq_addr. Qed.
rewrite !ltE; move/leq_trans => ->; rewrite leq_addr. Qed.

Lemma ltn_addl : `!m n p. m < n ==> m < p + n`. by arith. Qed.

Lemma addn_gt0 : `!m n. (0 < m + n) <=> (0 < m) \/ (0 < n)`.
--Proof. by rewrite !lt0n -negb_and addn_eq0. Qed.
move => m n.
by rewrite !lt0n -negb_and addn_eq0. Qed.

Lemma subn_gt0 m n: `(0 < n - m) = (m < n)`.
--Proof. by elim: m n => [|m IHm] [|n] //; exact: IHm n. Qed.
by arith. Qed.

Lemma subn_eq0 : `!m n. (m - n = 0) = (m <= n)`. by arith. Qed.

Lemma leqE : `!m n. m <= n <=> m - n = 0`. by arith. Qed.

Lemma leq_sub_add : `!m n p. (m - n <= p) = (m <= n + p)`.
--Proof. by rewrite -subn_eq0 subn_sub. Qed.
move => m n p.
by rewrite -subn_eq0 subn_sub -leqE. Qed.

Lemma leq_subr : `!m n. n - m <= n`.
by rewrite leq_sub_add leq_addl. Qed.

Lemma subnKC : `!m n. m <= n ==> m + (n - m) = n`.
--Proof. by elim: m n => [|m IHm] [|n] // /(IHm n) {2}<-. Qed.
by arith. Qed.

Lemma subnK : `!m n. m <= n ==> (n - m) + m = n`.
--Proof. by rewrite addnC; exact: subnKC. Qed.
by rewrite addnC; exact: subnKC. Qed.

Lemma addn_subA : `!m n p. p <= n ==> m + (n - p) = (m + n) - p`.
--Proof. by move=> le_pn; rewrite -{2}(subnK le_pn) addnA addnK. Qed.
move => m n p le_pn.
by rewrite -{2}(subnK le_pn) addnA addnK. Qed.

Lemma subn_subA : `!m n p. p <= n ==> m - (n - p) = (m + p) - n`.
--Proof. by move=> le_pn; rewrite -{2}(subnK le_pn) subn_add2r. Qed.
move => m n p le_pn.
by rewrite -{2}(subnK le_pn) subn_add2r. Qed.

Lemma subKn : `!m n. m <= n ==> n - (n - m) = m`.
--Proof. by move/subn_subA->; rewrite addKn. Qed.
move => m n.
by move/(subn_subA n) => ->; rewrite addKn. Qed.

Lemma leq_subS : `!m n. m <= n ==> SUC n - m = SUC (n - m)`.
--Proof. by rewrite -add1n => /addn_subA <-. Qed.
move => m n.
rewrite -add1n; move/(addn_subA `1`) => <-.
by rewrite add1n. Qed.

Lemma ltn_subS : `!m n. m < n ==> n - m = SUC (n - SUC m)`.
--Proof. exact: leq_subS m.+1 n. Qed.
by move => m n lt_mn; rewrite -leq_subS ?subSS // -ltE.
Qed.

Lemma leq_sub2r : `!p m n. m <= n ==> m - p <= n - p`.
-- by move=> le_mn; rewrite leq_sub_add (leq_trans le_mn) // -leq_sub_add. Qed.
move => p m n le_mn.
by rewrite leq_sub_add (leq_trans le_mn) -leq_sub_add leqnn. Qed.


Lemma leq_sub2l : `!p m n. m <= n ==> p - n <= p - m`.
--Proof.
--rewrite -(leq_add2r (p - m)) leq_sub_add.
--by apply: leq_trans; rewrite -leq_sub_add.
--Qed.
move => p m n.
rewrite -(leq_add2r `p - m`) leq_sub_add.
by apply: leq_trans; rewrite -leq_sub_add leqnn.
Qed.


Lemma leq_sub2 : `!m1 m2 n1 n2. m1 <= m2 ==> n2 <= n1 ==> m1 - n1 <= m2 - n2`.
-- by move/(leq_sub2r n1)=> le_m12; move/(leq_sub2l m2); exact: leq_trans.
move => m1 m2 n1 n2.
move/(leq_sub2r n1) => le_m12; move/(leq_sub2l m2); exact: leq_trans. Qed.

Lemma ltn_sub2r : `!p m n. p < n ==> m < n ==> m - p < n - p`.
--Proof. by move/ltn_subS->; exact: (@leq_sub2r p.+1). Qed.
move => p m n.
move/ltn_subS => ->; rewrite !ltE leqSS.
by move/(leq_sub2r `SUC p`); rewrite subSS.
Qed.

Lemma ltn_sub2l : `!p m n. m < p ==> m < n ==> p - n < p - m`.
--Proof. by move/ltn_subS->; exact: leq_sub2l. Qed.
move => p m n.
move/ltn_subS => ->; rewrite !ltE leqSS.
by move/(leq_sub2l p).
Qed.

Lemma ltn_add_sub : `!m n p. (m + n < p) = (n < p - m)`.
--Proof. by rewrite !ltnNge leq_sub_add. Qed.
move => m n p.
by rewrite !ltnNge leq_sub_add. Qed.

--(* Eliminating the idiom for structurally decreasing compare and subtract. *)
--Lemma subn_if_gt T m n F (E : T) :
--  (if m.+1 - n is m'.+1 then F m' else E) = (if n <= m then F (m - n) else E).
--Proof.
--by case: leqP => [le_nm | /eqnP-> //]; rewrite -{1}(subnK le_nm) -addSn addnK.
--Qed.

--(* Max and min *)

--Definition maxn m n := if m < n then n else m.

--Definition minn m n := if m < n then m else n.
"let maxn = new_definition `maxn m n = if m < n then n else m`".
"let minn = new_definition `minn m n = if m < n then m else n`".

Lemma max0n : `!n. maxn 0 n = n`. by rewrite maxn; arith. Qed.
Lemma maxn0 : `!n. maxn n 0 = n`. by rewrite maxn; arith. Qed.

Lemma maxnC : `!m n. maxn m n = maxn n m`. by rewrite !maxn; arith. Qed.

Lemma maxnl : `!m n. n <= m ==> maxn m n = m`.
--Proof. by rewrite /maxn; case leqP. Qed.
by rewrite maxn; arith. Qed.

Lemma maxnr : `!m n. m <= n ==> maxn m n = n`. by rewrite maxn; arith. Qed.

Lemma add_sub_maxn : `!m n. m + (n - m) = maxn m n`.
--Proof. by rewrite /maxn addnC; case: leqP => [/eqnP-> | /ltnW/subnK]. Qed.
by rewrite maxn; arith. Qed.

Lemma maxnAC : `!m n p. maxn (maxn m n) p = maxn (maxn m p) n`.
--by move=> m n p; rewrite -!add_sub_maxn -!addnA -!subn_sub !add_sub_maxn maxnC.
move => m n p.
by rewrite -!add_sub_maxn -!addnA -!subn_sub !add_sub_maxn maxnC.
Qed.

Lemma maxnA : `!m n p. maxn m (maxn n p) = maxn (maxn m n) p`.
--Proof. by move=> m n p; rewrite !(maxnC m) maxnAC. Qed.
move => m n p.
by rewrite ![`maxn m _1`]maxnC maxnAC. Qed.

Lemma maxnCA : `!m n p. maxn m (maxn n p) = maxn n (maxn m p)`.
--Proof. by move=> m n p; rewrite !maxnA (maxnC m). Qed.
by move => m n p; rewrite !maxnA [`maxn m _1`]maxnC. Qed.

Lemma eqn_maxr : `!m n. (maxn m n = n) = (m <= n)`.
--Proof. by rewrite maxnC -{2}[n]addn0 -add_sub_maxn eqn_addl. Qed.
move => m n.
by rewrite maxnC -{2}[`n`]addn0 -add_sub_maxn eqn_addl leqE. Qed.

Lemma eqn_maxl : `!m n. (maxn m n = m) = (n <= m)`.
--Proof. by rewrite -{2}[m]addn0 -add_sub_maxn eqn_addl. Qed.
move => m n.
by rewrite -{2}[`m`]addn0 -add_sub_maxn eqn_addl leqE. Qed.

Lemma maxnn : `!n. maxn n n = n`.
--Proof. by move=> n; rewrite maxnl. Qed.
move => n.
by rewrite maxnl // leqnn. Qed.

Lemma leq_maxr m n1 n2: `(m <= maxn n1 n2) <=> (m <= n1) \/ (m <= n2)`.
--Proof.
--wlog le_n21: n1 n2 / n2 <= n1.
--  by case/orP: (leq_total n2 n1) => le_n12; last rewrite maxnC orbC; auto.
--rewrite /maxn ltnNge le_n21 /=; case: leqP => // lt_m_n1.
--by rewrite leqNgt (leq_trans _ lt_m_n1).
--Qed.
wlog le_n21: n1 n2 / `n2 <= n1`.
  by case: (leq_total n2 n1) => le_n12; last rewrite maxnC orbC; rewrite le_n21.
move => le_n21.
rewrite maxn ltnNge le_n21 /=; case: (EXCLUDED_MIDDLE `m <= n1`) => /=.
by apply: contra; move/leq_trans => /(_ n1).
Qed.


Lemma leq_maxl m n1 n2 : `(maxn n1 n2 <= m) <=> (n1 <= m) /\ (n2 <= m)`.
--Proof. by rewrite leqNgt leq_maxr negb_or -!leqNgt. Qed.
by rewrite leqNgt ltE leq_maxr negb_or -!ltE -!leqNgt. Qed.

Lemma addn_maxl : `!m1 m2 n. (maxn m1 m2) + n = maxn (m1 + n) (m2 + n)`.
--Proof. by move=> m1 m2 n; rewrite -!add_sub_maxn subn_add2r addnAC. Qed.
by move => m1 m2 n; rewrite -!add_sub_maxn subn_add2r addnAC. Qed.

Lemma addn_maxr : `!m n1 n2. m + maxn n1 n2 = maxn (m + n1) (m + n2)`.
by move=> m n1 n2; rewrite ![`m + _1`]addnC addn_maxl. Qed.

Lemma min0n n: `minn 0 n = 0`. by rewrite minn; arith. Qed.
Lemma minn0 n: `minn n 0 = 0`. by rewrite minn; arith. Qed.

Lemma minnC m n: `minn m n = minn n m`.
by rewrite !minn; arith. Qed.

Lemma minnr m n : `n <= m ==> minn m n = n`. by rewrite minn; arith. Qed.

Lemma minnl m n : `m <= n ==> minn m n = m`. 
--Proof. by move/minnr; rewrite minnC. Qed.
by move/minnr; rewrite minnC. Qed.

Lemma addn_min_max m n : `minn m n + maxn m n = m + n`.
--Proof. by rewrite /minn /maxn; case: ltngtP => // [_|->] //; exact: addnC. Qed.
by rewrite minn maxn; arith. Qed.

Lemma minn_to_maxn m n : `minn m n = (m + n) - maxn m n`.
by rewrite -addn_min_max addnK. Qed.

Lemma sub_sub_minn m n : `m - (m - n) = minn m n`.
by rewrite minnC minn_to_maxn -add_sub_maxn subn_add2l. Qed.

Lemma minnCA : `!m1 m2 m3. minn m1 (minn m2 m3) = minn m2 (minn m1 m3)`.
--Proof.
--move=> m1 m2 m3; rewrite !(minn_to_maxn _ (minn _ _)).
--rewrite -(subn_add2r (maxn m2 m3)) -(subn_add2r (maxn m1 m3) (m2 + _)) -!addnA.
--by rewrite !addn_maxl !addn_min_max !addn_maxr addnCA maxnAC (addnC m2 m1).
--Qed.
move => m1 m2 m3; rewrite ![`minn _1 (minn _2 _3)`]minn_to_maxn.
rewrite -(subn_add2r `maxn m2 m3`) -[`(m2 + _1) - _2`](subn_add2r `maxn m1 m3`) -!addnA.
by rewrite !addn_maxl !addn_min_max !addn_maxr addnCA maxnAC [`m2 + m1`]addnC.
Qed.

Lemma minnA : `!m1 m2 m3. minn m1 (minn m2 m3) = minn (minn m1 m2) m3`.
move=> m1 m2 m3.
by rewrite [`minn m2 _1`]minnC minnCA minnC. Qed.

Lemma minnAC m1 m2 m3: `minn (minn m1 m2) m3 = minn (minn m1 m3) m2`.
by rewrite minnC minnCA minnA. Qed.

Lemma eqn_minr m n : `(minn m n = n) = (n <= m)`.
--by rewrite -(eqn_addr m) eq_sym addnC -addn_min_max eqn_addl eqn_maxl.
rewrite -(eqn_addr m).
by rewrite -[`n + m`]addn_min_max minnC eqn_addl [`m = _1`]eq_sym maxnC eqn_maxl. Qed.

Lemma eqn_minl m n : `(minn m n = m) = (m <= n)`.
--by rewrite -(eqn_addr n) eq_sym -addn_min_max eqn_addl eqn_maxr. Qed.
by rewrite -(eqn_addr n) [`_1 = m + n`]eq_sym -addn_min_max eqn_addl eqn_maxr. Qed.

Lemma minnn n: `minn n n = n`.
by rewrite minnr // leqnn. Qed.

Lemma leq_minr m n1 n2 : `(m <= minn n1 n2) <=> (m <= n1) /\ (m <= n2)`.
--Proof.
--wlog le_n21: n1 n2 / n2 <= n1.
--  by case/orP: (leq_total n2 n1) => ?; last rewrite minnC andbC; auto.
--by rewrite /minn ltnNge le_n21 /= andbC; case: leqP => // /leq_trans->.
--Qed.
by rewrite minn; arith. Qed.

Lemma leq_minl m n1 n2 : `(minn n1 n2 <= m) <=> (n1 <= m) \/ (n2 <= m)`.
--by rewrite leqNgt leq_minr negb_and -!leqNgt. Qed.
by rewrite leqNgt ltE leq_minr -!ltE negb_and -!leqNgt. Qed.

Lemma addn_minl : `!m1 m2 n. (minn m1 m2) + n = minn (m1 + n) (m2 + n)`.
move=> m1 m2 n; rewrite !minn_to_maxn -addn_maxl addnA subn_add2r addnAC.
by rewrite -![`_1 + n`](addnC n) addn_subA // -addn_min_max leq_addl.
Qed.

Lemma addn_minr : `!m n1 n2. m + minn n1 n2 = minn (m + n1) (m + n2)`.
move=> m n1 n2.
by rewrite ![`m + _1`](addnC m) addn_minl. Qed.

(* Quasi-cancellation (really, absorption) lemmas *)
Lemma maxnK m n : `minn (maxn m n) m = m`.
--by rewrite minnr // leq_maxr leqnn. Qed.
by rewrite minnr // leq_maxr leqnn. Qed.

Lemma maxKn m n : `minn n (maxn m n) = n`.
Proof. by rewrite minnC maxnC maxnK. Qed.

Lemma minnK m n : `maxn (minn m n) m = m`.
Proof. by rewrite maxnr // leq_minl leqnn. Qed.

Lemma minKn m n : `maxn n (minn m n) = n`.
Proof. by rewrite minnC maxnC minnK. Qed.

(* Distributivity. *)

Lemma maxn_minl m1 m2 n: `maxn (minn m1 m2) n = minn (maxn m1 n) (maxn m2 n)`.
--Proof.
--move=> m1 m2 n; wlog le_m21: m1 m2 / m2 <= m1.
--  move=> IH; case/orP: (leq_total m2 m1) => /IH //.
--  by rewrite minnC [in R in _ = R]minnC.
--apply/eqP; rewrite /minn ltnNge le_m21 eq_sym eqn_minr leq_maxr !leq_maxl.
--by rewrite le_m21 leqnn andbT; case: leqP => // /ltnW/(leq_trans le_m21)->.
--Qed.
(*have wlog: `!P G. (P ==> G) /\ ((P ==> G) ==> G) ==> G`; first by "MESON_TAC[]".
apply: (wlog `m2 <= m1`); split; first last.
  move => IH; case: (leq_total m2 m1); rewrite ?geqE.
	by move/IH.*)
rewrite !maxn !minn; arith. Qed.
  

Lemma maxn_minr m n1 n2: `maxn m (minn n1 n2) = minn (maxn m n1) (maxn m n2)`.
Proof. by rewrite ![`maxn m _1`](maxnC m) maxn_minl. Qed.

Lemma minn_maxl : `!m1 m2 n. minn (maxn m1 m2) n = maxn (minn m1 n) (minn m2 n)`.
by move => m1 m2 n; rewrite maxn_minr !maxn_minl -minnA maxnn [`maxn _1 n`]maxnC !maxnK.
Qed.

Lemma minn_maxr : `!m n1 n2. minn m (maxn n1 n2) = maxn (minn m n1) (minn m n2)`.
move=> m n1 n2.
by rewrite ![`minn m _1`](minnC m) minn_maxl. Qed.

(* Getting a concrete value from an abstract existence proof. *)
(*
Section ExMinn.

Variable P : `:num -> bool`.
Hypothesis exP : `?n. P n`.

Lemma find_ex_minn : `?m. P m /\ !n. P n ==> n >= m`.
--{m | P m & forall n, P n -> n >= m}.
--Proof.
--have: forall n, P n -> n >= 0 by [].
--have: acc_nat 0.
--  case exP => n; rewrite -(addn0 n); elim: n 0 => [|n IHn] j; first by left.
--  rewrite addSnnS; right; exact: IHn.
--move: 0; fix 2 => m IHm m_lb; case Pm: (P m); first by exists m.
--apply: find_ex_minn m.+1 _ _ => [|n Pn]; first by case: IHm; rewrite ?Pm.
--by rewrite ltn_neqAle m_lb //; case: eqP Pm => // -> /idP[].
--Qed.
have: `!n. P n ==> n >= 0`; first by arith.
move: exP.


Definition ex_minn := s2val find_ex_minn.

Inductive ex_minn_spec : nat -> Type :=
  ExMinnSpec m of P m & (forall n, P n -> n >= m) : ex_minn_spec m.

Lemma ex_minnP : ex_minn_spec ex_minn.
Proof. by rewrite /ex_minn; case: find_ex_minn. Qed.

End ExMinn.

Section ExMaxn.

Variables (P : pred nat) (m : nat).
Hypotheses (exP : exists i, P i) (ubP : forall i, P i -> i <= m).

Lemma ex_maxn_subproof : exists i, P (m - i).
Proof. by case: exP => i Pi; exists (m - i); rewrite subKn ?ubP. Qed.

Definition ex_maxn := m - ex_minn ex_maxn_subproof.

CoInductive ex_maxn_spec : nat -> Type :=
  ExMaxnSpec i of P i & (forall j, P j -> j <= i) : ex_maxn_spec i.

Lemma ex_maxnP : ex_maxn_spec ex_maxn.
Proof.
rewrite /ex_maxn; case: ex_minnP => i Pmi min_i; split=> // j Pj.
have le_i_mj: i <= m - j by rewrite min_i // subKn // ubP.
rewrite -subn_eq0 subn_subA ?(leq_trans le_i_mj) ?leq_subr //.
by rewrite addnC -subn_subA ?ubP.
Qed.

End ExMaxn.

Lemma eq_ex_minn P Q exP exQ : P =1 Q -> @ex_minn P exP = @ex_minn Q exQ.
Proof.
move=> eqPQ; case: ex_minnP => m1 Pm1 m1_lb; case: ex_minnP => m2 Pm2 m2_lb.
by apply/eqP; rewrite eqn_leq m1_lb (m2_lb, eqPQ) // -eqPQ.
Qed.

Lemma eq_ex_maxn (P Q : pred nat) m n exP ubP exQ ubQ :
  P =1 Q -> @ex_maxn P m exP ubP = @ex_maxn Q n exQ ubQ.
Proof.
move=> eqPQ; case: ex_maxnP => i Pi max_i; case: ex_maxnP => j Pj max_j.
by apply/eqP; rewrite eqn_leq max_i ?eqPQ // max_j -?eqPQ.
Qed.
*)

Section Iteration.

Variables m n : `:num`.
Variables x y : `:A`.

--Definition iter n f x :=
--  let fix loop m := if m is i.+1 then f (loop i) else x in loop n.
"let iter = define `iter (SUC n) f (x:A) = f (iter n f x) /\ iter 0 f x = x`".

--Definition iteri n f x :=
--  let fix loop m := if m is i.+1 then f i (loop i) else x in loop n.
"let iteri = define `iteri (SUC n) f (x:A) = f n (iteri n f x) /\ iteri 0 f x = x`".

--Definition iterop n op x :=
--  let f i y := if i is 0 then x else op x y in iteri n f.

Lemma iterSr n f x : `iter (SUC n) f (x : A) = iter n f (f x)`.
--Proof. by elim: n => //= n <-. Qed.
by elim: n; rewr !iter => n <-. Qed.

Lemma iterS n f x : `iter (SUC n) f (x:A) = f (iter n f x)`.
by rewr iter. Qed.

Lemma iter_add n m f x : `iter (n + m) f (x:A) = iter n f (iter m f x)`.
--Proof. by elim: n => //= n ->. Qed.
by elim: n; rewr !iter add0n // addSn => n <-; rewrite iterS. Qed.

Lemma iteriS n f x : `iteri (SUC n) f x = f n (iteri n f (x:A))`.
--Proof. by []. Qed.
by rewr iteri. Qed.

--Lemma iteropS idx n op x : iterop n.+1 op x idx = iter n (op x) x.
--Proof. by elim: n => //= n ->. Qed.

--Lemma eq_iter f f' : f =1 f' -> forall n, iter n f =1 iter n f'.
--Proof. by move=> eq_f n x; elim: n => //= n ->; rewrite eq_f. Qed.

--Lemma eq_iteri f f' : f =2 f' -> forall n, iteri n f =1 iteri n f'.
--Proof. by move=> eq_f n x; elim: n => //= n ->; rewrite eq_f. Qed.

--Lemma eq_iterop n op op' : op =2 op' -> iterop n op =2 iterop n op'.
--Proof. by move=> eq_op x; apply: eq_iteri; case. Qed.

End Iteration.


(* Multiplication. *)

Lemma mul0n n: `0 * n = 0`. Proof. by arith. Qed.
Lemma muln0 n: `n * 0 = 0`. Proof. by arith. Qed.
Lemma mul1n n: `1 * n = n`. by arith. Qed.
Lemma mulSn m n : `SUC m * n = n + m * n`. arith. Qed.
Lemma mulSnr m n : `SUC m * n = m * n + n`. arith. Qed.

Lemma mulnS m n : `m * SUC n = m + m * n`.
--Proof. by elim: m => // m; rewrite !mulSn !addSn addnCA => ->. Qed.
elim: m; rewrite ?mul0n ?addn0 // => m.
by rewrite !mulSn !addSn addnCA => ->. Qed.

Lemma mulnSr m n : `m * SUC n = m * n + m`.
Proof. by rewrite addnC mulnS. Qed.

Lemma muln1 n: `n * 1 = n`.
--Proof. by rewrite mulnSr muln0. Qed.
by rewrite "ARITH_RULE `1 = SUC 0`" mulnSr muln0 add0n. Qed.

Lemma mulnC : `!m n. m * n = n * m`.
--by move=> m n; elim: m => [|m]; rewrite (muln0, mulnS) // mulSn => ->.
move => m n.
by elim: m => [|m]; rewrite ?muln0 ?mulnS ?mul0n // mulSn => ->.
Qed.


Lemma muln_addl m1 m2 n: `(m1 + m2) * n = m1 * n + m2 * n`.
--Proof. by move=> m1 m2 n; elim: m1 => //= m1 IHm; rewrite -addnA -IHm. Qed.
elim: m1 => [|m1 IHm]; first by rewrite mul0n !add0n.
by rewrite mulSn -addnA -IHm -mulSn addSn. Qed.

Lemma muln_addr m n1 n2: `m * (n1 + n2) = m * n1 + m * n2`.
--Proof. by move=> m n1 n2; rewrite !(mulnC m) muln_addl. Qed.
by rewrite ![`m * _1`]mulnC muln_addl. Qed.

Lemma muln_subl : `!m n p. (m - n) * p = m * p - n * p`.
Proof.
move => m n [|n']; first by rewrite !muln0 subn0.
--by elim: m n => // [m IHm] [|n] //; rewrite mulSn subn_add2l -IHm.
elim: m n => [|m IHm] [|n]; rewrite ?(mul0n, sub0n, subn0) // !mulSn subn_add2l.
by rewrite -IHm subSS.
Qed.

Lemma muln_subr : `!m n p. m * (n - p) = m * n - m * p`.
Proof. by move=> m n p; rewrite ![`m * _1`]mulnC muln_subl. Qed.

Lemma mulnA : `!m n p. m * (n * p) = (m * n) * p`.
--Proof. by move=> m n p; elim: m => //= m; rewrite mulSn muln_addl => ->. Qed.
move => m n p.
elim: m => [|m]; first by rewrite !mul0n.
by rewrite !mulSn muln_addl => ->.
Qed.


Lemma mulnCA m n1 n2: `m * (n1 * n2) = n1 * (m * n2)`.
Proof. by rewrite !mulnA [`m * _1`](mulnC m). Qed.

Lemma mulnAC m n p: `(n * m) * p = (n * p) * m`.
by rewrite -!mulnA [`p * _1`]mulnC. Qed.

Lemma muln_eq0 m n : `(m * n = 0) <=> (m = 0) \/ (n = 0)`.
--Proof. by case: m n => // m [|n] //=; rewrite muln0. Qed.
case: m n => [|m] [|n]; rewrite ?(muln0, mul0n) //; arith. Qed.


Lemma eqn_mul1 m n : `(m * n = 1) <=> (m = 1) /\ (n = 1)`.
--Proof. by case: m n => [|[|m]] [|[|n]] //; rewrite muln0. Qed.
by case: m n => [|[|m]] [|[|n]]; arith. Qed.


Lemma muln_gt0 m n : `(0 < m * n) <=> (0 < m) /\ (0 < n)`.
--Proof. by case: m n => // m [|n] //=; rewrite muln0. Qed.
by case: m n => [|m] [|n]; arith. Qed.

Lemma leq_pmull m n : `0 < n ==> m <= n * m`.
--Proof. by move/prednK <-; exact: leq_addr. Qed.
by move/prednK => <-; rewrite mulSn leq_addr. Qed.

Lemma leq_pmulr m n : `0 < n ==> m <= m * n`.
--Proof. by move/leq_pmull; rewrite mulnC. Qed.
by move/(leq_pmull m); rewrite mulnC. Qed.

Lemma leq_mul2l m n1 n2 : `(m * n1 <= m * n2) <=> (m = 0) \/ (n1 <= n2)`.
--Proof. by rewrite {1}/leq -muln_subr muln_eq0. Qed.
by rewrite leqE -muln_subr muln_eq0 -leqE. Qed.

Lemma leq_mul2r m n1 n2 : `(n1 * m <= n2 * m) <=> (m = 0) \/ (n1 <= n2)`.
Proof. by rewrite -![`_1 * m`](mulnC m) leq_mul2l. Qed.

Lemma leq_mul m1 m2 n1 n2 : `m1 <= n1 ==> m2 <= n2 ==> m1 * m2 <= n1 * n2`.
Proof.
move=> le_mn1 le_mn2.
--apply: (leq_trans `m1 * n2`).
--  by rewrite leq_mul2l le_mn2 orbT.
--by rewrite leq_mul2r le_mn1 orbT.
move: (leq_trans `m1 * n2` `m1 * m2` `n1 * n2`).
"ANTS_TAC"; first by rewrite leq_mul2l le_mn2.
apply.
by rewrite leq_mul2r le_mn1.
Qed.



Lemma eqn_mul2l m n1 n2 : `(m * n1 = m * n2) <=> (m = 0) \/ (n1 = n2)`.
Proof. by rewrite eqn_leq !leq_mul2l -orb_andr -eqn_leq. Qed.

Lemma eqn_mul2r m n1 n2 : `(n1 * m = n2 * m) <=> (m = 0) \/ (n1 = n2)`.
Proof. by rewrite eqn_leq !leq_mul2r -orb_andr -eqn_leq. Qed.

Lemma leq_pmul2l m n1 n2 : `0 < m ==> ((m * n1 <= m * n2) <=> (n1 <= n2))`.
Proof. by move/prednK=> <-; rewrite leq_mul2l; rewr NOT_SUC orFb. Qed.

Lemma leq_pmul2r m n1 n2 : `0 < m ==> ((n1 * m <= n2 * m) <=> (n1 <= n2))`.
Proof. by move/prednK => <-; rewrite leq_mul2r; rewr NOT_SUC orFb. Qed.

Lemma eqn_pmul2l m n1 n2 : `0 < m ==> ((m * n1 = m * n2) <=> (n1 = n2))`.
Proof. by move/prednK => <-; rewrite eqn_mul2l; rewr NOT_SUC orFb. Qed.

Lemma eqn_pmul2r m n1 n2 : `0 < m ==> ((n1 * m = n2 * m) <=> (n1 = n2))`.
Proof. by move/prednK => <-; rewrite eqn_mul2r; rewr NOT_SUC orFb. Qed.

Lemma ltn_mul2l m n1 n2 : `(m * n1 < m * n2) <=> (0 < m) /\ (n1 < n2)`.
Proof. by rewrite lt0n !ltnNge leq_mul2l negb_or. Qed.

Lemma ltn_mul2r m n1 n2 : `(n1 * m < n2 * m) <=> (0 < m) /\ (n1 < n2)`.
Proof. by rewrite lt0n !ltnNge leq_mul2r negb_or. Qed.

Lemma ltn_pmul2l m n1 n2 : `0 < m ==> ((m * n1 < m * n2) <=> (n1 < n2))`.
Proof. by move/prednK => <-; rewrite ltn_mul2l LT_0 andTb. Qed.

Lemma ltn_pmul2r m n1 n2 : `0 < m ==> (n1 * m < n2 * m <=> n1 < n2)`.
Proof. by move/prednK => <-; rewrite ltn_mul2r LT_0. Qed.

Lemma ltn_Pmull m n : `1 < n ==> 0 < m ==> m < n * m`.
Proof. by move=> lt1n m_gt0; rewrite -{1}[`m`]mul1n ltn_pmul2r. Qed.

Lemma ltn_Pmulr m n : `1 < n ==> 0 < m ==> m < m * n`.
Proof. by move=> lt1n m_gt0; rewrite mulnC ltn_Pmull. Qed.

Lemma ltn_mul m1 m2 n1 n2 : `m1 < n1 ==> m2 < n2 ==> m1 * m2 < n1 * n2`.
Proof.
move=> lt_mn1 lt_mn2. 
move: (leq_ltn_trans `m1 * n2` `m1 * m2` `n1 * n2`).
"ANTS_TAC".
  by rewrite leq_mul2l orbC ltnW.
apply.
rewrite ltn_pmul2r //.
by move: lt_mn2; arith.
Qed.

Lemma maxn_mulr m n1 n2: `m * maxn n1 n2 = maxn (m * n1) (m * n2)`.
--Proof. by case=> // m n1 n2; rewrite /maxn (fun_if (muln _)) ltn_pmul2l. Qed.
case: m => [|n]; first by rewrite !mul0n maxnn.
by rewrite !maxn [`SUC n * _1`]fun_if ltn_pmul2l // LT_0. Qed.

Lemma maxn_mull m1 m2 n: `maxn m1 m2 * n = maxn (m1 * n) (m2 * n)`.
Proof. by rewrite -![`_1 * n`](mulnC n) maxn_mulr. Qed.

Lemma minn_mulr m n1 n2: `m * minn n1 n2 = minn (m * n1) (m * n2)`.
--Proof. by case=> // m n1 n2; rewrite /minn (fun_if (muln _)) ltn_pmul2l. Qed.
case: m => [|n]; first by rewrite !mul0n minn if_same.
rewrite !minn [`SUC n * _1`]fun_if ltn_pmul2l // LT_0. Qed.

Lemma minn_mull m1 m2 n: `minn m1 m2 * n = minn (m1 * n) (m2 * n)`.
Proof. by rewrite -![`_1 * n`](mulnC n) minn_mulr. Qed.

(* Exponentiation. *)

"parse_as_infix(\"^\", (24, \"left\"))".
"override_interface(\"^\", `EXP`)".

--Definition expn_rec m n := iterop n muln m 1.
--Notation "m ^ n" := (expn_rec m n) : nat_rec_scope.
--Definition expn := nosimpl expn_rec.
--Notation "m ^ n" := (expn m n) : nat_scope.

Lemma expn0 m : `m ^ 0 = 1`. by rewr EXP. Qed.
Lemma expn1 m : `m ^ 1 = m`. by rewr EXP_1. Qed.

Lemma expnS m n : `m ^ SUC n = m * m ^ n`. by rewr EXP. Qed.

Lemma expnSr m n :  `m ^ SUC n = m ^ n * m`.
Proof. by rewrite mulnC expnS. Qed.

Lemma exp0n n : `0 < n ==> 0 ^ n = 0`.
case: n => [|n]; first by rewrite LT_REFL.
by rewrite EXP mul0n. Qed.

Lemma exp1n n : `1 ^ n = 1`.
Proof. by elim: n; [rewrite expn0 | rewrite expnS mul1n]. Qed.

Lemma expn_add m n1 n2 : `m ^ (n1 + n2) = m ^ n1 * m ^ n2`.
--Proof. by elim: n1 => [|n1 IHn]; rewrite !(mul1n, expnS) // IHn mulnA. Qed.
elim: n1 => [|n1 IHn]; rewrite ?expn0 ?mul1n ?add0n // addSn !expnS.
by rewrite IHn mulnA. Qed.

Lemma expn_mull m1 m2 n : `(m1 * m2) ^ n = m1 ^ n * m2 ^ n`.
--Proof. by elim: n => // n IHn; rewrite !expnS IHn -!mulnA (mulnCA m2). Qed.
elim: n => [|n IHn]; first by rewrite !expn0 muln1.
by rewrite !expnS IHn -!mulnA [`m2 * _1`]mulnCA. Qed.

Lemma expn_mulr m n1 n2 : `m ^ (n1 * n2) = (m ^ n1) ^ n2`.
Proof.
elim: n1 => [|n1 IHn]; first by rewrite !expn0 mul0n expn0 exp1n.
--by rewrite expn_add expnS expn_mull IHn.
by rewrite mulSn expn_add expnS expn_mull IHn.
Qed.

Lemma expn_gt0 m n : `(0 < m ^ n) <=> (0 < m) \/ (n = 0)`.
--by case: m => [|m]; elim: n => //= n IHn; rewrite expnS // addn_gt0 IHn.
case: m => [|m]; elim: n => [|n IHn]; first by rewrite expn0; arith.
  by rewrite expnS mul0n; arith.
  by rewrite expn0; arith.
by rewrite expnS mulSn addn_gt0 IHn; arith.
Qed.


Lemma expn_eq0 m e : `(m ^ e = 0) <=> (m = 0) /\ (0 < e)`.
Proof. by rewrite !eqn0Ngt expn_gt0 negb_or -lt0n. Qed.

Lemma ltn_expl m n : `1 < m ==> n < m ^ n`.
--Proof.
--move=> m_gt1; elim: n => //= n; rewrite -(leq_pmul2l (ltnW m_gt1)) expnS.
--by apply: leq_trans; exact: ltn_Pmull.
move => m_gt1; elim: n => [|n]; first by rewrite expn0; arith.
move: (ltnW m_gt1); rewrite ONE -ltE; move/leq_pmul2l.
rewrite !ltE expnS => <-.
apply: leq_trans; rewrite -ltE.
by apply: (ltn_Pmull m_gt1); arith.
Qed.

Lemma leq_exp2l m n1 n2 : `1 < m ==> (m ^ n1 <= m ^ n2 <=> n1 <= n2)`.
(*Proof.
move=> m_gt1; elim: n1 n2 => [|n1 IHn] [|n2] //; last 1 first.
- by rewrite !expnS leq_pmul2l ?IHn // ltnW.
- by rewrite expn_gt0 ltnW.
by rewrite leqNgt (leq_trans m_gt1) // expnS leq_pmulr // expn_gt0 ltnW.
Qed.*)
move => m_gt1; elim: n1 n2 => [|n1 IHn]; move => [|q]; rewrite ?leqnn //; last 1 first.
  by rewrite !expnS leq_pmul2l ?leqSS // ltE ltnW -ONE.
  by rewrite expn0 ONE -ltE expn_gt0; move: m_gt1; arith.
rewrite leqNgt expn0.
move: m_gt1; rewrite ltE => m_gt1.
rewrite ltE (leq_trans m_gt1) -?ltE ?ltn0 // expnS leq_pmulr expn_gt0.
by move: m_gt1; arith. 
Qed.

Lemma ltn_exp2l m n1 n2 : `1 < m ==> (m ^ n1 < m ^ n2 <=> n1 < n2)`.
Proof. by move=> m_gt1; rewrite !ltnNge leq_exp2l. Qed.

Lemma eqn_exp2l m n1 n2 : `1 < m ==> (m ^ n1 = m ^ n2 <=> n1 = n2)`.
Proof. by move=> m_gt1; rewrite !eqn_leq !leq_exp2l. Qed.

Lemma expnI m : `1 < m ==> !e1 e2. m ^ e1 = m ^ e2 ==> e1 = e2`.
--Proof. by move=> m_gt1 e1 e2 /eqP; rewrite eqn_exp2l // => /eqP. Qed.
by move => m_gt1 e1 e2; rewrite eqn_exp2l. Qed.

Lemma leq_pexp2l m n1 n2 : `0 < m ==> n1 <= n2 ==> m ^ n1 <= m ^ n2`.
--Proof. by case: m => [|[|m]] // _; [rewrite !exp1n | rewrite leq_exp2l]. Qed.
by case: m => [|[|m]]; rewrite ?ltn0 //; [rewrite -ONE !exp1n leqnn | rewrite leq_exp2l //]; arith. Qed.

Lemma ltn_pexp2l m n1 n2 : `0 < m ==> m ^ n1 < m ^ n2 ==> n1 < n2`.
--Proof. by case: m => [|[|m]] // _; [rewrite !exp1n | rewrite ltn_exp2l]. Qed.
by case: m => [|[|m]]; rewrite ?ltn0 //; [rewrite -ONE !exp1n | rewrite ltn_exp2l]; arith. Qed.


Lemma ltn_exp2r m n e : `0 < e ==> (m ^ e < n ^ e <=> m < n)`.
--move=> e_gt0; apply/idP/idP=> [|ltmn].
--  rewrite !ltnNge; apply: contra => lemn.
--  by elim: e {e_gt0} => // e IHe; rewrite !expnS leq_mul.
--by elim: e e_gt0 => // [[|e] IHe] _; rewrite ?expn1 // ltn_mul // IHe.
move => e_gt0; split => [|ltmn].
  rewrite !ltnNge; apply: contra => lemn.
  by elim: e => [|e' IHe]; rewrite ?expn0 ?leqnn // !expnS leq_mul.
elim: e e_gt0; first by rewrite ltnn.
move => [|e IHe]; first by rewrite -ONE !expn1.
rewrite !expnS ltn_mul /= -!expnS IHe //; arith.
Qed.

Lemma leq_exp2r m n e : `0 < e ==> (m ^ e <= n ^ e <=> m <= n)`.
Proof. by move=> e_gt0; rewrite leqNgt ltn_exp2r // -leqNgt. Qed.

Lemma eqn_exp2r m n e : `0 < e ==> (m ^ e = n ^ e <=> m = n)`.
Proof. by move=> e_gt0; rewrite !eqn_leq !leq_exp2r. Qed.

Lemma expIn e : `0 < e ==> !m n. m ^ e = n ^ e ==> m = n`.
--Proof. by move=> e_gt1 m n /eqP; rewrite eqn_exp2r // => /eqP. Qed.
by move => e_gt0 m n; rewrite eqn_exp2r. Qed.

(* Factorial. *)

--Fixpoint fact_rec n := if n is n'.+1 then n * fact_rec n' else 1.
--Definition factorial := nosimpl fact_rec.
--Notation "n `!" := (factorial n) (at level 2, format "n `!") : nat_scope.

Lemma fact0 : `FACT 0 = 1`. by rewr FACT. Qed.

Lemma factS n : `FACT (SUC n)  = (SUC n) * FACT n`. by rewr FACT. Qed.

Lemma fact_gt0 n : `0 < FACT n`.
--Proof. by elim: n => //= n IHn; rewrite muln_gt0. Qed.
Proof. by elim: n => [|n]; rewr FACT ?muln_gt0; arith. Qed.

(* Parity and bits. *)

--Coercion nat_of_bool (b : bool) := if b then 1 else 0.
--Lemma leq_b1 (b : bool) : b <= 1. Proof. by case: b. Qed.
--Lemma addn_negb (b : bool) : ~~ b + b = 1. Proof. by case: b. Qed.
--Lemma eqb0 (b : bool) : (b == 0%N :> nat) = ~~ b. Proof. by case: b. Qed.
--Lemma lt0b (b : bool) : (b > 0) = b. Proof. by case: b. Qed.
--Lemma sub1b (b : bool) : 1 - b = ~~ b. Proof. by case: b. Qed.
--Lemma mulnb (b1 b2 : bool) : b1 * b2 = b1 && b2.
--Proof. by case: b1; case: b2. Qed.

--Fixpoint odd n := if n is n'.+1 then ~~ odd n' else false.
--Lemma oddb (b : bool) : odd b = b. Proof. by case: b. Qed.

"let odd = new_basic_definition `odd = ODD`".

Lemma odd0 : `odd 0 = F`. by rewrite odd; rewr 2!ODD. Qed.
Lemma oddS n: `odd (SUC n) = ~odd n`. by rewr odd ODD. Qed.
Lemma odd1 : `odd 1 = T`. by rewrite ONE oddS odd0. Qed.

Lemma odd_add m n : `odd (m + n) = odd m + odd n`.
--Proof. by elim: m => [|m IHn] //=; rewrite -addTb IHn addbA addTb. Qed.
elim: m => [|m IHn]; first by rewrite add0n odd0 addFb.
by rewrite addSn !oddS IHn -addTb addbA addTb.
Qed.

Lemma odd_sub m n : `n <= m ==> odd (m - n) = odd m + odd n`.
--by move=> le_nm; apply: (@canRL bool) (addbK _) _; rewrite -odd_add subnK.
by move => le_nm; apply: (addIb `odd n`); rewrite -odd_add subnK // addbK. Qed.

Lemma odd_opp i m : `odd m = F ==> i < m ==> odd (m - i) = odd i`.
--Proof. by move=> oddm lt_im; rewrite (odd_sub (ltnW lt_im)) oddm. Qed.
move => oddm lt_im.
by rewrite (odd_sub (ltnW lt_im)) oddm addFb.
Qed.

Lemma odd_mul m n : `odd (m * n) <=> odd m /\ odd n`.
--Proof. by elim: m => //= m IHm; rewrite odd_add -addTb andb_addl -IHm. Qed.
elim: m => [|m IHm]; first by rewrite mul0n odd0 andFb.
by rewrite mulSn odd_add oddS -addTb andb_addl -IHm andTb.
Qed.

Lemma odd_exp m n : `odd (m ^ n) <=> (n = 0) \/ odd m`.
--Proof. by elim: n => // n IHn; rewrite expnS odd_mul {}IHn orbC; case odd. Qed.
elim: n => [|n IHn]; first by rewrite expn0 odd1.
rewrite expnS odd_mul IHn orbC "ARITH_RULE `SUC n = 0 <=> F`" orFb.
set b := `odd m`.
move: b_def IHn => _ _.
by case: b => /=.
Qed.

(* Doubling. *)

--Fixpoint double_rec n := if n is n'.+1 then n'.*2%Nrec.+2 else 0
--where "n .*2" := (double_rec n) : nat_rec_scope.
--Definition double := nosimpl double_rec.
--Notation "n .*2" := (double n) : nat_scope.
--Lemma doubleE : double = double_rec. Proof. by []. Qed.

"let double = define `double 0 = 0 /\ (!n. double (SUC n) = SUC (SUC (double n)))`".

Lemma double0 : `double 0 = 0`. Proof. by rewr double. Qed.
Lemma doubleS n : `double (SUC n) = SUC (SUC (double n))`. by rewr double. Qed.

Lemma addnn n : `n + n = double n`.
--Proof. by apply: eqP; elim: n => // n IHn; rewrite addnS. Qed.
elim: n => [|n IHn]; first by rewrite addn0 double0.
by rewrite addnS addSn IHn doubleS.
Qed.

Lemma mul2n m : `2 * m = double m`.
--Proof. by rewrite mulSn mul1n addnn. Qed.
by rewrite "ARITH_RULE `2 = SUC 1`" mulSn mul1n addnn. Qed.

Lemma muln2 m : `m * 2 = double m`.
Proof. by rewrite mulnC mul2n. Qed.

Lemma double_add m n : `double (m + n) = double m + double n`.
Proof. by rewrite -!addnn -!addnA [`n + _1`](addnCA n). Qed.

Lemma double_sub m n : `double (m - n) = double m - double n`.
--Proof. elim: m n => [|m IHm] [|n] //; exact: IHm n. Qed.
elim: m n => [|m IHm] [|n]; rewrite ?sub0n ?subn0 ?double0 ?subn0 ?sub0n //.
by rewrite !doubleS !subSS IHm.
Qed.


Lemma leq_double m n : `(double m <= double n <=> m <= n)`.
--Proof. by rewrite /leq -double_sub; case (m - n). Qed.
by rewrite !leqE -double_sub; case: `m - n` => [|n]; rewrite double; arith. Qed.

Lemma ltn_double m n : `(double m < double n) = (m < n)`.
Proof. by rewrite 2!ltnNge leq_double. Qed.

Lemma ltn_Sdouble m n : `(SUC (double m) < double n) = (m < n)`.
--Proof. by rewrite -doubleS leq_double. Qed.
by rewrite -!muln2; arith. Qed.

Lemma leq_Sdouble m n : `(double m <= SUC (double n)) = (m <= n)`.
Proof. by rewrite leqNgt ltn_Sdouble -leqNgt. Qed.

Lemma odd_double n : `odd (double n) = F`.
Proof. by rewrite -addnn odd_add addbb. Qed.

Lemma double_gt0 n : `(0 < double n) = (0 < n)`.
--Proof. by case: n. Qed.
case: n => [|n]; rewrite ?double0 // doubleS; arith.
Qed.

Lemma double_eq0 n : `(double n = 0) = (n = 0)`.
--Proof. by case: n. Qed.
case: n => [|n]; rewrite ?double0 // doubleS; arith.
Qed.

Lemma double_mull m n : `double (m * n) = double m * n`.
Proof. by rewrite -!mul2n mulnA. Qed.

Lemma double_mulr m n : `double (m * n) = m * double n`.
Proof. by rewrite -!muln2 mulnA. Qed.

(* Halving. *)

--Fixpoint half (n : nat) : nat := if n is n'.+1 then uphalf n' else n
--with   uphalf (n : nat) : nat := if n is n'.+1 then n'./2.+1 else n
--where "n ./2" := (half n) : nat_scope.
"let half_def = define `HALF 0 = (0, 0) /\ 
	!n. HALF (SUC n) = (SND (HALF n), SUC (FST (HALF n)))`".
"let half = new_basic_definition `half = FST o HALF`".
"let uphalf = new_basic_definition `uphalf = SND o HALF`".

Lemma half0 : `half 0 = 0`. by rewr half o_DEF /= half_def. Qed.
Lemma uphalf0 : `uphalf 0 = 0`. by rewr uphalf o_DEF /= half_def. Qed.
Lemma halfS n: `half (SUC n) = uphalf n`. by rewr half uphalf o_DEF /= half_def. Qed.
Lemma uphalfS n : `uphalf (SUC n) = SUC (half n)`. by rewr half uphalf o_DEF /= half_def. Qed.

Lemma doubleK x : `half (double x) = x`.
--Proof. by elim=> //= n ->. Qed.
elim: x => [|n]; first by rewrite double0 half0.
by rewrite doubleS halfS uphalfS => ->.
Qed.

--Definition half_double := doubleK.
--Definition double_inj := can_inj doubleK.
"let half_double = doubleK".
Lemma double_inj: `!m n. double m = double n ==> m = n`.
move => m n.
by rewrite -{2}[`m`]doubleK -{2}[`n`]doubleK => ->.
Qed.

Lemma uphalf_double n : `uphalf (double n) = n`.
--Proof. by elim: n => //= n ->. Qed.
elim: n => [|n]; first by rewrite double0 uphalf0.
by rewrite doubleS uphalfS halfS => ->.
Qed.

Lemma uphalf_half n : `uphalf n = (if odd n then 1 else 0) + half n`.
--Proof. by elim: n => //= n ->; rewrite addnA addn_negb. Qed.
elim: n => [|n IHn]; first by rewrite uphalf0 half0 odd0 addn0.
rewrite halfS IHn addnA oddS uphalfS.
by case: `odd n` => /=; rewrite (add0n, addn0) add1n.
Qed.

Lemma odd_double_half n : `(if odd n then 1 else 0) + double (half n) = n`.
--by elim: n => //= n {3}<-; rewrite uphalf_half double_add; case (odd n).
elim: n => [|n IHn]; first by rewrite odd0 half0 double0 /= addn0.
rewrite -{3}IHn halfS uphalf_half double_add oddS.
move: IHn => _.
by case: `odd n` => /=; rewrite ?double0 add0n add1n // ONE doubleS !addSn double0 add0n.
Qed.


Lemma half_bit_double n b : `half ((if b then 1 else 0) + double n) = n`.
--Proof. by case: b; rewrite /= (half_double, uphalf_double). Qed.
by case: b; rewrite /= ?add0n ?add1n ?halfS (half_double, uphalf_double). Qed.

Lemma half_add m n : `half (m + n) = (if odd m /\ odd n then 1 else 0) + (half m + half n)`.
--rewrite -{1}[n]odd_double_half addnCA -{1}[m]odd_double_half -addnA -double_add.
--by do 2!case: odd; rewrite /= ?add0n ?half_double ?uphalf_double.
rewrite -{1}[`n`]odd_double_half addnCA -{1}[`m`]odd_double_half -addnA -double_add.
do 2!case: `odd _`; rewrite /= ?add0n ?half_double ?add1n ?halfS ?uphalfS ?uphalf_double //.
by rewrite half_double.
Qed.


Lemma half_leq m n : `m <= n ==> half m <= half n`.
--Proof. by move/subnK <-; rewrite half_add addnA leq_addl. Qed.
by move/subnK => <-; rewrite half_add addnA leq_addl. Qed.

Lemma half_gt0 n : `(0 < half n) = (1 < n)`.
--Proof. by case: n => [|[]]. Qed.
by case: n => [|[]]; rewrite ?halfS ?uphalfS ?uphalf0 ?half0; arith. Qed.

(* Squares and square identities. *)

Lemma mulnn m : `m * m = m ^ 2`.
Proof. by rewrite "ARITH_RULE `2 = SUC (SUC 0)`" !expnS expn0 muln1. Qed.

Lemma sqrn_add m n : `(m + n) ^ 2 = (m ^ 2 + n ^ 2) + 2 * (m * n)`.
Proof.
rewrite -!mulnn mul2n muln_addr !muln_addl [`n * _1`]mulnC -!addnA.
by rewrite EQ_ADD_LCANCEL addnA addnn addnC.
Qed.

Lemma sqrn_sub m n : `n <= m ==> (m - n) ^ 2 = (m ^ 2 + n ^ 2) - 2 * (m * n)`.
Proof.
move/subnK=> def_m.
--rewrite -{2}def_m sqrn_add -addnA addnAC.
--by rewrite -2!addnA addnn -mul2n -muln_addr -muln_addl def_m addnK.
rewrite -{2}def_m sqrn_add -addnA addnAC.
by rewrite -2!addnA addnn -mul2n -muln_addr -[`n EXP 2`]mulnn -muln_addl def_m addnK.
Qed.

Lemma sqrn_add_sub m n : `n <= m ==> (m + n) ^ 2 - 4 * (m * n) = (m - n) ^ 2`.
--move=> le_nm; rewrite -[4]/(2 * 2) -mulnA mul2n -addnn -subn_sub.
--by rewrite sqrn_add addnK sqrn_sub.
move => le_nm; rewrite "ARITH_RULE `4 = 2 * 2`" -mulnA mul2n -addnn -subn_sub.
by rewrite sqrn_add addnK sqrn_sub.
Qed.

Lemma subn_sqr m n : `m ^ 2 - n ^ 2 = (m - n) * (m + n)`.
Proof. by rewrite muln_subl !muln_addr addnC (mulnC m) subn_add2l !mulnn. Qed.

Lemma ltn_sqr m n : `(m ^ 2 < n ^ 2) = (m < n)`.
--Proof. by rewrite ltn_exp2r. Qed.
by rewrite ltn_exp2r //; arith. Qed.

Lemma leq_sqr m n : `(m ^ 2 <= n ^ 2) = (m <= n)`.
Proof. by rewrite leq_exp2r //; arith. Qed.

Lemma sqrn_gt0 n : `(0 < n ^ 2) = (0 < n)`.
--Proof. exact: (ltn_sqr 0). Qed.
move: (ltn_sqr `0`); rewrite exp0n; first by arith.
by move => ->.
Qed.

Lemma eqn_sqr m n : `(m ^ 2 = n ^ 2) = (m = n)`.
--Proof. by rewrite eqn_exp2r. Qed.
by rewrite eqn_exp2r //; arith. Qed.

Lemma sqrn_inj m n: `m ^ 2 = n ^ 2 ==> m = n`.
--Proof. exact: expIn. Qed.
move => eq.
move: (expIn "ARITH_RULE `0 < 2`") => inj.
by rewrite (inj eq).
Qed.

(* Almost strict inequality: an inequality that is strict unless some    *)
(* specific condition holds, such as the Cauchy-Schwartz or the AGM      *)
(* inequality (we only prove the order-2 AGM here; the general one       *)
(* requires sequences).                                                  *)
(*   We formalize the concept as a rewrite multirule, that can be used   *)
(* both to rewrite the non-strict inequality to true, and the equality   *)
(* to the specific condition (for strict inequalities use the ltn_neqAle *)
(* lemma); in addition, the conditional equality also coerces to a       *)
(* non-strict one.                                                       *)

--Definition leqif m n c := ((m <= n) * ((m == n) = c))%type.
"let leqif = new_definition `!m n c. leqif m n c <=> (m <= n /\ ((m = n) <=> c))`".

Lemma leqifP m n c : `leqif m n c <=> if c then m = n else m < n`.
rewrite ltn_neqAle leqif; split; first by case: c => /=.
by case: c => /=; rewrite leqnn.
Qed.

Lemma leqif_imp_le m n c: `leqif m n c ==> m <= n`. by rewrite leqif /=. Qed.
Lemma leqif_imp_eq m n c: `leqif m n c ==> (m = n <=> c)`. by rewrite leqif /=. Qed.

Lemma leqif_refl m c : `(leqif m m c) <=> c`.
--Proof. by apply: (iffP idP) => [-> | <-] //; split; rewrite ?eqxx. Qed.
by rewrite leqif leqnn. Qed.

Lemma leqif_trans m1 m2 m3 c1 c2 :
  `leqif m1 m2 c1 ==> leqif m2 m3 c2 ==> leqif m1 m3 (c1 /\ c2)`.
--move=> ltm12 ltm23; apply/leqifP; rewrite -ltm12.
--case eqm12: (m1 == m2).
--  by rewrite (eqP eqm12) ltn_neqAle !ltm23 andbT; case c2.
--by rewrite (@leq_trans m2) ?ltm23 // ltn_neqAle eqm12 ltm12.
rewrite !leqifP.
case: c1; case: c2 => /= lt12; first by move => <-.
by rewrite !ltE; apply: leq_trans; rewrite leqSS; exact: ltnW.
Qed.


Lemma monotone_leqif f : `(!m n. f m <= f n <=> m <= n) ==>
  !m n c. (leqif (f m) (f n) c) <=> (leqif m n c)`.
move=> f_mono m n c.
--by split=> /leqifP hyp; apply/leqifP; rewrite !eqn_leq !ltnNge !f_mono in hyp *.
by rewrite !leqifP !eqn_leq !ltnNge !f_mono.
Qed.

Lemma leqif_geq m n : `m <= n ==> leqif m n (n <= m)`.
--Proof. by move=> lemn; split=> //; rewrite eqn_leq lemn. Qed.
move => lemn; rewrite leqif; split => //; rewrite eqn_leq.
by rewrite lemn. Qed.

Lemma leqif_eq m n : `m <= n ==> leqif m n (m = n)`. by rewrite leqif. Qed.

Lemma geq_leqif a b C : `leqif a b C ==> ((b <= a) <=> C)`.
--Proof. by case=> le_ab; rewrite eqn_leq le_ab. Qed.
rewrite leqif; case => le_ab; rewrite eqn_leq.
by rewrite le_ab.
Qed.


Lemma ltn_leqif a b C : `leqif a b C ==> (a < b <=> ~ C)`.
--Proof. by move=> le_ab; rewrite ltnNge (geq_leqif le_ab). Qed.
move => le_ab.
by rewrite ltnNge (geq_leqif le_ab).
Qed.

Lemma leqif_add m1 n1 c1 m2 n2 c2 :
    `leqif m1 n1 c1 ==> leqif m2 n2 c2 ==> leqif (m1 + m2) (n1 + n2) (c1 /\ c2)`.
--move=> /(monotone_leqif (leq_add2r m2)) le1 /(monotone_leqif (leq_add2l n1)).
--exact: leqif_trans le1.
rewrite -(monotone_leqif (leq_add2r m2)) => le1.
rewrite -(monotone_leqif (leq_add2l n1)).
exact: leqif_trans.
Qed.


Lemma leqif_mul m1 n1 c1 m2 n2 c2 :
    `leqif m1 n1 c1 ==> leqif m2 n2 c2 ==>
	  leqif (m1 * m2) (n1 * n2) (n1 * n2 = 0 \/ (c1 /\ c2))`.
(*move=> le1 le2; case: posnP => [n12_0 | ].
  rewrite n12_0; move/eqP: n12_0 {le1 le2}le1.1 le2.1; rewrite muln_eq0.
  by case/orP=> /eqP->; case: m1 m2 => [|m1] [|m2] // _ _; 
    rewrite ?muln0; exact/leqif_refl.
rewrite muln_gt0 => /andP[n1_gt0 n2_gt0].
have [m2_0 | m2_gt0] := posnP m2.
  apply/leqifP; rewrite -le2 andbC eq_sym eqn_leq leqNgt m2_0 muln0.
  by rewrite muln_gt0 n1_gt0 n2_gt0.
move/leq_pmul2l: n1_gt0 => /monotone_leqif Mn1; move/Mn1: le2 => {Mn1}.
move/leq_pmul2r: m2_gt0 => /monotone_leqif Mm2; move/Mm2: le1 => {Mm2}.
exact: leqif_trans.*)
move => le1 le2.
case: (posnP `n1 * n2`) => [n12_0 | ].
  rewrite n12_0; move: n12_0 le1 le2; rewrite muln_eq0.
  case => ->; case: m1 m2 => [|m]; case => [|m'];
	rewrite !leqif ?muln0 ?mul0n ?leqnn /=; arith.
rewrite muln_gt0; move => [n1_gt0 n2_gt0].
move: (posnP m2) => [m2_0 | m2_gt0].
  rewrite leqifP; move: (le2); rewrite leqif => [] [_ <-].
  by rewrite andbC !eqn_leq !leqNgt m2_0 muln0 muln_gt0 n1_gt0 n2_gt0.
move/leq_pmul2l: (n1_gt0); move/monotone_leqif => Mn1. move: Mn1 le2 => <-.
move/leq_pmul2r: m2_gt0; move/monotone_leqif => Mm2. move: Mm2 le1 => <-.
move => leq1 leq2.
move: (leqif_trans leq1 leq2); rewrite !leqifP.
case: `c1 /\ c2` => /=.
by rewrite eqn_leq leqNgt muln_gt0 n1_gt0 n2_gt0.
Qed.


Lemma nat_Cauchy m n : `leqif (2 * (m * n)) (m ^ 2 + n ^ 2) (m = n)`.
--wlog le_nm: m n / n <= m.
--  by case: (leqP m n); auto; rewrite eq_sym addnC (mulnC m); auto.
--apply/leqifP; case: ifP => [/eqP-> | ne_mn]; first by rewrite mulnn addnn mul2n.
--by rewrite -subn_gt0 -sqrn_sub // sqrn_gt0 subn_gt0 ltn_neqAle eq_sym ne_mn.
wlog le_nm: m n / `n <= m`.
  case: (leqP n m) => //; rewrite eq_sym addnC [`m * _1`]mulnC => mn.
  by apply: le_nm; move: (ltnW mn).
move => le_nm.
rewrite leqifP.
case: (EXCLUDED_MIDDLE `m = n`) => [-> | ne_mn]; first by rewrite mulnn addnn mul2n.
by rewr ne_mn /=; rewrite -subn_gt0 -sqrn_sub // sqrn_gt0 subn_gt0 ltn_neqAle eq_sym.
Qed.

Lemma nat_AGM2 m n : `leqif (4 * (m * n)) ((m + n) ^ 2) (m = n)`.
--rewrite -[4]/(2 * 2) -mulnA mul2n -addnn sqrn_add; apply/leqifP.
--by rewrite ltn_add2r eqn_addr ltn_neqAle !nat_Cauchy; case: ifP => ->.
rewrite "ARITH_RULE `4 = 2 * 2`" -mulnA mul2n -addnn sqrn_add leqifP.
rewrite ltn_add2r eqn_addr ltn_neqAle.
by rewrite (leqif_imp_eq (nat_Cauchy m n)) (leqif_imp_le (nat_Cauchy m n)) /= if_same.
Qed.

(* Absolute difference / linear distance. *)

(* An auxiliary argument type allows lets us use the same grammar rules as   *)
(* generic ordered rings.                                                    *)

--CoInductive distn_arg := DistnArg of nat & nat.
--Notation "m - n" := (DistnArg m n) : distn_arg_scope.
"let distn = new_definition `!m n. distn m n = (m - n) + (n - m)`".

--Definition distn a := nosimpl (let: DistnArg m n := a in (m - n) + (n - m)).
--Arguments Scope distn [distn_arg_scope].
--Notation "`| a |" := (distn a) : nat_scope.

Lemma distnC m n : `distn m n = distn n m`.
--Proof. exact: addnC. Qed.
by rewrite !distn addnC. Qed.

Lemma distn_add2l d m n : `distn (d + m) (d + n) = distn m n`.
--Proof. by rewrite /distn !subn_add2l. Qed.
by rewrite !distn !subn_add2l. Qed.

Lemma distn_add2r d m n : `distn (m + d) (n + d) = distn m n`.
--Proof. by rewrite /distn !subn_add2r. Qed.
by rewrite !distn !subn_add2r. Qed.

Lemma distnEr m n : `m <= n ==> distn m n = n - m`.
--Proof. by move=> le_m_n; rewrite /distn (eqnP le_m_n). Qed.
move => le_m_n.
by rewrite distn ((EQ_IMP (leqE m n)) le_m_n) add0n.
Qed.

Lemma distnEl m n : `n <= m ==> distn m n = m - n`.
Proof. by move=> le_n_m; rewrite distnC distnEr. Qed.

Lemma dist0n n : `distn 0 n = n`.
--Proof. by case: n. Qed.
by case: n => [|m]; rewrite distn sub0n ?subn0 add0n. Qed.

Lemma distn0 n : `distn n 0 = n`.
Proof. by rewrite distnC dist0n. Qed.

Lemma distnn m : `distn m m = 0`.
Proof. by rewrite !distn subnn addn0. Qed.

Lemma distn_eq0 m n : `(distn m n = 0) <=> (m = n)`.
--Proof. by rewrite addn_eq0 !subn_eq0 -eqn_leq. Qed.
by rewrite distn addn_eq0 !subn_eq0 -eqn_leq. Qed.

Lemma distnS m : `distn m (SUC m) = 1`.
--Proof. exact: distn_add2r m 0 1. Qed.
by move: (distn_add2r m `0` `1`); rewrite add0n add1n dist0n. Qed.

Lemma distSn m : `distn (SUC m) m = 1`.
--Proof. exact: distn_add2r m 1 0. Qed.
by rewrite distnC distnS. Qed.

Lemma distn_eq1 m n :
  `(distn m n = 1) <=> (if m < n then SUC m = n else m = SUC n)`.
--case: ltnP => [lt_mn | le_nm].
--  by rewrite eq_sym -(eqn_addr m) distnEr ?subnK // ltnW.
--by rewrite -(eqn_addr n) distnEl ?subnK.
case: (ltnP m n) => [lt_mn | le_mn].
  by rewrite [`_ = 1`]eq_sym -(eqn_addr m) distnEr ?subnK ?add1n // ltnW.
by rewrite -(eqn_addr n) distnEl ?subnK // add1n ltnNge le_mn /=.
Qed.

Lemma leqif_add_distn m n p :
  `leqif (distn m p) (distn m n + distn n p) ((m <= n /\ n <= p) \/ (p <= n /\ n <= m))`.
(*
apply/leqifP; wlog le_mp : m p / m <= p.
  move=> IH; case/orP: (leq_total m p) => /IH //.
  by rewrite addnC orbC (distnC n) !(distnC p).
rewrite distnEr //; have [[le_mn le_np] /= | ] := altP andP.
  by rewrite !distnEr // addnC -(eqn_addr m) -addnA !subnK.
rewrite negb_and -!ltnNge => /orP[lt_nm | lt_pn].
  have lt_np := leq_trans lt_nm le_mp.
  by rewrite leqNgt lt_np ltn_addl //= distnEr ?ltn_sub2l // ltnW.
have lt_mn := leq_ltn_trans le_mp lt_pn.
by rewrite andbC leqNgt lt_mn ltn_addr //= distnEr ?ltn_sub2r // ltnW.
*)
suff IH: `!m p. m <= p ==> leqif (distn m p) (distn m n + distn n p) (m <= n /\ n <= p \/ p <= n /\ n <= m)`.
  case: (leq_total m p) => //; move/IH.
  by rewrite addnC orbC [`distn n _`](distnC n) ![`distn p _`]distnC.
move => m p le_mp.
rewrite distnEr //.
case: (EXCLUDED_MIDDLE `m <= n /\ n <= p`) => [[le_mn le_np] //= |].
  by rewrite !distnEr // addnC leqifP /= -(eqn_addr m) -addnA !subnK.
rewrite negb_and -!ltnNge => [] [lt_nm | lt_pn].
  move: (ltn_leq_trans lt_nm le_mp) => lt_np.
  by rewrite leqifP !leqNgt lt_nm lt_np /= ltn_addl distnEr ?ltnW // ltn_sub2l.
move: (leq_ltn_trans le_mp lt_pn) => lt_mn.
by rewrite leqifP !leqNgt lt_mn lt_pn /= ltn_addr distnEr ?ltn_sub2r // ltnW.
Qed.



Lemma leq_add_distn m n p : `distn m p <= distn m n + distn n p`.
--Proof. by rewrite leqif_add_distn. Qed.
by move: (leqif_imp_le (leqif_add_distn m n p)). Qed.

Lemma sqrn_distn m n : `(distn m n) ^ 2 + 2 * (m * n) = m ^ 2 + n ^ 2`.
--wlog le_nm: m n / n <= m.
--  move=> IH; case/orP: (leq_total n m) => /IH //.
--  by rewrite (addnC (n ^ 2)) (mulnC n) distnC.
--by rewrite distnEl ?sqrn_sub ?subnK ?nat_Cauchy.
wlog le_nm : m n / `n <= m`.
  case: (leq_total n m) => /le_nm //.
  by rewrite (addnC `n EXP 2`) (mulnC n) distnC.
by move => le_nm; rewrite distnEl // sqrn_sub // subnK // (leqif_imp_le (nat_Cauchy m n)).
Qed.
