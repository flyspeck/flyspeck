(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)

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
by rewrite -{1}[`n`]addn0 addnCA addn0. Qed.
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
by move: (addnK n `1`); rewrite add1n.
Qed.

Lemma subn_sub : `!m n p. (n - m) - p = n - (m + p)`.
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
Lemma eqn0Ngt : `!n. (n = 0) = ~(n > 0)`. by arith. Qed.
Lemma neq0_lt0n : `!n. (n = 0) = F ==> 0 < n`. by arith. Qed.

Lemma eqn_leq : `!m n. (m = n) = (m <= n /\ n <= m)`.
--Proof. elim: m n => [|m IHm] [|n] //; exact: IHm n. Qed.
by arith. Qed.

Lemma anti_leq : `!m n. m <= n /\ n <= m ==> m = n`.
-- Proof. by move=> m n; rewrite -eqn_leq => /eqP. Qed.
by move => m n; rewrite -eqn_leq. Qed.

Lemma negb_and : `!P Q. ~(P /\ Q) <=> ~P \/ ~Q`. by rewr DE_MORGAN_THM. Qed.
Lemma orbC : `!P Q. P \/ Q <=> Q \/ P`. by rewrite "CONJUNCT1 DISJ_ACI". Qed.
Lemma negb_or : `!P Q. ~(P \/ Q) <=> ~P /\ ~Q`. by rewr DE_MORGAN_THM. Qed.

Lemma neq_ltn : `!m n. ~(m = n) <=> (m < n) \/ (n < m)`.
-- Proof. by rewrite eqn_leq negb_and orbC -!ltnNge. Qed.
move => m n.
by rewrite eqn_leq negb_and orbC -!ltnNge. Qed.

Lemma leq_eqVlt : `!m n. (m <= n) <=> (m = n) \/ (m < n)`.
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

-- FIXME: rewriting fails
-- Lemma test : `!a. (a <=> F) ==> ~a`.
-- move => a ->.

Lemma implyNb : `!a b. (~a ==> b) <=> a \/ b`. "MESON_TAC[]". Qed.
-- move => a b. "EQ_TAC" => [na_b | [] /=].
-- move: (BOOL_CASES_AX a) => [-> // |].
-- move => H.
-- rewrite H. --FIXME: fails for no particular reason

Lemma geqE : `!m n. m >= n <=> n <= m`. by arith. Qed.

Lemma leq_total : `!m n. (m <= n) \/ (m >= n)`.
--Proof. by rewrite -implyNb -ltnNge; apply/implyP; exact: ltnW. Qed.
move => m n.
rewrite -implyNb -ltnNge geqE => lt_nm; exact: ltnW. Qed.


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

Lemma ltn_addr : `!m n p. m < n ==> m < n + p`.
--Proof. by move/leq_trans=> -> //; exact: leq_addr. Qed.
move => m n p.
rewrite !ltE.
move/(leq_trans n `SUC m` `n + p`); rewrite leq_addr; exact. Qed.

Lemma ltn_addl : `!m n p. m < n ==> m < p + n`. by arith. Qed.

Lemma addn_gt0 : `!m n. (0 < m + n) <=> (0 < m) \/ (0 < n)`.
--Proof. by rewrite !lt0n -negb_and addn_eq0. Qed.
move => m n.
by rewrite !lt0n -negb_and addn_eq0. Qed.

Lemma subn_gt0 : `!m n. (0 < n - m) = (m < n)`.
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

Lemma maxnl : `!m n. m >= n ==> maxn m n = m`.
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

Lemma eqn_maxl : `!m n. (maxn m n = m) = (m >= n)`.
--Proof. by rewrite -{2}[m]addn0 -add_sub_maxn eqn_addl. Qed.
move => m n.
by rewrite -{2}[`m`]addn0 -add_sub_maxn eqn_addl geqE leqE. Qed.

Lemma maxnn : `!n. maxn n n = n`.
--Proof. by move=> n; rewrite maxnl. Qed.
move => n.
by rewrite maxnl // geqE leqnn. Qed.

Lemma leq_maxr m n1 n2: `(m <= maxn n1 n2) <=> (m <= n1) \/ (m <= n2)`.
--Proof.
--wlog le_n21: n1 n2 / n2 <= n1.
--  by case/orP: (leq_total n2 n1) => le_n12; last rewrite maxnC orbC; auto.
--rewrite /maxn ltnNge le_n21 /=; case: leqP => // lt_m_n1.
--by rewrite leqNgt (leq_trans _ lt_m_n1).
--Qed.
(*
have wlog: `!P G. (P ==> G) /\ ((P ==> G) ==> G) ==> G`.
  by "MESON_TAC[]".
apply: (wlog `n2 <= n1`); split.
  case: (leq_total n2 n1) => le_n12.
*)
by rewrite maxn; arith. Qed.


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

Lemma minnr m n : `m >= n ==> minn m n = n`. by rewrite minn; arith. Qed.

Lemma minnl m n : `m <= n ==> minn m n = m`. 
--Proof. by move/minnr; rewrite minnC. Qed.
by rewrite -geqE; move/minnr; rewrite minnC. Qed.

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
by rewrite -[`n + m`]addn_min_max minnC eqn_addl [`m = _1`]eq_sym maxnC eqn_maxl geqE. Qed.

Lemma eqn_minl m n : `(minn m n = m) = (m <= n)`.
--by rewrite -(eqn_addr n) eq_sym -addn_min_max eqn_addl eqn_maxr. Qed.
by rewrite -(eqn_addr n) [`_1 = m + n`]eq_sym -addn_min_max eqn_addl eqn_maxr. Qed.

Lemma minnn n: `minn n n = n`.
by rewrite minnr // geqE leqnn. Qed.

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
by rewrite minnr // geqE leq_maxr leqnn. Qed.

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
move=> m n [->|[n' pH]]; first by rewrite !muln0 subn0.
--by elim: m n => // [m IHm] [|n] //; rewrite mulSn subn_add2l -IHm.
elim: m n; first by rewrite mul0n !sub0n mul0n.
move => [m IHm] [|[n2 nH]].
  by move => ->; rewrite mul0n !subn0 mulSn.
  by rewrite nH subSS !mulSn IHm subn_add2l.
  by move => ->; rewrite mul0n !subn0.
by rewrite nH subSS !mulSn IHm subn_add2l.
Qed.

Lemma muln_subr : `!m n p. m * (n - p) = m * n - m * p`.
Proof. by move=> m n p; rewrite ![`m * _1`]mulnC muln_subl. Qed.

Lemma mulnA : associative muln.
Proof. by move=> m n p; elim: m => //= m; rewrite mulSn muln_addl => ->. Qed.

Lemma mulnCA : left_commutative muln.
Proof. by move=> m n1 n2; rewrite !mulnA (mulnC m). Qed.

Lemma mulnAC : right_commutative muln.
Proof. by move=> m n p; rewrite -!mulnA (mulnC n). Qed.

Lemma muln_eq0 m n : (m * n == 0) = (m == 0) || (n == 0).
Proof. by case: m n => // m [|n] //=; rewrite muln0. Qed.

Lemma eqn_mul1 m n : (m * n == 1) = (m == 1) && (n == 1).
Proof. by case: m n => [|[|m]] [|[|n]] //; rewrite muln0. Qed.

Lemma muln_gt0 m n : (0 < m * n) = (0 < m) && (0 < n).
Proof. by case: m n => // m [|n] //=; rewrite muln0. Qed.

Lemma leq_pmull m n : n > 0 -> m <= n * m.
Proof. by move/prednK <-; exact: leq_addr. Qed.

Lemma leq_pmulr m n : n > 0 -> m <= m * n.
Proof. by move/leq_pmull; rewrite mulnC. Qed.

Lemma leq_mul2l m n1 n2 : (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof. by rewrite {1}/leq -muln_subr muln_eq0. Qed.

Lemma leq_mul2r m n1 n2 : (n1 * m <= n2 * m) = (m == 0) || (n1 <= n2).
Proof. by rewrite -!(mulnC m) leq_mul2l. Qed.

Lemma leq_mul m1 m2 n1 n2 : m1 <= n1 -> m2 <= n2 -> m1 * m2 <= n1 * n2.
Proof.
move=> le_mn1 le_mn2; apply (@leq_trans (m1 * n2)).
  by rewrite leq_mul2l le_mn2 orbT.
by rewrite leq_mul2r le_mn1 orbT.
Qed.

Lemma eqn_mul2l m n1 n2 : (m * n1 == m * n2) = (m == 0) || (n1 == n2).
Proof. by rewrite eqn_leq !leq_mul2l -orb_andr -eqn_leq. Qed.

Lemma eqn_mul2r m n1 n2 : (n1 * m == n2 * m) = (m == 0) || (n1 == n2).
Proof. by rewrite eqn_leq !leq_mul2r -orb_andr -eqn_leq. Qed.

Lemma leq_pmul2l m n1 n2 : 0 < m -> (m * n1 <= m * n2) = (n1 <= n2).
Proof. by move/prednK=> <-; rewrite leq_mul2l. Qed.
Implicit Arguments leq_pmul2l [m n1 n2].

Lemma leq_pmul2r m n1 n2 : 0 < m -> (n1 * m <= n2 * m) = (n1 <= n2).
Proof. by move/prednK <-; rewrite leq_mul2r. Qed.
Implicit Arguments leq_pmul2r [m n1 n2].

Lemma eqn_pmul2l m n1 n2 : 0 < m -> (m * n1 == m * n2) = (n1 == n2).
Proof. by move/prednK <-; rewrite eqn_mul2l. Qed.
Implicit Arguments eqn_pmul2l [m n1 n2].

Lemma eqn_pmul2r m n1 n2 : 0 < m -> (n1 * m == n2 * m) = (n1 == n2).
Proof. by move/prednK <-; rewrite eqn_mul2r. Qed.
Implicit Arguments eqn_pmul2r [m n1 n2].

Lemma ltn_mul2l m n1 n2 : (m * n1 < m * n2) = (0 < m) && (n1 < n2).
Proof. by rewrite lt0n !ltnNge leq_mul2l negb_or. Qed.

Lemma ltn_mul2r m n1 n2 : (n1 * m < n2 * m) = (0 < m) && (n1 < n2).
Proof. by rewrite lt0n !ltnNge leq_mul2r negb_or. Qed.

Lemma ltn_pmul2l m n1 n2 : 0 < m -> (m * n1 < m * n2) = (n1 < n2).
Proof. by move/prednK <-; rewrite ltn_mul2l. Qed.
Implicit Arguments ltn_pmul2l [m n1 n2].

Lemma ltn_pmul2r m n1 n2 : 0 < m -> (n1 * m < n2 * m) = (n1 < n2).
Proof. by move/prednK <-; rewrite ltn_mul2r. Qed.
Implicit Arguments ltn_pmul2r [m n1 n2].

Lemma ltn_Pmull m n : 1 < n -> 0 < m -> m < n * m.
Proof. by move=> lt1n m_gt0; rewrite -{1}[m]mul1n ltn_pmul2r. Qed.

Lemma ltn_Pmulr m n : 1 < n -> 0 < m -> m < m * n.
Proof. by move=> lt1n m_gt0; rewrite mulnC ltn_Pmull. Qed.

Lemma ltn_mul m1 m2 n1 n2 : m1 < n1 -> m2 < n2 -> m1 * m2 < n1 * n2.
Proof.
move=> lt_mn1 lt_mn2; apply (@leq_ltn_trans (m1 * n2)).
  by rewrite leq_mul2l orbC ltnW.
by rewrite ltn_pmul2r // (leq_trans _ lt_mn2).
Qed.

Lemma maxn_mulr : right_distributive muln maxn.
Proof. by case=> // m n1 n2; rewrite /maxn (fun_if (muln _)) ltn_pmul2l. Qed.

Lemma maxn_mull : left_distributive muln maxn.
Proof. by move=> m1 m2 n; rewrite -!(mulnC n) maxn_mulr. Qed.

Lemma minn_mulr : right_distributive muln minn.
Proof. by case=> // m n1 n2; rewrite /minn (fun_if (muln _)) ltn_pmul2l. Qed.

Lemma minn_mull : left_distributive muln minn.
Proof. by move=> m1 m2 n; rewrite -!(mulnC n) minn_mulr. Qed.

(* Exponentiation. *)

Definition expn_rec m n := iterop n muln m 1.
Notation "m ^ n" := (expn_rec m n) : nat_rec_scope.
Definition expn := nosimpl expn_rec.
Notation "m ^ n" := (expn m n) : nat_scope.

Lemma expnE : expn = expn_rec. Proof. by []. Qed.

Lemma expn0 : forall m, m ^ 0 = 1. Proof. by []. Qed.
Lemma expn1 : forall m, m ^ 1 = m. Proof. by []. Qed.

Lemma expnS : forall m n, m ^ n.+1 = m * m ^ n.
Proof. by move=> m [|n] //; rewrite muln1. Qed.

Lemma expnSr : forall m n, m ^ n.+1 = m ^ n * m.
Proof. by move=> m n; rewrite mulnC expnS. Qed.

Lemma exp0n n : 0 < n -> 0 ^ n = 0. Proof. by case: n => [|[]]. Qed.

Lemma exp1n n : 1 ^ n = 1.
Proof. by elim: n => // n; rewrite expnS mul1n. Qed.

Lemma expn_add m n1 n2 : m ^ (n1 + n2) = m ^ n1 * m ^ n2.
Proof. by elim: n1 => [|n1 IHn]; rewrite !(mul1n, expnS) // IHn mulnA. Qed.

Lemma expn_mull m1 m2 n : (m1 * m2) ^ n = m1 ^ n * m2 ^ n.
Proof. by elim: n => // n IHn; rewrite !expnS IHn -!mulnA (mulnCA m2). Qed.

Lemma expn_mulr m n1 n2 : m ^ (n1 * n2) = (m ^ n1) ^ n2.
Proof.
elim: n1 => [|n1 IHn]; first by rewrite exp1n.
by rewrite expn_add expnS expn_mull IHn.
Qed.

Lemma expn_gt0 m n : (0 < m ^ n) = (0 < m) || (n == 0).
Proof.
by case: m => [|m]; elim: n => //= n IHn; rewrite expnS // addn_gt0 IHn.
Qed.

Lemma expn_eq0 m e : (m ^ e == 0) = (m == 0) && (e > 0).
Proof. by rewrite !eqn0Ngt expn_gt0 negb_or -lt0n. Qed.

Lemma ltn_expl m n : 1 < m -> n < m ^ n.
Proof.
move=> m_gt1; elim: n => //= n; rewrite -(leq_pmul2l (ltnW m_gt1)) expnS.
by apply: leq_trans; exact: ltn_Pmull.
Qed.

Lemma leq_exp2l m n1 n2 : 1 < m -> (m ^ n1 <= m ^ n2) = (n1 <= n2).
Proof.
move=> m_gt1; elim: n1 n2 => [|n1 IHn] [|n2] //; last 1 first.
- by rewrite !expnS leq_pmul2l ?IHn // ltnW.
- by rewrite expn_gt0 ltnW.
by rewrite leqNgt (leq_trans m_gt1) // expnS leq_pmulr // expn_gt0 ltnW.
Qed.

Lemma ltn_exp2l m n1 n2 : 1 < m -> (m ^ n1 < m ^ n2) = (n1 < n2).
Proof. by move=> m_gt1; rewrite !ltnNge leq_exp2l. Qed.

Lemma eqn_exp2l m n1 n2 : 1 < m -> (m ^ n1 == m ^ n2) = (n1 == n2).
Proof. by move=> m_gt1; rewrite !eqn_leq !leq_exp2l. Qed.

Lemma expnI m : 1 < m -> injective (expn m).
Proof. by move=> m_gt1 e1 e2 /eqP; rewrite eqn_exp2l // => /eqP. Qed.

Lemma leq_pexp2l m n1 n2 : 0 < m -> n1 <= n2 -> m ^ n1 <= m ^ n2.
Proof. by case: m => [|[|m]] // _; [rewrite !exp1n | rewrite leq_exp2l]. Qed.

Lemma ltn_pexp2l m n1 n2 : 0 < m -> m ^ n1 < m ^ n2 -> n1 < n2.
Proof. by case: m => [|[|m]] // _; [rewrite !exp1n | rewrite ltn_exp2l]. Qed.

Lemma ltn_exp2r m n e : e > 0 -> (m ^ e < n ^ e) = (m < n).
Proof.
move=> e_gt0; apply/idP/idP=> [|ltmn].
  rewrite !ltnNge; apply: contra => lemn.
  by elim: e {e_gt0} => // e IHe; rewrite !expnS leq_mul.
by elim: e e_gt0 => // [[|e] IHe] _; rewrite ?expn1 // ltn_mul // IHe.
Qed.

Lemma leq_exp2r m n e : e > 0 -> (m ^ e <= n ^ e) = (m <= n).
Proof. by move=> e_gt0; rewrite leqNgt ltn_exp2r // -leqNgt. Qed.

Lemma eqn_exp2r m n e : e > 0 -> (m ^ e == n ^ e) = (m == n).
Proof. by move=> e_gt0; rewrite !eqn_leq !leq_exp2r. Qed.

Lemma expIn e : e > 0 -> injective (expn^~ e).
Proof. by move=> e_gt1 m n /eqP; rewrite eqn_exp2r // => /eqP. Qed.

(* Factorial. *)

Fixpoint fact_rec n := if n is n'.+1 then n * fact_rec n' else 1.

Definition factorial := nosimpl fact_rec.

Notation "n `!" := (factorial n) (at level 2, format "n `!") : nat_scope.

Lemma factE : factorial = fact_rec. Proof. by []. Qed.

Lemma fact0 : 0`! = 1. Proof. by []. Qed.

Lemma factS n : (n.+1)`!  = n.+1 * n`!. Proof. by []. Qed.

Lemma fact_gt0 n : n`! > 0.
Proof. by elim: n => //= n IHn; rewrite muln_gt0. Qed.

(* Parity and bits. *)

Coercion nat_of_bool (b : bool) := if b then 1 else 0.

Lemma leq_b1 (b : bool) : b <= 1. Proof. by case: b. Qed.

Lemma addn_negb (b : bool) : ~~ b + b = 1. Proof. by case: b. Qed.

Lemma eqb0 (b : bool) : (b == 0%N :> nat) = ~~ b. Proof. by case: b. Qed.

Lemma lt0b (b : bool) : (b > 0) = b. Proof. by case: b. Qed.

Lemma sub1b (b : bool) : 1 - b = ~~ b. Proof. by case: b. Qed.

Lemma mulnb (b1 b2 : bool) : b1 * b2 = b1 && b2.
Proof. by case: b1; case: b2. Qed.

Fixpoint odd n := if n is n'.+1 then ~~ odd n' else false.

Lemma oddb (b : bool) : odd b = b. Proof. by case: b. Qed.

Lemma odd_add m n : odd (m + n) = odd m (+) odd n.
Proof. by elim: m => [|m IHn] //=; rewrite -addTb IHn addbA addTb. Qed.

Lemma odd_sub m n : n <= m -> odd (m - n) = odd m (+) odd n.
Proof.
by move=> le_nm; apply: (@canRL bool) (addbK _) _; rewrite -odd_add subnK.
Qed.

Lemma odd_opp i m : odd m = false -> i < m -> odd (m - i) = odd i.
Proof. by move=> oddm lt_im; rewrite (odd_sub (ltnW lt_im)) oddm. Qed.

Lemma odd_mul m n : odd (m * n) = odd m && odd n.
Proof. by elim: m => //= m IHm; rewrite odd_add -addTb andb_addl -IHm. Qed.

Lemma odd_exp m n : odd (m ^ n) = (n == 0) || odd m.
Proof. by elim: n => // n IHn; rewrite expnS odd_mul {}IHn orbC; case odd. Qed.

(* Doubling. *)

Fixpoint double_rec n := if n is n'.+1 then n'.*2%Nrec.+2 else 0
where "n .*2" := (double_rec n) : nat_rec_scope.

Definition double := nosimpl double_rec.
Notation "n .*2" := (double n) : nat_scope.

Lemma doubleE : double = double_rec. Proof. by []. Qed.

Lemma double0 : 0.*2 = 0. Proof. by []. Qed.

Lemma doubleS n : n.+1.*2 = n.*2.+2. Proof. by []. Qed.

Lemma addnn n : n + n = n.*2.
Proof. by apply: eqP; elim: n => // n IHn; rewrite addnS. Qed.

Lemma mul2n m : 2 * m = m.*2.
Proof. by rewrite mulSn mul1n addnn. Qed.

Lemma muln2 m : m * 2 = m.*2.
Proof. by rewrite mulnC mul2n. Qed.

Lemma double_add m n : (m + n).*2 = m.*2 + n.*2.
Proof. by rewrite -!addnn -!addnA (addnCA n). Qed.

Lemma double_sub m n : (m - n).*2 = m.*2 - n.*2.
Proof. elim: m n => [|m IHm] [|n] //; exact: IHm n. Qed.

Lemma leq_double m n : (m.*2 <= n.*2) = (m <= n).
Proof. by rewrite /leq -double_sub; case (m - n). Qed.

Lemma ltn_double m n : (m.*2 < n.*2) = (m < n).
Proof. by rewrite 2!ltnNge leq_double. Qed.

Lemma ltn_Sdouble m n : (m.*2.+1 < n.*2) = (m < n).
Proof. by rewrite -doubleS leq_double. Qed.

Lemma leq_Sdouble m n : (m.*2 <= n.*2.+1) = (m <= n).
Proof. by rewrite leqNgt ltn_Sdouble -leqNgt. Qed.

Lemma odd_double n : odd n.*2 = false.
Proof. by rewrite -addnn odd_add addbb. Qed.

Lemma double_gt0 n : (0 < n.*2) = (0 < n).
Proof. by case: n. Qed.

Lemma double_eq0 n : (n.*2 == 0) = (n == 0).
Proof. by case: n. Qed.

Lemma double_mull m n : (m * n).*2 = m.*2 * n.
Proof. by rewrite -!mul2n mulnA. Qed.

Lemma double_mulr m n : (m * n).*2 = m * n.*2.
Proof. by rewrite -!muln2 mulnA. Qed.

(* Halving. *)

Fixpoint half (n : nat) : nat := if n is n'.+1 then uphalf n' else n
with   uphalf (n : nat) : nat := if n is n'.+1 then n'./2.+1 else n
where "n ./2" := (half n) : nat_scope.

Lemma doubleK : cancel double half.
Proof. by elim=> //= n ->. Qed.

Definition half_double := doubleK.
Definition double_inj := can_inj doubleK.

Lemma uphalf_double n : uphalf n.*2 = n.
Proof. by elim: n => //= n ->. Qed.

Lemma uphalf_half n : uphalf n = odd n + n./2.
Proof. by elim: n => //= n ->; rewrite addnA addn_negb. Qed.

Lemma odd_double_half n : odd n + n./2.*2 = n.
Proof.
by elim: n => //= n {3}<-; rewrite uphalf_half double_add; case (odd n).
Qed.

Lemma half_bit_double n (b : bool) : (b + n.*2)./2 = n.
Proof. by case: b; rewrite /= (half_double, uphalf_double). Qed.

Lemma half_add m n : (m + n)./2 = (odd m && odd n) + (m./2 + n./2).
Proof.
rewrite -{1}[n]odd_double_half addnCA -{1}[m]odd_double_half -addnA -double_add.
by do 2!case: odd; rewrite /= ?add0n ?half_double ?uphalf_double.
Qed.

Lemma half_leq m n : m <= n -> m./2 <= n./2.
Proof. by move/subnK <-; rewrite half_add addnA leq_addl. Qed.

Lemma half_gt0 n : (0 < n./2) = (1 < n).
Proof. by case: n => [|[]]. Qed.

(* Squares and square identities. *)

Lemma mulnn m : m * m = m ^ 2.
Proof. by rewrite !expnS muln1. Qed.

Lemma sqrn_add m n : (m + n) ^ 2 = m ^ 2 + n ^ 2 + 2 * (m * n).
Proof.
rewrite -!mulnn mul2n muln_addr !muln_addl (mulnC n) -!addnA.
by congr (_ + _); rewrite addnA addnn addnC.
Qed.

Lemma sqrn_sub m n : n <= m -> (m - n) ^ 2 = m ^ 2 + n ^ 2 - 2 * (m * n).
Proof.
move/subnK=> def_m; rewrite -{2}def_m sqrn_add -addnA addnAC.
by rewrite -2!addnA addnn -mul2n -muln_addr -muln_addl def_m addnK.
Qed.

Lemma sqrn_add_sub m n : n <= m -> (m + n) ^ 2 - 4 * (m * n) = (m - n) ^ 2.
Proof.
move=> le_nm; rewrite -[4]/(2 * 2) -mulnA mul2n -addnn -subn_sub.
by rewrite sqrn_add addnK sqrn_sub.
Qed.

Lemma subn_sqr m n : m ^ 2 - n ^ 2 = (m - n) * (m + n).
Proof. by rewrite muln_subl !muln_addr addnC (mulnC m) subn_add2l !mulnn. Qed.

Lemma ltn_sqr m n : (m ^ 2 < n ^ 2) = (m < n).
Proof. by rewrite ltn_exp2r. Qed.

Lemma leq_sqr m n : (m ^ 2 <= n ^ 2) = (m <= n).
Proof. by rewrite leq_exp2r. Qed.

Lemma sqrn_gt0 n : (0 < n ^ 2) = (0 < n).
Proof. exact: (ltn_sqr 0). Qed.

Lemma eqn_sqr m n : (m ^ 2 == n ^ 2) = (m == n).
Proof. by rewrite eqn_exp2r. Qed.

Lemma sqrn_inj : injective (expn ^~ 2).
Proof. exact: expIn. Qed.

(* Almost strict inequality: an inequality that is strict unless some    *)
(* specific condition holds, such as the Cauchy-Schwartz or the AGM      *)
(* inequality (we only prove the order-2 AGM here; the general one       *)
(* requires sequences).                                                  *)
(*   We formalize the concept as a rewrite multirule, that can be used   *)
(* both to rewrite the non-strict inequality to true, and the equality   *)
(* to the specific condition (for strict inequalities use the ltn_neqAle *)
(* lemma); in addition, the conditional equality also coerces to a       *)
(* non-strict one.                                                       *)

Definition leqif m n c := ((m <= n) * ((m == n) = c))%type.

Notation "m <= n ?= 'iff' c" := (leqif m n c)
    (at level 70, n at next level,
  format "m '[hv'  <=  n '/'  ?=  'iff'  c ']'") : nat_scope.

Coercion leq_of_leqif m n c (H : m <= n ?= iff c) := H.1 : m <= n.

Lemma leqifP m n c : reflect (m <= n ?= iff c) (if c then m == n else m < n).
Proof.
rewrite ltn_neqAle; apply: (iffP idP) => [|lte]; last by rewrite !lte; case c.
by case c => [/eqP-> | /andP[/negPf]]; split=> //; exact: eqxx.
Qed.

Lemma leqif_refl m c : reflect (m <= m ?= iff c) c.
Proof. by apply: (iffP idP) => [-> | <-] //; split; rewrite ?eqxx. Qed.

Lemma leqif_trans m1 m2 m3 c1 c2 :
  m1 <= m2 ?= iff c1 -> m2 <= m3 ?= iff c2 -> m1 <= m3 ?= iff c1 && c2.
Proof.
move=> ltm12 ltm23; apply/leqifP; rewrite -ltm12.
case eqm12: (m1 == m2).
  by rewrite (eqP eqm12) ltn_neqAle !ltm23 andbT; case c2.
by rewrite (@leq_trans m2) ?ltm23 // ltn_neqAle eqm12 ltm12.
Qed.

Lemma monotone_leqif f : monotone f ->
  forall m n c, (f m <= f n ?= iff c) <-> (m <= n ?= iff c).
Proof.
move=> f_mono m n c.
by split=> /leqifP hyp; apply/leqifP; rewrite !eqn_leq !ltnNge !f_mono in hyp *.
Qed.

Lemma leqif_geq m n : m <= n -> m <= n ?= iff (m >= n).
Proof. by move=> lemn; split=> //; rewrite eqn_leq lemn. Qed.

Lemma leqif_eq m n : m <= n -> m <= n ?= iff (m == n).
Proof. by []. Qed.

Lemma geq_leqif a b C : a <= b ?= iff C -> (b <= a) = C.
Proof. by case=> le_ab; rewrite eqn_leq le_ab. Qed.

Lemma ltn_leqif a b C : a <= b ?= iff C -> (a < b) = ~~ C.
Proof. by move=> le_ab; rewrite ltnNge (geq_leqif le_ab). Qed.

Lemma leqif_add m1 n1 c1 m2 n2 c2 :
    m1 <= n1 ?= iff c1 -> m2 <= n2 ?= iff c2 ->
  m1 + m2 <= n1 + n2 ?= iff c1 && c2.
Proof.
move=> /(monotone_leqif (leq_add2r m2)) le1 /(monotone_leqif (leq_add2l n1)).
exact: leqif_trans le1.
Qed.

Lemma leqif_mul m1 n1 c1 m2 n2 c2 :
    m1 <= n1 ?= iff c1 -> m2 <= n2 ?= iff c2 ->
  m1 * m2 <= n1 * n2 ?= iff (n1 * n2 == 0) || (c1 && c2).
Proof.
move=> le1 le2; case: posnP => [n12_0 | ].
  rewrite n12_0; move/eqP: n12_0 {le1 le2}le1.1 le2.1; rewrite muln_eq0.
  by case/orP=> /eqP->; case: m1 m2 => [|m1] [|m2] // _ _; 
    rewrite ?muln0; exact/leqif_refl.
rewrite muln_gt0 => /andP[n1_gt0 n2_gt0].
have [m2_0 | m2_gt0] := posnP m2.
  apply/leqifP; rewrite -le2 andbC eq_sym eqn_leq leqNgt m2_0 muln0.
  by rewrite muln_gt0 n1_gt0 n2_gt0.
move/leq_pmul2l: n1_gt0 => /monotone_leqif Mn1; move/Mn1: le2 => {Mn1}.
move/leq_pmul2r: m2_gt0 => /monotone_leqif Mm2; move/Mm2: le1 => {Mm2}.
exact: leqif_trans.
Qed.

Lemma nat_Cauchy m n : 2 * (m * n) <= m ^ 2 + n ^ 2 ?= iff (m == n).
Proof.
wlog le_nm: m n / n <= m.
  by case: (leqP m n); auto; rewrite eq_sym addnC (mulnC m); auto.
apply/leqifP; case: ifP => [/eqP-> | ne_mn]; first by rewrite mulnn addnn mul2n.
by rewrite -subn_gt0 -sqrn_sub // sqrn_gt0 subn_gt0 ltn_neqAle eq_sym ne_mn.
Qed.

Lemma nat_AGM2 m n : 4 * (m * n) <= (m + n) ^ 2 ?= iff (m == n).
Proof.
rewrite -[4]/(2 * 2) -mulnA mul2n -addnn sqrn_add; apply/leqifP.
by rewrite ltn_add2r eqn_addr ltn_neqAle !nat_Cauchy; case: ifP => ->.
Qed.

(* Absolute difference / linear distance. *)

(* An auxiliary argument type allows lets us use the same grammar rules as   *)
(* generic ordered rings.                                                    *)

CoInductive distn_arg := DistnArg of nat & nat.
Notation "m - n" := (DistnArg m n) : distn_arg_scope.

Definition distn a := nosimpl (let: DistnArg m n := a in (m - n) + (n - m)).
Arguments Scope distn [distn_arg_scope].
Notation "`| a |" := (distn a) : nat_scope.

Lemma distnC m n : `|m - n| = `|n - m|.
Proof. exact: addnC. Qed.

Lemma distn_add2l d m n : `|d + m - (d + n)| = `|m - n|.
Proof. by rewrite /distn !subn_add2l. Qed.

Lemma distn_add2r d m n : `|m + d - (n + d)| = `|m - n|.
Proof. by rewrite /distn !subn_add2r. Qed.

Lemma distnEr m n : m <= n -> `|m - n| = n - m.
Proof. by move=> le_m_n; rewrite /distn (eqnP le_m_n). Qed.

Lemma distnEl m n : n <= m -> `|m - n| = m - n.
Proof. by move=> le_n_m; rewrite distnC distnEr. Qed.

Lemma dist0n n : `|0 - n| = n.
Proof. by case: n. Qed.

Lemma distn0 n : `|n - 0| = n.
Proof. by rewrite distnC dist0n. Qed.

Lemma distnn m : `|m - m| = 0.
Proof. by rewrite /distn subnn. Qed.

Lemma distn_eq0 m n : (`|m - n| == 0) = (m == n).
Proof. by rewrite addn_eq0 !subn_eq0 -eqn_leq. Qed.

Lemma distnS m : `|m - m.+1| = 1.
Proof. exact: distn_add2r m 0 1. Qed.

Lemma distSn m : `|m.+1 - m| = 1.
Proof. exact: distn_add2r m 1 0. Qed.

Lemma distn_eq1 m n :
  (`|m - n| == 1) = (if m < n then m.+1 == n else m == n.+1).
Proof.
case: ltnP => [lt_mn | le_nm].
  by rewrite eq_sym -(eqn_addr m) distnEr ?subnK // ltnW.
by rewrite -(eqn_addr n) distnEl ?subnK.
Qed.

Lemma leqif_add_distn m n p :
  `|m - p| <= `|m - n| + `|n - p| ?= iff (m <= n <= p) || (p <= n <= m).
Proof.
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
Qed.

Lemma leq_add_distn m n p : `|m - p| <= `|m - n| + `|n - p|.
Proof. by rewrite leqif_add_distn. Qed.

Lemma sqrn_distn m n : `|m - n| ^ 2 + 2 * (m * n) = m ^ 2 + n ^ 2.
Proof.
wlog le_nm: m n / n <= m.
  move=> IH; case/orP: (leq_total n m) => /IH //.
  by rewrite (addnC (n ^ 2)) (mulnC n) distnC.
by rewrite distnEl ?sqrn_sub ?subnK ?nat_Cauchy.
Qed.

(* Support for larger integers. The normal definitions of +, - and even  *)
(* IO are unsuitable for Peano integers larger than 2000 or so because   *)
(* they are not tail-recursive. We provide a workaround module, along    *)
(* with a rewrite multirule to change the tailrec operators to the       *)
(* normal ones. We handle IO via the NatBin module, but provide our      *)
(* own (more efficient) conversion functions.                            *)

Module NatTrec.

(*   Usage:                                             *)
(*     Import NatTrec.                                  *)
(*        in section definining functions, rebinds all  *)
(*        non-tail recursive operators.                 *)
(*     rewrite !trecE.                                  *)
(*        in the correctness proof, restores operators  *)

Fixpoint add m n := if m is m'.+1 then m' + n.+1 else n
where "n + m" := (add n m) : nat_scope.

Fixpoint add_mul m n s := if m is m'.+1 then add_mul m' n (n + s) else s.

Definition mul m n := if m is m'.+1 then add_mul m' n n else 0.

Notation "n * m" := (mul n m) : nat_scope.

Fixpoint mul_exp m n p := if n is n'.+1 then mul_exp m n' (m * p) else p.

Definition exp m n := if n is n'.+1 then mul_exp m n' m else 1.

Notation "n ^ m" := (exp n m) : nat_scope.

Notation Local oddn := odd.
Fixpoint odd n := if n is n'.+2 then odd n' else eqn n 1.

Notation Local doublen := double.
Definition double n := if n is n'.+1 then n' + n.+1 else 0.
Notation "n .*2" := (double n) : nat_scope.

Lemma addE : add =2 addn.
Proof. by elim=> //= n IHn m; rewrite IHn addSnnS. Qed.

Lemma doubleE : double =1 doublen.
Proof. by case=> // n; rewrite -addnn -addE. Qed.

Lemma add_mulE n m s : add_mul n m s = addn (muln n m) s.
Proof. by elim: n => //= n IHn in m s *; rewrite IHn addE addnCA addnA. Qed.

Lemma mulE : mul =2 muln.
Proof. by case=> //= n m; rewrite add_mulE addnC. Qed.

Lemma mul_expE m n p : mul_exp m n p = muln (expn m n) p.
Proof.
by elim: n => [|n IHn] in p *; rewrite ?mul1n //= expnS IHn mulE mulnCA mulnA.
Qed.

Lemma expE : exp =2 expn.
Proof. by move=> m [|n] //=; rewrite mul_expE expnS mulnC. Qed.

Lemma oddE : odd =1 oddn.
Proof.
move=> n; rewrite -{1}[n]odd_double_half addnC.
by elim: n./2 => //=; case (oddn n).
Qed.

Definition trecE := (addE, (doubleE, oddE), (mulE, add_mulE, (expE, mul_expE))).

End NatTrec.

Notation natTrecE := NatTrec.trecE.

Lemma eq_binP : Equality.axiom Ndec.Neqb.
Proof.
move=> p q; apply: (iffP idP) => [|[<-]]; last by case: p => //; elim.
by case: q; case: p => //; elim=> [p IHp|p IHp|] [q|q|] //=; case/IHp=> ->.
Qed.

Canonical bin_nat_eqMixin := EqMixin eq_binP.
Canonical bin_nat_eqType := Eval hnf in EqType N bin_nat_eqMixin.

Section NumberInterpretation.

Import BinPos.

Section Trec.

Import NatTrec.

Fixpoint nat_of_pos p0 :=
  match p0 with
  | xO p => (nat_of_pos p).*2
  | xI p => (nat_of_pos p).*2.+1
  | xH   => 1
  end.

End Trec.

Coercion Local nat_of_pos : positive >-> nat.

Coercion nat_of_bin b := if b is Npos p then p : nat else 0.

Fixpoint pos_of_nat n0 m0 :=
  match n0, m0 with
  | n.+1, m.+2 => pos_of_nat n m
  | n.+1,    1 => xO (pos_of_nat n n)
  | n.+1,    0 => xI (pos_of_nat n n)
  |    0,    _ => xH
  end.

Definition bin_of_nat n0 := if n0 is n.+1 then Npos (pos_of_nat n n) else 0%num.

Lemma bin_of_natK : cancel bin_of_nat nat_of_bin.
Proof.
have sub2nn n : n.*2 - n = n by rewrite -addnn addKn.
case=> //= n; rewrite -{3}[n]sub2nn.
by elim: n {2 4}n => // m IHm [|[|n]] //=; rewrite IHm // natTrecE sub2nn.
Qed.

Lemma nat_of_binK : cancel nat_of_bin bin_of_nat.
Proof.
case=> //=; elim=> //= p; case: (nat_of_pos p) => //= n [<-].
  by rewrite natTrecE !addnS {2}addnn; elim: {1 3}n.
by rewrite natTrecE addnS /= addnS {2}addnn; elim: {1 3}n.
Qed.

Lemma nat_of_succ_gt0 p : Psucc p = p.+1 :> nat.
Proof. by elim: p => //= p ->; rewrite !natTrecE. Qed.

Lemma nat_of_addn_gt0 p q : (p + q)%positive = p + q :> nat.
Proof.
apply: fst (Pplus_carry p q = (p + q).+1 :> nat) _.
elim: p q => [p IHp|p IHp|] [q|q|] //=; rewrite !natTrecE //;
  by rewrite ?IHp ?nat_of_succ_gt0 ?(doubleS, double_add, addn1, addnS).
Qed.

Lemma nat_of_add_bin b1 b2 : (b1 + b2)%num = b1 + b2 :> nat.
Proof. case: b1 b2 => [|p] [|q] //=; exact: nat_of_addn_gt0. Qed.

Lemma nat_of_mul_bin b1 b2 : (b1 * b2)%num = b1 * b2 :> nat.
Proof.
case: b1 b2 => [|p] [|q] //=; elim: p => [p IHp|p IHp|] /=;
  by rewrite ?(mul1n, nat_of_addn_gt0, mulSn) //= !natTrecE IHp double_mull.
Qed.

Lemma nat_of_exp_bin n (b : N) : n ^ b = pow_N 1 muln n b.
Proof.
case: b => [|p] /=; first exact: expn0.
by elim: p => //= p <-; rewrite natTrecE mulnn -expn_mulr muln2 ?expnS.
Qed.

End NumberInterpretation.

(* Big(ger) nat IO; usage:                              *)
(*     Num 1 072 399                                    *)
(*        to create large numbers for test cases        *)
(* Eval compute in [Num of some expression]             *)
(*        to display the resut of an expression that    *)
(*        returns a larger integer.                     *)

Record number : Type := Num {bin_of_number :> N}.

Definition extend_number (nn : number) m := Num (nn * 1000 + bin_of_nat m).

Coercion extend_number : number >-> Funclass.

Canonical number_subType := [newType for bin_of_number by number_rect].
Definition number_eqMixin := Eval hnf in [eqMixin of number by <:].
Canonical number_eqType := Eval hnf in EqType number number_eqMixin.

Notation "[ 'Num' 'of' e ]" := (Num (bin_of_nat e))
  (at level 0, format "[ 'Num'  'of'  e ]") : nat_scope.

(* Interface to ring/ring_simplify tactics *)

Lemma nat_semi_ring : semi_ring_theory 0 1 addn muln (@eq _).
Proof. exact: mk_srt add0n addnC addnA mul1n mul0n mulnC mulnA muln_addl. Qed.

Lemma nat_semi_morph :
  semi_morph 0 1 addn muln (@eq _) 0%num 1%num Nplus Nmult pred1 nat_of_bin.
Proof.
by move: nat_of_add_bin nat_of_mul_bin; split=> //= m n; move/eqP->.
Qed.

Lemma nat_power_theory : power_theory 1 muln (@eq _) nat_of_bin expn.
Proof. split; exact: nat_of_exp_bin. Qed.

(* Interface to the ring tactic machinery. *)

Fixpoint pop_succn e := if e is e'.+1 then fun n => pop_succn e' n.+1 else id.

Ltac pop_succn e := eval lazy beta iota delta [pop_succn] in (pop_succn e 1).

Ltac nat_litteral e :=
  match pop_succn e with
  | ?n.+1 => constr: (bin_of_nat n)
  |     _ => NotConstant
  end.

Ltac succn_to_add :=
  match goal with
  | |- context G [?e.+1] =>
    let x := fresh "NatLit0" in
    match pop_succn e with
    | ?n.+1 => pose x := n.+1; let G' := context G [x] in change G'
    | _ ?e' ?n => pose x := n; let G' := context G [x + e'] in change G'
    end; succn_to_add; rewrite {}/x
  | _ => idtac
  end.

Add Ring nat_ring_ssr : nat_semi_ring (morphism nat_semi_morph,
   constants [nat_litteral], preprocess [succn_to_add],
   power_tac nat_power_theory [nat_litteral]).

(* A congruence tactic, similar to the boolean one, along with an .+1/+  *)
(* normalization tactic.                                                 *)


Ltac nat_norm :=
  succn_to_add; rewrite ?add0n ?addn0 -?addnA ?(addSn, addnS, add0n, addn0).

Ltac nat_congr := first
 [ apply: (congr1 succn _)
 | apply: (congr1 predn _)
 | apply: (congr1 (addn _) _)
 | apply: (congr1 (subn _) _)
 | apply: (congr1 (addn^~ _) _)
 | match goal with |- (?X1 + ?X2 = ?X3) =>
     symmetry;
     rewrite -1?(addnC X1) -?(addnCA X1);
     apply: (congr1 (addn X1) _);
     symmetry
   end ].
