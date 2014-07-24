(*  Title:      HOL/Nat.thy
    Author:     Tobias Nipkow and Lawrence C Paulson and Markus Wenzel

Type "nat" is a linear order, and a datatype; arithmetic operators + -
and * (for div and mod, see theory Divides).
*)

header {* Natural numbers *}

theory Nat
imports Inductive Typedef Fun Fields
begin

ML_file "~~/src/Tools/rat.ML"
ML_file "Tools/arith_data.ML"
ML_file "~~/src/Provers/Arith/fast_lin_arith.ML"


subsection {* Type @{text ind} *}

typedecl ind

axiomatization Zero_Rep :: ind and Suc_Rep :: "ind => ind" where
  -- {* the axiom of infinity in 2 parts *}
  Suc_Rep_inject:       "Suc_Rep x = Suc_Rep y ==> x = y" and
  Suc_Rep_not_Zero_Rep: "Suc_Rep x \<noteq> Zero_Rep"

subsection {* Type nat *}

text {* Type definition *}

inductive Nat :: "ind \<Rightarrow> bool" where
  Zero_RepI: "Nat Zero_Rep"
| Suc_RepI: "Nat i \<Longrightarrow> Nat (Suc_Rep i)"

typedef nat = "{n. Nat n}"
  morphisms Rep_Nat Abs_Nat
  using Nat.Zero_RepI by auto

lemma Nat_Rep_Nat:
  "Nat (Rep_Nat n)"
  using Rep_Nat by simp

lemma Nat_Abs_Nat_inverse:
  "Nat n \<Longrightarrow> Rep_Nat (Abs_Nat n) = n"
  using Abs_Nat_inverse by simp

lemma Nat_Abs_Nat_inject:
  "Nat n \<Longrightarrow> Nat m \<Longrightarrow> Abs_Nat n = Abs_Nat m \<longleftrightarrow> n = m"
  using Abs_Nat_inject by simp

instantiation nat :: zero
begin

definition Zero_nat_def:
  "0 = Abs_Nat Zero_Rep"

instance ..

end

definition Suc :: "nat \<Rightarrow> nat" where
  "Suc n = Abs_Nat (Suc_Rep (Rep_Nat n))"

lemma Suc_not_Zero: "Suc m \<noteq> 0"
  by (simp add: Zero_nat_def Suc_def Suc_RepI Zero_RepI Nat_Abs_Nat_inject Suc_Rep_not_Zero_Rep Nat_Rep_Nat)

lemma Zero_not_Suc: "0 \<noteq> Suc m"
  by (rule not_sym, rule Suc_not_Zero not_sym)

lemma Suc_Rep_inject': "Suc_Rep x = Suc_Rep y \<longleftrightarrow> x = y"
  by (rule iffI, rule Suc_Rep_inject) simp_all

rep_datatype "0 \<Colon> nat" Suc
  apply (unfold Zero_nat_def Suc_def)
  apply (rule Rep_Nat_inverse [THEN subst]) -- {* types force good instantiation *}
   apply (erule Nat_Rep_Nat [THEN Nat.induct])
   apply (iprover elim: Nat_Abs_Nat_inverse [THEN subst])
    apply (simp_all add: Nat_Abs_Nat_inject Nat_Rep_Nat
      Suc_RepI Zero_RepI Suc_Rep_not_Zero_Rep
      Suc_Rep_not_Zero_Rep [symmetric]
      Suc_Rep_inject' Rep_Nat_inject)
  done

lemma nat_induct [case_names 0 Suc, induct type: nat]:
  -- {* for backward compatibility -- names of variables differ *}
  fixes n
  assumes "P 0"
    and "\<And>n. P n \<Longrightarrow> P (Suc n)"
  shows "P n"
  using assms by (rule nat.induct)

declare nat.exhaust [case_names 0 Suc, cases type: nat]

lemmas nat_rec_0 = nat.recs(1)
  and nat_rec_Suc = nat.recs(2)

lemmas nat_case_0 = nat.cases(1)
  and nat_case_Suc = nat.cases(2)
   

text {* Injectiveness and distinctness lemmas *}

lemma inj_Suc[simp]: "inj_on Suc N"
  by (simp add: inj_on_def)

lemma Suc_neq_Zero: "Suc m = 0 \<Longrightarrow> R"
by (rule notE, rule Suc_not_Zero)

lemma Zero_neq_Suc: "0 = Suc m \<Longrightarrow> R"
by (rule Suc_neq_Zero, erule sym)

lemma Suc_inject: "Suc x = Suc y \<Longrightarrow> x = y"
by (rule inj_Suc [THEN injD])

lemma n_not_Suc_n: "n \<noteq> Suc n"
by (induct n) simp_all

lemma Suc_n_not_n: "Suc n \<noteq> n"
by (rule not_sym, rule n_not_Suc_n)

text {* A special form of induction for reasoning
  about @{term "m < n"} and @{term "m - n"} *}

lemma diff_induct: "(!!x. P x 0) ==> (!!y. P 0 (Suc y)) ==>
    (!!x y. P x y ==> P (Suc x) (Suc y)) ==> P m n"
  apply (rule_tac x = m in spec)
  apply (induct n)
  prefer 2
  apply (rule allI)
  apply (induct_tac x, iprover+)
  done


subsection {* Arithmetic operators *}

instantiation nat :: comm_monoid_diff
begin

primrec plus_nat where
  add_0:      "0 + n = (n\<Colon>nat)"
| add_Suc:  "Suc m + n = Suc (m + n)"

lemma add_0_right [simp]: "m + 0 = (m::nat)"
  by (induct m) simp_all

lemma add_Suc_right [simp]: "m + Suc n = Suc (m + n)"
  by (induct m) simp_all

declare add_0 [code]

lemma add_Suc_shift [code]: "Suc m + n = m + Suc n"
  by simp

primrec minus_nat where
  diff_0 [code]: "m - 0 = (m\<Colon>nat)"
| diff_Suc: "m - Suc n = (case m - n of 0 => 0 | Suc k => k)"

declare diff_Suc [simp del]

lemma diff_0_eq_0 [simp, code]: "0 - n = (0::nat)"
  by (induct n) (simp_all add: diff_Suc)

lemma diff_Suc_Suc [simp, code]: "Suc m - Suc n = m - n"
  by (induct n) (simp_all add: diff_Suc)

instance proof
  fix n m q :: nat
  show "(n + m) + q = n + (m + q)" by (induct n) simp_all
  show "n + m = m + n" by (induct n) simp_all
  show "0 + n = n" by simp
  show "n - 0 = n" by simp
  show "0 - n = 0" by simp
  show "(q + n) - (q + m) = n - m" by (induct q) simp_all
  show "n - m - q = n - (m + q)" by (induct q) (simp_all add: diff_Suc)
qed

end

hide_fact (open) add_0 add_0_right diff_0

instantiation nat :: comm_semiring_1_cancel
begin

definition
  One_nat_def [simp]: "1 = Suc 0"

primrec times_nat where
  mult_0:     "0 * n = (0\<Colon>nat)"
| mult_Suc: "Suc m * n = n + (m * n)"

lemma mult_0_right [simp]: "(m::nat) * 0 = 0"
  by (induct m) simp_all

lemma mult_Suc_right [simp]: "m * Suc n = m + (m * n)"
  by (induct m) (simp_all add: add_left_commute)

lemma add_mult_distrib: "(m + n) * k = (m * k) + ((n * k)::nat)"
  by (induct m) (simp_all add: add_assoc)

instance proof
  fix n m q :: nat
  show "0 \<noteq> (1::nat)" unfolding One_nat_def by simp
  show "1 * n = n" unfolding One_nat_def by simp
  show "n * m = m * n" by (induct n) simp_all
  show "(n * m) * q = n * (m * q)" by (induct n) (simp_all add: add_mult_distrib)
  show "(n + m) * q = n * q + m * q" by (rule add_mult_distrib)
  assume "n + m = n + q" thus "m = q" by (induct n) simp_all
qed

end

subsubsection {* Addition *}

lemma nat_add_assoc: "(m + n) + k = m + ((n + k)::nat)"
  by (rule add_assoc)

lemma nat_add_commute: "m + n = n + (m::nat)"
  by (rule add_commute)

lemma nat_add_left_commute: "x + (y + z) = y + ((x + z)::nat)"
  by (rule add_left_commute)

lemma nat_add_left_cancel [simp]: "(k + m = k + n) = (m = (n::nat))"
  by (rule add_left_cancel)

lemma nat_add_right_cancel [simp]: "(m + k = n + k) = (m=(n::nat))"
  by (rule add_right_cancel)

text {* Reasoning about @{text "m + 0 = 0"}, etc. *}

lemma add_is_0 [iff]:
  fixes m n :: nat
  shows "(m + n = 0) = (m = 0 & n = 0)"
  by (cases m) simp_all

lemma add_is_1:
  "(m+n= Suc 0) = (m= Suc 0 & n=0 | m=0 & n= Suc 0)"
  by (cases m) simp_all

lemma one_is_add:
  "(Suc 0 = m + n) = (m = Suc 0 & n = 0 | m = 0 & n = Suc 0)"
  by (rule trans, rule eq_commute, rule add_is_1)

lemma add_eq_self_zero:
  fixes m n :: nat
  shows "m + n = m \<Longrightarrow> n = 0"
  by (induct m) simp_all

lemma inj_on_add_nat[simp]: "inj_on (%n::nat. n+k) N"
  apply (induct k)
   apply simp
  apply(drule comp_inj_on[OF _ inj_Suc])
  apply (simp add:o_def)
  done

lemma Suc_eq_plus1: "Suc n = n + 1"
  unfolding One_nat_def by simp

lemma Suc_eq_plus1_left: "Suc n = 1 + n"
  unfolding One_nat_def by simp


subsubsection {* Difference *}

lemma diff_self_eq_0 [simp]: "(m\<Colon>nat) - m = 0"
  by (induct m) simp_all

lemma diff_diff_left: "(i::nat) - j - k = i - (j + k)"
  by (induct i j rule: diff_induct) simp_all

lemma Suc_diff_diff [simp]: "(Suc m - n) - Suc k = m - n - k"
  by (simp add: diff_diff_left)

lemma diff_commute: "(i::nat) - j - k = i - k - j"
  by (simp add: diff_diff_left add_commute)

lemma diff_add_inverse: "(n + m) - n = (m::nat)"
  by (induct n) simp_all

lemma diff_add_inverse2: "(m + n) - n = (m::nat)"
  by (simp add: diff_add_inverse add_commute [of m n])

lemma diff_cancel: "(k + m) - (k + n) = m - (n::nat)"
  by (induct k) simp_all

lemma diff_cancel2: "(m + k) - (n + k) = m - (n::nat)"
  by (simp add: diff_cancel add_commute)

lemma diff_add_0: "n - (n + m) = (0::nat)"
  by (induct n) simp_all

lemma diff_Suc_1 [simp]: "Suc n - 1 = n"
  unfolding One_nat_def by simp

text {* Difference distributes over multiplication *}

lemma diff_mult_distrib: "((m::nat) - n) * k = (m * k) - (n * k)"
by (induct m n rule: diff_induct) (simp_all add: diff_cancel)

lemma diff_mult_distrib2: "k * ((m::nat) - n) = (k * m) - (k * n)"
by (simp add: diff_mult_distrib mult_commute [of k])
  -- {* NOT added as rewrites, since sometimes they are used from right-to-left *}


subsubsection {* Multiplication *}

lemma nat_mult_assoc: "(m * n) * k = m * ((n * k)::nat)"
  by (rule mult_assoc)

lemma nat_mult_commute: "m * n = n * (m::nat)"
  by (rule mult_commute)

lemma add_mult_distrib2: "k * (m + n) = (k * m) + ((k * n)::nat)"
  by (rule distrib_left)

lemma mult_is_0 [simp]: "((m::nat) * n = 0) = (m=0 | n=0)"
  by (induct m) auto

lemmas nat_distrib =
  add_mult_distrib add_mult_distrib2 diff_mult_distrib diff_mult_distrib2

lemma mult_eq_1_iff [simp]: "(m * n = Suc 0) = (m = Suc 0 & n = Suc 0)"
  apply (induct m)
   apply simp
  apply (induct n)
   apply auto
  done

lemma one_eq_mult_iff [simp,no_atp]: "(Suc 0 = m * n) = (m = Suc 0 & n = Suc 0)"
  apply (rule trans)
  apply (rule_tac [2] mult_eq_1_iff, fastforce)
  done

lemma nat_mult_eq_1_iff [simp]: "m * n = (1::nat) \<longleftrightarrow> m = 1 \<and> n = 1"
  unfolding One_nat_def by (rule mult_eq_1_iff)

lemma nat_1_eq_mult_iff [simp]: "(1::nat) = m * n \<longleftrightarrow> m = 1 \<and> n = 1"
  unfolding One_nat_def by (rule one_eq_mult_iff)

lemma mult_cancel1 [simp]: "(k * m = k * n) = (m = n | (k = (0::nat)))"
proof -
  have "k \<noteq> 0 \<Longrightarrow> k * m = k * n \<Longrightarrow> m = n"
  proof (induct n arbitrary: m)
    case 0 then show "m = 0" by simp
  next
    case (Suc n) then show "m = Suc n"
      by (cases m) (simp_all add: eq_commute [of "0"])
  qed
  then show ?thesis by auto
qed

lemma mult_cancel2 [simp]: "(m * k = n * k) = (m = n | (k = (0::nat)))"
  by (simp add: mult_commute)

lemma Suc_mult_cancel1: "(Suc k * m = Suc k * n) = (m = n)"
  by (subst mult_cancel1) simp


subsection {* Orders on @{typ nat} *}

subsubsection {* Operation definition *}

instantiation nat :: linorder
begin

primrec less_eq_nat where
  "(0\<Colon>nat) \<le> n \<longleftrightarrow> True"
| "Suc m \<le> n \<longleftrightarrow> (case n of 0 \<Rightarrow> False | Suc n \<Rightarrow> m \<le> n)"

declare less_eq_nat.simps [simp del]
lemma [code]: "(0\<Colon>nat) \<le> n \<longleftrightarrow> True" by (simp add: less_eq_nat.simps)
lemma le0 [iff]: "0 \<le> (n\<Colon>nat)" by (simp add: less_eq_nat.simps)

definition less_nat where
  less_eq_Suc_le: "n < m \<longleftrightarrow> Suc n \<le> m"

lemma Suc_le_mono [iff]: "Suc n \<le> Suc m \<longleftrightarrow> n \<le> m"
  by (simp add: less_eq_nat.simps(2))

lemma Suc_le_eq [code]: "Suc m \<le> n \<longleftrightarrow> m < n"
  unfolding less_eq_Suc_le ..

lemma le_0_eq [iff]: "(n\<Colon>nat) \<le> 0 \<longleftrightarrow> n = 0"
  by (induct n) (simp_all add: less_eq_nat.simps(2))

lemma not_less0 [iff]: "\<not> n < (0\<Colon>nat)"
  by (simp add: less_eq_Suc_le)

lemma less_nat_zero_code [code]: "n < (0\<Colon>nat) \<longleftrightarrow> False"
  by simp

lemma Suc_less_eq [iff]: "Suc m < Suc n \<longleftrightarrow> m < n"
  by (simp add: less_eq_Suc_le)

lemma less_Suc_eq_le [code]: "m < Suc n \<longleftrightarrow> m \<le> n"
  by (simp add: less_eq_Suc_le)

lemma le_SucI: "m \<le> n \<Longrightarrow> m \<le> Suc n"
  by (induct m arbitrary: n)
    (simp_all add: less_eq_nat.simps(2) split: nat.splits)

lemma Suc_leD: "Suc m \<le> n \<Longrightarrow> m \<le> n"
  by (cases n) (auto intro: le_SucI)

lemma less_SucI: "m < n \<Longrightarrow> m < Suc n"
  by (simp add: less_eq_Suc_le) (erule Suc_leD)

lemma Suc_lessD: "Suc m < n \<Longrightarrow> m < n"
  by (simp add: less_eq_Suc_le) (erule Suc_leD)

instance
proof
  fix n m :: nat
  show "n < m \<longleftrightarrow> n \<le> m \<and> \<not> m \<le> n" 
  proof (induct n arbitrary: m)
    case 0 then show ?case by (cases m) (simp_all add: less_eq_Suc_le)
  next
    case (Suc n) then show ?case by (cases m) (simp_all add: less_eq_Suc_le)
  qed
next
  fix n :: nat show "n \<le> n" by (induct n) simp_all
next
  fix n m :: nat assume "n \<le> m" and "m \<le> n"
  then show "n = m"
    by (induct n arbitrary: m)
      (simp_all add: less_eq_nat.simps(2) split: nat.splits)
next
  fix n m q :: nat assume "n \<le> m" and "m \<le> q"
  then show "n \<le> q"
  proof (induct n arbitrary: m q)
    case 0 show ?case by simp
  next
    case (Suc n) then show ?case
      by (simp_all (no_asm_use) add: less_eq_nat.simps(2) split: nat.splits, clarify,
        simp_all (no_asm_use) add: less_eq_nat.simps(2) split: nat.splits, clarify,
        simp_all (no_asm_use) add: less_eq_nat.simps(2) split: nat.splits)
  qed
next
  fix n m :: nat show "n \<le> m \<or> m \<le> n"
    by (induct n arbitrary: m)
      (simp_all add: less_eq_nat.simps(2) split: nat.splits)
qed

end

instantiation nat :: bot
begin

definition bot_nat :: nat where
  "bot_nat = 0"

instance proof
qed (simp add: bot_nat_def)

end

subsubsection {* Introduction properties *}

lemma lessI [iff]: "n < Suc n"
  by (simp add: less_Suc_eq_le)

lemma zero_less_Suc [iff]: "0 < Suc n"
  by (simp add: less_Suc_eq_le)


subsubsection {* Elimination properties *}

lemma less_not_refl: "~ n < (n::nat)"
  by (rule order_less_irrefl)

lemma less_not_refl2: "n < m ==> m \<noteq> (n::nat)"
  by (rule not_sym) (rule less_imp_neq) 

lemma less_not_refl3: "(s::nat) < t ==> s \<noteq> t"
  by (rule less_imp_neq)

lemma less_irrefl_nat: "(n::nat) < n ==> R"
  by (rule notE, rule less_not_refl)

lemma less_zeroE: "(n::nat) < 0 ==> R"
  by (rule notE) (rule not_less0)

lemma less_Suc_eq: "(m < Suc n) = (m < n | m = n)"
  unfolding less_Suc_eq_le le_less ..

lemma less_Suc0 [iff]: "(n < Suc 0) = (n = 0)"
  by (simp add: less_Suc_eq)

lemma less_one [iff, no_atp]: "(n < (1::nat)) = (n = 0)"
  unfolding One_nat_def by (rule less_Suc0)

lemma Suc_mono: "m < n ==> Suc m < Suc n"
  by simp

text {* "Less than" is antisymmetric, sort of *}
lemma less_antisym: "\<lbrakk> \<not> n < m; n < Suc m \<rbrakk> \<Longrightarrow> m = n"
  unfolding not_less less_Suc_eq_le by (rule antisym)

lemma nat_neq_iff: "((m::nat) \<noteq> n) = (m < n | n < m)"
  by (rule linorder_neq_iff)

lemma nat_less_cases: assumes major: "(m::nat) < n ==> P n m"
  and eqCase: "m = n ==> P n m" and lessCase: "n<m ==> P n m"
  shows "P n m"
  apply (rule less_linear [THEN disjE])
  apply (erule_tac [2] disjE)
  apply (erule lessCase)
  apply (erule sym [THEN eqCase])
  apply (erule major)
  done


subsubsection {* Inductive (?) properties *}

lemma Suc_lessI: "m < n ==> Suc m \<noteq> n ==> Suc m < n"
  unfolding less_eq_Suc_le [of m] le_less by simp 

lemma lessE:
  assumes major: "i < k"
  and p1: "k = Suc i ==> P" and p2: "!!j. i < j ==> k = Suc j ==> P"
  shows P
proof -
  from major have "\<exists>j. i \<le> j \<and> k = Suc j"
    unfolding less_eq_Suc_le by (induct k) simp_all
  then have "(\<exists>j. i < j \<and> k = Suc j) \<or> k = Suc i"
    by (clarsimp simp add: less_le)
  with p1 p2 show P by auto
qed

lemma less_SucE: assumes major: "m < Suc n"
  and less: "m < n ==> P" and eq: "m = n ==> P" shows P
  apply (rule major [THEN lessE])
  apply (rule eq, blast)
  apply (rule less, blast)
  done

lemma Suc_lessE: assumes major: "Suc i < k"
  and minor: "!!j. i < j ==> k = Suc j ==> P" shows P
  apply (rule major [THEN lessE])
  apply (erule lessI [THEN minor])
  apply (erule Suc_lessD [THEN minor], assumption)
  done

lemma Suc_less_SucD: "Suc m < Suc n ==> m < n"
  by simp

lemma less_trans_Suc:
  assumes le: "i < j" shows "j < k ==> Suc i < k"
  apply (induct k, simp_all)
  apply (insert le)
  apply (simp add: less_Suc_eq)
  apply (blast dest: Suc_lessD)
  done

text {* Can be used with @{text less_Suc_eq} to get @{term "n = m | n < m"} *}
lemma not_less_eq: "\<not> m < n \<longleftrightarrow> n < Suc m"
  unfolding not_less less_Suc_eq_le ..

lemma not_less_eq_eq: "\<not> m \<le> n \<longleftrightarrow> Suc n \<le> m"
  unfolding not_le Suc_le_eq ..

text {* Properties of "less than or equal" *}

lemma le_imp_less_Suc: "m \<le> n ==> m < Suc n"
  unfolding less_Suc_eq_le .

lemma Suc_n_not_le_n: "~ Suc n \<le> n"
  unfolding not_le less_Suc_eq_le ..

lemma le_Suc_eq: "(m \<le> Suc n) = (m \<le> n | m = Suc n)"
  by (simp add: less_Suc_eq_le [symmetric] less_Suc_eq)

lemma le_SucE: "m \<le> Suc n ==> (m \<le> n ==> R) ==> (m = Suc n ==> R) ==> R"
  by (drule le_Suc_eq [THEN iffD1], iprover+)

lemma Suc_leI: "m < n ==> Suc(m) \<le> n"
  unfolding Suc_le_eq .

text {* Stronger version of @{text Suc_leD} *}
lemma Suc_le_lessD: "Suc m \<le> n ==> m < n"
  unfolding Suc_le_eq .

lemma less_imp_le_nat: "m < n ==> m \<le> (n::nat)"
  unfolding less_eq_Suc_le by (rule Suc_leD)

text {* For instance, @{text "(Suc m < Suc n) = (Suc m \<le> n) = (m < n)"} *}
lemmas le_simps = less_imp_le_nat less_Suc_eq_le Suc_le_eq


text {* Equivalence of @{term "m \<le> n"} and @{term "m < n | m = n"} *}

lemma less_or_eq_imp_le: "m < n | m = n ==> m \<le> (n::nat)"
  unfolding le_less .

lemma le_eq_less_or_eq: "(m \<le> (n::nat)) = (m < n | m=n)"
  by (rule le_less)

text {* Useful with @{text blast}. *}
lemma eq_imp_le: "(m::nat) = n ==> m \<le> n"
  by auto

lemma le_refl: "n \<le> (n::nat)"
  by simp

lemma le_trans: "[| i \<le> j; j \<le> k |] ==> i \<le> (k::nat)"
  by (rule order_trans)

lemma le_antisym: "[| m \<le> n; n \<le> m |] ==> m = (n::nat)"
  by (rule antisym)

lemma nat_less_le: "((m::nat) < n) = (m \<le> n & m \<noteq> n)"
  by (rule less_le)

lemma le_neq_implies_less: "(m::nat) \<le> n ==> m \<noteq> n ==> m < n"
  unfolding less_le ..

lemma nat_le_linear: "(m::nat) \<le> n | n \<le> m"
  by (rule linear)

lemmas linorder_neqE_nat = linorder_neqE [where 'a = nat]

lemma le_less_Suc_eq: "m \<le> n ==> (n < Suc m) = (n = m)"
  unfolding less_Suc_eq_le by auto

lemma not_less_less_Suc_eq: "~ n < m ==> (n < Suc m) = (n = m)"
  unfolding not_less by (rule le_less_Suc_eq)

lemmas not_less_simps = not_less_less_Suc_eq le_less_Suc_eq

text {* These two rules ease the use of primitive recursion.
NOTE USE OF @{text "=="} *}
lemma def_nat_rec_0: "(!!n. f n == nat_rec c h n) ==> f 0 = c"
by simp

lemma def_nat_rec_Suc: "(!!n. f n == nat_rec c h n) ==> f (Suc n) = h n (f n)"
by simp

lemma not0_implies_Suc: "n \<noteq> 0 ==> \<exists>m. n = Suc m"
by (cases n) simp_all

lemma gr0_implies_Suc: "n > 0 ==> \<exists>m. n = Suc m"
by (cases n) simp_all

lemma gr_implies_not0: fixes n :: nat shows "m<n ==> n \<noteq> 0"
by (cases n) simp_all

lemma neq0_conv[iff]: fixes n :: nat shows "(n \<noteq> 0) = (0 < n)"
by (cases n) simp_all

text {* This theorem is useful with @{text blast} *}
lemma gr0I: "((n::nat) = 0 ==> False) ==> 0 < n"
by (rule neq0_conv[THEN iffD1], iprover)

lemma gr0_conv_Suc: "(0 < n) = (\<exists>m. n = Suc m)"
by (fast intro: not0_implies_Suc)

lemma not_gr0 [iff,no_atp]: "!!n::nat. (~ (0 < n)) = (n = 0)"
using neq0_conv by blast

lemma Suc_le_D: "(Suc n \<le> m') ==> (? m. m' = Suc m)"
by (induct m') simp_all

text {* Useful in certain inductive arguments *}
lemma less_Suc_eq_0_disj: "(m < Suc n) = (m = 0 | (\<exists>j. m = Suc j & j < n))"
by (cases m) simp_all


subsubsection {* Monotonicity of Addition *}

lemma Suc_pred [simp]: "n>0 ==> Suc (n - Suc 0) = n"
by (simp add: diff_Suc split: nat.split)

lemma Suc_diff_1 [simp]: "0 < n ==> Suc (n - 1) = n"
unfolding One_nat_def by (rule Suc_pred)

lemma nat_add_left_cancel_le [simp]: "(k + m \<le> k + n) = (m\<le>(n::nat))"
by (induct k) simp_all

lemma nat_add_left_cancel_less [simp]: "(k + m < k + n) = (m<(n::nat))"
by (induct k) simp_all

lemma add_gr_0 [iff]: "!!m::nat. (m + n > 0) = (m>0 | n>0)"
by(auto dest:gr0_implies_Suc)

text {* strict, in 1st argument *}
lemma add_less_mono1: "i < j ==> i + k < j + (k::nat)"
by (induct k) simp_all

text {* strict, in both arguments *}
lemma add_less_mono: "[|i < j; k < l|] ==> i + k < j + (l::nat)"
  apply (rule add_less_mono1 [THEN less_trans], assumption+)
  apply (induct j, simp_all)
  done

text {* Deleted @{text less_natE}; use @{text "less_imp_Suc_add RS exE"} *}
lemma less_imp_Suc_add: "m < n ==> (\<exists>k. n = Suc (m + k))"
  apply (induct n)
  apply (simp_all add: order_le_less)
  apply (blast elim!: less_SucE
               intro!: Nat.add_0_right [symmetric] add_Suc_right [symmetric])
  done

text {* strict, in 1st argument; proof is by induction on @{text "k > 0"} *}
lemma mult_less_mono2: "(i::nat) < j ==> 0<k ==> k * i < k * j"
apply(auto simp: gr0_conv_Suc)
apply (induct_tac m)
apply (simp_all add: add_less_mono)
done

text{*The naturals form an ordered @{text comm_semiring_1_cancel}*}
instance nat :: linordered_semidom
proof
  fix i j k :: nat
  show "0 < (1::nat)" by simp
  show "i \<le> j ==> k + i \<le> k + j" by simp
  show "i < j ==> 0 < k ==> k * i < k * j" by (simp add: mult_less_mono2)
qed

instance nat :: no_zero_divisors
proof
  fix a::nat and b::nat show "a ~= 0 \<Longrightarrow> b ~= 0 \<Longrightarrow> a * b ~= 0" by auto
qed


subsubsection {* @{term min} and @{term max} *}

lemma mono_Suc: "mono Suc"
by (rule monoI) simp

lemma min_0L [simp]: "min 0 n = (0::nat)"
by (rule min_absorb1) simp

lemma min_0R [simp]: "min n 0 = (0::nat)"
by (rule min_absorb2) simp

lemma min_Suc_Suc [simp]: "min (Suc m) (Suc n) = Suc (min m n)"
by (simp add: mono_Suc min_of_mono)

lemma min_Suc1:
   "min (Suc n) m = (case m of 0 => 0 | Suc m' => Suc(min n m'))"
by (simp split: nat.split)

lemma min_Suc2:
   "min m (Suc n) = (case m of 0 => 0 | Suc m' => Suc(min m' n))"
by (simp split: nat.split)

lemma max_0L [simp]: "max 0 n = (n::nat)"
by (rule max_absorb2) simp

lemma max_0R [simp]: "max n 0 = (n::nat)"
by (rule max_absorb1) simp

lemma max_Suc_Suc [simp]: "max (Suc m) (Suc n) = Suc(max m n)"
by (simp add: mono_Suc max_of_mono)

lemma max_Suc1:
   "max (Suc n) m = (case m of 0 => Suc n | Suc m' => Suc(max n m'))"
by (simp split: nat.split)

lemma max_Suc2:
   "max m (Suc n) = (case m of 0 => Suc n | Suc m' => Suc(max m' n))"
by (simp split: nat.split)

lemma nat_mult_min_left:
  fixes m n q :: nat
  shows "min m n * q = min (m * q) (n * q)"
  by (simp add: min_def not_le) (auto dest: mult_right_le_imp_le mult_right_less_imp_less le_less_trans)

lemma nat_mult_min_right:
  fixes m n q :: nat
  shows "m * min n q = min (m * n) (m * q)"
  by (simp add: min_def not_le) (auto dest: mult_left_le_imp_le mult_left_less_imp_less le_less_trans)

lemma nat_add_max_left:
  fixes m n q :: nat
  shows "max m n + q = max (m + q) (n + q)"
  by (simp add: max_def)

lemma nat_add_max_right:
  fixes m n q :: nat
  shows "m + max n q = max (m + n) (m + q)"
  by (simp add: max_def)

lemma nat_mult_max_left:
  fixes m n q :: nat
  shows "max m n * q = max (m * q) (n * q)"
  by (simp add: max_def not_le) (auto dest: mult_right_le_imp_le mult_right_less_imp_less le_less_trans)

lemma nat_mult_max_right:
  fixes m n q :: nat
  shows "m * max n q = max (m * n) (m * q)"
  by (simp add: max_def not_le) (auto dest: mult_left_le_imp_le mult_left_less_imp_less le_less_trans)


subsubsection {* Additional theorems about @{term "op \<le>"} *}

text {* Complete induction, aka course-of-values induction *}

instance nat :: wellorder proof
  fix P and n :: nat
  assume step: "\<And>n::nat. (\<And>m. m < n \<Longrightarrow> P m) \<Longrightarrow> P n"
  have "\<And>q. q \<le> n \<Longrightarrow> P q"
  proof (induct n)
    case (0 n)
    have "P 0" by (rule step) auto
    thus ?case using 0 by auto
  next
    case (Suc m n)
    then have "n \<le> m \<or> n = Suc m" by (simp add: le_Suc_eq)
    thus ?case
    proof
      assume "n \<le> m" thus "P n" by (rule Suc(1))
    next
      assume n: "n = Suc m"
      show "P n"
        by (rule step) (rule Suc(1), simp add: n le_simps)
    qed
  qed
  then show "P n" by auto
qed

lemma Least_Suc:
     "[| P n; ~ P 0 |] ==> (LEAST n. P n) = Suc (LEAST m. P(Suc m))"
  apply (cases n, auto)
  apply (frule LeastI)
  apply (drule_tac P = "%x. P (Suc x) " in LeastI)
  apply (subgoal_tac " (LEAST x. P x) \<le> Suc (LEAST x. P (Suc x))")
  apply (erule_tac [2] Least_le)
  apply (cases "LEAST x. P x", auto)
  apply (drule_tac P = "%x. P (Suc x) " in Least_le)
  apply (blast intro: order_antisym)
  done

lemma Least_Suc2:
   "[|P n; Q m; ~P 0; !k. P (Suc k) = Q k|] ==> Least P = Suc (Least Q)"
  apply (erule (1) Least_Suc [THEN ssubst])
  apply simp
  done

lemma ex_least_nat_le: "\<not>P(0) \<Longrightarrow> P(n::nat) \<Longrightarrow> \<exists>k\<le>n. (\<forall>i<k. \<not>P i) & P(k)"
  apply (cases n)
   apply blast
  apply (rule_tac x="LEAST k. P(k)" in exI)
  apply (blast intro: Least_le dest: not_less_Least intro: LeastI_ex)
  done

lemma ex_least_nat_less: "\<not>P(0) \<Longrightarrow> P(n::nat) \<Longrightarrow> \<exists>k<n. (\<forall>i\<le>k. \<not>P i) & P(k+1)"
  unfolding One_nat_def
  apply (cases n)
   apply blast
  apply (frule (1) ex_least_nat_le)
  apply (erule exE)
  apply (case_tac k)
   apply simp
  apply (rename_tac k1)
  apply (rule_tac x=k1 in exI)
  apply (auto simp add: less_eq_Suc_le)
  done

lemma nat_less_induct:
  assumes "!!n. \<forall>m::nat. m < n --> P m ==> P n" shows "P n"
  using assms less_induct by blast

lemma measure_induct_rule [case_names less]:
  fixes f :: "'a \<Rightarrow> nat"
  assumes step: "\<And>x. (\<And>y. f y < f x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P a"
by (induct m\<equiv>"f a" arbitrary: a rule: less_induct) (auto intro: step)

text {* old style induction rules: *}
lemma measure_induct:
  fixes f :: "'a \<Rightarrow> nat"
  shows "(\<And>x. \<forall>y. f y < f x \<longrightarrow> P y \<Longrightarrow> P x) \<Longrightarrow> P a"
  by (rule measure_induct_rule [of f P a]) iprover

lemma full_nat_induct:
  assumes step: "(!!n. (ALL m. Suc m <= n --> P m) ==> P n)"
  shows "P n"
  by (rule less_induct) (auto intro: step simp:le_simps)

text{*An induction rule for estabilishing binary relations*}
lemma less_Suc_induct:
  assumes less:  "i < j"
     and  step:  "!!i. P i (Suc i)"
     and  trans: "!!i j k. i < j ==> j < k ==>  P i j ==> P j k ==> P i k"
  shows "P i j"
proof -
  from less obtain k where j: "j = Suc (i + k)" by (auto dest: less_imp_Suc_add)
  have "P i (Suc (i + k))"
  proof (induct k)
    case 0
    show ?case by (simp add: step)
  next
    case (Suc k)
    have "0 + i < Suc k + i" by (rule add_less_mono1) simp
    hence "i < Suc (i + k)" by (simp add: add_commute)
    from trans[OF this lessI Suc step]
    show ?case by simp
  qed
  thus "P i j" by (simp add: j)
qed

text {* The method of infinite descent, frequently used in number theory.
Provided by Roelof Oosterhuis.
$P(n)$ is true for all $n\in\mathbb{N}$ if
\begin{itemize}
  \item case ``0'': given $n=0$ prove $P(n)$,
  \item case ``smaller'': given $n>0$ and $\neg P(n)$ prove there exists
        a smaller integer $m$ such that $\neg P(m)$.
\end{itemize} *}

text{* A compact version without explicit base case: *}
lemma infinite_descent:
  "\<lbrakk> !!n::nat. \<not> P n \<Longrightarrow>  \<exists>m<n. \<not>  P m \<rbrakk> \<Longrightarrow>  P n"
by (induct n rule: less_induct) auto

lemma infinite_descent0[case_names 0 smaller]: 
  "\<lbrakk> P 0; !!n. n>0 \<Longrightarrow> \<not> P n \<Longrightarrow> (\<exists>m::nat. m < n \<and> \<not>P m) \<rbrakk> \<Longrightarrow> P n"
by (rule infinite_descent) (case_tac "n>0", auto)

text {*
Infinite descent using a mapping to $\mathbb{N}$:
$P(x)$ is true for all $x\in D$ if there exists a $V: D \to \mathbb{N}$ and
\begin{itemize}
\item case ``0'': given $V(x)=0$ prove $P(x)$,
\item case ``smaller'': given $V(x)>0$ and $\neg P(x)$ prove there exists a $y \in D$ such that $V(y)<V(x)$ and $~\neg P(y)$.
\end{itemize}
NB: the proof also shows how to use the previous lemma. *}

corollary infinite_descent0_measure [case_names 0 smaller]:
  assumes A0: "!!x. V x = (0::nat) \<Longrightarrow> P x"
    and   A1: "!!x. V x > 0 \<Longrightarrow> \<not>P x \<Longrightarrow> (\<exists>y. V y < V x \<and> \<not>P y)"
  shows "P x"
proof -
  obtain n where "n = V x" by auto
  moreover have "\<And>x. V x = n \<Longrightarrow> P x"
  proof (induct n rule: infinite_descent0)
    case 0 -- "i.e. $V(x) = 0$"
    with A0 show "P x" by auto
  next -- "now $n>0$ and $P(x)$ does not hold for some $x$ with $V(x)=n$"
    case (smaller n)
    then obtain x where vxn: "V x = n " and "V x > 0 \<and> \<not> P x" by auto
    with A1 obtain y where "V y < V x \<and> \<not> P y" by auto
    with vxn obtain m where "m = V y \<and> m<n \<and> \<not> P y" by auto
    then show ?case by auto
  qed
  ultimately show "P x" by auto
qed

text{* Again, without explicit base case: *}
lemma infinite_descent_measure:
assumes "!!x. \<not> P x \<Longrightarrow> \<exists>y. (V::'a\<Rightarrow>nat) y < V x \<and> \<not> P y" shows "P x"
proof -
  from assms obtain n where "n = V x" by auto
  moreover have "!!x. V x = n \<Longrightarrow> P x"
  proof (induct n rule: infinite_descent, auto)
    fix x assume "\<not> P x"
    with assms show "\<exists>m < V x. \<exists>y. V y = m \<and> \<not> P y" by auto
  qed
  ultimately show "P x" by auto
qed

text {* A [clumsy] way of lifting @{text "<"}
  monotonicity to @{text "\<le>"} monotonicity *}
lemma less_mono_imp_le_mono:
  "\<lbrakk> !!i j::nat. i < j \<Longrightarrow> f i < f j; i \<le> j \<rbrakk> \<Longrightarrow> f i \<le> ((f j)::nat)"
by (simp add: order_le_less) (blast)


text {* non-strict, in 1st argument *}
lemma add_le_mono1: "i \<le> j ==> i + k \<le> j + (k::nat)"
by (rule add_right_mono)

text {* non-strict, in both arguments *}
lemma add_le_mono: "[| i \<le> j;  k \<le> l |] ==> i + k \<le> j + (l::nat)"
by (rule add_mono)

lemma le_add2: "n \<le> ((m + n)::nat)"
by (insert add_right_mono [of 0 m n], simp)

lemma le_add1: "n \<le> ((n + m)::nat)"
by (simp add: add_commute, rule le_add2)

lemma less_add_Suc1: "i < Suc (i + m)"
by (rule le_less_trans, rule le_add1, rule lessI)

lemma less_add_Suc2: "i < Suc (m + i)"
by (rule le_less_trans, rule le_add2, rule lessI)

lemma less_iff_Suc_add: "(m < n) = (\<exists>k. n = Suc (m + k))"
by (iprover intro!: less_add_Suc1 less_imp_Suc_add)

lemma trans_le_add1: "(i::nat) \<le> j ==> i \<le> j + m"
by (rule le_trans, assumption, rule le_add1)

lemma trans_le_add2: "(i::nat) \<le> j ==> i \<le> m + j"
by (rule le_trans, assumption, rule le_add2)

lemma trans_less_add1: "(i::nat) < j ==> i < j + m"
by (rule less_le_trans, assumption, rule le_add1)

lemma trans_less_add2: "(i::nat) < j ==> i < m + j"
by (rule less_le_trans, assumption, rule le_add2)

lemma add_lessD1: "i + j < (k::nat) ==> i < k"
apply (rule le_less_trans [of _ "i+j"])
apply (simp_all add: le_add1)
done

lemma not_add_less1 [iff]: "~ (i + j < (i::nat))"
apply (rule notI)
apply (drule add_lessD1)
apply (erule less_irrefl [THEN notE])
done

lemma not_add_less2 [iff]: "~ (j + i < (i::nat))"
by (simp add: add_commute)

lemma add_leD1: "m + k \<le> n ==> m \<le> (n::nat)"
apply (rule order_trans [of _ "m+k"])
apply (simp_all add: le_add1)
done

lemma add_leD2: "m + k \<le> n ==> k \<le> (n::nat)"
apply (simp add: add_commute)
apply (erule add_leD1)
done

lemma add_leE: "(m::nat) + k \<le> n ==> (m \<le> n ==> k \<le> n ==> R) ==> R"
by (blast dest: add_leD1 add_leD2)

text {* needs @{text "!!k"} for @{text add_ac} to work *}
lemma less_add_eq_less: "!!k::nat. k < l ==> m + l = k + n ==> m < n"
by (force simp del: add_Suc_right
    simp add: less_iff_Suc_add add_Suc_right [symmetric] add_ac)


subsubsection {* More results about difference *}

text {* Addition is the inverse of subtraction:
  if @{term "n \<le> m"} then @{term "n + (m - n) = m"}. *}
lemma add_diff_inverse: "~  m < n ==> n + (m - n) = (m::nat)"
by (induct m n rule: diff_induct) simp_all

lemma le_add_diff_inverse [simp]: "n \<le> m ==> n + (m - n) = (m::nat)"
by (simp add: add_diff_inverse linorder_not_less)

lemma le_add_diff_inverse2 [simp]: "n \<le> m ==> (m - n) + n = (m::nat)"
by (simp add: add_commute)

lemma Suc_diff_le: "n \<le> m ==> Suc m - n = Suc (m - n)"
by (induct m n rule: diff_induct) simp_all

lemma diff_less_Suc: "m - n < Suc m"
apply (induct m n rule: diff_induct)
apply (erule_tac [3] less_SucE)
apply (simp_all add: less_Suc_eq)
done

lemma diff_le_self [simp]: "m - n \<le> (m::nat)"
by (induct m n rule: diff_induct) (simp_all add: le_SucI)

lemma le_iff_add: "(m::nat) \<le> n = (\<exists>k. n = m + k)"
  by (auto simp: le_add1 dest!: le_add_diff_inverse sym [of _ n])

lemma less_imp_diff_less: "(j::nat) < k ==> j - n < k"
by (rule le_less_trans, rule diff_le_self)

lemma diff_Suc_less [simp]: "0<n ==> n - Suc i < n"
by (cases n) (auto simp add: le_simps)

lemma diff_add_assoc: "k \<le> (j::nat) ==> (i + j) - k = i + (j - k)"
by (induct j k rule: diff_induct) simp_all

lemma diff_add_assoc2: "k \<le> (j::nat) ==> (j + i) - k = (j - k) + i"
by (simp add: add_commute diff_add_assoc)

lemma le_imp_diff_is_add: "i \<le> (j::nat) ==> (j - i = k) = (j = k + i)"
by (auto simp add: diff_add_inverse2)

lemma diff_is_0_eq [simp]: "((m::nat) - n = 0) = (m \<le> n)"
by (induct m n rule: diff_induct) simp_all

lemma diff_is_0_eq' [simp]: "m \<le> n ==> (m::nat) - n = 0"
by (rule iffD2, rule diff_is_0_eq)

lemma zero_less_diff [simp]: "(0 < n - (m::nat)) = (m < n)"
by (induct m n rule: diff_induct) simp_all

lemma less_imp_add_positive:
  assumes "i < j"
  shows "\<exists>k::nat. 0 < k & i + k = j"
proof
  from assms show "0 < j - i & i + (j - i) = j"
    by (simp add: order_less_imp_le)
qed

text {* a nice rewrite for bounded subtraction *}
lemma nat_minus_add_max:
  fixes n m :: nat
  shows "n - m + m = max n m"
    by (simp add: max_def not_le order_less_imp_le)

lemma nat_diff_split:
  "P(a - b::nat) = ((a<b --> P 0) & (ALL d. a = b + d --> P d))"
    -- {* elimination of @{text -} on @{text nat} *}
by (cases "a < b")
  (auto simp add: diff_is_0_eq [THEN iffD2] diff_add_inverse
    not_less le_less dest!: sym [of a] sym [of b] add_eq_self_zero)

lemma nat_diff_split_asm:
  "P(a - b::nat) = (~ (a < b & ~ P 0 | (EX d. a = b + d & ~ P d)))"
    -- {* elimination of @{text -} on @{text nat} in assumptions *}
by (auto split: nat_diff_split)

lemma Suc_pred': "0 < n ==> n = Suc(n - 1)"
  by simp

lemma add_eq_if: "(m::nat) + n = (if m=0 then n else Suc ((m - 1) + n))"
  unfolding One_nat_def by (cases m) simp_all

lemma mult_eq_if: "(m::nat) * n = (if m=0 then 0 else n + ((m - 1) * n))"
  unfolding One_nat_def by (cases m) simp_all

lemma Suc_diff_eq_diff_pred: "0 < n ==> Suc m - n = m - (n - 1)"
  unfolding One_nat_def by (cases n) simp_all

lemma diff_Suc_eq_diff_pred: "m - Suc n = (m - 1) - n"
  unfolding One_nat_def by (cases m) simp_all

lemma Let_Suc [simp]: "Let (Suc n) f == f (Suc n)"
  by (fact Let_def)


subsubsection {* Monotonicity of Multiplication *}

lemma mult_le_mono1: "i \<le> (j::nat) ==> i * k \<le> j * k"
by (simp add: mult_right_mono)

lemma mult_le_mono2: "i \<le> (j::nat) ==> k * i \<le> k * j"
by (simp add: mult_left_mono)

text {* @{text "\<le>"} monotonicity, BOTH arguments *}
lemma mult_le_mono: "i \<le> (j::nat) ==> k \<le> l ==> i * k \<le> j * l"
by (simp add: mult_mono)

lemma mult_less_mono1: "(i::nat) < j ==> 0 < k ==> i * k < j * k"
by (simp add: mult_strict_right_mono)

text{*Differs from the standard @{text zero_less_mult_iff} in that
      there are no negative numbers.*}
lemma nat_0_less_mult_iff [simp]: "(0 < (m::nat) * n) = (0 < m & 0 < n)"
  apply (induct m)
   apply simp
  apply (case_tac n)
   apply simp_all
  done

lemma one_le_mult_iff [simp]: "(Suc 0 \<le> m * n) = (Suc 0 \<le> m & Suc 0 \<le> n)"
  apply (induct m)
   apply simp
  apply (case_tac n)
   apply simp_all
  done

lemma mult_less_cancel2 [simp]: "((m::nat) * k < n * k) = (0 < k & m < n)"
  apply (safe intro!: mult_less_mono1)
  apply (cases k, auto)
  apply (simp del: le_0_eq add: linorder_not_le [symmetric])
  apply (blast intro: mult_le_mono1)
  done

lemma mult_less_cancel1 [simp]: "(k * (m::nat) < k * n) = (0 < k & m < n)"
by (simp add: mult_commute [of k])

lemma mult_le_cancel1 [simp]: "(k * (m::nat) \<le> k * n) = (0 < k --> m \<le> n)"
by (simp add: linorder_not_less [symmetric], auto)

lemma mult_le_cancel2 [simp]: "((m::nat) * k \<le> n * k) = (0 < k --> m \<le> n)"
by (simp add: linorder_not_less [symmetric], auto)

lemma Suc_mult_less_cancel1: "(Suc k * m < Suc k * n) = (m < n)"
by (subst mult_less_cancel1) simp

lemma Suc_mult_le_cancel1: "(Suc k * m \<le> Suc k * n) = (m \<le> n)"
by (subst mult_le_cancel1) simp

lemma le_square: "m \<le> m * (m::nat)"
  by (cases m) (auto intro: le_add1)

lemma le_cube: "(m::nat) \<le> m * (m * m)"
  by (cases m) (auto intro: le_add1)

text {* Lemma for @{text gcd} *}
lemma mult_eq_self_implies_10: "(m::nat) = m * n ==> n = 1 | m = 0"
  apply (drule sym)
  apply (rule disjCI)
  apply (rule nat_less_cases, erule_tac [2] _)
   apply (drule_tac [2] mult_less_mono2)
    apply (auto)
  done

text {* the lattice order on @{typ nat} *}

instantiation nat :: distrib_lattice
begin

definition
  "(inf \<Colon> nat \<Rightarrow> nat \<Rightarrow> nat) = min"

definition
  "(sup \<Colon> nat \<Rightarrow> nat \<Rightarrow> nat) = max"

instance by intro_classes
  (auto simp add: inf_nat_def sup_nat_def max_def not_le min_def
    intro: order_less_imp_le antisym elim!: order_trans order_less_trans)

end


subsection {* Natural operation of natural numbers on functions *}

text {*
  We use the same logical constant for the power operations on
  functions and relations, in order to share the same syntax.
*}

consts compow :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"

abbreviation compower :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infixr "^^" 80) where
  "f ^^ n \<equiv> compow n f"

notation (latex output)
  compower ("(_\<^bsup>_\<^esup>)" [1000] 1000)

notation (HTML output)
  compower ("(_\<^bsup>_\<^esup>)" [1000] 1000)

text {* @{text "f ^^ n = f o ... o f"}, the n-fold composition of @{text f} *}

overloading
  funpow == "compow :: nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)"
begin

primrec funpow :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "funpow 0 f = id"
| "funpow (Suc n) f = f o funpow n f"

end

lemma funpow_Suc_right:
  "f ^^ Suc n = f ^^ n \<circ> f"
proof (induct n)
  case 0 then show ?case by simp
next
  fix n
  assume "f ^^ Suc n = f ^^ n \<circ> f"
  then show "f ^^ Suc (Suc n) = f ^^ Suc n \<circ> f"
    by (simp add: o_assoc)
qed

lemmas funpow_simps_right = funpow.simps(1) funpow_Suc_right

text {* for code generation *}

definition funpow :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  funpow_code_def [code_abbrev]: "funpow = compow"

lemma [code]:
  "funpow (Suc n) f = f o funpow n f"
  "funpow 0 f = id"
  by (simp_all add: funpow_code_def)

hide_const (open) funpow

lemma funpow_add:
  "f ^^ (m + n) = f ^^ m \<circ> f ^^ n"
  by (induct m) simp_all

lemma funpow_mult:
  fixes f :: "'a \<Rightarrow> 'a"
  shows "(f ^^ m) ^^ n = f ^^ (m * n)"
  by (induct n) (simp_all add: funpow_add)

lemma funpow_swap1:
  "f ((f ^^ n) x) = (f ^^ n) (f x)"
proof -
  have "f ((f ^^ n) x) = (f ^^ (n + 1)) x" by simp
  also have "\<dots>  = (f ^^ n o f ^^ 1) x" by (simp only: funpow_add)
  also have "\<dots> = (f ^^ n) (f x)" by simp
  finally show ?thesis .
qed

lemma comp_funpow:
  fixes f :: "'a \<Rightarrow> 'a"
  shows "comp f ^^ n = comp (f ^^ n)"
  by (induct n) simp_all


subsection {* Kleene iteration *}

lemma Kleene_iter_lpfp: assumes "mono f" and "f p \<le> p" shows "(f^^k) bot \<le> p"
proof(induction k)
  case 0 show ?case by simp
next
  case Suc
  from monoD[OF assms(1) Suc] assms(2)
  show ?case by simp
qed

lemma lfp_Kleene_iter: assumes "mono f" and "(f^^Suc k) bot = (f^^k) bot"
shows "lfp f = (f^^k) bot"
proof(rule antisym)
  show "lfp f \<le> (f^^k) bot"
  proof(rule lfp_lowerbound)
    show "f ((f^^k) bot) \<le> (f^^k) bot" using assms(2) by simp
  qed
next
  show "(f^^k) bot \<le> lfp f"
    using Kleene_iter_lpfp[OF assms(1)] lfp_unfold[OF assms(1)] by simp
qed


subsection {* Embedding of the Naturals into any @{text semiring_1}: @{term of_nat} *}

context semiring_1
begin

definition of_nat :: "nat \<Rightarrow> 'a" where
  "of_nat n = (plus 1 ^^ n) 0"

lemma of_nat_simps [simp]:
  shows of_nat_0: "of_nat 0 = 0"
    and of_nat_Suc: "of_nat (Suc m) = 1 + of_nat m"
  by (simp_all add: of_nat_def)

lemma of_nat_1 [simp]: "of_nat 1 = 1"
  by (simp add: of_nat_def)

lemma of_nat_add [simp]: "of_nat (m + n) = of_nat m + of_nat n"
  by (induct m) (simp_all add: add_ac)

lemma of_nat_mult: "of_nat (m * n) = of_nat m * of_nat n"
  by (induct m) (simp_all add: add_ac distrib_right)

primrec of_nat_aux :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "of_nat_aux inc 0 i = i"
| "of_nat_aux inc (Suc n) i = of_nat_aux inc n (inc i)" -- {* tail recursive *}

lemma of_nat_code:
  "of_nat n = of_nat_aux (\<lambda>i. i + 1) n 0"
proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "\<And>i. of_nat_aux (\<lambda>i. i + 1) n (i + 1) = of_nat_aux (\<lambda>i. i + 1) n i + 1"
    by (induct n) simp_all
  from this [of 0] have "of_nat_aux (\<lambda>i. i + 1) n 1 = of_nat_aux (\<lambda>i. i + 1) n 0 + 1"
    by simp
  with Suc show ?case by (simp add: add_commute)
qed

end

declare of_nat_code [code]

text{*Class for unital semirings with characteristic zero.
 Includes non-ordered rings like the complex numbers.*}

class semiring_char_0 = semiring_1 +
  assumes inj_of_nat: "inj of_nat"
begin

lemma of_nat_eq_iff [simp]: "of_nat m = of_nat n \<longleftrightarrow> m = n"
  by (auto intro: inj_of_nat injD)

text{*Special cases where either operand is zero*}

lemma of_nat_0_eq_iff [simp, no_atp]: "0 = of_nat n \<longleftrightarrow> 0 = n"
  by (fact of_nat_eq_iff [of 0 n, unfolded of_nat_0])

lemma of_nat_eq_0_iff [simp, no_atp]: "of_nat m = 0 \<longleftrightarrow> m = 0"
  by (fact of_nat_eq_iff [of m 0, unfolded of_nat_0])

end

context linordered_semidom
begin

lemma of_nat_0_le_iff [simp]: "0 \<le> of_nat n"
  by (induct n) simp_all

lemma of_nat_less_0_iff [simp]: "\<not> of_nat m < 0"
  by (simp add: not_less)

lemma of_nat_less_iff [simp]: "of_nat m < of_nat n \<longleftrightarrow> m < n"
  by (induct m n rule: diff_induct, simp_all add: add_pos_nonneg)

lemma of_nat_le_iff [simp]: "of_nat m \<le> of_nat n \<longleftrightarrow> m \<le> n"
  by (simp add: not_less [symmetric] linorder_not_less [symmetric])

lemma less_imp_of_nat_less: "m < n \<Longrightarrow> of_nat m < of_nat n"
  by simp

lemma of_nat_less_imp_less: "of_nat m < of_nat n \<Longrightarrow> m < n"
  by simp

text{*Every @{text linordered_semidom} has characteristic zero.*}

subclass semiring_char_0 proof
qed (auto intro!: injI simp add: eq_iff)

text{*Special cases where either operand is zero*}

lemma of_nat_le_0_iff [simp, no_atp]: "of_nat m \<le> 0 \<longleftrightarrow> m = 0"
  by (rule of_nat_le_iff [of _ 0, simplified])

lemma of_nat_0_less_iff [simp]: "0 < of_nat n \<longleftrightarrow> 0 < n"
  by (rule of_nat_less_iff [of 0, simplified])

end

context ring_1
begin

lemma of_nat_diff: "n \<le> m \<Longrightarrow> of_nat (m - n) = of_nat m - of_nat n"
by (simp add: algebra_simps of_nat_add [symmetric])

end

context linordered_idom
begin

lemma abs_of_nat [simp]: "\<bar>of_nat n\<bar> = of_nat n"
  unfolding abs_if by auto

end

lemma of_nat_id [simp]: "of_nat n = n"
  by (induct n) simp_all

lemma of_nat_eq_id [simp]: "of_nat = id"
  by (auto simp add: fun_eq_iff)


subsection {* The Set of Natural Numbers *}

context semiring_1
begin

definition Nats  :: "'a set" where
  "Nats = range of_nat"

notation (xsymbols)
  Nats  ("\<nat>")

lemma of_nat_in_Nats [simp]: "of_nat n \<in> \<nat>"
  by (simp add: Nats_def)

lemma Nats_0 [simp]: "0 \<in> \<nat>"
apply (simp add: Nats_def)
apply (rule range_eqI)
apply (rule of_nat_0 [symmetric])
done

lemma Nats_1 [simp]: "1 \<in> \<nat>"
apply (simp add: Nats_def)
apply (rule range_eqI)
apply (rule of_nat_1 [symmetric])
done

lemma Nats_add [simp]: "a \<in> \<nat> \<Longrightarrow> b \<in> \<nat> \<Longrightarrow> a + b \<in> \<nat>"
apply (auto simp add: Nats_def)
apply (rule range_eqI)
apply (rule of_nat_add [symmetric])
done

lemma Nats_mult [simp]: "a \<in> \<nat> \<Longrightarrow> b \<in> \<nat> \<Longrightarrow> a * b \<in> \<nat>"
apply (auto simp add: Nats_def)
apply (rule range_eqI)
apply (rule of_nat_mult [symmetric])
done

lemma Nats_cases [cases set: Nats]:
  assumes "x \<in> \<nat>"
  obtains (of_nat) n where "x = of_nat n"
  unfolding Nats_def
proof -
  from `x \<in> \<nat>` have "x \<in> range of_nat" unfolding Nats_def .
  then obtain n where "x = of_nat n" ..
  then show thesis ..
qed

lemma Nats_induct [case_names of_nat, induct set: Nats]:
  "x \<in> \<nat> \<Longrightarrow> (\<And>n. P (of_nat n)) \<Longrightarrow> P x"
  by (rule Nats_cases) auto

end


subsection {* Further Arithmetic Facts Concerning the Natural Numbers *}

lemma subst_equals:
  assumes 1: "t = s" and 2: "u = t"
  shows "u = s"
  using 2 1 by (rule trans)

setup Arith_Data.setup

ML_file "Tools/nat_arith.ML"

simproc_setup nateq_cancel_sums
  ("(l::nat) + m = n" | "(l::nat) = m + n" | "Suc m = n" | "m = Suc n") =
  {* fn phi => fn ss => try Nat_Arith.cancel_eq_conv *}

simproc_setup natless_cancel_sums
  ("(l::nat) + m < n" | "(l::nat) < m + n" | "Suc m < n" | "m < Suc n") =
  {* fn phi => fn ss => try Nat_Arith.cancel_less_conv *}

simproc_setup natle_cancel_sums
  ("(l::nat) + m \<le> n" | "(l::nat) \<le> m + n" | "Suc m \<le> n" | "m \<le> Suc n") =
  {* fn phi => fn ss => try Nat_Arith.cancel_le_conv *}

simproc_setup natdiff_cancel_sums
  ("(l::nat) + m - n" | "(l::nat) - (m + n)" | "Suc m - n" | "m - Suc n") =
  {* fn phi => fn ss => try Nat_Arith.cancel_diff_conv *}

ML_file "Tools/lin_arith.ML"
setup {* Lin_Arith.global_setup *}
declaration {* K Lin_Arith.setup *}

simproc_setup fast_arith_nat ("(m::nat) < n" | "(m::nat) <= n" | "(m::nat) = n") =
  {* fn _ => fn ss => fn ct => Lin_Arith.simproc ss (term_of ct) *}
(* Because of this simproc, the arithmetic solver is really only
useful to detect inconsistencies among the premises for subgoals which are
*not* themselves (in)equalities, because the latter activate
fast_nat_arith_simproc anyway. However, it seems cheaper to activate the
solver all the time rather than add the additional check. *)


lemmas [arith_split] = nat_diff_split split_min split_max

context order
begin

lemma lift_Suc_mono_le:
  assumes mono: "!!n. f n \<le> f(Suc n)" and "n\<le>n'"
  shows "f n \<le> f n'"
proof (cases "n < n'")
  case True
  thus ?thesis
    by (induct n n' rule: less_Suc_induct[consumes 1]) (auto intro: mono)
qed (insert `n \<le> n'`, auto) -- {*trivial for @{prop "n = n'"} *}

lemma lift_Suc_mono_less:
  assumes mono: "!!n. f n < f(Suc n)" and "n < n'"
  shows "f n < f n'"
using `n < n'`
by (induct n n' rule: less_Suc_induct[consumes 1]) (auto intro: mono)

lemma lift_Suc_mono_less_iff:
  "(!!n. f n < f(Suc n)) \<Longrightarrow> f(n) < f(m) \<longleftrightarrow> n<m"
by(blast intro: less_asym' lift_Suc_mono_less[of f]
         dest: linorder_not_less[THEN iffD1] le_eq_less_or_eq[THEN iffD1])

end

lemma mono_iff_le_Suc: "mono f = (\<forall>n. f n \<le> f (Suc n))"
  unfolding mono_def by (auto intro: lift_Suc_mono_le [of f])

lemma mono_nat_linear_lb:
  "(!!m n::nat. m<n \<Longrightarrow> f m < f n) \<Longrightarrow> f(m)+k \<le> f(m+k)"
apply(induct_tac k)
 apply simp
apply(erule_tac x="m+n" in meta_allE)
apply(erule_tac x="Suc(m+n)" in meta_allE)
apply simp
done


text{*Subtraction laws, mostly by Clemens Ballarin*}

lemma diff_less_mono: "[| a < (b::nat); c \<le> a |] ==> a-c < b-c"
by arith

lemma less_diff_conv: "(i < j-k) = (i+k < (j::nat))"
by arith

lemma le_diff_conv: "(j-k \<le> (i::nat)) = (j \<le> i+k)"
by arith

lemma le_diff_conv2: "k \<le> j ==> (i \<le> j-k) = (i+k \<le> (j::nat))"
by arith

lemma diff_diff_cancel [simp]: "i \<le> (n::nat) ==> n - (n - i) = i"
by arith

lemma le_add_diff: "k \<le> (n::nat) ==> m \<le> n + m - k"
by arith

(*Replaces the previous diff_less and le_diff_less, which had the stronger
  second premise n\<le>m*)
lemma diff_less[simp]: "!!m::nat. [| 0<n; 0<m |] ==> m - n < m"
by arith

text {* Simplification of relational expressions involving subtraction *}

lemma diff_diff_eq: "[| k \<le> m;  k \<le> (n::nat) |] ==> ((m-k) - (n-k)) = (m-n)"
by (simp split add: nat_diff_split)

hide_fact (open) diff_diff_eq

lemma eq_diff_iff: "[| k \<le> m;  k \<le> (n::nat) |] ==> (m-k = n-k) = (m=n)"
by (auto split add: nat_diff_split)

lemma less_diff_iff: "[| k \<le> m;  k \<le> (n::nat) |] ==> (m-k < n-k) = (m<n)"
by (auto split add: nat_diff_split)

lemma le_diff_iff: "[| k \<le> m;  k \<le> (n::nat) |] ==> (m-k \<le> n-k) = (m\<le>n)"
by (auto split add: nat_diff_split)

text{*(Anti)Monotonicity of subtraction -- by Stephan Merz*}

(* Monotonicity of subtraction in first argument *)
lemma diff_le_mono: "m \<le> (n::nat) ==> (m-l) \<le> (n-l)"
by (simp split add: nat_diff_split)

lemma diff_le_mono2: "m \<le> (n::nat) ==> (l-n) \<le> (l-m)"
by (simp split add: nat_diff_split)

lemma diff_less_mono2: "[| m < (n::nat); m<l |] ==> (l-n) < (l-m)"
by (simp split add: nat_diff_split)

lemma diffs0_imp_equal: "!!m::nat. [| m-n = 0; n-m = 0 |] ==>  m=n"
by (simp split add: nat_diff_split)

lemma min_diff: "min (m - (i::nat)) (n - i) = min m n - i"
by auto

lemma inj_on_diff_nat: 
  assumes k_le_n: "\<forall>n \<in> N. k \<le> (n::nat)"
  shows "inj_on (\<lambda>n. n - k) N"
proof (rule inj_onI)
  fix x y
  assume a: "x \<in> N" "y \<in> N" "x - k = y - k"
  with k_le_n have "x - k + k = y - k + k" by auto
  with a k_le_n show "x = y" by auto
qed

text{*Rewriting to pull differences out*}

lemma diff_diff_right [simp]: "k\<le>j --> i - (j - k) = i + (k::nat) - j"
by arith

lemma diff_Suc_diff_eq1 [simp]: "k \<le> j ==> m - Suc (j - k) = m + k - Suc j"
by arith

lemma diff_Suc_diff_eq2 [simp]: "k \<le> j ==> Suc (j - k) - m = Suc j - (k + m)"
by arith

lemma Suc_diff_Suc: "n < m \<Longrightarrow> Suc (m - Suc n) = m - n"
by simp

(*The others are
      i - j - k = i - (j + k),
      k \<le> j ==> j - k + i = j + i - k,
      k \<le> j ==> i + (j - k) = i + j - k *)
lemmas add_diff_assoc = diff_add_assoc [symmetric]
lemmas add_diff_assoc2 = diff_add_assoc2[symmetric]
declare diff_diff_left [simp]  add_diff_assoc [simp] add_diff_assoc2[simp]

text{*At present we prove no analogue of @{text not_less_Least} or @{text
Least_Suc}, since there appears to be no need.*}

text{*Lemmas for ex/Factorization*}

lemma one_less_mult: "[| Suc 0 < n; Suc 0 < m |] ==> Suc 0 < m*n"
by (cases m) auto

lemma n_less_m_mult_n: "[| Suc 0 < n; Suc 0 < m |] ==> n<m*n"
by (cases m) auto

lemma n_less_n_mult_m: "[| Suc 0 < n; Suc 0 < m |] ==> n<n*m"
by (cases m) auto

text {* Specialized induction principles that work "backwards": *}

lemma inc_induct[consumes 1, case_names base step]:
  assumes less: "i <= j"
  assumes base: "P j"
  assumes step: "!!i. [| i < j; P (Suc i) |] ==> P i"
  shows "P i"
  using less
proof (induct d=="j - i" arbitrary: i)
  case (0 i)
  hence "i = j" by simp
  with base show ?case by simp
next
  case (Suc d i)
  hence "i < j" "P (Suc i)"
    by simp_all
  thus "P i" by (rule step)
qed

lemma strict_inc_induct[consumes 1, case_names base step]:
  assumes less: "i < j"
  assumes base: "!!i. j = Suc i ==> P i"
  assumes step: "!!i. [| i < j; P (Suc i) |] ==> P i"
  shows "P i"
  using less
proof (induct d=="j - i - 1" arbitrary: i)
  case (0 i)
  with `i < j` have "j = Suc i" by simp
  with base show ?case by simp
next
  case (Suc d i)
  hence "i < j" "P (Suc i)"
    by simp_all
  thus "P i" by (rule step)
qed

lemma zero_induct_lemma: "P k ==> (!!n. P (Suc n) ==> P n) ==> P (k - i)"
  using inc_induct[of "k - i" k P, simplified] by blast

lemma zero_induct: "P k ==> (!!n. P (Suc n) ==> P n) ==> P 0"
  using inc_induct[of 0 k P] by blast

text {* Further induction rule similar to @{thm inc_induct} *}

lemma dec_induct[consumes 1, case_names base step]:
  "i \<le> j \<Longrightarrow> P i \<Longrightarrow> (\<And>n. i \<le> n \<Longrightarrow> P n \<Longrightarrow> P (Suc n)) \<Longrightarrow> P j"
  by (induct j arbitrary: i) (auto simp: le_Suc_eq)

 
subsection {* The divides relation on @{typ nat} *}

lemma dvd_1_left [iff]: "Suc 0 dvd k"
unfolding dvd_def by simp

lemma dvd_1_iff_1 [simp]: "(m dvd Suc 0) = (m = Suc 0)"
by (simp add: dvd_def)

lemma nat_dvd_1_iff_1 [simp]: "m dvd (1::nat) \<longleftrightarrow> m = 1"
by (simp add: dvd_def)

lemma dvd_antisym: "[| m dvd n; n dvd m |] ==> m = (n::nat)"
  unfolding dvd_def
  by (force dest: mult_eq_self_implies_10 simp add: mult_assoc)

text {* @{term "op dvd"} is a partial order *}

interpretation dvd: order "op dvd" "\<lambda>n m \<Colon> nat. n dvd m \<and> \<not> m dvd n"
  proof qed (auto intro: dvd_refl dvd_trans dvd_antisym)

lemma dvd_diff_nat[simp]: "[| k dvd m; k dvd n |] ==> k dvd (m-n :: nat)"
unfolding dvd_def
by (blast intro: diff_mult_distrib2 [symmetric])

lemma dvd_diffD: "[| k dvd m-n; k dvd n; n\<le>m |] ==> k dvd (m::nat)"
  apply (erule linorder_not_less [THEN iffD2, THEN add_diff_inverse, THEN subst])
  apply (blast intro: dvd_add)
  done

lemma dvd_diffD1: "[| k dvd m-n; k dvd m; n\<le>m |] ==> k dvd (n::nat)"
by (drule_tac m = m in dvd_diff_nat, auto)

lemma dvd_reduce: "(k dvd n + k) = (k dvd (n::nat))"
  apply (rule iffI)
   apply (erule_tac [2] dvd_add)
   apply (rule_tac [2] dvd_refl)
  apply (subgoal_tac "n = (n+k) -k")
   prefer 2 apply simp
  apply (erule ssubst)
  apply (erule dvd_diff_nat)
  apply (rule dvd_refl)
  done

lemma dvd_mult_cancel: "!!k::nat. [| k*m dvd k*n; 0<k |] ==> m dvd n"
  unfolding dvd_def
  apply (erule exE)
  apply (simp add: mult_ac)
  done

lemma dvd_mult_cancel1: "0<m ==> (m*n dvd m) = (n = (1::nat))"
  apply auto
   apply (subgoal_tac "m*n dvd m*1")
   apply (drule dvd_mult_cancel, auto)
  done

lemma dvd_mult_cancel2: "0<m ==> (n*m dvd m) = (n = (1::nat))"
  apply (subst mult_commute)
  apply (erule dvd_mult_cancel1)
  done

lemma dvd_imp_le: "[| k dvd n; 0 < n |] ==> k \<le> (n::nat)"
by (auto elim!: dvdE) (auto simp add: gr0_conv_Suc)

lemma nat_dvd_not_less:
  fixes m n :: nat
  shows "0 < m \<Longrightarrow> m < n \<Longrightarrow> \<not> n dvd m"
by (auto elim!: dvdE) (auto simp add: gr0_conv_Suc)


subsection {* aliasses *}

lemma nat_mult_1: "(1::nat) * n = n"
  by simp
 
lemma nat_mult_1_right: "n * (1::nat) = n"
  by simp


subsection {* size of a datatype value *}

class size =
  fixes size :: "'a \<Rightarrow> nat" -- {* see further theory @{text Wellfounded} *}


subsection {* code module namespace *}

code_modulename SML
  Nat Arith

code_modulename OCaml
  Nat Arith

code_modulename Haskell
  Nat Arith

hide_const (open) of_nat_aux

end

