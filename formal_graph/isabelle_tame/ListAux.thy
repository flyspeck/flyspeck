(*  Author:     Gertrud Bauer, Tobias Nipkow
*)

header {* Basic Functions Old and New *}

theory ListAux
imports Main
begin

declare Let_def[simp]

subsection {* HOL *}

lemma pairD:  "(a,b) = p \<Longrightarrow> a = fst p \<and> b = snd p"
by auto


lemmas conj_aci = conj_comms conj_assoc conj_absorb conj_left_absorb

definition enum :: "nat \<Rightarrow> nat set" where
  [code del]: "enum n = {..<n}"

declare enum_def [symmetric, code_unfold]

lemma [code]:
  "enum 0 = {}"
  "enum (Suc n) = insert n (enum n)"
  unfolding enum_def lessThan_0 lessThan_Suc by rule+


subsection {* Lists *}

declare List.member_def[simp] list_all_iff[simp] list_ex_iff[simp]


subsubsection{* @{text length} *}

notation length  ("|_|")

lemma length3D: "|xs| = 3 \<Longrightarrow> \<exists>x y z. xs = [x, y, z]"
apply (cases xs) apply simp
apply (case_tac list) apply simp
apply (case_tac lista) by simp_all

lemma length4D: "|xs| = 4 \<Longrightarrow> \<exists> a b c d. xs = [a, b, c, d]"
 apply (case_tac xs) apply simp
 apply (case_tac list) apply simp
 apply (case_tac lista) apply simp
 apply (case_tac listb) by simp_all


subsubsection {* @{const filter} *}

lemma filter_emptyE[dest]: "(filter P xs = []) \<Longrightarrow>  x \<in> set xs \<Longrightarrow>  \<not> P x" 
  by (simp add: filter_empty_conv)

lemma filter_comm: "[x \<leftarrow> xs. P x \<and> Q x] = [x \<leftarrow> xs. Q x \<and> P x]"
  by (simp add: conj_aci)

lemma filter_prop: "x \<in> set [u\<leftarrow>ys . P u] \<Longrightarrow> P x"
proof (induct ys arbitrary: x)
  case Nil then show ?case by simp 
next 
  case Cons then show ?case by (auto split: split_if_asm)
qed
   
lemma filter_compl1: 
 "([x\<leftarrow>xs. P x] = []) = ([x\<leftarrow>xs. \<not> P x] = xs)" (is "?lhs = ?rhs")
proof
  show "?rhs \<Longrightarrow> ?lhs" 
  proof (induct xs) 
    case Nil then show ?case by simp
  next
    case (Cons x xs) 
    have "[u\<leftarrow>xs . \<not> P u] \<noteq> x # xs"
    proof 
      assume "[u\<leftarrow>xs . \<not> P u] = x # xs" 
      then have "|x # xs| = |[u\<leftarrow>xs . \<not> P u]|" by simp
      also have "... \<le> |xs|" by simp 
      finally show False by simp 
    qed
    with Cons show ?case by auto  
  qed
next
  show "?lhs \<Longrightarrow> ?rhs" 
    by (induct xs) (simp_all split: split_if_asm)
qed
lemma [simp]: "Not \<circ> (Not \<circ> P) = P"
  by (rule ext) simp

lemma filter_eqI: 
  "(\<And>v. v \<in> set vs \<Longrightarrow> P v = Q v) \<Longrightarrow> [v\<leftarrow>vs . P v] = [v\<leftarrow>vs . Q v]"
  by (induct vs) simp_all

lemma filter_simp: "(\<And>x. x \<in> set xs \<Longrightarrow> P x) \<Longrightarrow> [x\<leftarrow>xs. P x \<and> Q x] = [x\<leftarrow>xs. Q x]"
 by (induct xs) auto

lemma filter_True_eq1: 
  "(length [y\<leftarrow>xs. P y] = length xs) \<Longrightarrow> (\<And>y. y \<in> set xs \<Longrightarrow> P y)"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  have l: "length (filter P xs) \<le> length xs"
    by (simp add: length_filter_le)
  have hyp: "length (filter P (x # xs)) = length (x # xs)" by fact
  then have "P x"  by (simp split: split_if_asm) (insert l, arith)
  moreover with hyp have "length (filter P xs) = length xs" 
    by (simp split: split_if_asm)
  moreover have "y \<in> set (x#xs)" by fact
  ultimately show ?case by (auto dest: Cons(1))
qed

lemma [simp]: "[f x. x <- xs, P x] = [f x. x <- [x \<leftarrow> xs. P x]]"
  by (induct xs) auto


subsubsection {* @{const concat} *}

syntax (xsymbols)
  "_concat" :: "idt => 'a list => 'a list \<Rightarrow> 'a list"  ("\<Squnion>\<^bsub>_\<in> _\<^esub> _" 10)
translations "\<Squnion>\<^bsub>x\<in>xs\<^esub> f" == "CONST concat [f. x <- xs]" 


subsubsection {* List product *}

definition listProd1 :: "'a \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
 "listProd1 a bs \<equiv> [(a,b). b <- bs]"

definition listProd :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" (infix "\<times>" 50) where
 "as \<times> bs \<equiv> \<Squnion>\<^bsub>a \<in> as\<^esub> listProd1 a bs"

lemma(*<*)[simp]: (*>*) "set (xs \<times> ys) = (set xs) \<times> (set ys)" 
  by (auto simp: listProd_def listProd1_def)


subsubsection {*  Minimum and maximum *}

primrec minimal:: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> 'a" where
 "minimal m (x#xs) =
  (if xs=[] then x else
   let mxs = minimal m xs in
   if m x \<le> m mxs then x else mxs)"


lemma minimal_in_set[simp]: "xs \<noteq> [] \<Longrightarrow> minimal f xs : set xs"
by(induct xs) auto

primrec min_list :: "nat list \<Rightarrow> nat" where
  "min_list (x#xs) = (if xs=[] then x else min x (min_list xs))"

primrec max_list :: "nat list \<Rightarrow> nat" where
  "max_list (x#xs) = (if xs=[] then x else max x (max_list xs))"


lemma min_list_conv_Min[simp]:
 "xs \<noteq> [] \<Longrightarrow> min_list xs = Min (set xs)"
by (induct xs) auto

lemma max_list_conv_Max[simp]:
 "xs \<noteq> [] \<Longrightarrow> max_list xs = Max (set xs)"
by (induct xs) auto


subsubsection {* replace *}

primrec replace :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow>  'a list" where
  "replace x ys [] = []"
| "replace x ys (z#zs) = 
     (if z = x then ys @ zs else z # (replace x ys zs))"

primrec mapAt :: "nat list \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a list \<Rightarrow> 'a list)" where
  "mapAt [] f as = as"
| "mapAt (n#ns) f as = 
     (if n < |as| then mapAt ns f (as[n:= f (as!n)])
     else mapAt ns f as)"


lemma length_mapAt[simp]: "!!xs. length(mapAt vs f xs) = length xs"
by(induct vs) auto

lemma length_replace1[simp]: "length(replace x [y] xs) = length xs"
by(induct xs) simp_all

lemma replace_id[simp]: "replace x [x] xs = xs"
by(induct xs) simp_all

lemma len_replace_ge_same:
"length ys \<ge> 1 \<Longrightarrow> length(replace x ys xs) \<ge> length xs"
by (induct xs) auto

lemma len_replace_ge[simp]:
"\<lbrakk> length ys \<ge> 1; length xs \<ge> length zs \<rbrakk> \<Longrightarrow>
 length(replace x ys xs) \<ge> length zs"
apply(drule len_replace_ge_same[where x = x and xs = xs])
apply arith
done


lemma replace_append[simp]:
  "replace x ys (as @ bs) =
   (if x \<in> set as then replace x ys as @ bs else as @ replace x ys bs)"
by(induct as) auto

lemma distinct_set_replace: "distinct xs \<Longrightarrow>
 set (replace x ys xs) =
 (if x \<in> set xs then (set xs - {x}) \<union> set ys else set xs)"
apply(induct xs)
 apply(simp)
apply simp
apply blast
done

lemma replace1:
 "f \<in> set (replace f' fs ls ) \<Longrightarrow> f \<notin> set ls \<Longrightarrow> f \<in> set fs" 
proof (induct ls)
  case Nil then show ?case by simp
next
  case (Cons l ls) then show ?case by (simp split: split_if_asm)
qed

lemma replace2:
 "f' \<notin> set ls \<Longrightarrow> replace f' fs ls  = ls" 
proof (induct ls)
  case Nil then show ?case by simp
next
  case (Cons l ls) then show ?case by (auto split: split_if_asm)
qed

lemma replace3[intro]:
  "f' \<in> set ls \<Longrightarrow> f \<in> set fs \<Longrightarrow> f \<in> set (replace f' fs ls)"
by (induct ls) auto

lemma replace4:
  "f \<in> set ls \<Longrightarrow> oldF \<noteq> f \<Longrightarrow> f \<in> set (replace oldF fs ls)" 
by (induct ls) auto

lemma replace5: "f \<in> set (replace oldF newfs fs) \<Longrightarrow> f \<in> set fs \<or> f \<in> set newfs"
by (induct fs) (auto split: split_if_asm) 

lemma replace6: "distinct oldfs \<Longrightarrow> x \<in> set (replace oldF newfs oldfs) = 
  ((x \<noteq> oldF \<or> oldF \<in> set newfs) \<and> ((oldF \<in> set oldfs \<and> x \<in> set newfs) \<or> x \<in> set oldfs))"
by (induct oldfs) auto


lemma distinct_replace: 
"distinct fs \<Longrightarrow> distinct newFs \<Longrightarrow> set fs \<inter> set newFs \<subseteq> {oldF} \<Longrightarrow>
 distinct (replace oldF newFs fs)"
proof (induct fs)
  case Nil then show ?case by simp
next
  case (Cons f fs)
  then show ?case
  proof (cases "f = oldF") 
    case True with Cons show ?thesis by simp blast
  next
    case False 
    moreover with Cons have "f \<notin> set newFs" by simp blast
    with Cons have "f \<notin> set (replace oldF newFs fs)" 
     by simp (blast dest: replace1) 
    moreover from Cons have "distinct (replace oldF newFs fs)"
      by (rule_tac Cons) auto  
    ultimately show ?thesis by simp 
  qed
qed

lemma replace_replace[simp]: "oldf \<notin> set newfs \<Longrightarrow> distinct xs \<Longrightarrow> 
  replace oldf newfs (replace oldf newfs xs) = replace oldf newfs xs"
apply (induct xs) apply auto apply (rule replace2) by simp 

lemma replace_distinct: "distinct fs \<Longrightarrow> distinct newfs \<Longrightarrow> oldf \<in> set fs \<longrightarrow> set newfs \<inter> set fs \<subseteq> {oldf} \<Longrightarrow> 
  distinct (replace oldf newfs fs)"
apply (case_tac "oldf \<in> set fs") apply simp
apply (induct fs) apply simp
apply (auto simp: replace2) apply (drule replace1)
by auto


lemma filter_replace2:
 "\<lbrakk> \<not> P x; \<forall>y\<in> set ys. \<not> P y \<rbrakk> \<Longrightarrow>
  filter P (replace x ys xs) = filter P xs"
apply(cases "x \<in> set xs")
 prefer 2 apply(simp add:replace2)
apply(induct xs)
 apply simp
apply clarsimp
done

lemma length_filter_replace1:
 "\<lbrakk> x \<in> set xs; \<not> P x \<rbrakk> \<Longrightarrow>
  length(filter P (replace x ys xs)) =
  length(filter P xs) + length(filter P ys)"
apply(induct xs)
 apply simp
apply fastforce
done

lemma length_filter_replace2:
 "\<lbrakk> x \<in> set xs; P x \<rbrakk> \<Longrightarrow>
  length(filter P (replace x ys xs)) =
  length(filter P xs) + length(filter P ys) - 1"
apply(induct xs)
 apply simp
apply auto
apply(drule split_list)
apply clarsimp
done


subsubsection {* @{const"distinct"} *}

lemma dist_at1: "\<And> c vs. distinct vs \<Longrightarrow> vs = a @ r # b \<Longrightarrow> vs = c @ r # d \<Longrightarrow> a = c"
proof (induct a)
  case Nil
  assume dist: "distinct vs" and vs1: "vs = [] @ r # b" and vs2: "vs = c @ r # d"
  from dist vs2 have rc: "r \<notin> set c" by auto
  from vs1 vs2 have "c @ r # d = r # b" by auto
  then have "hd (c @ r # d) = r" by auto
  then have "c \<noteq> [] \<Longrightarrow> hd c = r" by auto
  then have "c \<noteq> [] \<Longrightarrow> r \<in> set c" by (induct c) auto
  with rc have c: "c = []" by auto
  then show ?case by auto
next
  case (Cons x xs) then show ?case by (induct c)  auto
qed

lemma dist_at: "distinct vs \<Longrightarrow> vs = a @ r # b \<Longrightarrow> vs = c @ r # d \<Longrightarrow> a = c \<and> b = d"
proof -
  assume dist: "distinct vs" and vs1: "vs = a @ r # b" and vs2: "vs = c @ r # d"
  then have "a = c" by (rule_tac dist_at1) auto
  with dist vs1 vs2 show ?thesis by simp
qed

lemma dist_at2: "distinct vs \<Longrightarrow> vs = a @ r # b \<Longrightarrow> vs = c @ r # d \<Longrightarrow> b = d"
proof -
  assume dist: "distinct vs" and vs1: "vs = a @ r # b" and vs2: "vs = c @ r # d"
  then have "a = c \<and> b = d" by (rule_tac dist_at) auto
  then show ?thesis by auto
qed

lemma distinct_split1: "distinct xs \<Longrightarrow> xs = y @ [r] @ z  \<Longrightarrow> r \<notin> set y"
  apply auto done

lemma distinct_split2: "distinct xs \<Longrightarrow> xs = y @ [r] @ z  \<Longrightarrow> r \<notin> set z" apply auto done

lemma distinct_hd_not_cons: "distinct vs \<Longrightarrow> \<exists> as bs. vs = as @ x # hd vs # bs \<Longrightarrow> False"
proof -
  assume d: "distinct vs" and ex: "\<exists> as bs. vs = as @ x # hd vs # bs"
  from ex have vsne: "vs \<noteq> []" by auto
  with d ex show ?thesis apply (elim exE) apply (case_tac "as")
    apply (subgoal_tac "hd vs = x") apply simp apply (rule sym)  apply simp
    apply (subgoal_tac "x = hd (x # (hd vs # bs))") apply simp apply (thin_tac "vs = x # hd vs # bs")
    apply auto
    apply (subgoal_tac "hd vs = a") apply simp
    apply (subgoal_tac "a = hd (a # list @ x # hd vs # bs)") apply simp
    apply (thin_tac "vs = a # list @ x # hd vs # bs") by auto
qed

subsubsection {* Misc *}

(* FIXME move to List *)
lemma drop_last_in: "!!n. n < length ls \<Longrightarrow> last ls \<in> set (drop n ls)"
apply (frule_tac last_drop) apply(erule subst)
apply (case_tac "drop n ls" rule: rev_exhaust) by simp_all

lemma nth_last_Suc_n: "distinct ls \<Longrightarrow> n < length ls \<Longrightarrow> last ls = ls ! n \<Longrightarrow> Suc n = length ls"
proof (rule ccontr)
  assume d: "distinct ls" and n: "n < length ls" and l: "last ls = ls ! n" and not: "Suc n \<noteq> length ls"
  then have s: "Suc n < length ls" by auto
  def lls \<equiv>  "ls!n"
  with n have "take (Suc n) ls = take n ls @ [lls]" apply simp by (rule take_Suc_conv_app_nth)
  then have "take (Suc n) ls @ drop (Suc n) ls = take n ls @ [lls] @ drop (Suc n) ls" by auto
  then have ls: "ls = take n ls @ [lls] @ drop (Suc n) ls" by auto
  with d have dls: "distinct (take n ls @ [lls] @ drop (Suc n) ls)" by auto
  from lls_def l have "lls = (last ls)" by auto
  with s have "lls \<in> set (drop (Suc n) ls)" apply simp by (rule_tac drop_last_in)
  with dls show False by auto
qed


(****************************** rotate *************************)

subsubsection {* @{const rotate} *}

lemma  plus_length1[simp]: "rotate (k+(length ls)) ls = rotate k ls "
proof -
  have "\<And> k ls. rotate k (rotate (length ls) ls) = rotate (k+(length ls)) ls"
    by (rule rotate_rotate)
  then have "\<And> k ls. rotate k ls =  rotate (k+(length ls)) ls" by auto
  then show ?thesis by (rule sym)
qed

lemma  plus_length2[simp]: "rotate ((length ls)+k) ls = rotate k ls "
proof -
  def x \<equiv> "(length ls)+k"
  then have "x = k+(length ls)" by auto
  with x_def have "rotate x ls = rotate (k+(length ls)) ls" by simp
  then have "rotate x ls = rotate k ls" by simp
  with x_def show ?thesis by simp
qed

lemma rotate_minus1: "n > 0 \<Longrightarrow> m > 0 \<Longrightarrow>
 rotate n ls = rotate m ms \<Longrightarrow> rotate (n - 1) ls = rotate (m - 1) ms"
proof (cases "ls = []")
  assume r: "rotate n ls = rotate m ms"
  case True with r
  have "rotate m ms = []" by auto
  then have "ms = []" by auto
  with True show ?thesis by auto
next
  assume n: "n > 0" and m: "m > 0" and r: "rotate n ls = rotate m ms"
  case False
  then have lls: "length ls > 0" by auto
  with r have lms: "length ms > 0" by auto
  have mem1: "rotate (n - 1) ls = rotate ((n - 1) + length ls) ls" by auto
  from n lls have "(n - 1) + length ls = (length ls - 1) + n" by arith
  then have "rotate ((n - 1) + length ls) ls = rotate ((length ls - 1) + n) ls" by auto
  with mem1 have mem2: "rotate (n - 1) ls = rotate ((length ls - 1) + n) ls" by auto
  have "rotate ((length ls - 1) + n) ls = rotate (length ls - 1) (rotate n ls)" apply (rule sym)
    by (rule rotate_rotate)
  with mem2 have mem3: "rotate (n - 1) ls = rotate (length ls - 1) (rotate n ls)" by auto
  from r have "rotate (length ls - 1) (rotate n ls) = rotate (length ls - 1) (rotate m ms)" by auto
  with mem3 have mem4: "rotate (n - 1) ls = rotate (length ls - 1) (rotate m ms)" by auto
  have "rotate (length ls - 1) (rotate m ms) = rotate (length ls - 1 + m) ms"  by (rule rotate_rotate)
  with mem4 have mem5: "rotate (n - 1) ls = rotate (length ls - 1 + m) ms" by auto
  from r have "length (rotate n ls) = length (rotate m ms)" by simp
  then have "length ls = length ms" by auto
  with m lms have "length ls - 1 + m = (m - 1) + length ms" by arith
  with mem5 have mem6: "rotate (n - 1) ls = rotate ((m - 1) + length ms) ms" by auto
  have "rotate ((m - 1) + length ms) ms = rotate (m - 1) (rotate (length ms) ms)" by auto
  then have "rotate ((m - 1) + length ms) ms = rotate (m - 1) ms" by auto
  with mem6 show ?thesis by auto
qed

lemma rotate_minus1': "n > 0 \<Longrightarrow> rotate n ls = ms \<Longrightarrow>
  rotate (n - 1) ls = rotate (length ms - 1) ms"
proof (cases "ls = []")
  assume r: "rotate n ls = ms"
  case True with r show ?thesis by auto
next
  assume n: "n > 0" and r:"rotate n ls = ms"
  then have r': "rotate n ls = rotate (length ms) ms" by auto
  case False
  with n r' show ?thesis apply (rule_tac rotate_minus1) by auto
qed

lemma rotate_inv1: "\<And> ms. n < length ls \<Longrightarrow> rotate n ls = ms \<Longrightarrow>
  ls = rotate ((length ls) - n) ms"
proof (induct n)
  case 0 then show ?case by auto
next
  case (Suc n) then show ?case
  proof (cases "ls = []")
    case True with Suc
    show ?thesis by auto
  next
    case False
    then have ll: "length ls > 0" by auto
    from Suc have nl: "n < length ls" by auto
    from Suc have r: "rotate (Suc n) ls = ms" by auto
    then have "rotate (Suc n - 1) ls = rotate (length ms - 1) ms" apply (rule_tac rotate_minus1') by auto
    then have "rotate n ls = rotate (length ms - 1) ms" by auto
    then have mem: "ls = rotate (length ls - n) (rotate (length ms - 1) ms)"
      apply (rule_tac Suc) by (auto simp: nl)
    have " rotate (length ls - n) (rotate (length ms - 1) ms) = rotate (length ls - n + (length ms - 1)) ms"
      by (rule rotate_rotate)
    with mem have mem2: "ls =  rotate (length ls - n + (length ms - 1)) ms" by auto
    from r have leq: "length ms = length ls" by auto
    with False nl have "length ls - n + (length ms - 1) = length ms + (length ms - (Suc n))"
      by arith
    then have "rotate (length ls - n + (length ms - 1)) ms = rotate (length ms + (length ms - (Suc n))) ms"
      by auto
    with mem2 have mem3: "ls = rotate (length ms + (length ms - (Suc n))) ms" by auto
    have "rotate (length ms + (length ms - (Suc n))) ms = rotate (length ms - (Suc n)) ms" by simp
    with mem3 leq show ?thesis by auto
  qed
qed

lemma rotate_conv_mod'[simp]: "rotate (n mod length ls) ls = rotate n ls"
by(simp add:rotate_drop_take)

lemma rotate_inv2: "rotate n ls = ms \<Longrightarrow>
 ls = rotate ((length ls) - (n mod length ls)) ms"
proof (cases "ls  = []")
  assume r: "rotate n ls = ms"
  case True with r show ?thesis by auto
next
  assume r: "rotate n ls = ms"
  then have r': "rotate (n mod length ls) ls = ms" by auto
  case False
  then have "length ls > 0" by auto
  with r' show ?thesis apply (rule_tac rotate_inv1) by auto
qed

lemma rotate_id[simp]: "rotate ((length ls) - (n mod length ls)) (rotate n ls) = ls"
apply (rule sym) apply (rule rotate_inv2) by simp

lemma nth_rotate1_Suc: "Suc n < length ls \<Longrightarrow> ls!(Suc n) = (rotate1 ls)!n"
  apply (cases ls) apply auto
  by (simp add: nth_append)

lemma nth_rotate1_0: "ls!0 = (rotate1 ls)!(length ls - 1)" apply (cases ls)  by auto

lemma nth_rotate1: "0 < length ls \<Longrightarrow> ls!((Suc n) mod (length ls)) = (rotate1 ls)!(n mod (length ls))"
proof (cases "0 < (Suc n) mod (length ls)")
  assume lls: "0 < length ls"
  case True
  def m \<equiv> "(Suc n) mod (length ls) - 1"
  with True have m: "Suc m = (Suc n) mod (length ls)" by auto
  with lls have a: "(Suc m) <   length ls" by auto
  from lls m have "m = n mod (length ls)" by (simp add: mod_Suc split:split_if_asm)
  with a m show ?thesis apply (drule_tac nth_rotate1_Suc) by auto
next
  assume lls: "0 < length ls"
  case False
  then have a: "(Suc n) mod (length ls) = 0" by auto
  with lls have "Suc (n mod (length ls)) = (length ls)" by (auto simp: mod_Suc split: split_if_asm)
  then have "(n mod (length ls)) = (length ls) - 1" by arith
  with a show ?thesis by (auto simp: nth_rotate1_0)
qed

lemma rotate_Suc2[simp]: "rotate n (rotate1 xs) = rotate (Suc n) xs"
apply (simp add:rotate_def) apply (induct n) by auto

lemma nth_rotate: "\<And> ls. 0 < length ls \<Longrightarrow> ls!((n+m) mod (length ls)) = (rotate m ls)!(n mod (length ls))"
proof (induct m)
  case 0 then show ?case by auto
next
  case (Suc m)
  def z \<equiv> "n + m"
  then have "n + Suc m = Suc (z)" by auto
  with Suc have r1: "ls ! ((Suc z) mod length ls) = rotate1 ls ! (z mod length ls)"
    by (rule_tac nth_rotate1)
  from Suc have "0 < length (rotate1 ls)" by auto
  then have "(rotate1 ls) ! ((n + m) mod length (rotate1 ls))
    = rotate m (rotate1 ls) ! (n mod length (rotate1 ls))" by (rule Suc)
  with r1 z_def have "ls ! ((n + Suc m) mod length ls)
    = rotate m (rotate1 ls) ! (n mod length (rotate1 ls))" by auto
  then show ?case by auto
qed


(************************* SplitAt *******************************************)

subsection {* @{text splitAt} *}

primrec splitAtRec :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list" where
  "splitAtRec c bs [] = (bs,[])"
| "splitAtRec c bs (a#as) = (if a = c then (bs, as)
                              else splitAtRec c (bs@[a]) as)"

definition splitAt :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list" where
  "splitAt c as  \<equiv> splitAtRec c [] as"


subsubsection {* @{const splitAtRec} *}

lemma splitAtRec_conv: "!!bs.
 splitAtRec x bs xs =
 (bs @ takeWhile (%y. y\<noteq>x) xs, tl(dropWhile (%y. y\<noteq>x) xs))"
by(induct xs) auto

lemma splitAtRec_distinct_fst: "\<And> s. distinct vs \<Longrightarrow> distinct s \<Longrightarrow> (set s) \<inter>  (set vs) = {} \<Longrightarrow> distinct (fst (splitAtRec ram1 s vs))"
by (induct vs) auto

lemma splitAtRec_distinct_snd: "\<And> s. distinct vs \<Longrightarrow> distinct s \<Longrightarrow> (set s) \<inter>  (set vs) = {} \<Longrightarrow> distinct (snd (splitAtRec ram1 s vs))"
by (induct vs) auto

lemma splitAtRec_ram:
  "\<And> us a b. ram \<in> set vs \<Longrightarrow> (a, b) = splitAtRec ram us vs \<Longrightarrow>
  us @ vs = a @ [ram] @ b"
proof (induct vs)
case  Nil then show ?case by simp
next
case (Cons v vs) then show ?case by (auto dest: Cons(1) split: split_if_asm)
qed

lemma splitAtRec_notRam:
 "\<And> us. ram \<notin>  set vs \<Longrightarrow> splitAtRec ram us vs = (us @ vs, [])"
proof (induct vs)
case  Nil then show ?case by simp
next
case (Cons v vs) then show ?case by auto
qed

lemma splitAtRec_distinct: "\<And> s. distinct vs \<Longrightarrow>
  distinct s \<Longrightarrow> (set s) \<inter> (set vs) = {} \<Longrightarrow>
  set (fst (splitAtRec ram s vs)) \<inter> set (snd (splitAtRec ram s vs)) = {}"
by (induct vs) auto



subsubsection {* @{const splitAt} *}

lemma splitAt_conv:
 "splitAt x xs = (takeWhile (%y. y\<noteq>x) xs, tl(dropWhile (%y. y\<noteq>x) xs))"
by(simp add: splitAt_def splitAtRec_conv)

lemma splitAt_no_ram[simp]:
  "ram \<notin> set vs \<Longrightarrow> splitAt ram vs = (vs, [])"
  by (auto simp: splitAt_def splitAtRec_notRam)

lemma splitAt_split:
  "ram \<in> set vs \<Longrightarrow> (a,b) = splitAt ram vs \<Longrightarrow> vs = a @ ram # b"
  by (auto simp: splitAt_def dest: splitAtRec_ram)

lemma splitAt_ram:
  "ram \<in> set vs \<Longrightarrow> vs = fst (splitAt ram vs) @ ram # snd (splitAt ram vs)"
 by (rule_tac splitAt_split) auto

lemma fst_splitAt_last:
 "\<lbrakk> xs \<noteq> []; distinct xs \<rbrakk> \<Longrightarrow> fst (splitAt (last xs) xs) = butlast xs"
by(simp add:splitAt_conv takeWhile_not_last)


subsubsection {* Sets *}

lemma splitAtRec_union:
"\<And> a b s. (a,b) = splitAtRec ram s vs \<Longrightarrow> (set a \<union> set b) - {ram} = (set vs \<union> set s) - {ram}"
  apply (induct vs) by (auto split: split_if_asm)

lemma splitAt_subset_ab:
  "(a,b) = splitAt ram vs \<Longrightarrow> set a \<subseteq> set vs \<and> set b \<subseteq> set vs"
  apply (cases "ram \<in> set vs")
  by (auto dest: splitAt_split simp: splitAt_no_ram)

lemma splitAt_in_fst[dest]: "v \<in> set (fst (splitAt ram vs)) \<Longrightarrow> v \<in> set vs"
proof (cases "ram \<in> set vs")
  assume v: "v \<in> set (fst (splitAt ram vs))"
  def a \<equiv> "fst (splitAt ram vs)"
  with v have vin: "v \<in> set a" by auto
  def b \<equiv> "snd (splitAt ram vs)"
  case True with a_def b_def  have "vs = a @ ram # b" by (auto dest: splitAt_ram)
  with vin show "v \<in> set vs" by auto
next
  assume v: "v \<in> set (fst (splitAt ram vs))"
  case False with v show ?thesis by (auto dest: splitAt_no_ram del: notI)
qed

lemma splitAt_not1:
"v \<notin> set vs \<Longrightarrow> v \<notin> set (fst (splitAt ram vs))" by (auto dest: splitAt_in_fst)

lemma splitAt_in_snd[dest]: "v \<in> set (snd (splitAt ram vs)) \<Longrightarrow> v \<in> set vs"
proof (cases "ram \<in> set vs")
  assume v: "v \<in> set (snd (splitAt ram vs))"
  def a \<equiv> "fst (splitAt ram vs)"
  def b \<equiv> "snd (splitAt ram vs)"
  with v have vin: "v \<in> set b" by auto
  case True with a_def b_def  have "vs = a @ ram # b" by (auto dest: splitAt_ram)
  with vin show "v \<in> set vs" by auto
next
  assume v: "v \<in> set (snd (splitAt ram vs))"
  case False with v show ?thesis by (auto dest: splitAt_no_ram del: notI)
qed


subsubsection {* Distinctness *}

lemma splitAt_distinct_ab_aux:
 "distinct vs \<Longrightarrow> (a,b) = splitAt ram vs \<Longrightarrow> distinct a \<and> distinct b"
apply (cases "ram \<in> set vs") by (auto dest: splitAt_split simp: splitAt_no_ram)

lemma splitAt_distinct_fst_aux[intro]:
 "distinct vs \<Longrightarrow> distinct (fst (splitAt ram vs))"
proof -
  assume d: "distinct vs"
  def b: b \<equiv> "snd (splitAt ram vs)"
  def a: a \<equiv> "fst (splitAt ram vs)"
  with b have "(a,b) = splitAt ram vs" by auto
  with a d show ?thesis  by (auto dest: splitAt_distinct_ab_aux)
qed

lemma splitAt_distinct_snd_aux[intro]:
 "distinct vs \<Longrightarrow> distinct (snd (splitAt ram vs))"
proof -
  assume d: "distinct vs"
  def b: b \<equiv> "snd (splitAt ram vs)"
  def a: a \<equiv> "fst (splitAt ram vs)"
  with b have "(a,b) = splitAt ram vs" by auto
  with b d show ?thesis  by (auto dest: splitAt_distinct_ab_aux)
qed

lemma splitAt_distinct_ab:
  "distinct vs \<Longrightarrow>  (a,b) = splitAt ram vs \<Longrightarrow> set a \<inter> set b = {}"
  apply (cases "ram \<in> set vs") apply (drule_tac splitAt_split)
  by (auto simp: splitAt_no_ram)

lemma splitAt_distinct_fst_snd:
    "distinct vs \<Longrightarrow>  set (fst (splitAt ram vs)) \<inter> set (snd (splitAt ram vs)) = {}"
  by (rule_tac splitAt_distinct_ab) simp_all

lemma splitAt_distinct_ram_fst[intro]:
  "distinct vs \<Longrightarrow> ram \<notin> set (fst (splitAt ram vs))"
  apply (case_tac "ram \<in> set vs") apply (drule_tac splitAt_ram)
  apply (rule distinct_split1) by (force dest: splitAt_in_fst)+
(*  apply (frule splitAt_no_ram) by auto  *)

lemma splitAt_distinct_ram_snd[intro]:
  "distinct vs \<Longrightarrow> ram \<notin> set (snd (splitAt ram vs))"
  apply (case_tac "ram \<in> set vs") apply (drule_tac splitAt_ram)
  apply (rule distinct_split2) by (force dest: splitAt_in_fst)+

lemma splitAt_1[simp]:
  "splitAt ram [] = ([],[])" by (simp add: splitAt_def)

lemma splitAt_2:
  "v \<in> set vs \<Longrightarrow> (a,b) = splitAt ram vs \<Longrightarrow> v \<in> set a \<or> v \<in> set b \<or> v = ram "
apply (cases "ram \<in> set vs")
 by (auto dest: splitAt_split simp: splitAt_no_ram)

lemma splitAt_distinct_fst: "distinct vs \<Longrightarrow> distinct (fst (splitAt ram1 vs))"
by (simp add: splitAt_def splitAtRec_distinct_fst)

lemma splitAt_distinct_a: "distinct vs \<Longrightarrow> (a,b) = splitAt ram vs \<Longrightarrow> distinct a"
by (auto dest: splitAt_distinct_fst pairD)

lemma splitAt_distinct_snd: "distinct vs \<Longrightarrow> distinct (snd (splitAt ram1 vs))"
by (simp add: splitAt_def splitAtRec_distinct_snd)

lemma splitAt_distinct_b: "distinct vs \<Longrightarrow> (a,b) = splitAt ram vs \<Longrightarrow> distinct b"
by (auto dest: splitAt_distinct_snd pairD)

lemma splitAt_distinct: "distinct vs \<Longrightarrow> set (fst (splitAt ram vs)) \<inter> set (snd (splitAt ram vs)) = {}"
by (simp add: splitAt_def splitAtRec_distinct)

lemma splitAt_subset: "(a,b) = splitAt ram vs \<Longrightarrow> (set a \<subseteq> set vs) \<and> (set b \<subseteq> set vs)"
apply (cases "ram \<in> set vs") by (auto dest: splitAt_split simp: splitAt_no_ram)


subsubsection {* @{const splitAt} composition *}

lemma set_help: "v \<in> set ( as @ bs) \<Longrightarrow> v \<in> set as \<or> v \<in> set bs" by auto

lemma splitAt_elements: "ram1 \<in> set vs \<Longrightarrow> ram2 \<in> set vs \<Longrightarrow> ram2 \<in> set( fst (splitAt ram1 vs)) \<or> ram2 \<in> set [ram1] \<or>  ram2 \<in> set( snd (splitAt ram1 vs))"
proof -
  assume r1: "ram1 \<in> set vs" and r2: "ram2 \<in> set vs"
  then have "ram2 \<in> set( fst (splitAt ram1 vs) @ [ram1]) \<or>  ram2 \<in> set( snd (splitAt ram1 vs))"
  apply (rule_tac set_help)
  apply (drule_tac splitAt_ram) by auto
  then show ?thesis by auto
qed

lemma splitAt_ram3: "ram2 \<notin>  set (fst (splitAt ram1 vs)) \<Longrightarrow>
  ram1 \<in> set vs \<Longrightarrow> ram2 \<in> set vs \<Longrightarrow> ram1 \<noteq> ram2 \<Longrightarrow>
  ram2 \<in> set (snd (splitAt ram1 vs))" by (auto dest: splitAt_elements)

lemma splitAt_dist_ram: "distinct vs \<Longrightarrow>
 vs = a @ ram # b \<Longrightarrow> (a,b) = splitAt ram vs"
proof -
  assume dist: "distinct vs" and vs: "vs = a @ ram # b"
  from vs have r:"ram \<in> set vs" by auto
  with dist vs have "fst (splitAt ram vs) = a" apply (drule_tac splitAt_ram) by (rule_tac dist_at1)  auto
  then have first:"a = fst (splitAt ram vs)" by   auto
  from r dist have second: "b = snd (splitAt ram vs)" apply (drule_tac splitAt_ram) apply (rule dist_at2) apply simp
    by (auto simp: vs)
  show ?thesis by (auto simp: first second)
qed

lemma distinct_unique1: "distinct vs \<Longrightarrow> ram \<in> set vs \<Longrightarrow> EX! s. vs = (fst s) @ ram # (snd s)"
proof
  assume d: "distinct vs" and r: "ram \<in> set vs"
  def s  \<equiv> "splitAt ram vs" with r show  "vs = (fst s) @ ram # (snd s)"
    by (auto intro: splitAt_ram)
next
  fix s
  assume d: "distinct vs" and vs1: "vs = fst s @ ram # snd s"
  from d vs1 show "s = splitAt ram vs" apply (drule_tac splitAt_dist_ram) apply simp by simp
qed

lemma splitAt_dist_ram2: "distinct vs \<Longrightarrow> vs = a @ ram1 # b @ ram2 # c \<Longrightarrow>
 (a @ ram1 # b, c) = splitAt ram2 vs"
by (auto intro: splitAt_dist_ram)

lemma splitAt_dist_ram20: "distinct vs \<Longrightarrow> vs = a @ ram1 # b @ ram2 # c \<Longrightarrow>
  c = snd (splitAt ram2 vs)"
proof -
  assume dist: "distinct vs" and vs: "vs = a @ ram1 # b @ ram2 # c"
  then show "c = snd (splitAt ram2 vs)" apply (drule_tac splitAt_dist_ram2) by (auto dest: pairD)
qed

lemma splitAt_dist_ram21: "distinct vs \<Longrightarrow> vs = a @ ram1 # b @ ram2 # c \<Longrightarrow> (a, b) = splitAt ram1 (fst (splitAt ram2 vs))"
proof -
  assume dist: "distinct vs" and vs: "vs = a @ ram1 # b @ ram2 # c"
  then have "fst (splitAt ram2 vs) = a @ ram1 # b" apply (drule_tac splitAt_dist_ram2) by (auto dest: pairD)
  with dist vs show ?thesis by (rule_tac splitAt_dist_ram) auto
qed

lemma splitAt_dist_ram22: "distinct vs \<Longrightarrow> vs = a @ ram1 # b @ ram2 # c \<Longrightarrow>  (c, []) = splitAt ram1 (snd (splitAt ram2 vs))"
proof -
  assume dist: "distinct vs" and vs: "vs = a @ ram1 # b @ ram2 # c"
  then have "snd (splitAt ram2 vs) = c" apply (drule_tac splitAt_dist_ram2) by (auto dest: pairD)
  with dist vs have "splitAt ram1 (snd (splitAt ram2 vs)) = (c, [])" by (auto intro: splitAt_no_ram)
  then show ?thesis by auto
qed

lemma splitAt_dist_ram1: "distinct vs \<Longrightarrow> vs = a @ ram1 # b @ ram2 # c \<Longrightarrow> (a, b @ ram2 # c) = splitAt ram1 vs"
by (auto intro: splitAt_dist_ram)

lemma splitAt_dist_ram10: "distinct vs \<Longrightarrow> vs = a @ ram1 # b @ ram2 # c \<Longrightarrow> a = fst (splitAt ram1 vs)"
proof -
  assume dist: "distinct vs" and vs: "vs = a @ ram1 # b @ ram2 # c"
  then show "a = fst (splitAt ram1 vs)" apply (drule_tac splitAt_dist_ram1) by (auto dest: pairD)
qed

lemma splitAt_dist_ram11: "distinct vs \<Longrightarrow> vs = a @ ram1 # b @ ram2 # c \<Longrightarrow> (a, []) = splitAt ram2 (fst (splitAt ram1 vs))"
proof -
  assume dist: "distinct vs" and vs: "vs = a @ ram1 # b @ ram2 # c"
  then have "fst (splitAt ram1 vs) = a" apply (drule_tac splitAt_dist_ram1) by (auto dest: pairD)
  with dist vs have "splitAt ram2 (fst (splitAt ram1 vs)) = (a, [])" by (auto intro: splitAt_no_ram)
  then show ?thesis by auto
qed

lemma splitAt_dist_ram12: "distinct vs \<Longrightarrow> vs = a @ ram1 # b @ ram2 # c \<Longrightarrow>  (b, c) = splitAt ram2 (snd (splitAt ram1 vs))"
proof -
  assume dist: "distinct vs" and vs: "vs = a @ ram1 # b @ ram2 # c"
  then have "snd (splitAt ram1 vs) = b @ ram2 # c" apply (drule_tac splitAt_dist_ram1) by (auto dest: pairD)
  with dist vs show ?thesis by (rule_tac splitAt_dist_ram)  auto
qed

lemma splitAt_dist_ram_all:
  "distinct vs \<Longrightarrow> vs = a @ ram1 # b @ ram2 # c
  \<Longrightarrow> (a, b) = splitAt ram1 (fst (splitAt ram2 vs))
  \<and> (c, []) = splitAt ram1 (snd (splitAt ram2 vs))
  \<and> (a, []) = splitAt ram2 (fst (splitAt ram1 vs))
  \<and> (b, c) = splitAt ram2 (snd (splitAt ram1 vs))
  \<and>  c = snd (splitAt ram2 vs)
  \<and>  a = fst (splitAt ram1 vs)"
  apply (rule_tac conjI) apply (rule_tac splitAt_dist_ram21) apply simp apply simp
  apply (rule_tac conjI) apply (rule_tac splitAt_dist_ram22) apply simp apply simp
  apply (rule_tac conjI) apply (rule_tac splitAt_dist_ram11 splitAt_dist_ram22) apply simp apply simp
  apply (rule_tac conjI) apply (rule_tac splitAt_dist_ram12)apply simp apply simp
  apply (rule_tac conjI) apply (rule_tac splitAt_dist_ram20) apply simp apply simp
                            by (rule_tac splitAt_dist_ram10) auto


subsubsection {* Mixed *}

lemma fst_splitAt_rev:
 "distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow>
  fst(splitAt x (rev xs)) = rev(snd(splitAt x xs))"
by(simp add:splitAt_conv takeWhile_neq_rev)

lemma snd_splitAt_rev:
 "distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow>
  snd(splitAt x (rev xs)) = rev(fst(splitAt x xs))"
by(simp add:splitAt_conv dropWhile_neq_rev)

lemma splitAt_take[simp]: "distinct ls \<Longrightarrow> i < length ls \<Longrightarrow> fst (splitAt (ls!i) ls) = take i ls"
proof -
  assume d: "distinct ls" and si: "i < length ls"
  then have ls1: "ls = take i ls @ ls!i # drop (Suc i) ls" by (rule_tac id_take_nth_drop)
  from si have "ls!i \<in> set ls" by auto
  then have ls2: "ls = fst (splitAt (ls!i) ls) @ ls!i # snd (splitAt (ls!i) ls)" by (auto dest: splitAt_ram)
  from d ls2 ls1 have "fst (splitAt (ls!i) ls) = take i ls \<and> snd (splitAt (ls!i) ls) = drop (Suc i) ls" by (rule dist_at)
   then show ?thesis by auto
qed

lemma splitAt_drop[simp]: "distinct ls \<Longrightarrow>  i < length ls \<Longrightarrow> snd (splitAt (ls!i) ls) = drop (Suc i) ls"
proof -
  assume d: "distinct ls" and si: "i < length ls"
  then have ls1: "ls = take i ls @ ls!i # drop (Suc i) ls" by (rule_tac id_take_nth_drop)
  from si have "ls!i \<in> set ls" by auto
  then have ls2: "ls = fst (splitAt (ls!i) ls) @ ls!i # snd (splitAt (ls!i) ls)" by (auto dest: splitAt_ram)
  from d ls2 ls1 have "fst (splitAt (ls!i) ls) = take i ls \<and> snd (splitAt (ls!i) ls) = drop (Suc i) ls" by (rule dist_at)
   then show ?thesis by auto
qed

lemma fst_splitAt_upt:
 "j <= i \<Longrightarrow> i < k \<Longrightarrow> fst(splitAt i [j..<k]) = [j..<i]"
using splitAt_take[where ls = "[j..<k]" and i="i-j"]
apply (simp del:splitAt_take)
done

lemma snd_splitAt_upt:
 "j <= i \<Longrightarrow> i < k \<Longrightarrow> snd(splitAt i [j..<k]) = [i+1..<k]"
using splitAt_drop[where ls = "[j..<k]" and i="i-j"]
by simp

lemma local_help1: "\<And> a vs. vs = c @ r # d \<Longrightarrow> vs = a @ r # b \<Longrightarrow> r \<notin> set a \<Longrightarrow> r \<notin> set b \<Longrightarrow> a = c"
proof (induct c)
  case Nil
  then have ra: "r \<notin> set a" and vs1: "vs = a @ r # b" and vs2: "vs = [] @ r # d"
    by auto
  from vs1 vs2 have "a @ r # b = r # d" by auto
  then have "hd (a @ r # b) = r" by auto
  then have "a \<noteq> [] \<Longrightarrow> hd a = r" by auto
  then have "a \<noteq> [] \<Longrightarrow> r \<in> set a" by (induct a) auto
  with ra have a: "a = []" by auto
  then show ?case by auto
next
  case (Cons x xs) then show ?case by (induct a) auto
qed

lemma local_help: "vs = a @ r # b \<Longrightarrow> vs = c @ r # d \<Longrightarrow> r \<notin> set a \<Longrightarrow> r \<notin> set b \<Longrightarrow> a = c \<and> b = d"
proof -
  assume dist: "r \<notin> set a" "r \<notin> set b" and vs1: "vs = a @ r # b" and vs2: "vs = c @ r # d"
  from vs2 vs1 dist have "a = c" by (rule local_help1)
  with dist vs1 vs2 show ?thesis by simp
qed

lemma local_help': "a @ r # b = c @ r # d \<Longrightarrow> r \<notin> set a \<Longrightarrow> r \<notin> set b \<Longrightarrow> a = c \<and> b = d"
by (rule local_help) auto


lemma splitAt_simp1: "ram \<notin> set a \<Longrightarrow> ram \<notin> set b \<Longrightarrow> fst (splitAt ram (a @ ram # b)) = a "
proof -
  assume ramab: "ram \<notin> set a"  "ram \<notin> set b"
  def vs \<equiv> "a @ ram # b"
  then have vs: "vs = a @ ram # b" by auto
  then have "ram \<in> set vs" by auto
  then have "vs = fst (splitAt ram vs) @ ram # snd (splitAt ram vs)" by (auto dest: splitAt_ram)
  with  vs ramab show ?thesis apply simp apply (rule_tac sym)  apply (rule_tac local_help1) apply simp
    apply (rule sym) apply assumption by auto
qed


lemma help'''_in: "\<And> xs. ram \<in> set b \<Longrightarrow> fst (splitAtRec ram xs b) = xs @ fst (splitAtRec ram [] b)"
proof (induct b)
case Nil then show ?case by auto
next
case (Cons b bs) show ?case using Cons(2)
  apply (case_tac "b = ram") apply simp
  apply simp
  apply (subgoal_tac "fst (splitAtRec ram (xs @ [b]) bs) = (xs@[b]) @ fst (splitAtRec ram [] bs)") apply simp
  apply (subgoal_tac "fst (splitAtRec ram [b] bs) = [b] @ fst (splitAtRec ram [] bs)") apply simp
  apply (rule Cons) apply force
  apply (rule Cons) by force
qed

lemma help'''_notin: "\<And> xs. ram \<notin>  set b \<Longrightarrow> fst (splitAtRec ram xs b) = xs @ fst (splitAtRec ram [] b)"
proof (induct b)
case Nil then show ?case by auto
next
case (Cons b bs)
then have "ram \<notin> set bs" by auto
then show ?case
  apply (case_tac "b = ram") apply simp
  apply simp
  apply (subgoal_tac "fst (splitAtRec ram (xs @ [b]) bs) = (xs@[b]) @ fst (splitAtRec ram [] bs)") apply simp
  apply (subgoal_tac "fst (splitAtRec ram [b] bs) = [b] @ fst (splitAtRec ram [] bs)") apply simp
  apply (rule Cons) apply simp
  apply (rule Cons) by simp
qed

lemma help''': "fst (splitAtRec ram xs b) = xs @ fst (splitAtRec ram [] b)"
apply (cases "ram \<in> set b")
apply (rule_tac help'''_in) apply simp
apply (rule_tac help'''_notin) apply simp done

lemma splitAt_simpA[simp]: "fst (splitAt ram (ram # b)) = []" by (simp add: splitAt_def)
lemma splitAt_simpB[simp]: "ram \<noteq> a \<Longrightarrow> fst (splitAt ram (a # b)) = a # fst (splitAt ram b)" apply (simp add: splitAt_def)
  apply (subgoal_tac "fst (splitAtRec ram [a] b) = [a] @ fst (splitAtRec ram [] b)") apply simp by (rule help''')
lemma splitAt_simpB'[simp]: "a \<noteq> ram \<Longrightarrow> fst (splitAt ram (a # b)) = a # fst (splitAt ram b)" apply (rule splitAt_simpB) by auto
lemma splitAt_simpC[simp]: "ram \<notin> set a  \<Longrightarrow> fst (splitAt ram (a @ b)) = a @ fst (splitAt ram b)"
apply (induct a) by auto

lemma help'''': "\<And> xs ys. snd (splitAtRec ram xs b) = snd (splitAtRec ram ys b)"
apply (induct b) by auto

lemma splitAt_simpD[simp]: "\<And> a. ram \<noteq> a \<Longrightarrow> snd (splitAt ram (a # b)) = snd (splitAt ram b)" apply (simp add: splitAt_def)
by (rule help'''')
lemma splitAt_simpD'[simp]: "\<And> a. a \<noteq> ram \<Longrightarrow> snd (splitAt ram (a # b)) = snd (splitAt ram b)" apply (rule splitAt_simpD) by auto

lemma splitAt_simpE[simp]: "snd (splitAt ram (ram # b)) = b" by (simp add: splitAt_def)

lemma splitAt_simpF[simp]: "ram \<notin> set a  \<Longrightarrow> snd (splitAt ram (a @ b)) = snd (splitAt ram b) "
apply (induct a) by auto


lemma splitAt_rotate_pair_conv:
  "!!xs. \<lbrakk> distinct xs; x \<in> set xs \<rbrakk>
  \<Longrightarrow> snd (splitAt x (rotate n xs)) @ fst (splitAt x (rotate n xs)) =
      snd (splitAt x xs) @ fst (splitAt x xs)"
apply(induct n) apply simp
apply(simp del:rotate_Suc2 add:rotate1_rotate_swap)
apply(case_tac xs) apply clarsimp+
apply(erule disjE) apply simp
apply(drule split_list)
apply clarsimp
done


subsection {* @{text between} *}

definition between :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list" where
 "between vs ram\<^sub>1 ram\<^sub>2 \<equiv>
     let (pre\<^sub>1, post\<^sub>1) = splitAt ram\<^sub>1 vs in
     if ram\<^sub>2 \<in> set post\<^sub>1
     then let (pre\<^sub>2, post\<^sub>2) = splitAt ram\<^sub>2 post\<^sub>1 in pre\<^sub>2
     else let (pre\<^sub>2, post\<^sub>2) = splitAt ram\<^sub>2 pre\<^sub>1 in post\<^sub>1 @ pre\<^sub>2"

lemma inbetween_inset:
 "x \<in> set(between xs a b) \<Longrightarrow> x \<in> set xs"
apply(simp add:between_def split_def split:split_if_asm)
 apply(blast dest:splitAt_in_snd)
apply(blast dest:splitAt_in_snd)
done

lemma notinset_notinbetween:
 "x \<notin> set xs \<Longrightarrow> x \<notin> set(between xs a b)"
by(blast dest:inbetween_inset)


lemma set_between_id:
 "distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow>
  set(between xs x x) = set xs - {x}"
apply(drule split_list)
apply (clarsimp simp:between_def split_def Un_commute)
done


lemma split_between:
 "\<lbrakk> distinct vs; r \<in> set vs; v \<in> set vs; u \<in> set(between vs r v) \<rbrakk> \<Longrightarrow>
  between vs r v =
 (if r=u then [] else between vs r u @ [u]) @ between vs u v"
apply(cases  "r = v")
 apply(clarsimp)
 apply(frule split_list[of v])
 apply(clarsimp)
 apply(simp add:between_def split_def split:split_if_asm)
 apply(erule disjE)
  apply(frule split_list[of u])
  apply(clarsimp)
  apply(frule split_list[of u])
  apply(clarsimp)
 apply(clarsimp)
 apply(frule split_list[of r])
apply(clarsimp)
apply(rename_tac as bs)
apply(erule disjE)
 apply(frule split_list[of v])
 apply(clarsimp)
 apply(rename_tac cs ds)
 apply(subgoal_tac "between (cs @ v # ds @ r # bs) r v = bs @ cs")
  prefer 2 apply(simp add:between_def split_def split:split_if_asm)
 apply simp
 apply(erule disjE)
  apply(frule split_list[of u])
  apply(clarsimp simp:between_def split_def split:split_if_asm)
 apply(frule split_list[of u])
 apply(clarsimp simp:between_def split_def split:split_if_asm)
apply(frule split_list[of v])
apply(clarsimp)
apply(rename_tac cs ds)
apply(subgoal_tac "between (as @ r # cs @ v # ds) r v = cs")
 prefer 2 apply(simp add:between_def split_def split:split_if_asm)
apply simp
apply(frule split_list[of u])
apply(clarsimp simp:between_def split_def split:split_if_asm)
done


subsection {* Tables *}

type_synonym ('a, 'b) table = "('a \<times> 'b) list"

definition isTable :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) table \<Rightarrow> bool" where
  "isTable f vs t \<equiv> \<forall>p. p \<in> set t \<longrightarrow> snd p = f (fst p) \<and> fst p \<in> set vs" 

lemma isTable_eq: "isTable E vs ((a,b)#ps) \<Longrightarrow> b = E a"
  by (auto simp add: isTable_def)

lemma isTable_subset: 
  "set qs \<subseteq> set ps \<Longrightarrow> isTable E vs ps \<Longrightarrow> isTable E vs qs"
  by (unfold isTable_def) auto

lemma isTable_Cons: "isTable E vs ((a,b)#ps) \<Longrightarrow> isTable E vs ps"
  by (unfold isTable_def) auto


definition removeKey :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
"removeKey a ps \<equiv> [p \<leftarrow> ps. a \<noteq> fst p]"

primrec removeKeyList :: "'a list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "removeKeyList [] ps = ps"
| "removeKeyList (w#ws) ps = removeKey w (removeKeyList ws ps)"

lemma removeKey_subset[simp]: "set (removeKey a ps) \<subseteq> set ps"
  by (simp add: removeKey_def) blast

lemma length_removeKey[simp]: "|removeKey w ps| \<le> |ps|"
  by (simp add: removeKey_def) 

lemma length_removeKeyList: 
  "length (removeKeyList ws ps) \<le> length ps" (is "?P ws")
proof (induct ws)
    show "?P []" by simp
    fix w ws
    have "length (removeKey w (removeKeyList ws ps)) 
      \<le> length (removeKeyList ws ps)" 
      by (rule length_removeKey)
    also assume "?P ws" 
    finally show "?P (w#ws)" by simp
qed

lemma removeKeyList_subset[simp]: "set (removeKeyList ws ps) \<subseteq> set ps"
proof (induct ws) 
  case Nil then show ?case by simp
next
  case (Cons w ws) 
  have "set (removeKey w (removeKeyList ws ps)) \<subseteq> set (removeKeyList ws ps)"
    by (rule removeKey_subset)
  with Cons show ?case by (simp add: removeKey_def)
qed

lemma notin_removeKey1: "(a, b) \<notin> set (removeKey a ps)"
  by (induct ps) (auto simp add: removeKey_def)

lemma removeKeyList_eq:
  "removeKeyList as ps = [p \<leftarrow> ps. \<forall>a \<in> set as. a \<noteq> fst p]"
by (induct as) (simp_all add: filter_comm removeKey_def)

lemma removeKey_empty[simp]: "removeKey a [] = []"
  by (simp add: removeKey_def)
lemma removeKeyList_empty[simp]: "removeKeyList ps [] = []"
  by (induct ps) simp_all
lemma removeKeyList_cons[simp]: 
  "removeKeyList ws (p#ps) 
  = (if fst p \<in> set ws then removeKeyList ws ps else p#(removeKeyList ws ps))"
  by (induct ws) (simp_all split: split_if_asm add: removeKey_def)

end
