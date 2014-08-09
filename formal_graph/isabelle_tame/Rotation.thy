(*  Author:     Tobias Nipkow
*)

header {* More Rotation *}

theory Rotation
imports ListAux PlaneGraphIso
begin

definition rotate_to :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"rotate_to vs v \<equiv>  v # snd (splitAt v vs) @ fst (splitAt v vs)"

definition rotate_min :: "nat list \<Rightarrow> nat list" where
"rotate_min vs \<equiv> rotate_to vs (min_list vs)"


lemma cong_rotate_to:
 "x \<in> set xs \<Longrightarrow> xs \<cong> rotate_to xs x"
proof -
  assume x: "x \<in> set xs"
  hence ls1: "xs = fst (splitAt x xs) @ x # snd (splitAt x xs)" by (auto dest: splitAt_ram)
  def i \<equiv> "length(fst(splitAt x xs))"
  hence "i < length((fst(splitAt x xs)) @ [x] @ snd(splitAt x xs))" by auto
  with ls1 have i_len: "i < length xs" by auto
  hence ls2: "xs = take i xs @ xs!i # drop (Suc i) xs" by (auto intro: id_take_nth_drop)
  from i_len have "length (take i xs) = i" by auto
  with i_def have len_eq: "length(take i xs) = length(fst(splitAt x xs))" by auto
  moreover
  from ls1 ls2 have eq: "take i xs @ xs!i # drop (Suc i) xs = fst(splitAt x xs) @ x # snd(splitAt x xs)" by simp
  ultimately have
    v_simp: "x = xs!i" and
    take_i: "fst(splitAt x xs) = take i xs" and
    drop_i': "snd(splitAt x xs) = drop (Suc i) xs" by auto
  from i_len have ls3: "xs = take i xs @ drop i xs" by auto
  with take_i have eq: "xs = fst(splitAt x xs) @ drop i xs" by auto
  with ls1 have "fst(splitAt x xs) @ drop i xs = fst(splitAt x xs) @ x # snd(splitAt x xs)" by auto
  then have drop_i: "drop i xs = x # snd(splitAt x xs)" by auto
  have "rotate i xs = drop (i mod length xs) xs @ take (i mod length xs) xs" by (rule rotate_drop_take)
  with i_len have "rotate i xs = drop i xs @ take i xs" by auto
  with take_i drop_i have "rotate i xs = (x # snd(splitAt x xs)) @ fst(splitAt x xs)" by auto
  thus ?thesis apply (auto simp: congs_def rotate_to_def) apply (rule exI) apply (rule sym) .
qed

lemma face_cong_if_norm_eq:
 "\<lbrakk> rotate_min xs = rotate_min ys; xs \<noteq> []; ys \<noteq> [] \<rbrakk> \<Longrightarrow> xs \<cong> ys"
apply(simp add:rotate_min_def)
apply(subgoal_tac "xs \<cong> rotate_to xs (Min (set xs))")
 apply(subgoal_tac "ys \<cong> rotate_to ys (Min (set ys))")
  apply(simp) apply(blast intro:congs_sym congs_trans)
 apply(simp add: cong_rotate_to)
apply(drule sym)
apply(simp add: cong_rotate_to)
done

lemma norm_eq_if_face_cong:
  "\<lbrakk> xs \<cong> ys; distinct xs; xs \<noteq> [] \<rbrakk> \<Longrightarrow> rotate_min xs = rotate_min ys"
by(auto simp:congs_def rotate_min_def rotate_to_def
  splitAt_rotate_pair_conv insert_absorb)

lemma norm_eq_iff_face_cong:
 "\<lbrakk> distinct xs; xs \<noteq> []; ys \<noteq> [] \<rbrakk> \<Longrightarrow>
  (rotate_min xs = rotate_min ys) = (xs \<cong> ys)"
by(blast intro: face_cong_if_norm_eq norm_eq_if_face_cong)

lemma inj_on_rotate_min_iff:
assumes "\<forall>vs \<in> A. distinct vs"  "[] \<notin> A"
shows "inj_on rotate_min A = inj_on (\<lambda>vs. {vs}//{\<cong>}) A"
proof -
  { fix xs ys assume xs: "xs \<in> A" and ys : "ys \<in> A"
    hence "xs \<noteq> [] \<and> ys \<noteq> []" using assms(2) by blast
    hence "(rotate_min xs = rotate_min ys) = (xs \<cong> ys)"
      using xs assms(1)
      by(simp add: singleton_list_cong_eq_iff norm_eq_iff_face_cong)
  } thus ?thesis by(simp add:inj_on_def)
qed


end
