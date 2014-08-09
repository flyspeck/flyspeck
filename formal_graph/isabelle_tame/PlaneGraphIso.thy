(*  Author: Tobias Nipkow  *)

header{* Isomorphisms Between Plane Graphs *}

theory PlaneGraphIso
imports Main Quasi_Order
begin

(* FIXME globalize *)
lemma image_image_id_if[simp]: "(!!x. f(f x) = x) \<Longrightarrow> f ` f ` M = M"
by (auto simp: image_iff)


declare not_None_eq [iff] not_Some_eq [iff]


text{* The symbols @{text "\<cong>"} and @{text "\<simeq>"} are overloaded.  They
denote congruence and isomorphism on arbitrary types. On lists
(representing faces of graphs), @{text "\<cong>"} means congruence modulo
rotation; @{text "\<simeq>"} is currently unused. On graphs, @{text "\<simeq>"}
means isomorphism and is a weaker version of @{text "\<cong>"} (proper
isomorphism): @{text "\<simeq>"} also allows to reverse the orientation of
all faces. *}

consts
 pr_isomorphic  :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<cong>" 60)
(* isomorphic :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<simeq>" 60)
*)
(*
definition "congs"  :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "\<cong>" 60) where
 "F\<^sub>1 \<cong> (F\<^sub>2::'a list) \<equiv> \<exists>n. F\<^sub>2 = rotate n F\<^sub>1"
*)
definition Iso :: "('a list * 'a list) set" ("{\<cong>}") where
 "{\<cong>} \<equiv> {(F\<^sub>1, F\<^sub>2). F\<^sub>1 \<cong> F\<^sub>2}"

lemma [iff]: "((x,y) \<in> {\<cong>}) = x \<cong> y"
by(simp add:Iso_def)

text{* A plane graph is a set or list (for executability) of faces
(hence @{text Fgraph} and @{text fgraph}) and a face is a list of
nodes: *}

type_synonym 'a Fgraph = "'a list set"
type_synonym 'a fgraph = "'a list list"

subsection{* Equivalence of faces *}

text{* Two faces are equivalent modulo rotation: *}

defs (overloaded) congs_def:
 "F\<^sub>1 \<cong> (F\<^sub>2::'a list) \<equiv> \<exists>n. F\<^sub>2 = rotate n F\<^sub>1"

lemma congs_refl[iff]: "(xs::'a list) \<cong> xs"
apply(simp add:congs_def)
apply(rule_tac x = 0 in exI)
apply (simp)
done

lemma congs_sym: assumes A: "(xs::'a list) \<cong> ys" shows "ys \<cong> xs"
proof (simp add:congs_def)
  let ?l = "length xs"
  from A obtain n where ys: "ys = rotate n xs" by(fastforce simp add:congs_def)
  have "xs = rotate ?l xs" by simp
  also have "\<dots> = rotate (?l - n mod ?l + n mod ?l) xs"
  proof (cases)
    assume "xs = []" thus ?thesis by simp
  next
    assume "xs \<noteq> []"
    hence "n mod ?l < ?l" by simp
    hence "?l = ?l - n mod ?l + n mod ?l" by arith
    thus ?thesis by simp
  qed
  also have "\<dots> = rotate (?l - n mod ?l) (rotate (n mod ?l) xs)"
    by(simp add:rotate_rotate)
  also have "rotate (n mod ?l) xs = rotate n xs"
    by(rule rotate_conv_mod[symmetric])
  finally show "\<exists>m. xs = rotate m ys" by(fastforce simp add:ys)
qed

lemma congs_trans: "(xs::'a list) \<cong> ys \<Longrightarrow> ys \<cong> zs \<Longrightarrow> xs \<cong> zs"
apply(clarsimp simp:congs_def rotate_def)
apply(rename_tac m n)
apply(rule_tac x = "n+m" in exI)
apply (simp add:funpow_add)
done

lemma equiv_EqF: "equiv (UNIV::'a list set) {\<cong>}"
apply(unfold equiv_def sym_def trans_def refl_on_def)
apply(rule conjI)
 apply simp
apply(rule conjI)
 apply(fastforce intro:congs_sym)
apply(fastforce intro:congs_trans)
done

lemma congs_distinct:
  "F\<^sub>1 \<cong> F\<^sub>2 \<Longrightarrow> distinct F\<^sub>2 = distinct F\<^sub>1"
by (auto simp: congs_def)

lemma congs_length:
  "F\<^sub>1 \<cong> F\<^sub>2 \<Longrightarrow> length F\<^sub>2 = length F\<^sub>1"
by (auto simp: congs_def)

lemma congs_pres_nodes: "F\<^sub>1 \<cong> F\<^sub>2 \<Longrightarrow> set F\<^sub>1 = set F\<^sub>2"
by(clarsimp simp:congs_def)

lemma congs_map:
  "F\<^sub>1 \<cong> F\<^sub>2 \<Longrightarrow> map f F\<^sub>1 \<cong> map f F\<^sub>2"
by (auto simp: congs_def rotate_map)

lemma congs_map_eq_iff:
 "inj_on f (set xs \<union> set ys) \<Longrightarrow> (map f xs \<cong> map f ys) = (xs \<cong> ys)"
apply(simp add:congs_def)
apply(rule iffI)
 apply(clarsimp simp: rotate_map)
 apply(drule map_inj_on)
  apply(simp add:Un_commute)
 apply (fastforce)
apply clarsimp
apply(fastforce simp: rotate_map)
done


lemma list_cong_rev_iff[simp]:
  "(rev xs \<cong> rev ys) = (xs \<cong> ys)"
apply(simp add:congs_def rotate_rev)
apply(rule iffI)
 apply fast
apply clarify
apply(cases "length xs = 0")
 apply simp
apply(case_tac "n mod length xs = 0")
 apply(rule_tac x = "n" in exI)
 apply simp
apply(subst rotate_conv_mod)
apply(rule_tac x = "length xs - n mod length xs" in exI)
apply simp
done


lemma singleton_list_cong_eq_iff[simp]:
  "({xs::'a list} // {\<cong>} = {ys} // {\<cong>}) = (xs \<cong> ys)"
by(simp add: eq_equiv_class_iff2[OF equiv_EqF])


subsection{* Homomorphism and isomorphism *}

definition is_pr_Hom :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Fgraph \<Rightarrow> 'b Fgraph \<Rightarrow> bool" where
"is_pr_Hom \<phi> Fs\<^sub>1 Fs\<^sub>2 \<equiv> (map \<phi> ` Fs\<^sub>1)//{\<cong>} = Fs\<^sub>2 //{\<cong>}"

definition is_pr_Iso :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Fgraph \<Rightarrow> 'b Fgraph \<Rightarrow> bool" where
"is_pr_Iso \<phi> Fs\<^sub>1 Fs\<^sub>2 \<equiv> is_pr_Hom \<phi> Fs\<^sub>1 Fs\<^sub>2 \<and> inj_on \<phi> (\<Union>F \<in> Fs\<^sub>1. set F)"

definition is_pr_iso :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fgraph \<Rightarrow> 'b fgraph \<Rightarrow> bool" where
"is_pr_iso \<phi> Fs\<^sub>1 Fs\<^sub>2 \<equiv> is_pr_Iso \<phi> (set Fs\<^sub>1) (set Fs\<^sub>2)"

text{* Homomorphisms preserve the set of nodes. *}

lemma UN_subset_iff: "((\<Union>i\<in>I. f i) \<subseteq> B) = (\<forall>i\<in>I. f i \<subseteq> B)"
by blast

declare Image_Collect_split[simp del]

lemma pr_Hom_pres_face_nodes:
 "is_pr_Hom \<phi> Fs\<^sub>1 Fs\<^sub>2 \<Longrightarrow> (\<Union>F\<in>Fs\<^sub>1. {\<phi> ` (set F)}) = (\<Union>F\<in>Fs\<^sub>2. {set F})"
apply(clarsimp simp:is_pr_Hom_def quotient_def)
apply auto
apply(subgoal_tac "EX F' : Fs\<^sub>2. {\<cong>} `` {map \<phi> F} = {\<cong>} `` {F'}")
 prefer 2 apply blast
apply (fastforce simp: eq_equiv_class_iff[OF equiv_EqF] dest!:congs_pres_nodes)
apply(subgoal_tac "EX F' : Fs\<^sub>1. {\<cong>} `` {map \<phi> F'} = {\<cong>} `` {F}")
 apply (fastforce simp: eq_equiv_class_iff[OF equiv_EqF] dest!:congs_pres_nodes)
apply (erule equalityE)
apply(fastforce simp:UN_subset_iff)
done

lemma pr_Hom_pres_nodes:
  "is_pr_Hom \<phi> Fs\<^sub>1 Fs\<^sub>2 \<Longrightarrow> \<phi> ` (\<Union>F\<in>Fs\<^sub>1. set F) = (\<Union>F\<in>Fs\<^sub>2. set F)"
apply(drule pr_Hom_pres_face_nodes)
apply(rule equalityI)
 apply blast
apply(clarsimp)
apply(subgoal_tac "set F : (\<Union>F\<in>Fs\<^sub>2. {set F})")
 prefer 2 apply blast
apply(subgoal_tac "set F : (\<Union>F\<in>Fs\<^sub>1. {\<phi> ` set F})")
 prefer 2 apply blast
apply(subgoal_tac "EX F':Fs\<^sub>1. \<phi> ` set F' = set F")
 prefer 2 apply blast
apply blast
done

text{* Therefore isomorphisms preserve cardinality of node set. *}

lemma pr_Iso_same_no_nodes:
  "\<lbrakk> is_pr_Iso \<phi> Fs\<^sub>1 Fs\<^sub>2; finite Fs\<^sub>1 \<rbrakk>
   \<Longrightarrow> card(\<Union>F\<in>Fs\<^sub>1. set F) = card(\<Union>F\<in>Fs\<^sub>2. set F)"
by(clarsimp simp add: is_pr_Iso_def pr_Hom_pres_nodes[symmetric] card_image)

lemma pr_iso_same_no_nodes:
  "is_pr_iso \<phi> Fs\<^sub>1 Fs\<^sub>2 \<Longrightarrow> card(\<Union>F\<in>set Fs\<^sub>1. set F) = card(\<Union>F\<in>set Fs\<^sub>2. set F)"
by(simp add: is_pr_iso_def pr_Iso_same_no_nodes)

text{* Isomorphisms preserve the number of faces. *}

lemma pr_iso_same_no_faces:
  assumes dist1: "distinct Fs\<^sub>1" and dist2: "distinct Fs\<^sub>2"
  and inj1: "inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>1)"
  and inj2: "inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>2)" and iso: "is_pr_iso \<phi> Fs\<^sub>1 Fs\<^sub>2"
  shows "length Fs\<^sub>1 = length Fs\<^sub>2"
proof -
  have injphi: "\<forall>F\<in>set Fs\<^sub>1. \<forall>F'\<in>set Fs\<^sub>1. inj_on \<phi> (set F \<union> set F')" using iso
    by(auto simp:is_pr_iso_def is_pr_Iso_def is_pr_Hom_def inj_on_def)
  have inj1': "inj_on (%xs. {xs} // {\<cong>}) (map \<phi> ` set Fs\<^sub>1)"
    apply(rule inj_on_imageI)
    apply(simp add:inj_on_def quotient_def eq_equiv_class_iff[OF equiv_EqF])
    apply(simp add: congs_map_eq_iff injphi)
    using inj1
    apply(simp add:inj_on_def quotient_def eq_equiv_class_iff[OF equiv_EqF])
    done
  have "length Fs\<^sub>1 = card(set Fs\<^sub>1)" by(simp add:distinct_card[OF dist1])
  also have "\<dots> = card(map \<phi> ` set Fs\<^sub>1)" using iso
    by(auto simp:is_pr_iso_def is_pr_Iso_def is_pr_Hom_def inj_on_mapI card_image)
  also have "\<dots> = card((map \<phi> ` set Fs\<^sub>1) // {\<cong>})"
    by(simp add: card_quotient_disjoint[OF _ inj1'])
  also have "(map \<phi> ` set Fs\<^sub>1)//{\<cong>} = set Fs\<^sub>2 // {\<cong>}"
    using iso by(simp add: is_pr_iso_def is_pr_Iso_def is_pr_Hom_def)
  also have "card(\<dots>) = card(set Fs\<^sub>2)"
    by(simp add: card_quotient_disjoint[OF _ inj2])
  also have "\<dots> = length Fs\<^sub>2" by(simp add:distinct_card[OF dist2])
  finally show ?thesis .
qed


lemma is_Hom_distinct:
 "\<lbrakk> is_pr_Hom \<phi> Fs\<^sub>1 Fs\<^sub>2; \<forall>F\<in>Fs\<^sub>1. distinct F; \<forall>F\<in>Fs\<^sub>2. distinct F \<rbrakk>
  \<Longrightarrow> \<forall>F\<in>Fs\<^sub>1. distinct(map \<phi> F)"
apply(clarsimp simp add:is_pr_Hom_def)
apply(subgoal_tac "\<exists> F' \<in> Fs\<^sub>2. (map \<phi> F, F') : {\<cong>}")
 apply(fastforce simp add: congs_def)
apply(subgoal_tac "\<exists> F' \<in> Fs\<^sub>2. {map \<phi> F}//{\<cong>} = {F'}//{\<cong>}")
 apply clarify
 apply(rule_tac x = F' in bexI)
  apply(rule eq_equiv_class[OF _ equiv_EqF])
   apply(simp add:singleton_quotient)
  apply blast
 apply assumption
apply(simp add:quotient_def)
apply(rotate_tac 1)
apply blast
done


lemma Collect_congs_eq_iff[simp]:
  "Collect (op \<cong> x) = Collect (op \<cong> y) \<longleftrightarrow> (x \<cong> (y::'a list))"
using eq_equiv_class_iff2[OF equiv_EqF]
apply(simp add: quotient_def Iso_def)
apply blast
done

lemma is_pr_Hom_trans: assumes f: "is_pr_Hom f A B" and g: "is_pr_Hom g B C"
shows "is_pr_Hom (g o f) A C"
proof-
  from f have f1: "ALL a:A. EX b:B. map f a \<cong> b"
    apply(simp add: is_pr_Hom_def quotient_def Iso_def)
    apply(erule equalityE)
    apply blast
    done
  from f have f2: "ALL b:B. EX a:A. map f a \<cong> b"
    apply(simp add: is_pr_Hom_def quotient_def Iso_def)
    apply(erule equalityE)
    apply blast
    done
  from g have g1: "ALL b:B. EX c:C. map g b \<cong> c"
    apply(simp add: is_pr_Hom_def quotient_def Iso_def)
    apply(erule equalityE)
    apply blast
    done
  from g have g2: "ALL c:C. EX b:B. map g b \<cong> c"
    apply(simp add: is_pr_Hom_def quotient_def Iso_def)
    apply(erule equalityE)
    apply blast
    done
  show ?thesis
    apply(auto simp add: is_pr_Hom_def quotient_def Iso_def Image_def
      map_comp_map[symmetric] image_comp simp del: map_map map_comp_map)
    apply (metis congs_map[of _ _ g] congs_trans f1 g1)
    by (metis congs_map[of _ _ g] congs_sym congs_trans f2 g2)
qed

lemma is_pr_Hom_rev:
  "is_pr_Hom \<phi> A B \<Longrightarrow> is_pr_Hom \<phi> (rev ` A) (rev ` B)"
apply(auto simp add: is_pr_Hom_def quotient_def Image_def Iso_def rev_map[symmetric])
 apply(erule equalityE)
 apply blast
apply(erule equalityE)
apply blast
done


text{* A kind of recursion rule, a first step towards executability: *}

lemma is_pr_Iso_rec:
 "\<lbrakk> inj_on (%xs. {xs}//{\<cong>}) Fs\<^sub>1; inj_on (%xs. {xs}//{\<cong>}) Fs\<^sub>2; F\<^sub>1 \<in> Fs\<^sub>1 \<rbrakk> \<Longrightarrow>
 is_pr_Iso \<phi> Fs\<^sub>1 Fs\<^sub>2 =
 (\<exists>F\<^sub>2 \<in> Fs\<^sub>2. length F\<^sub>1 = length F\<^sub>2 \<and> is_pr_Iso \<phi> (Fs\<^sub>1 - {F\<^sub>1}) (Fs\<^sub>2 - {F\<^sub>2})
    \<and> (\<exists>n. map \<phi> F\<^sub>1 = rotate n F\<^sub>2)
    \<and> inj_on \<phi> (\<Union>F\<in>Fs\<^sub>1. set F))"
apply(drule mk_disjoint_insert[of F\<^sub>1])
apply clarify
apply(rename_tac Fs\<^sub>1')
apply(rule iffI)

apply (clarsimp simp add:is_pr_Iso_def)
apply(clarsimp simp:is_pr_Hom_def quotient_diff1)
apply(drule_tac s="?a // ?b" in sym)
apply(clarsimp)
apply(subgoal_tac "{\<cong>} `` {map \<phi> F\<^sub>1} : Fs\<^sub>2 // {\<cong>}")
 prefer 2 apply(simp add:quotient_def)
apply(erule quotientE)
apply(rename_tac F\<^sub>2)
apply(drule eq_equiv_class[OF _ equiv_EqF])
 apply blast
apply(rule_tac x = F\<^sub>2 in bexI)
 prefer 2 apply assumption
apply(rule conjI)
 apply(clarsimp simp: congs_def)
apply(rule conjI)
 apply(subgoal_tac "{\<cong>} `` {F\<^sub>2} = {\<cong>} `` {map \<phi> F\<^sub>1}")
  prefer 2
  apply(rule equiv_class_eq[OF equiv_EqF])
  apply(fastforce intro: congs_sym)
 apply(subgoal_tac "{F\<^sub>2}//{\<cong>} = {map \<phi> F\<^sub>1}//{\<cong>}")
  prefer 2 apply(simp add:singleton_quotient)
 apply(subgoal_tac "\<forall>F\<in>Fs\<^sub>1'. \<not> (map \<phi> F) \<cong> (map \<phi> F\<^sub>1)")
  apply(fastforce simp:Iso_def quotient_def Image_Collect_split simp del: Collect_congs_eq_iff
                 dest!: eq_equiv_class[OF _ equiv_EqF])
 apply clarify
 apply(subgoal_tac "inj_on \<phi> (set F \<union> set F\<^sub>1)")
  prefer 2
  apply(erule subset_inj_on)
  apply(blast)
 apply(clarsimp simp add:congs_map_eq_iff)
 apply(subgoal_tac "{\<cong>} `` {F\<^sub>1} = {\<cong>} `` {F}")
  apply(simp add:singleton_quotient)
 apply(rule equiv_class_eq[OF equiv_EqF])
 apply(blast intro:congs_sym)
apply(subgoal_tac "F\<^sub>2 \<cong> (map \<phi> F\<^sub>1)")
 apply (simp add:congs_def inj_on_Un)
apply(clarsimp intro!:congs_sym)

apply(clarsimp simp add: is_pr_Iso_def is_pr_Hom_def quotient_diff1)
apply (simp add:singleton_quotient)
apply(subgoal_tac "F\<^sub>2 \<cong> (map \<phi> F\<^sub>1)")
 prefer 2 apply(fastforce simp add:congs_def)
apply(subgoal_tac "{\<cong>}``{map \<phi> F\<^sub>1} = {\<cong>}``{F\<^sub>2}")
 prefer 2
 apply(rule equiv_class_eq[OF equiv_EqF])
 apply(fastforce intro:congs_sym)
apply(subgoal_tac "{\<cong>}``{F\<^sub>2} \<in> Fs\<^sub>2 // {\<cong>}")
 prefer 2 apply(erule quotientI)
apply (simp add:insert_absorb quotient_def)
done


lemma is_iso_Cons:
 "\<lbrakk> distinct (F\<^sub>1#Fs\<^sub>1'); distinct Fs\<^sub>2;
    inj_on (%xs.{xs}//{\<cong>}) (set(F\<^sub>1#Fs\<^sub>1')); inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>2) \<rbrakk>
  \<Longrightarrow>
 is_pr_iso \<phi> (F\<^sub>1#Fs\<^sub>1') Fs\<^sub>2 =
 (\<exists>F\<^sub>2 \<in> set Fs\<^sub>2. length F\<^sub>1 = length F\<^sub>2 \<and> is_pr_iso \<phi> Fs\<^sub>1' (remove1 F\<^sub>2 Fs\<^sub>2)
    \<and> (\<exists>n. map \<phi> F\<^sub>1 = rotate n F\<^sub>2)
    \<and> inj_on \<phi> (set F\<^sub>1 \<union> (\<Union>F\<in>set Fs\<^sub>1'. set F)))"
apply(simp add:is_pr_iso_def)
apply(subst is_pr_Iso_rec[where ?F\<^sub>1.0 = F\<^sub>1])
apply(simp_all)
done


subsection{* Isomorphism tests *}

lemma map_upd_submap:
  "x \<notin> dom m \<Longrightarrow> (m(x \<mapsto> y) \<subseteq>\<^sub>m m') = (m' x = Some y \<and> m \<subseteq>\<^sub>m m')"
apply(simp add:map_le_def dom_def)
apply(rule iffI)
 apply(rule conjI) apply (blast intro:sym)
 apply clarify
 apply(case_tac "a=x")
  apply auto
done

lemma map_of_zip_submap: "\<lbrakk> length xs = length ys; distinct xs \<rbrakk> \<Longrightarrow>
 (map_of (zip xs ys) \<subseteq>\<^sub>m Some \<circ> f) = (map f xs = ys)"
apply(induct rule: list_induct2)
 apply(simp)
apply (clarsimp simp: map_upd_submap simp del:o_apply fun_upd_apply)
apply simp
done

primrec pr_iso_test0 :: "('a ~=> 'b) \<Rightarrow> 'a fgraph \<Rightarrow> 'b fgraph \<Rightarrow> bool" where
  "pr_iso_test0 m [] Fs\<^sub>2 = (Fs\<^sub>2 = [])"
| "pr_iso_test0 m (F\<^sub>1#Fs\<^sub>1) Fs\<^sub>2 =
   (\<exists>F\<^sub>2 \<in> set Fs\<^sub>2. length F\<^sub>1 = length F\<^sub>2 \<and>
      (\<exists>n. let m' = map_of(zip F\<^sub>1 (rotate n F\<^sub>2)) in
          if m \<subseteq>\<^sub>m m ++ m' \<and> inj_on (m++m') (dom(m++m'))
          then pr_iso_test0 (m ++ m') Fs\<^sub>1 (remove1 F\<^sub>2 Fs\<^sub>2) else False))"

lemma map_compatI: "\<lbrakk> f \<subseteq>\<^sub>m Some o h; g \<subseteq>\<^sub>m Some o h \<rbrakk> \<Longrightarrow> f \<subseteq>\<^sub>m f++g"
by (fastforce simp add: map_le_def map_add_def dom_def split:option.splits)

lemma inj_on_map_addI1:
 "\<lbrakk> inj_on m A; m \<subseteq>\<^sub>m m++m'; A \<subseteq> dom m \<rbrakk> \<Longrightarrow> inj_on (m++m') A"
apply (clarsimp simp add: inj_on_def map_add_def map_le_def dom_def
                split:option.splits)
apply(rule conjI)
 apply fastforce
apply auto
 apply fastforce
apply (rename_tac x a y)
apply(subgoal_tac "m x = Some a")
 prefer 2 apply (fastforce)
apply(subgoal_tac "m y = Some a")
 prefer 2 apply (fastforce)
apply(subgoal_tac "m x = m y")
 prefer 2 apply simp
apply (blast)
done

lemma map_image_eq: "\<lbrakk> A \<subseteq> dom m; m \<subseteq>\<^sub>m m' \<rbrakk> \<Longrightarrow> m ` A = m' ` A"
by(force simp:map_le_def dom_def split:option.splits)

lemma inj_on_map_add_Un:
 "\<lbrakk> inj_on m (dom m); inj_on m' (dom m'); m \<subseteq>\<^sub>m Some o f; m' \<subseteq>\<^sub>m Some o f;
    inj_on f (dom m' \<union> dom m); A = dom m'; B = dom m \<rbrakk>
  \<Longrightarrow> inj_on (m ++ m') (A \<union> B)"
apply(simp add:inj_on_Un)
apply(rule conjI)
 apply(fastforce intro!: inj_on_map_addI1 map_compatI)
apply(clarify)
apply(subgoal_tac "m ++ m' \<subseteq>\<^sub>m Some \<circ> f")
 prefer 2 apply(fast intro:map_add_le_mapI map_compatI)
apply(subgoal_tac "dom m' - dom m \<subseteq> dom(m++m')")
 prefer 2 apply(fastforce)
apply(insert map_image_eq[of "dom m' - dom m" "m++m'" "Some o f"])
apply(subgoal_tac "dom m - dom m' \<subseteq> dom(m++m')")
 prefer 2 apply(fastforce)
apply(insert map_image_eq[of "dom m - dom m'" "m++m'" "Some o f"])
apply (clarsimp simp add: image_comp [symmetric])
apply blast
done

lemma map_of_zip_eq_SomeD: "length xs = length ys \<Longrightarrow>
  map_of (zip xs ys) x = Some y \<Longrightarrow> y \<in> set ys"
apply(induct rule:list_induct2)
 apply simp
apply (auto split:if_splits)
done

lemma inj_on_map_of_zip:
  "\<lbrakk> length xs = length ys; distinct ys \<rbrakk>
   \<Longrightarrow> inj_on (map_of (zip xs ys)) (set xs)"
apply(induct rule:list_induct2)
 apply simp
apply clarsimp
apply(rule conjI)
 apply(erule inj_on_fun_updI)
 apply(simp add:image_def)
 apply clarsimp
 apply(drule (1) map_of_zip_eq_SomeD[OF _ sym])
 apply fast
apply(clarsimp simp add:image_def)
apply(drule (1) map_of_zip_eq_SomeD[OF _ sym])
apply fast
done

lemma pr_iso_test0_correct: "\<And>m Fs\<^sub>2.
 \<lbrakk> \<forall>F\<in>set Fs\<^sub>1. distinct F; \<forall>F\<in>set Fs\<^sub>2. distinct F;
   distinct Fs\<^sub>1; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>1);
   distinct Fs\<^sub>2; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>2); inj_on m (dom m) \<rbrakk> \<Longrightarrow>
       pr_iso_test0 m Fs\<^sub>1 Fs\<^sub>2 =
       (\<exists>\<phi>. is_pr_iso \<phi> Fs\<^sub>1 Fs\<^sub>2 \<and> m \<subseteq>\<^sub>m Some o \<phi> \<and>
            inj_on \<phi> (dom m \<union> (\<Union>F\<in>set Fs\<^sub>1. set F)))"
apply(induct Fs\<^sub>1)
 apply(simp add:inj_on_def dom_def)
 apply(rule iffI)
  apply (simp add:is_pr_iso_def is_pr_Iso_def is_pr_Hom_def)
  apply(rule_tac x = "the o m" in exI)
  apply (fastforce simp: map_le_def)
 apply (clarsimp simp:is_pr_iso_def is_pr_Iso_def is_pr_Hom_def)
apply(rename_tac F\<^sub>1 Fs\<^sub>1' m Fs\<^sub>2)
apply(clarsimp simp:Let_def Ball_def)
apply(simp add: is_iso_Cons)
apply(rule iffI)

apply clarify
apply(clarsimp simp add:map_of_zip_submap inj_on_diff)
apply(rule_tac x = \<phi> in exI)
apply(rule conjI)
 apply(rule_tac x = F\<^sub>2 in bexI)
  prefer 2 apply assumption
 apply(frule map_add_le_mapE)
 apply(simp add:map_of_zip_submap is_pr_iso_def is_pr_Iso_def)
 apply(rule conjI)
  apply blast
 apply(erule subset_inj_on)
 apply blast
 apply(rule conjI)
  apply(blast intro: map_le_trans)
 apply(erule subset_inj_on)
 apply blast

apply(clarsimp simp: inj_on_diff)
apply(rule_tac x = F\<^sub>2 in bexI)
 prefer 2 apply assumption
apply simp
apply(rule_tac x = n in exI)
apply(rule conjI)
apply clarsimp
apply(rule_tac x = \<phi> in exI)
apply simp
apply(rule conjI)
 apply(fastforce intro!:map_add_le_mapI simp:map_of_zip_submap)
apply(simp add:Un_ac)
apply(rule context_conjI)
apply(simp add:map_of_zip_submap[symmetric])
apply(erule (1) map_compatI)
apply(simp add:map_of_zip_submap[symmetric])
apply(erule inj_on_map_add_Un)
     apply(simp add:inj_on_map_of_zip)
    apply assumption
   apply assumption
  apply simp
  apply(erule subset_inj_on)
  apply fast
 apply simp
apply(rule refl)
done

corollary pr_iso_test0_corr:
 "\<lbrakk> \<forall>F\<in>set Fs\<^sub>1. distinct F; \<forall>F\<in>set Fs\<^sub>2. distinct F;
   distinct Fs\<^sub>1; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>1);
   distinct Fs\<^sub>2; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>2) \<rbrakk> \<Longrightarrow>
       pr_iso_test0 empty Fs\<^sub>1 Fs\<^sub>2 = (\<exists>\<phi>. is_pr_iso \<phi> Fs\<^sub>1 Fs\<^sub>2)"
apply(subst pr_iso_test0_correct)
 apply assumption+
 apply simp
apply (simp add:is_pr_iso_def is_pr_Iso_def)
done

text{* Now we bound the number of rotations needed. We have to exclude
the empty face @{term"[]"} to be able to restrict the search to
@{prop"n < length xs"} (which would otherwise be vacuous). *}

primrec pr_iso_test1 :: "('a ~=> 'b) \<Rightarrow> 'a fgraph \<Rightarrow> 'b fgraph \<Rightarrow> bool" where
  "pr_iso_test1 m [] Fs\<^sub>2 = (Fs\<^sub>2 = [])"
| "pr_iso_test1 m (F\<^sub>1#Fs\<^sub>1) Fs\<^sub>2 =
   (\<exists>F\<^sub>2 \<in> set Fs\<^sub>2. length F\<^sub>1 = length F\<^sub>2 \<and>
      (\<exists>n < length F\<^sub>2. let m' = map_of(zip F\<^sub>1 (rotate n F\<^sub>2)) in
          if  m \<subseteq>\<^sub>m m ++ m' \<and> inj_on (m++m') (dom(m++m'))
          then pr_iso_test1 (m ++ m') Fs\<^sub>1 (remove1 F\<^sub>2 Fs\<^sub>2) else False))"

lemma test0_conv_test1:
 "!!m Fs\<^sub>2. [] \<notin> set Fs\<^sub>2 \<Longrightarrow> pr_iso_test1 m Fs\<^sub>1 Fs\<^sub>2 = pr_iso_test0 m Fs\<^sub>1 Fs\<^sub>2"
apply(induct Fs\<^sub>1)
 apply simp
apply simp
apply(rule iffI)
 apply blast
apply (clarsimp simp:Let_def)
apply(rule_tac x = F\<^sub>2 in bexI)
 prefer 2 apply assumption
apply simp
apply(subgoal_tac "F\<^sub>2 \<noteq> []")
 prefer 2 apply blast
apply(rule_tac x = "n mod length F\<^sub>2" in exI)
apply(simp add:rotate_conv_mod[symmetric])
done

text{* Thus correctness carries over to @{text pr_iso_test1}: *}

corollary pr_iso_test1_corr:
 "\<lbrakk> \<forall>F\<in>set Fs\<^sub>1. distinct F; \<forall>F\<in>set Fs\<^sub>2. distinct F; [] \<notin> set Fs\<^sub>2;
   distinct Fs\<^sub>1; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>1);
   distinct Fs\<^sub>2; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>2) \<rbrakk> \<Longrightarrow>
       pr_iso_test1 empty Fs\<^sub>1 Fs\<^sub>2 = (\<exists>\<phi>. is_pr_iso \<phi> Fs\<^sub>1 Fs\<^sub>2)"
by(simp add: test0_conv_test1 pr_iso_test0_corr)

subsubsection{* Implementing maps by lists *}

text{* The representation are lists of pairs with no repetition in the
first or second component. *}

definition oneone :: "('a * 'b)list \<Rightarrow> bool" where
"oneone xys  \<equiv>  distinct(map fst xys) \<and> distinct(map snd xys)"
declare oneone_def[simp]

type_synonym
  ('a,'b)tester = "('a * 'b)list \<Rightarrow> ('a * 'b)list \<Rightarrow> bool"
type_synonym
  ('a,'b)merger = "('a * 'b)list \<Rightarrow> ('a * 'b)list \<Rightarrow> ('a * 'b)list"

primrec pr_iso_test2 :: "('a,'b)tester \<Rightarrow> ('a,'b)merger \<Rightarrow>
                ('a * 'b)list \<Rightarrow> 'a fgraph \<Rightarrow> 'b fgraph \<Rightarrow> bool" where
  "pr_iso_test2 tst mrg I [] Fs\<^sub>2 = (Fs\<^sub>2 = [])"
| "pr_iso_test2 tst mrg I (F\<^sub>1#Fs\<^sub>1) Fs\<^sub>2 =
   (\<exists>F\<^sub>2 \<in> set Fs\<^sub>2. length F\<^sub>1 = length F\<^sub>2 \<and>
      (\<exists>n < length F\<^sub>2. let I' = zip F\<^sub>1 (rotate n F\<^sub>2) in
          if  tst I' I
          then pr_iso_test2 tst mrg (mrg I' I) Fs\<^sub>1 (remove1 F\<^sub>2 Fs\<^sub>2) else False))"

lemma notin_range_map_of:
 "y \<notin> snd ` set xys \<Longrightarrow> Some y \<notin> range(map_of xys)"
apply(induct xys)
 apply (simp add:image_def)
apply(clarsimp split:if_splits)
done


lemma inj_on_map_upd:
  "\<lbrakk> inj_on m (dom m); Some y \<notin> range m \<rbrakk> \<Longrightarrow> inj_on (m(x\<mapsto>y)) (dom m)"
apply(simp add:inj_on_def dom_def image_def)
apply (blast intro:sym)
done

lemma [simp]:
 "distinct(map snd xys) \<Longrightarrow> inj_on (map_of xys) (dom(map_of xys))"
apply(induct xys)
 apply simp
apply (simp add: notin_range_map_of inj_on_map_upd)
apply(clarsimp simp add:image_def)
apply(drule map_of_is_SomeD)
apply fastforce
done

lemma lem: "Ball (set xs) P \<Longrightarrow> Ball (set (remove1 x xs)) P = True"
by(induct xs) simp_all

lemma pr_iso_test2_conv_1:
  "!!I Fs\<^sub>2.
  \<lbrakk> \<forall>I I'. oneone I \<longrightarrow> oneone I' \<longrightarrow>
           tst I' I = (let m = map_of I; m' = map_of I'
                       in m \<subseteq>\<^sub>m m ++ m' \<and> inj_on (m++m') (dom(m++m')));
   \<forall>I I'. oneone I \<longrightarrow> oneone I' \<longrightarrow> tst I' I
          \<longrightarrow> map_of(mrg I' I) = map_of I ++ map_of I';
   \<forall>I I'. oneone I & oneone I' \<longrightarrow> tst I' I \<longrightarrow> oneone (mrg I' I);
   oneone I;
   \<forall>F \<in> set Fs\<^sub>1. distinct F; \<forall>F \<in> set Fs\<^sub>2. distinct F \<rbrakk> \<Longrightarrow>
  pr_iso_test2 tst mrg I Fs\<^sub>1 Fs\<^sub>2 = pr_iso_test1 (map_of I) Fs\<^sub>1 Fs\<^sub>2"
apply(induct Fs\<^sub>1)
 apply simp
apply(simp add:Let_def lem inj_on_map_of_zip del: mod_less cong: conj_cong)
done

text{* A simple implementation *}

definition compat :: "('a,'b)tester" where
 "compat I I' ==
  \<forall>(x,y) \<in> set I. \<forall>(x',y') \<in> set I'. (x = x') = (y = y')"

lemma image_map_upd:
  "x \<notin> dom m \<Longrightarrow> m(x\<mapsto>y) ` A = m ` (A-{x}) \<union> (if x \<in> A then {Some y} else {})"
by(auto simp:image_def dom_def)


lemma image_map_of_conv_Image:
 "!!A. \<lbrakk> distinct(map fst xys) \<rbrakk>
 \<Longrightarrow> map_of xys ` A = Some ` (set xys `` A) \<union> (if A \<subseteq> fst ` set xys then {} else {None})"
apply (induct xys)
 apply (simp add:image_def Image_def Collect_conv_if)
apply (simp add:image_map_upd dom_map_of_conv_image_fst)
apply(erule thin_rl)
apply (clarsimp simp:image_def Image_def)
apply((rule conjI, clarify)+, fastforce)
apply fastforce
apply(clarify)
apply((rule conjI, clarify)+, fastforce)
apply fastforce
apply fastforce
apply fastforce
done


lemma [simp]: "m++m' ` (dom m' - A) = m' ` (dom m' - A)"
apply(clarsimp simp add:map_add_def image_def dom_def inj_on_def split:option.splits)
apply auto
apply (blast intro:sym)
apply (blast intro:sym)
apply (rule_tac x = xa in bexI)
prefer 2 apply blast
apply simp
done

declare Diff_subset [iff]

lemma compat_correct:
 "\<lbrakk> oneone I; oneone I' \<rbrakk> \<Longrightarrow>
  compat I' I = (let m = map_of I; m' = map_of I'
                 in m \<subseteq>\<^sub>m m ++ m' \<and> inj_on (m++m') (dom(m++m')))"
apply(simp add: compat_def Let_def map_le_iff_map_add_commute)
apply(rule iffI)
 apply(rule context_conjI)
  apply(rule ext)
  apply (fastforce simp add:map_add_def split:option.split)
 apply(simp add:inj_on_Un)
 apply(drule sym)
 apply simp
 apply(simp add: dom_map_of_conv_image_fst image_map_of_conv_Image)
 apply(simp add: image_def Image_def)
 apply fastforce
apply clarsimp
apply(rename_tac a b aa ba)
apply(rule iffI)
 apply (clarsimp simp: fun_eq_iff)
 apply(erule_tac x = aa in allE)
 apply (simp add:map_add_def)
apply (clarsimp simp:dom_map_of_conv_image_fst)
apply(simp (no_asm_use) add:inj_on_def)
apply(drule_tac x = a in bspec)
 apply force
apply(drule_tac x = aa in bspec)
 apply force
apply(erule mp)
apply simp
apply(drule sym)
apply simp
done

corollary compat_corr:
 "\<forall>I I'. oneone I \<longrightarrow> oneone I' \<longrightarrow>
         compat I' I = (let m = map_of I; m' = map_of I'
                      in m \<subseteq>\<^sub>m m ++ m' \<and> inj_on (m++m') (dom(m++m')))"
by(simp add: compat_correct)

definition merge0 :: "('a,'b)merger" where
"merge0 I' I  \<equiv>  [xy \<leftarrow> I'. fst xy \<notin> fst ` set I] @ I"


lemma help1:
"distinct(map fst xys) \<Longrightarrow> map_of (filter P xys) =
 map_of xys |` {x. \<exists>y. (x,y) \<in> set xys \<and> P(x,y)}"
apply(induct xys)
 apply simp
apply(rule ext)
apply (simp add:restrict_map_def)
apply force
done

lemma merge0_correct:
  "\<forall>I I'. oneone I \<longrightarrow> oneone I' \<longrightarrow> compat I' I
  \<longrightarrow> map_of(merge0 I' I) = map_of I ++ map_of I'"
apply(simp add:compat_def merge0_def help1 fun_eq_iff map_add_def restrict_map_def split:option.split)
apply fastforce
done

lemma merge0_inv:
  "\<forall>I I'. oneone I \<and> oneone I' \<longrightarrow> compat I' I \<longrightarrow> oneone (merge0 I' I)"
apply(auto simp add:merge0_def distinct_map compat_def split_def)
apply(blast intro:subset_inj_on)+
done

corollary pr_iso_test2_corr:
 "\<lbrakk> \<forall>F\<in>set Fs\<^sub>1. distinct F; \<forall>F\<in>set Fs\<^sub>2. distinct F; [] \<notin> set Fs\<^sub>2;
   distinct Fs\<^sub>1; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>1);
   distinct Fs\<^sub>2; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>2) \<rbrakk> \<Longrightarrow>
       pr_iso_test2 compat merge0 [] Fs\<^sub>1 Fs\<^sub>2 = (\<exists>\<phi>. is_pr_iso \<phi> Fs\<^sub>1 Fs\<^sub>2)"
by(simp add: pr_iso_test2_conv_1[OF compat_corr merge0_correct merge0_inv]
             pr_iso_test1_corr)

text{* Implementing merge as a recursive function: *}

primrec merge :: "('a,'b)merger" where
  "merge [] I = I"
| "merge (xy#xys) I = (let (x,y) = xy in
    if \<forall> (x',y') \<in> set I. x \<noteq> x' then xy # merge xys I else merge xys I)"

lemma merge_conv_merge0: "merge I' I = merge0 I' I"
apply(induct I')
 apply(simp add:merge0_def)
apply(force simp add:Let_def list_all_iff merge0_def)
done


primrec pr_iso_test_rec :: "('a * 'b)list \<Rightarrow> 'a fgraph \<Rightarrow> 'b fgraph \<Rightarrow> bool" where
  "pr_iso_test_rec I [] Fs\<^sub>2 = (Fs\<^sub>2 = [])"
| "pr_iso_test_rec I (F\<^sub>1#Fs\<^sub>1) Fs\<^sub>2 =
   (\<exists> F\<^sub>2 \<in> set Fs\<^sub>2. length F\<^sub>1 = length F\<^sub>2 \<and>
      (\<exists>n < length F\<^sub>2. let I' = zip F\<^sub>1 (rotate n F\<^sub>2) in
          compat I' I \<and> pr_iso_test_rec (merge I' I) Fs\<^sub>1 (remove1 F\<^sub>2 Fs\<^sub>2)))"

lemma pr_iso_test_rec_conv_2:
  "!!I Fs\<^sub>2. pr_iso_test_rec I Fs\<^sub>1 Fs\<^sub>2 = pr_iso_test2 compat merge0 I Fs\<^sub>1 Fs\<^sub>2"
apply(induct Fs\<^sub>1)
 apply simp
apply(auto simp: merge_conv_merge0 list_ex_iff Bex_def Let_def)
done

corollary pr_iso_test_rec_corr:
 "\<lbrakk> \<forall>F\<in>set Fs\<^sub>1. distinct F; \<forall>F\<in>set Fs\<^sub>2. distinct F; [] \<notin> set Fs\<^sub>2;
   distinct Fs\<^sub>1; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>1);
   distinct Fs\<^sub>2; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>2) \<rbrakk> \<Longrightarrow>
       pr_iso_test_rec [] Fs\<^sub>1 Fs\<^sub>2 = (\<exists>\<phi>. is_pr_iso \<phi> Fs\<^sub>1 Fs\<^sub>2)"
by(simp add: pr_iso_test_rec_conv_2 pr_iso_test2_corr)

definition pr_iso_test :: "'a fgraph \<Rightarrow> 'b fgraph \<Rightarrow> bool" where
"pr_iso_test Fs\<^sub>1 Fs\<^sub>2 = pr_iso_test_rec [] Fs\<^sub>1 Fs\<^sub>2"

corollary pr_iso_test_correct:
 "\<lbrakk> \<forall>F\<in>set Fs\<^sub>1. distinct F; \<forall>F\<in>set Fs\<^sub>2. distinct F; [] \<notin> set Fs\<^sub>2;
   distinct Fs\<^sub>1; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>1);
   distinct Fs\<^sub>2; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>2) \<rbrakk> \<Longrightarrow>
  pr_iso_test Fs\<^sub>1 Fs\<^sub>2 = (\<exists>\<phi>. is_pr_iso \<phi> Fs\<^sub>1 Fs\<^sub>2)"
apply(simp add:pr_iso_test_def pr_iso_test_rec_corr)
done

subsubsection{* `Improper' Isomorphisms *}

definition is_Iso :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Fgraph \<Rightarrow> 'b Fgraph \<Rightarrow> bool" where
"is_Iso \<phi> Fs\<^sub>1 Fs\<^sub>2 \<equiv> is_pr_Iso \<phi> Fs\<^sub>1 Fs\<^sub>2 \<or> is_pr_Iso \<phi> Fs\<^sub>1 (rev ` Fs\<^sub>2)"

definition is_iso :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fgraph \<Rightarrow> 'b fgraph \<Rightarrow> bool" where
"is_iso \<phi> Fs\<^sub>1 Fs\<^sub>2 \<equiv> is_Iso \<phi> (set Fs\<^sub>1) (set Fs\<^sub>2)"

definition iso_fgraph :: "'a fgraph \<Rightarrow> 'a fgraph \<Rightarrow> bool" (infix "\<simeq>" 60) where
"g\<^sub>1 \<simeq> g\<^sub>2  \<equiv>  \<exists>\<phi>. is_iso \<phi> g\<^sub>1 g\<^sub>2"


lemma iso_fgraph_trans: assumes "f \<simeq> (g::'a fgraph)" and "g \<simeq> h" shows "f \<simeq> h"
proof-
  { fix \<phi> \<phi>' assume "is_pr_Hom \<phi> (set f) (set g)" "inj_on \<phi> (\<Union>F\<in>set f. set F)"
    "is_pr_Hom \<phi>' (set g) (set h)" "inj_on \<phi>' (\<Union>F\<in>set g. set F)"
    hence "is_pr_Hom (\<phi>' \<circ> \<phi>) (set f) (set h) \<and>
          inj_on (\<phi>' \<circ> \<phi>) (\<Union>F\<in>set f. set F)"
      by(simp add: is_pr_Hom_trans comp_inj_on pr_Hom_pres_nodes)
  } moreover
  { fix \<phi> \<phi>' assume "is_pr_Hom \<phi> (set f) (set g)" "inj_on \<phi> (\<Union>F\<in>set f. set F)"
    "is_pr_Hom \<phi>' (set g) (rev ` set h)" "inj_on \<phi>' (\<Union>F\<in>set g. set F)"
    hence "is_pr_Hom (\<phi>' \<circ> \<phi>) (set f) (rev ` set h) \<and>
          inj_on (\<phi>' \<circ> \<phi>) (\<Union>F\<in>set f. set F)"
      by(simp add: is_pr_Hom_trans comp_inj_on pr_Hom_pres_nodes)
  } moreover
  { fix \<phi> \<phi>' assume "is_pr_Hom \<phi> (set f) (rev ` set g)" "inj_on \<phi> (\<Union>F\<in>set f. set F)"
    "is_pr_Hom \<phi>' (set g) (set h)" "inj_on \<phi>' (\<Union>F\<in>set g. set F)"
    with this(3)[THEN is_pr_Hom_rev]
    have "is_pr_Hom (\<phi>' \<circ> \<phi>) (set f) (rev ` set h) \<and>
          inj_on (\<phi>' \<circ> \<phi>) (\<Union>F\<in>set f. set F)"
      by(simp add: is_pr_Hom_trans comp_inj_on pr_Hom_pres_nodes)
  } moreover
  { fix \<phi> \<phi>' assume "is_pr_Hom \<phi> (set f) (rev ` set g)" "inj_on \<phi> (\<Union>F\<in>set f. set F)"
    "is_pr_Hom \<phi>' (set g) (rev ` set h)" "inj_on \<phi>' (\<Union>F\<in>set g. set F)"
    with this(3)[THEN is_pr_Hom_rev]
    have "is_pr_Hom (\<phi>' \<circ> \<phi>) (set f) (set h) \<and>
          inj_on (\<phi>' \<circ> \<phi>) (\<Union>F\<in>set f. set F)"
      by(simp add: is_pr_Hom_trans comp_inj_on pr_Hom_pres_nodes)
  } ultimately show ?thesis using assms
    by(simp add: iso_fgraph_def is_iso_def is_Iso_def is_pr_Iso_def) blast
qed



definition iso_test :: "'a fgraph \<Rightarrow> 'b fgraph \<Rightarrow> bool" where
"iso_test g\<^sub>1 g\<^sub>2 \<longleftrightarrow> pr_iso_test g\<^sub>1 g\<^sub>2 \<or> pr_iso_test g\<^sub>1 (map rev g\<^sub>2)"

theorem iso_correct:
 "\<lbrakk> \<forall>F\<in>set Fs\<^sub>1. distinct F; \<forall>F\<in>set Fs\<^sub>2. distinct F; [] \<notin> set Fs\<^sub>2;
   distinct Fs\<^sub>1; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>1);
   distinct Fs\<^sub>2; inj_on (%xs.{xs}//{\<cong>}) (set Fs\<^sub>2) \<rbrakk> \<Longrightarrow>
  iso_test Fs\<^sub>1 Fs\<^sub>2 = (Fs\<^sub>1 \<simeq> Fs\<^sub>2)"
apply(simp add:iso_test_def pr_iso_test_correct iso_fgraph_def)
apply(subst pr_iso_test_correct)
       apply simp
      apply simp
     apply (simp add:image_def)
    apply simp
   apply simp
  apply (simp add:distinct_map)
 apply (simp add:inj_on_image_iff)
apply(simp add:is_iso_def is_Iso_def is_pr_iso_def)
apply blast
done

lemma iso_fgraph_refl[iff]: "g \<simeq> g"
apply(simp add: iso_fgraph_def)
apply(rule_tac x = "id" in exI)
apply(simp add: is_iso_def is_Iso_def is_pr_Iso_def is_pr_Hom_def id_def)
done


subsection{* Elementhood and containment modulo *}

interpretation qle_gr: quasi_order "op \<simeq>"
proof qed (auto intro:iso_fgraph_trans)

abbreviation qle_gr_in :: "'a fgraph \<Rightarrow> 'a fgraph set \<Rightarrow> bool"  (infix "\<in>\<^sub>\<simeq>" 60)
where "x \<in>\<^sub>\<simeq> M \<equiv> qle_gr.in_qle x M"
abbreviation qle_gr_sub :: "'a fgraph set \<Rightarrow> 'a fgraph set \<Rightarrow> bool"  (infix "\<subseteq>\<^sub>\<simeq>" 60)
where "x \<subseteq>\<^sub>\<simeq> M \<equiv> qle_gr.subseteq_qle x M"
abbreviation qle_gr_eq :: "'a fgraph set \<Rightarrow> 'a fgraph set \<Rightarrow> bool"  (infix "=\<^sub>\<simeq>" 60)
where "x =\<^sub>\<simeq> M \<equiv> qle_gr.seteq_qle x M"

end