(*  Author:     Tobias Nipkow
*)

header {* Combining All Completeness Proofs *}

theory Completeness
imports ArchCompProps ArchComp
begin

definition Archive :: "vertex fgraph set" where
"Archive \<equiv>
 set(Tri @ Quad @ Pent @ Hex)"

theorem TameEnum_Archive:  "fgraph ` TameEnum \<subseteq>\<^isub>\<simeq> Archive"
using combine_evals[OF pre_iso_test3 same3]
      combine_evals[OF pre_iso_test4 same4]
      combine_evals[OF pre_iso_test5 same5]
      combine_evals[OF pre_iso_test6 same6]
by(fastsimp simp:TameEnum_def Archive_def image_def iso_subseteq_def
       iso_in_def eval_nat_numeral le_Suc_eq)


lemma TameEnum_comp:
assumes "Seed\<^bsub>p\<^esub> [next_plane\<^bsub>p\<^esub>]\<rightarrow>* g" and "final g" and "tame g"
shows "Seed\<^bsub>p\<^esub> [next_tame\<^bsub>p\<^esub>]\<rightarrow>* g"
proof -
  from assms have "Seed\<^bsub>p\<^esub> [next_tame0 p]\<rightarrow>* g" by(rule next_tame0_comp)
  with assms show "Seed\<^bsub>p\<^esub> [next_tame\<^bsub>p\<^esub>]\<rightarrow>* g" by(blast intro: next_tame_comp)
qed

(* final not necessary but slightly simpler because of lemmas *)
lemma tame5:
assumes g: "Seed\<^bsub>p\<^esub> [next_plane0\<^bsub>p\<^esub>]\<rightarrow>* g" and "final g" and "tame g"
shows "p \<le> 3"
proof -
  from `tame g` have bound: "\<forall>f \<in> \<F> g. |vertices f| \<le> 6"
    by (simp add: tame_def tame9a_def)
  show "p \<le> 3"
  proof (rule ccontr)
    assume 6: "\<not> p \<le> 3"
    obtain f where "f \<in> set (finals g) & |vertices f| = p+3"
      using max_face_ex[OF g] by auto
    also from `final g` have "set (finals g) = set (faces g)" by simp
    finally have "f \<in> \<F> g & 6 < |vertices f|" using 6 by arith
    with bound show False by auto
  qed
qed


theorem completeness:
assumes "g \<in> PlaneGraphs" and "tame g" shows "fgraph g \<in>\<^isub>\<simeq> Archive"
proof -
  from `g \<in> PlaneGraphs` obtain p where g1: "Seed\<^bsub>p\<^esub> [next_plane\<^bsub>p\<^esub>]\<rightarrow>* g"
    and "final g"
    by(auto simp:PlaneGraphs_def PlaneGraphsP_def)
  have "Seed\<^bsub>p\<^esub> [next_plane0\<^bsub>p\<^esub>]\<rightarrow>* g"
    by(rule RTranCl_subset2[OF g1])
      (blast intro:inv_mgp inv_Seed mgp_next_plane0_if_next_plane
	dest:RTranCl_inv[OF inv_inv_next_plane])
  with `tame g` `final g` have "p \<le> 3" by(blast intro:tame5)
  with g1 `tame g` `final g` show ?thesis using TameEnum_Archive
    by(simp add: iso_subseteq_def TameEnum_def TameEnumP_def)
      (blast intro: TameEnum_comp)
qed

end
