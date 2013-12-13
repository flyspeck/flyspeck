(*  Author:  Gertrud Bauer, Tobias Nipkow  *)

header {* Transitive Closure of Successor List Function *}

theory RTranCl
imports Main
begin

text{* The reflexive transitive closure of a relation induced by a
function of type @{typ"'a \<Rightarrow> 'a list"}. Instead of defining the closure
again it would have been simpler to take @{term"{(x,y) . y \<in> set(f x)}\<^sup>*"}. *}

abbreviation (input)
  in_set :: "'a => ('a => 'b list) => 'b => bool" ("_ [_]\<rightarrow> _" [55,0,55] 50) where
  "g [succs]\<rightarrow> g' == g' \<in> set (succs g)"

inductive_set
  RTranCl :: "('a \<Rightarrow> 'a list) \<Rightarrow> ('a * 'a) set"
  and in_RTranCl :: "'a \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> 'a \<Rightarrow> bool"
    ("_ [_]\<rightarrow>* _" [55,0,55] 50)
  for succs :: "'a \<Rightarrow> 'a list"
where
  "g [succs]\<rightarrow>* g' \<equiv> (g,g') \<in> RTranCl succs"
| refl: "g [succs]\<rightarrow>* g"
| succs: "g [succs]\<rightarrow> g' \<Longrightarrow> g' [succs]\<rightarrow>* g'' \<Longrightarrow> g [succs]\<rightarrow>* g''"

inductive_cases RTranCl_elim: "(h,h') : RTranCl succs"

lemma RTranCl_induct(*<*) [induct set: RTranCl, consumes 1, case_names refl succs] (*>*):
 "(h, h') \<in> RTranCl succs \<Longrightarrow> 
  P h \<Longrightarrow> 
  (\<And>g g'. g' \<in> set (succs g) \<Longrightarrow> P g \<Longrightarrow> P g') \<Longrightarrow> 
  P h'"
proof -
  assume s: "\<And>g g'. g' \<in> set (succs g) \<Longrightarrow> P g \<Longrightarrow> P g'"
  assume "(h, h') \<in> RTranCl succs" "P h"
  then show "P h'"
  proof (induct rule: RTranCl.induct)
    fix g assume "P g" then show "P g" . 
  next
    fix g g' g''
    assume IH: "P g' \<Longrightarrow> P g''"
    assume "g' \<in> set(succs g)" "P g"
    then have "P g'" by (rule s)
    then show "P g''" by (rule IH)
  qed
qed

definition invariant :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> bool" where
"invariant P succs \<equiv> \<forall>g g'. g' \<in> set(succs g) \<longrightarrow> P g \<longrightarrow> P g'"

lemma invariantE:
  "invariant P succs  \<Longrightarrow> g [succs]\<rightarrow> g' \<Longrightarrow> P g \<Longrightarrow> P g'"
by(simp add:invariant_def)

lemma inv_subset:
 "invariant P f \<Longrightarrow> (!!g. P g \<Longrightarrow> set(f' g) \<subseteq> set(f g)) \<Longrightarrow> invariant P f'"
by(auto simp:invariant_def)

lemma RTranCl_inv:
  "invariant P succs \<Longrightarrow> (g,g') \<in> RTranCl succs \<Longrightarrow> P g \<Longrightarrow> P g'"
by (erule RTranCl_induct)(auto simp:invariant_def)

lemma RTranCl_subset2:
assumes a: "(s,g) : RTranCl f"
shows "(!!g. (s,g) \<in> RTranCl f \<Longrightarrow> set(f g) \<subseteq> set(h g)) \<Longrightarrow> (s,g) : RTranCl h"
using a
proof (induct rule: RTranCl.induct)
  case refl show ?case by(rule RTranCl.intros)
next
  case succs thus ?case by(blast intro: RTranCl.intros)
qed

end
