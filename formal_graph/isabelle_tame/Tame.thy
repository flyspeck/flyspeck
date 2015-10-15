(*  Author:     Gertrud Bauer, Tobias Nipkow
The definitions should be identical to the ones in the file
text_formalization/tame/tame_defs.hl
by Thomas Hales. Modulo a few inessential rearrangements.
*)

header{* Tameness *}

theory Tame
imports Graph ListSum
begin


subsection {* Constants \label{sec:TameConstants}*}

definition squanderTarget :: "nat" where
 "squanderTarget \<equiv> 15410" 

definition excessTCount :: "nat" (*<*) ("\<a>")(*>*)where

 "\<a> \<equiv> 6295"

definition squanderVertex :: "nat \<Rightarrow> nat \<Rightarrow> nat" (*<*)("\<b>")(*>*)where

 "\<b> p q \<equiv> if p = 0 \<and> q = 3 then 6177 
     else if p = 0 \<and> q = 4 then  9696
     else if p = 1 \<and> q = 2 then  6557 
     else if p = 1 \<and> q = 3 then  6176 
     else if p = 2 \<and> q = 1 then  7967 
     else if p = 2 \<and> q = 2 then  4116 
     else if p = 2 \<and> q = 3 then 12846 
     else if p = 3 \<and> q = 1 then  3106 
     else if p = 3 \<and> q = 2 then  8165 
     else if p = 4 \<and> q = 0 then  3466 
     else if p = 4 \<and> q = 1 then  3655 
     else if p = 5 \<and> q = 0 then   395 
     else if p = 5 \<and> q = 1 then 11354 
     else if p = 6 \<and> q = 0 then  6854 
     else if p = 7 \<and> q = 0 then 14493 
     else squanderTarget"

definition squanderFace :: "nat \<Rightarrow> nat" (*<*)("\<d>")(*>*)where

 "\<d> n \<equiv> if n = 3 then 0
     else if n = 4 then 2058
     else if n = 5 then 4819
     else if n = 6 then 7120
     else squanderTarget" 

text_raw{* 
\index{@{text "\<a>"}}
\index{@{text "\<b>"}}
\index{@{text "\<d>"}}
*}

subsection{* Separated sets of vertices \label{sec:TameSeparated}*}


text {* A set of vertices $V$ is {\em separated},
\index{separated}
\index{@{text "separated"}}
iff the following conditions hold:
 *}

text {*  2. No two vertices in V are adjacent: *}

definition separated\<^sub>2 :: "graph \<Rightarrow> vertex set \<Rightarrow> bool" where
 "separated\<^sub>2 g V \<equiv> \<forall>v \<in> V. \<forall>f \<in> set (facesAt g v). f\<bullet>v \<notin> V"

text {*  3. No two vertices lie on a common quadrilateral: *}

definition separated\<^sub>3 :: "graph \<Rightarrow> vertex set \<Rightarrow> bool" where
 "separated\<^sub>3 g V \<equiv> 
     \<forall>v \<in> V. \<forall>f \<in> set (facesAt g v). |vertices f|\<le>4 \<longrightarrow> \<V> f \<inter> V = {v}"

text {*  A set of vertices  is  called {\em separated},
\index{separated} \index{@{text "separated"}}
iff no two vertices are adjacent or lie on a common quadrilateral: *}

definition separated :: "graph \<Rightarrow> vertex set \<Rightarrow> bool" where
 "separated g V \<equiv> separated\<^sub>2 g V \<and> separated\<^sub>3 g V"

subsection{* Admissible weight assignments\label{sec:TameAdmissible} *}

text {*  
A weight assignment @{text "w :: face \<Rightarrow> nat"} 
assigns a natural number to every face.

\index{@{text "admissible"}}
\index{admissible weight assignment}

We formalize the admissibility requirements as follows:
 *}

definition admissible\<^sub>1 :: "(face \<Rightarrow> nat) \<Rightarrow> graph \<Rightarrow> bool" where  
 "admissible\<^sub>1 w g \<equiv> \<forall>f \<in> \<F> g. \<d> |vertices f| \<le> w f"

definition admissible\<^sub>2 :: "(face \<Rightarrow> nat) \<Rightarrow> graph \<Rightarrow> bool" where  
 "admissible\<^sub>2 w g \<equiv> 
  \<forall>v \<in> \<V> g. except g v = 0 \<longrightarrow> \<b> (tri g v) (quad g v) \<le> (\<Sum>\<^bsub>f\<in>facesAt g v\<^esub> w f)"

definition admissible\<^sub>3 :: "(face \<Rightarrow> nat) \<Rightarrow> graph \<Rightarrow> bool" where  
 "admissible\<^sub>3 w g  \<equiv>
  \<forall>v \<in> \<V> g. vertextype g v = (5,0,1) \<longrightarrow> (\<Sum>\<^bsub>f\<in>filter triangle (facesAt g v)\<^esub> w(f)) >= \<a>"


text {* Finally we define admissibility of weights functions. *}


definition admissible :: "(face \<Rightarrow> nat) \<Rightarrow> graph \<Rightarrow> bool" where  
 "admissible w g \<equiv> admissible\<^sub>1 w g \<and> admissible\<^sub>2 w g \<and> admissible\<^sub>3 w g"
 
subsection{* Tameness \label{sec:TameDef} *}

definition tame9a :: "graph \<Rightarrow> bool" where
"tame9a g \<equiv> \<forall>f \<in> \<F> g. 3 \<le> |vertices f| \<and> |vertices f| \<le> 6"

definition tame10 :: "graph \<Rightarrow> bool" where
"tame10 g = (let n = countVertices g in 13 <= n & n <= 15)"

definition tame10ub :: "graph \<Rightarrow> bool" where
"tame10ub g = (countVertices g <= 15)"

definition tame11a :: "graph \<Rightarrow> bool" where
"tame11a g = (\<forall>v \<in> \<V> g. 3 <= degree g v)"

definition tame11b :: "graph \<Rightarrow> bool" where
"tame11b g = (\<forall>v \<in> \<V> g. degree g v \<le> (if except g v = 0 then 7 else 6))"

definition tame12o :: "graph \<Rightarrow> bool" where
"tame12o g =
 (\<forall>v \<in> \<V> g. except g v \<noteq> 0 \<and> degree g v = 6 \<longrightarrow> vertextype g v = (5,0,1))"
 
text {* 7. There exists an admissible weight assignment of total
weight less than the target: *}

definition tame13a :: "graph \<Rightarrow> bool" where
"tame13a g = (\<exists>w. admissible w g \<and> (\<Sum>\<^bsub>f \<in> faces g\<^esub> w f) < squanderTarget)"

text {* Finally we define the notion of tameness. *}

definition tame :: "graph \<Rightarrow> bool" where
"tame g \<equiv> tame9a g \<and> tame10 g \<and> tame11a g \<and> tame11b g \<and> tame12o g \<and> tame13a g"
(*<*)
end
(*>*)
