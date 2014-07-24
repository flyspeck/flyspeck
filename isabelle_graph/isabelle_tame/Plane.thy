(*  Author:     Gertrud Bauer
*)

header{* Plane Graph Enumeration *}

theory Plane
imports Enumerator FaceDivision RTranCl
begin


definition maxGon :: "nat \<Rightarrow> nat" where
"maxGon p \<equiv> p+3"

declare maxGon_def [simp]


definition duplicateEdge :: "graph \<Rightarrow> face \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> bool" where
 "duplicateEdge g f a b \<equiv> 
  2 \<le> directedLength f a b \<and> 2 \<le> directedLength f b a \<and> b \<in> set (neighbors g a)"

primrec containsUnacceptableEdgeSnd :: 
      "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
 "containsUnacceptableEdgeSnd N v [] = False" |
 "containsUnacceptableEdgeSnd N v (w#ws) = 
     (case ws of [] \<Rightarrow> False
         | (w'#ws') \<Rightarrow> if v < w \<and> w < w' \<and> N w w' then True
                      else containsUnacceptableEdgeSnd N w ws)"

primrec containsUnacceptableEdge :: "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> bool" where
 "containsUnacceptableEdge N [] = False" |
 "containsUnacceptableEdge N (v#vs) =
     (case vs of [] \<Rightarrow> False
           | (w#ws) \<Rightarrow> if v < w \<and> N v w then True
                      else containsUnacceptableEdgeSnd N v vs)"

definition containsDuplicateEdge :: "graph \<Rightarrow> face \<Rightarrow> vertex \<Rightarrow> nat list \<Rightarrow> bool" where
 "containsDuplicateEdge g f v is \<equiv> 
     containsUnacceptableEdge (\<lambda>i j. duplicateEdge g f (f\<^bsup>i\<^esup>\<bullet>v) (f\<^bsup>j\<^esup>\<bullet>v)) is" 

definition containsDuplicateEdge' :: "graph \<Rightarrow> face \<Rightarrow> vertex \<Rightarrow> nat list \<Rightarrow> bool" where
 "containsDuplicateEdge' g f v is \<equiv> 
  2 \<le> |is| \<and> 
  ((\<exists>k < |is| - 2. let i0 = is!k; i1 = is!(k+1); i2 = is!(k+2) in
    (duplicateEdge g f (f\<^bsup>i1 \<^esup>\<bullet>v) (f\<^bsup>i2 \<^esup>\<bullet>v)) \<and> (i0 < i1) \<and> (i1 < i2))
  \<or> (let i0 = is!0; i1 = is!1 in
    (duplicateEdge g f (f\<^bsup>i0 \<^esup>\<bullet>v) (f\<^bsup>i1 \<^esup>\<bullet>v)) \<and> (i0 < i1)))" 


definition generatePolygon :: "nat \<Rightarrow> vertex \<Rightarrow> face \<Rightarrow> graph \<Rightarrow> graph list" where
 "generatePolygon n v f g \<equiv> 
     let enumeration = enumerator n |vertices f|;
     enumeration = [is \<leftarrow> enumeration. \<not> containsDuplicateEdge g f v is];
     vertexLists = [indexToVertexList f v is. is \<leftarrow> enumeration] in
     [subdivFace g f vs. vs \<leftarrow> vertexLists]"

definition next_plane0 :: "nat \<Rightarrow> graph \<Rightarrow> graph list" ("next'_plane0\<^bsub>_\<^esub>") where
 "next_plane0\<^bsub>p\<^esub> g \<equiv>
     if final g then [] 
     else \<Squnion>\<^bsub>f\<in>nonFinals g\<^esub> \<Squnion>\<^bsub>v\<in>vertices f\<^esub> \<Squnion>\<^bsub>i\<in>[3..<Suc(maxGon p)]\<^esub> generatePolygon i v f g"


definition Seed :: "nat \<Rightarrow> graph" ("Seed\<^bsub>_\<^esub>") where
  "Seed\<^bsub>p\<^esub> \<equiv> graph(maxGon p)"

lemma Seed_not_final[iff]: "\<not> final (Seed p)"
by(simp add:Seed_def graph_def finalGraph_def nonFinals_def)

definition PlaneGraphs0 :: "graph set" where 
"PlaneGraphs0 \<equiv> \<Union>p. {g. Seed\<^bsub>p\<^esub> [next_plane0\<^bsub>p\<^esub>]\<rightarrow>* g \<and> final g}"

end
