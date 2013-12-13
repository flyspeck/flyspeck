(*  Title:      Plane1.thy
    Author:     Gertrud Bauer, Tobias Nipkow

Fixing a single face and vertex in each refinement step.
*)

theory Plane1
imports Plane
begin

text{* This is an optimized definition of plane graphs and the one we
adopt as our point of reference. In every step only one fixed nonfinal
face (the smallest one) and one edge in that face are picked. *}


definition minimalFace :: "face list \<Rightarrow> face" where
 "minimalFace \<equiv> minimal (length \<circ> vertices)"

definition minimalVertex :: "graph \<Rightarrow> face \<Rightarrow> vertex" where
 "minimalVertex g f \<equiv> minimal (height g) (vertices f)" 

definition next_plane :: "nat \<Rightarrow> graph \<Rightarrow> graph list" ("next'_plane\<^bsub>_\<^esub>") where
 "next_plane\<^bsub>p\<^esub> g \<equiv>
     let fs = nonFinals g in
     if fs = [] then [] 
     else let f = minimalFace fs; v = minimalVertex g f in
          \<Squnion>\<^bsub>i\<in>[3..<Suc(maxGon p)]\<^esub> generatePolygon i v f g"

definition PlaneGraphsP :: "nat \<Rightarrow> graph set" ("PlaneGraphs\<^bsub>_\<^esub>") where
"PlaneGraphs\<^bsub>p\<^esub> \<equiv> {g. Seed\<^bsub>p\<^esub> [next_plane\<^bsub>p\<^esub>]\<rightarrow>* g \<and> final g}"

definition PlaneGraphs :: "graph set" where
"PlaneGraphs \<equiv> \<Union>p. PlaneGraphs\<^bsub>p\<^esub>"

end
