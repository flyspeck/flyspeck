(*  Author:     Gertrud Bauer, Tobias Nipkow
*)

header {* Graph *}

theory Graph
imports Rotation
begin

syntax (xsymbols)
  "_UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>(00\<^bsub>_\<^esub>)/ _)" [0, 10] 10)
  "_INTER1"     :: "pttrns => 'b set => 'b set"           ("(3\<Inter>(00\<^bsub>_\<^esub>)/ _)" [0, 10] 10)
  "_UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>(00\<^bsub>_\<in>_\<^esub>)/ _)" [0, 0, 10] 10)
  "_INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Inter>(00\<^bsub>_\<in>_\<^esub>)/ _)" [0, 0, 10] 10)

subsection{* Notation *}

type_synonym vertex = "nat"

consts
  vertices :: "'a \<Rightarrow> vertex list"
  edges :: "'a \<Rightarrow> (vertex \<times> vertex) set" ("\<E>")

abbreviation vertices_set :: "'a \<Rightarrow> vertex set" ("\<V>") where
  "\<V> f \<equiv> set (vertices f)"


subsection {* Faces *}

text {*
We represent faces by (distinct) lists of vertices and a face type.
*}

datatype facetype = Final | Nonfinal

datatype face = Face "(vertex list)"  facetype

consts final :: "'a \<Rightarrow> bool"
consts type :: "'a \<Rightarrow> facetype"

overloading
  final_face \<equiv> "final :: face \<Rightarrow> bool"
  type_face \<equiv> "type :: face \<Rightarrow> facetype"
  vertices_face \<equiv> "vertices :: face \<Rightarrow> vertex list"
begin

primrec final_face where
  "final (Face vs f) = (case f of Final \<Rightarrow> True | Nonfinal \<Rightarrow> False)"

primrec type_face where
  "type (Face vs f) = f"

primrec vertices_face where
  "vertices (Face vs f) = vs"

end

defs (overloaded) cong_face_def:
 "f\<^sub>1 \<cong> (f\<^sub>2::face) \<equiv> vertices f\<^sub>1 \<cong> vertices f\<^sub>2"

text {* The following operation makes a face final. *}

definition setFinal :: "face \<Rightarrow> face" where
  "setFinal f \<equiv> Face (vertices f) Final"


text {* The function @{text nextVertex} (written @{text "f \<bullet> v"}) is based on
@{text nextElem}, that returns the successor of an element in a list.  *}

primrec nextElem :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
 "nextElem [] b x = b"
|"nextElem (a#as) b x =
    (if x=a then (case as of [] \<Rightarrow> b | (a'#as') \<Rightarrow> a') else nextElem as b x)"

definition nextVertex :: "face \<Rightarrow> vertex \<Rightarrow> vertex" (*<*)("_ \<bullet>" [999]) (*>*)where (* *)
 "f \<bullet> \<equiv> let vs = vertices f in nextElem vs (hd vs)"


text {* @{text nextVertices} is $n$-fold application of
@{text nextvertex}. *}

definition nextVertices :: "face \<Rightarrow> nat \<Rightarrow> vertex \<Rightarrow> vertex" (*<*)("_\<^bsup>_\<^esup> \<bullet> _" [100, 0, 100]) (*>*)where (* *)
  "f\<^bsup>n\<^esup> \<bullet> v \<equiv> (f \<bullet> ^^ n) v"

lemma nextV2: "f\<^bsup>2\<^esup>\<bullet>v = f\<bullet> (f\<bullet> v)"
by (simp add: nextVertices_def eval_nat_numeral)

(*<*) defs edges_face_def: (*>*)
  "edges (f::face) \<equiv> {(a, f \<bullet> a)|a. a \<in> \<V> f}"


(*<*)consts op :: "'a \<Rightarrow> 'a" ("_\<^bsup>op\<^esup>" [1000] 999)  (*>*) (* *)
defs (*<*) op_vertices_def:(*>*) "(vs::vertex list)\<^bsup>op\<^esup> \<equiv> rev vs"
overloading
  op_graph \<equiv> "Graph.op :: face \<Rightarrow> face"
begin

primrec op_graph where "(Face vs f)\<^bsup>op\<^esup> = Face (rev vs) f"  (*<*)

end

lemma [simp]: "vertices ((f::face)\<^bsup>op\<^esup>) = (vertices f)\<^bsup>op\<^esup>"
  by (induct f) (simp add: op_vertices_def)
lemma [simp]: "xs \<noteq> [] \<Longrightarrow> hd (rev xs)= last xs"
  by(induct xs) simp_all (*>*) (* *)

definition prevVertex :: "face \<Rightarrow> vertex \<Rightarrow> vertex" (*<*)("_\<^bsup>-1\<^esup> \<bullet>" [100]) (*>*)where (* *)
  "f\<^bsup>-1\<^esup> \<bullet> v \<equiv> (let vs = vertices f in nextElem (rev vs) (last vs) v)"

abbreviation
  triangle :: "face \<Rightarrow> bool" where
  "triangle f == |vertices f| = 3"


subsection {* Graphs *}

datatype graph = Graph "(face list)" "nat" "face list list" "nat list"

primrec faces :: "graph \<Rightarrow> face list" where
  "faces (Graph fs n f h) = fs"

abbreviation
  Faces :: "graph \<Rightarrow> face set" ("\<F>") where
  "\<F> g == set(faces g)"

primrec countVertices :: "graph \<Rightarrow> nat" where
  "countVertices (Graph fs n f h) = n"

overloading
  vertices_graph \<equiv> "vertices :: graph \<Rightarrow> vertex list"
begin

primrec vertices_graph where "vertices (Graph fs n f h) = [0 ..< n]"

end

lemma vertices_graph: "vertices g = [0 ..< countVertices g]"
by (induct g) simp

lemma in_vertices_graph:
  "v \<in> set (vertices g) = (v < countVertices g)"
by (simp add:vertices_graph)

lemma len_vertices_graph:
  "|vertices g| = countVertices g"
by (simp add:vertices_graph)

primrec faceListAt :: "graph \<Rightarrow> face list list" where
  "faceListAt (Graph fs n f h) = f"

definition facesAt :: "graph \<Rightarrow> vertex \<Rightarrow> face list" where
 "facesAt g v \<equiv> (*if v \<in> set(vertices g) then*) faceListAt g ! v (*else []*)"

primrec heights :: "graph \<Rightarrow> nat list" where
  "heights (Graph fs n f h) = h"

definition height :: "graph \<Rightarrow> vertex \<Rightarrow> nat" where
  "height g v \<equiv> heights g ! v"

definition graph :: "nat \<Rightarrow> graph" where
  "graph n \<equiv>
    (let vs = [0 ..< n];
     fs = [ Face vs Final, Face (rev vs) Nonfinal]
     in (Graph fs n (replicate n fs) (replicate n 0)))"

subsection{* Operations on graphs *}

text {* final graph, final / nonfinal faces *}

definition finals :: "graph \<Rightarrow> face list" where
  "finals g \<equiv> [f \<leftarrow> faces g. final f]"

definition nonFinals :: "graph \<Rightarrow> face list" where
  "nonFinals g \<equiv> [f \<leftarrow> faces g. \<not> final f]"

definition countNonFinals :: "graph \<Rightarrow> nat" where
  "countNonFinals g \<equiv> |nonFinals g|"

defs finalGraph_def: "final g \<equiv> (nonFinals g = [])"

lemma finalGraph_faces[simp]: "final g \<Longrightarrow> finals g = faces g"
 by (simp add: finalGraph_def finals_def nonFinals_def filter_compl1)

lemma finalGraph_face: "final g \<Longrightarrow> f \<in> set (faces g) \<Longrightarrow> final f"
  by (simp only: finalGraph_faces[symmetric]) (simp add: finals_def)


definition finalVertex :: "graph \<Rightarrow> vertex \<Rightarrow> bool" where
  "finalVertex g v \<equiv> \<forall>f \<in> set(facesAt g v). final f"

lemma finalVertex_final_face[dest]:
  "finalVertex g v \<Longrightarrow> f \<in> set (facesAt g v) \<Longrightarrow> final f"
  by (auto simp add: finalVertex_def)




text {* counting faces *}

definition degree :: "graph \<Rightarrow> vertex \<Rightarrow> nat" where
  "degree g v \<equiv> |facesAt g v|"

definition tri :: "graph \<Rightarrow> vertex \<Rightarrow> nat" where
 "tri g v \<equiv> |[f \<leftarrow> facesAt g v. final f \<and> |vertices f| = 3]|"

definition quad :: "graph \<Rightarrow> vertex \<Rightarrow> nat" where
 "quad g v \<equiv> |[f \<leftarrow> facesAt g v. final f \<and> |vertices f| = 4]|"

definition except :: "graph \<Rightarrow> vertex \<Rightarrow> nat" where
 "except g v \<equiv> |[f \<leftarrow> facesAt g v. final f \<and> 5 \<le> |vertices f| ]|"

definition vertextype :: "graph \<Rightarrow> vertex \<Rightarrow> nat \<times> nat \<times> nat" where
  "vertextype g v \<equiv> (tri g v, quad g v, except g v)"

lemma[simp]: "0 \<le> tri g v" by (simp add: tri_def)

lemma[simp]: "0 \<le> quad g v" by (simp add: quad_def)

lemma[simp]: "0 \<le> except g v" by (simp add: except_def)


definition exceptionalVertex :: "graph \<Rightarrow> vertex \<Rightarrow> bool" where
  "exceptionalVertex g v \<equiv> except g v \<noteq> 0"

definition noExceptionals :: "graph \<Rightarrow> vertex set \<Rightarrow> bool" where
  "noExceptionals g V \<equiv> (\<forall>v \<in> V. \<not> exceptionalVertex g v)"


text {* An edge $(a,b)$ is contained in face f,
  $b$ is the successor of $a$ in $f$. *}

defs edges_graph_def: (*>*)
 "edges (g::graph) \<equiv> \<Union>\<^bsub>f \<in> \<F> g\<^esub> edges f"

definition neighbors :: "graph \<Rightarrow> vertex \<Rightarrow> vertex list" where
 "neighbors g v \<equiv> [f\<bullet>v. f \<leftarrow> facesAt g v]"


subsection {* Navigation in graphs *}

text {*
The function $s'$ permutating the faces at a vertex,
is implemeted by the function @{text nextFace}
*}

definition nextFace :: "graph \<times> vertex \<Rightarrow> face \<Rightarrow> face" (*<*)("_ \<bullet>") (*>*)where
(*<*) nextFace_def_aux: "p \<bullet> \<equiv> \<lambda>f. (let (g,v) = p; fs = (facesAt g v) in
   (case fs of [] \<Rightarrow> f
           | g#gs \<Rightarrow> nextElem fs (hd fs) f))"  (*>*)


(* precondition a b in f *)
definition directedLength :: "face \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> nat" where
  "directedLength f a b \<equiv>
  if a = b then 0 else |(between (vertices f) a b)| + 1"


subsection {* Code generator setup *}

definition final_face :: "face \<Rightarrow> bool" where
  final_face_code_def: "final_face = final"
declare final_face_code_def [symmetric, code_unfold]

lemma final_face_code [code]:
  "final_face (Face vs Final) \<longleftrightarrow> True"
  "final_face (Face vs Nonfinal) \<longleftrightarrow> False"
  by (simp_all add: final_face_code_def)

definition final_graph :: "graph \<Rightarrow> bool" where
  final_graph_code_def: "final_graph = final"
declare final_graph_code_def [symmetric, code_unfold]

lemma final_graph_code [code]: "final_graph g = List.null (nonFinals g)"
  unfolding final_graph_code_def finalGraph_def null_def ..

definition vertices_face :: "face \<Rightarrow> vertex list" where
  vertices_face_code_def: "vertices_face = vertices"
declare vertices_face_code_def [symmetric, code_unfold]

lemma vertices_face_code [code]: "vertices_face (Face vs f) = vs"
  unfolding vertices_face_code_def by simp

definition vertices_graph :: "graph \<Rightarrow> vertex list" where
  vertices_graph_code_def: "vertices_graph = vertices"
declare vertices_graph_code_def [symmetric, code_unfold]

lemma vertices_graph_code [code]:
  "vertices_graph (Graph fs n f h) = [0 ..< n]"
  unfolding vertices_graph_code_def by simp

end
