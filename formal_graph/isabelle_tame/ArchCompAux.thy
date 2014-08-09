(*  Author: Tobias Nipkow  *)

header {* Comparing Enumeration and Archive *}

theory ArchCompAux
imports TameEnum Tries Arch Worklist
begin

function qsort :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"qsort le []       = []" |
"qsort le (x#xs) = qsort le [y\<leftarrow>xs . ~ le x y] @ [x] @
                   qsort le [y\<leftarrow>xs . le x y]"
by pat_completeness auto
termination by (relation "measure (size o snd)")
  (auto simp add: length_filter_le [THEN le_less_trans])

definition nof_vertices :: "'a fgraph \<Rightarrow> nat" where
"nof_vertices = length o remdups o concat"

definition fgraph :: "graph \<Rightarrow> nat fgraph" where
"fgraph g = map vertices (faces g)"

definition hash :: "nat fgraph \<Rightarrow> nat list" where
  "hash fs = (let n = nof_vertices fs in
     [n, size fs] @
     qsort (%x y. y < x) (map (%i. foldl (op +) 0 (map size [f\<leftarrow>fs. i \<in> set f]))
                             [0..<n]))"
(*
definition diff2 :: "nat fgraph list \<Rightarrow> nat fgraph list
   \<Rightarrow> nat fgraph list * nat fgraph list" where
"diff2 fgs ags =
 (let tfgs = trie_of_list hash fgs;
      tags = trie_of_list hash ags in
  (filter (%fg. ~list_ex (iso_test fg) (lookup_trie tags (hash fg))) fgs,
   filter (%ag. ~list_ex (iso_test ag) (lookup_trie tfgs (hash ag))) ags))"
*)
definition samet :: "(nat,nat fgraph) tries option \<Rightarrow> nat fgraph list \<Rightarrow> bool"
where
  "samet fgto ags = (case fgto of None \<Rightarrow> False | Some tfgs \<Rightarrow>
   let tags = trie_of_list hash ags in
   (Tries.all (%fg. list_ex (iso_test fg) (Tries.lookup tags (hash fg))) tfgs &
    Tries.all (%ag. list_ex (iso_test ag) (Tries.lookup tfgs (hash ag))) tags))"

definition pre_iso_test :: "vertex fgraph \<Rightarrow> bool" where
  "pre_iso_test Fs \<longleftrightarrow>
   [] \<notin> set Fs \<and> (\<forall>F\<in>set Fs. distinct F) \<and> distinct (map rotate_min Fs)"

end
