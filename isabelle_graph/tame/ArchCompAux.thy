(*  Author:     Tobias Nipkow
*)

header {* Comparing Enumeration and Archive *}

theory ArchCompAux
imports TameEnum TrieList Arch Worklist
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

definition enum_finals :: "(graph \<Rightarrow> graph list) \<Rightarrow> graph list
  \<Rightarrow> nat fgraph list \<Rightarrow> nat fgraph list option" where
"enum_finals succs =
  worklist succs (%fins g. if final g then fgraph g # fins else fins)"


primrec enum_filter_finals ::
  "(graph \<Rightarrow> graph list) \<Rightarrow> nat \<Rightarrow> graph list \<Rightarrow> nat fgraph list
   \<Rightarrow> (nat,nat fgraph)trie \<Rightarrow> nat fgraph list option" where
"enum_filter_finals succs 0 todo fins fint = None" |
"enum_filter_finals succs (Suc n) todo fins fint =
 (if todo = [] then Some fins
  else let g = hd todo; todo' = tl todo in
       if final g
       then let fg = fgraph g; h = hash fg; ags = lookup_trie fint h in
            if EX ag : set ags. iso_test fg ag
            then enum_filter_finals succs n todo' fins fint
            else (*let u = Debug1.write (length fins); v = Debug1.write n in*)
                 enum_filter_finals succs n todo' (fg # fins) (insert_trie fint h fg)
        else enum_filter_finals succs n (succs g @ todo') fins fint)"

definition tameEnum :: "nat \<Rightarrow> nat fgraph list option" where
"tameEnum p = enum_finals (next_tame p) [Seed p] []"

definition tameEnumFilter :: "nat \<Rightarrow> nat \<Rightarrow> nat fgraph list option" where
"tameEnumFilter p n =
 enum_filter_finals (next_tame p) n [Seed p] [] (Trie [] [])"

definition diff2 :: "nat fgraph list \<Rightarrow> nat fgraph list
   \<Rightarrow> nat fgraph list * nat fgraph list" where
"diff2 fgs ags =
 (let tfgs = trie_of_list hash fgs;
      tags = trie_of_list hash ags in
  (filter (%fg. ~list_ex (iso_test fg) (lookup_trie tags (hash fg))) fgs,
   filter (%ag. ~list_ex (iso_test ag) (lookup_trie tfgs (hash ag))) ags))"

definition same :: "nat fgraph list option \<Rightarrow> nat fgraph list \<Rightarrow> bool" where
  "same fgso ags = (case fgso of None \<Rightarrow> False | Some fgs \<Rightarrow>
   let tfgs = trie_of_list hash fgs;
       tags = trie_of_list hash ags in
   (list_all (%fg. list_ex (iso_test fg) (lookup_trie tags (hash fg))) fgs &
    list_all (%ag. list_ex (iso_test ag) (lookup_trie tfgs (hash ag))) ags))"

definition pre_iso_test :: "vertex fgraph \<Rightarrow> bool" where
  "pre_iso_test Fs \<longleftrightarrow>
   [] \<notin> set Fs \<and> (\<forall>F\<in>set Fs. distinct F) \<and> distinct (map rotate_min Fs)"

end
