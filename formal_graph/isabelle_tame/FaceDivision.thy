(*  Author:     Gertrud Bauer, Tobias Nipkow
*)

header{* Subdividing a Face *}

theory FaceDivision
imports Graph
begin

definition split_face :: "face \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex list \<Rightarrow> face \<times> face" where
 "split_face f ram\<^sub>1 ram\<^sub>2 newVs \<equiv> let vs = vertices f;
     f\<^sub>1 = [ram\<^sub>1] @ between vs ram\<^sub>1 ram\<^sub>2 @ [ram\<^sub>2];
     f\<^sub>2 = [ram\<^sub>2] @ between vs ram\<^sub>2 ram\<^sub>1 @ [ram\<^sub>1] in
     (Face (rev newVs @ f\<^sub>1) Nonfinal,
     Face (f\<^sub>2 @ newVs) Nonfinal)"


definition replacefacesAt :: "nat list \<Rightarrow> face \<Rightarrow> face list \<Rightarrow> face list list \<Rightarrow> face list list" where
 "replacefacesAt ns f fs F \<equiv> mapAt ns (replace f fs) F"


definition makeFaceFinalFaceList :: "face \<Rightarrow> face list \<Rightarrow> face list" where
  "makeFaceFinalFaceList f fs \<equiv> replace f [setFinal f] fs"

definition makeFaceFinal :: "face \<Rightarrow> graph \<Rightarrow> graph" where
 "makeFaceFinal f g \<equiv>
     Graph (makeFaceFinalFaceList f (faces g))
           (countVertices g)
           [makeFaceFinalFaceList f fs. fs \<leftarrow> faceListAt g]
           (heights g)"


definition heightsNewVertices :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
 "heightsNewVertices h\<^sub>1 h\<^sub>2 n \<equiv> [min (h\<^sub>1 + i + 1) (h\<^sub>2 + n - i). i \<leftarrow> [0 ..< n]]"

definition splitFace
 :: "graph \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> face \<Rightarrow> vertex list \<Rightarrow> face \<times> face \<times> graph" where
 "splitFace g ram\<^sub>1 ram\<^sub>2 oldF newVs \<equiv>
     let fs = faces g;
     n = countVertices g;
     Fs = faceListAt g;
     h = heights g;
     vs\<^sub>1 = between (vertices oldF) ram\<^sub>1 ram\<^sub>2;
     vs\<^sub>2 = between (vertices oldF) ram\<^sub>2 ram\<^sub>1;
     (f\<^sub>1, f\<^sub>2) = split_face oldF ram\<^sub>1 ram\<^sub>2 newVs;
     Fs = replacefacesAt vs\<^sub>1 oldF [f\<^sub>1] Fs;
     Fs = replacefacesAt vs\<^sub>2 oldF [f\<^sub>2] Fs;
     Fs = replacefacesAt [ram\<^sub>1] oldF [f\<^sub>2, f\<^sub>1] Fs;
     Fs = replacefacesAt [ram\<^sub>2] oldF [f\<^sub>1, f\<^sub>2] Fs;
     Fs = Fs @ replicate |newVs| [f\<^sub>1, f\<^sub>2] in
     (f\<^sub>1, f\<^sub>2, Graph ((replace oldF [f\<^sub>2] fs)@ [f\<^sub>1])
                        (n + |newVs| )
                        Fs
                        (h @ heightsNewVertices (h!ram\<^sub>1)(h!ram\<^sub>2) |newVs| ))"



primrec subdivFace' :: "graph \<Rightarrow> face \<Rightarrow> vertex \<Rightarrow> nat \<Rightarrow> vertex option list \<Rightarrow> graph" where
  "subdivFace' g f u n [] = makeFaceFinal f g"
| "subdivFace' g f u n (vo#vos) =
     (case vo of None \<Rightarrow> subdivFace' g f u (Suc n) vos
         | (Some v) \<Rightarrow>
            if f\<bullet>u = v \<and> n = 0
            then subdivFace' g f v 0 vos
            else let ws = [countVertices g  ..< countVertices g + n];
            (f\<^sub>1, f\<^sub>2, g') = splitFace g u v f ws in
            subdivFace' g' f\<^sub>2 v 0 vos)"

definition subdivFace :: "graph \<Rightarrow> face \<Rightarrow> vertex option list \<Rightarrow> graph" where
"subdivFace g f vos \<equiv> subdivFace' g f (the(hd vos)) 0 (tl vos)"

end
