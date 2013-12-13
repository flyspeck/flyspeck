(*  Author:     Gertrud Bauer, Tobias Nipkow
*)

header{* Subdividing a Face *}

theory FaceDivision
imports Graph
begin

definition split_face :: "face \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex list \<Rightarrow> face \<times> face" where
 "split_face f ram\<^isub>1 ram\<^isub>2 newVs \<equiv> let vs = vertices f;
     f\<^isub>1 = [ram\<^isub>1] @ between vs ram\<^isub>1 ram\<^isub>2 @ [ram\<^isub>2];
     f\<^isub>2 = [ram\<^isub>2] @ between vs ram\<^isub>2 ram\<^isub>1 @ [ram\<^isub>1] in
     (Face (rev newVs @ f\<^isub>1) Nonfinal,
     Face (f\<^isub>2 @ newVs) Nonfinal)"


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
 "heightsNewVertices h\<^isub>1 h\<^isub>2 n \<equiv> [min (h\<^isub>1 + i + 1) (h\<^isub>2 + n - i). i \<leftarrow> [0 ..< n]]"

definition splitFace
 :: "graph \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> face \<Rightarrow> vertex list \<Rightarrow> face \<times> face \<times> graph" where
 "splitFace g ram\<^isub>1 ram\<^isub>2 oldF newVs \<equiv>
     let fs = faces g;
     n = countVertices g;
     Fs = faceListAt g;
     h = heights g;
     vs\<^isub>1 = between (vertices oldF) ram\<^isub>1 ram\<^isub>2;
     vs\<^isub>2 = between (vertices oldF) ram\<^isub>2 ram\<^isub>1;
     (f\<^isub>1, f\<^isub>2) = split_face oldF ram\<^isub>1 ram\<^isub>2 newVs;
     Fs = replacefacesAt vs\<^isub>1 oldF [f\<^isub>1] Fs;
     Fs = replacefacesAt vs\<^isub>2 oldF [f\<^isub>2] Fs;
     Fs = replacefacesAt [ram\<^isub>1] oldF [f\<^isub>2, f\<^isub>1] Fs;
     Fs = replacefacesAt [ram\<^isub>2] oldF [f\<^isub>1, f\<^isub>2] Fs;
     Fs = Fs @ replicate |newVs| [f\<^isub>1, f\<^isub>2] in
     (f\<^isub>1, f\<^isub>2, Graph ((replace oldF [f\<^isub>2] fs)@ [f\<^isub>1])
                        (n + |newVs| )
                        Fs
                        (h @ heightsNewVertices (h!ram\<^isub>1)(h!ram\<^isub>2) |newVs| ))"



primrec subdivFace' :: "graph \<Rightarrow> face \<Rightarrow> vertex \<Rightarrow> nat \<Rightarrow> vertex option list \<Rightarrow> graph" where
  "subdivFace' g f u n [] = makeFaceFinal f g"
| "subdivFace' g f u n (vo#vos) =
     (case vo of None \<Rightarrow> subdivFace' g f u (Suc n) vos
         | (Some v) \<Rightarrow>
            if f\<bullet>u = v \<and> n = 0
            then subdivFace' g f v 0 vos
            else let ws = [countVertices g  ..< countVertices g + n];
            (f\<^isub>1, f\<^isub>2, g') = splitFace g u v f ws in
            subdivFace' g' f\<^isub>2 v 0 vos)"

definition subdivFace :: "graph \<Rightarrow> face \<Rightarrow> vertex option list \<Rightarrow> graph" where
"subdivFace g f vos \<equiv> subdivFace' g f (the(hd vos)) 0 (tl vos)"

end
