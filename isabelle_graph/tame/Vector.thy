(*  Author:     Gertrud Bauer, Tobias Nipkow
*)

header {* Vector *}

theory Vector
imports Main
begin

datatype 'a vector = Vector "'a list"

subsection {* Tabulation *}

definition tabulate' :: "nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> 'a vector" where
  [code del]: "tabulate' p \<equiv> Vector (map (snd p) [0 ..< fst p])"
        (* map int [0..nat (fst p)])])*)

definition tabulate :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a vector" where
  "tabulate n f \<equiv> tabulate' (n, f)"

definition tabulate2 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> 'a vector vector" where
  "tabulate2 m n f \<equiv> tabulate m (\<lambda>i .tabulate n (f i))"

definition tabulate3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
  (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> 'a vector vector vector" where
  "tabulate3 l m n f \<equiv> tabulate l (\<lambda>i. tabulate m (\<lambda>j .tabulate n (\<lambda>k. f i j k)))"


syntax 
 "_tabulate" :: "'a \<Rightarrow> pttrn \<Rightarrow> nat \<Rightarrow> 'a vector"  ("(\<lbrakk>_. _ < _\<rbrakk>)") 
 "_tabulate2" :: "'a \<Rightarrow> pttrn \<Rightarrow> nat \<Rightarrow> 
    pttrn \<Rightarrow> nat \<Rightarrow> 'a vector"
  ("(\<lbrakk>_. _ < _, _ < _\<rbrakk>)")
 "_tabulate3" :: "'a \<Rightarrow> pttrn \<Rightarrow> nat \<Rightarrow> 
     pttrn \<Rightarrow> nat \<Rightarrow> 
     pttrn \<Rightarrow> nat \<Rightarrow> 'a vector"
  ("(\<lbrakk>_. _ < _, _ < _, _ < _ \<rbrakk>)")
translations 
  "\<lbrakk>f. x < n\<rbrakk>" == "CONST tabulate n (\<lambda>x. f)"
  "\<lbrakk>f. x < m, y < n\<rbrakk>" == "CONST tabulate2 m n (\<lambda>x y. f)"
  "\<lbrakk>f. x < l, y < m, z < n\<rbrakk>" == "CONST tabulate3 l m n (\<lambda>x y z. f)"


subsection {* Access *}

definition sub1 :: "'a vector \<times> nat \<Rightarrow> 'a" where
 [code del]: "sub1 p \<equiv> let (a, n) = p in case a of (Vector as) \<Rightarrow> as ! n"

definition sub :: "'a vector \<Rightarrow> nat \<Rightarrow> 'a" where
 "sub a n \<equiv> sub1 (a, n)"

abbreviation
  sub1_syntax :: "'a vector \<Rightarrow> nat \<Rightarrow> 'a"  ("(_\<lbrakk>_\<rbrakk>)" [1000] 999)
  where "a\<lbrakk>n\<rbrakk> == sub a n"

abbreviation
  sub2_syntax :: "'a vector vector \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a"  ("(_\<lbrakk>_,_\<rbrakk>)" [1000] 999)
  where "as\<lbrakk>m, n\<rbrakk> == sub (sub as m) n"

abbreviation
  sub3_syntax :: "'a vector vector vector \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" ("(_\<lbrakk>_,_,_\<rbrakk>)" [1000] 999)
  where "as\<lbrakk>l, m, n\<rbrakk> == sub (sub (sub as l) m) n"

text {* examples:  @{term "\<lbrakk>0. i < 5\<rbrakk>"}, @{term "\<lbrakk>i. i < 5, j < 3\<rbrakk>"}  *}

subsection {* Code generator setup *}

declare vector.cases [code del]
code_abort vector_case

code_type vector
  (SML "_/ vector")

code_const Vector and tabulate' and sub1
  (SML "Vector.fromList" and "Vector.tabulate" and "Vector.sub")

code_reserved SML Vector


types_code
  vector  ("_ vector")

consts_code
  "tabulate'"  ("Vector.tabulate")
  "sub1"       ("Vector.sub")

end
