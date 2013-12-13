(*  Title:      HOL/Option.thy
    Author:     Folklore
*)

header {* Datatype option *}

theory Option
imports Datatype
begin

datatype 'a option = None | Some 'a

lemma not_None_eq [iff]: "(x ~= None) = (EX y. x = Some y)"
  by (induct x) auto

lemma not_Some_eq [iff]: "(ALL y. x ~= Some y) = (x = None)"
  by (induct x) auto

text{*Although it may appear that both of these equalities are helpful
only when applied to assumptions, in practice it seems better to give
them the uniform iff attribute. *}

lemma inj_Some [simp]: "inj_on Some A"
by (rule inj_onI) simp

lemma option_caseE:
  assumes c: "(case x of None => P | Some y => Q y)"
  obtains
    (None) "x = None" and P
  | (Some) y where "x = Some y" and "Q y"
  using c by (cases x) simp_all

lemma UNIV_option_conv: "UNIV = insert None (range Some)"
by(auto intro: classical)


subsubsection {* Operations *}

primrec the :: "'a option => 'a" where
"the (Some x) = x"

primrec set :: "'a option => 'a set" where
"set None = {}" |
"set (Some x) = {x}"

lemma ospec [dest]: "(ALL x:set A. P x) ==> A = Some x ==> P x"
  by simp

declaration {* fn _ =>
  Classical.map_cs (fn cs => cs addSD2 ("ospec", @{thm ospec}))
*}

lemma elem_set [iff]: "(x : set xo) = (xo = Some x)"
  by (cases xo) auto

lemma set_empty_eq [simp]: "(set xo = {}) = (xo = None)"
  by (cases xo) auto

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option" where
  "map = (%f y. case y of None => None | Some x => Some (f x))"

lemma option_map_None [simp, code]: "map f None = None"
  by (simp add: map_def)

lemma option_map_Some [simp, code]: "map f (Some x) = Some (f x)"
  by (simp add: map_def)

lemma option_map_is_None [iff]:
    "(map f opt = None) = (opt = None)"
  by (simp add: map_def split add: option.split)

lemma option_map_eq_Some [iff]:
    "(map f xo = Some y) = (EX z. xo = Some z & f z = y)"
  by (simp add: map_def split add: option.split)

lemma option_map_comp:
    "map f (map g opt) = map (f o g) opt"
  by (simp add: map_def split add: option.split)

lemma option_map_o_sum_case [simp]:
    "map f o sum_case g h = sum_case (map f o g) (map f o h)"
  by (rule ext) (simp split: sum.split)

lemma map_cong: "x = y \<Longrightarrow> (\<And>a. y = Some a \<Longrightarrow> f a = g a) \<Longrightarrow> map f x = map g y"
by (cases x) auto

enriched_type map: Option.map proof -
  fix f g
  show "Option.map f \<circ> Option.map g = Option.map (f \<circ> g)"
  proof
    fix x
    show "(Option.map f \<circ> Option.map g) x= Option.map (f \<circ> g) x"
      by (cases x) simp_all
  qed
next
  show "Option.map id = id"
  proof
    fix x
    show "Option.map id x = id x"
      by (cases x) simp_all
  qed
qed

primrec bind :: "'a option \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option" where
bind_lzero: "bind None f = None" |
bind_lunit: "bind (Some x) f = f x"

lemma bind_runit[simp]: "bind x Some = x"
by (cases x) auto

lemma bind_assoc[simp]: "bind (bind x f) g = bind x (\<lambda>y. bind (f y) g)"
by (cases x) auto

lemma bind_rzero[simp]: "bind x (\<lambda>x. None) = None"
by (cases x) auto

lemma bind_cong: "x = y \<Longrightarrow> (\<And>a. y = Some a \<Longrightarrow> f a = g a) \<Longrightarrow> bind x f = bind y g"
by (cases x) auto

definition these :: "'a option set \<Rightarrow> 'a set"
where
  "these A = the ` {x \<in> A. x \<noteq> None}"

lemma these_empty [simp]:
  "these {} = {}"
  by (simp add: these_def)

lemma these_insert_None [simp]:
  "these (insert None A) = these A"
  by (auto simp add: these_def)

lemma these_insert_Some [simp]:
  "these (insert (Some x) A) = insert x (these A)"
proof -
  have "{y \<in> insert (Some x) A. y \<noteq> None} = insert (Some x) {y \<in> A. y \<noteq> None}"
    by auto
  then show ?thesis by (simp add: these_def)
qed

lemma in_these_eq:
  "x \<in> these A \<longleftrightarrow> Some x \<in> A"
proof
  assume "Some x \<in> A"
  then obtain B where "A = insert (Some x) B" by auto
  then show "x \<in> these A" by (auto simp add: these_def intro!: image_eqI)
next
  assume "x \<in> these A"
  then show "Some x \<in> A" by (auto simp add: these_def)
qed

lemma these_image_Some_eq [simp]:
  "these (Some ` A) = A"
  by (auto simp add: these_def intro!: image_eqI)

lemma Some_image_these_eq:
  "Some ` these A = {x\<in>A. x \<noteq> None}"
  by (auto simp add: these_def image_image intro!: image_eqI)

lemma these_empty_eq:
  "these B = {} \<longleftrightarrow> B = {} \<or> B = {None}"
  by (auto simp add: these_def)

lemma these_not_empty_eq:
  "these B \<noteq> {} \<longleftrightarrow> B \<noteq> {} \<and> B \<noteq> {None}"
  by (auto simp add: these_empty_eq)

hide_const (open) set map bind these
hide_fact (open) map_cong bind_cong


subsubsection {* Code generator setup *}

definition is_none :: "'a option \<Rightarrow> bool" where
  [code_post]: "is_none x \<longleftrightarrow> x = None"

lemma is_none_code [code]:
  shows "is_none None \<longleftrightarrow> True"
    and "is_none (Some x) \<longleftrightarrow> False"
  unfolding is_none_def by simp_all

lemma [code_unfold]:
  "HOL.equal x None \<longleftrightarrow> is_none x"
  by (simp add: equal is_none_def)

hide_const (open) is_none

code_type option
  (SML "_ option")
  (OCaml "_ option")
  (Haskell "Maybe _")
  (Scala "!Option[(_)]")

code_const None and Some
  (SML "NONE" and "SOME")
  (OCaml "None" and "Some _")
  (Haskell "Nothing" and "Just")
  (Scala "!None" and "Some")

code_instance option :: equal
  (Haskell -)

code_const "HOL.equal \<Colon> 'a option \<Rightarrow> 'a option \<Rightarrow> bool"
  (Haskell infix 4 "==")

code_reserved SML
  option NONE SOME

code_reserved OCaml
  option None Some

code_reserved Scala
  Option None Some

end

