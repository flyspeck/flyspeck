(*  Title:      HOL/HOL.thy
    Author:     Tobias Nipkow, Markus Wenzel, and Larry Paulson
*)

header {* The basis of Higher-Order Logic *}

theory HOL
imports Pure "~~/src/Tools/Code_Generator"
keywords
  "try" "solve_direct" "quickcheck" "print_coercions" "print_claset"
    "print_induct_rules" :: diag and
  "quickcheck_params" :: thy_decl
begin

ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Tools/try.ML"
ML_file "~~/src/Tools/quickcheck.ML"
ML_file "~~/src/Tools/solve_direct.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Provers/hypsubst.ML"
ML_file "~~/src/Provers/splitter.ML"
ML_file "~~/src/Provers/classical.ML"
ML_file "~~/src/Provers/blast.ML"
ML_file "~~/src/Provers/clasimp.ML"
ML_file "~~/src/Tools/coherent.ML"
ML_file "~~/src/Tools/eqsubst.ML"
ML_file "~~/src/Provers/quantifier1.ML"
ML_file "~~/src/Tools/atomize_elim.ML"
ML_file "~~/src/Tools/induct.ML"
ML_file "~~/src/Tools/cong_tac.ML"
ML_file "~~/src/Tools/intuitionistic.ML"
ML_file "~~/src/Tools/project_rule.ML"
ML_file "~~/src/Tools/subtyping.ML"
ML_file "~~/src/Tools/case_product.ML"

setup {*
  Intuitionistic.method_setup @{binding iprover}
  #> Subtyping.setup
  #> Case_Product.setup
*}

subsection {* Primitive logic *}

subsubsection {* Core syntax *}

classes type
default_sort type
setup {* Object_Logic.add_base_sort @{sort type} *}

arities
  "fun" :: (type, type) type
  itself :: (type) type

typedecl bool

judgment
  Trueprop      :: "bool => prop"                   ("(_)" 5)

axiomatization
  implies       :: "[bool, bool] => bool"           (infixr "-->" 25)  and
  eq            :: "['a, 'a] => bool"               (infixl "=" 50)  and
  The           :: "('a => bool) => 'a"

consts
  True          :: bool
  False         :: bool
  Not           :: "bool => bool"                   ("~ _" [40] 40)

  conj          :: "[bool, bool] => bool"           (infixr "&" 35)
  disj          :: "[bool, bool] => bool"           (infixr "|" 30)

  All           :: "('a => bool) => bool"           (binder "ALL " 10)
  Ex            :: "('a => bool) => bool"           (binder "EX " 10)
  Ex1           :: "('a => bool) => bool"           (binder "EX! " 10)


subsubsection {* Additional concrete syntax *}

notation (output)
  eq  (infix "=" 50)

abbreviation
  not_equal :: "['a, 'a] => bool"  (infixl "~=" 50) where
  "x ~= y == ~ (x = y)"

notation (output)
  not_equal  (infix "~=" 50)

notation (xsymbols)
  Not  ("\<not> _" [40] 40) and
  conj  (infixr "\<and>" 35) and
  disj  (infixr "\<or>" 30) and
  implies  (infixr "\<longrightarrow>" 25) and
  not_equal  (infixl "\<noteq>" 50)

notation (xsymbols output)
  not_equal  (infix "\<noteq>" 50)

notation (HTML output)
  Not  ("\<not> _" [40] 40) and
  conj  (infixr "\<and>" 35) and
  disj  (infixr "\<or>" 30) and
  not_equal  (infix "\<noteq>" 50)

abbreviation (iff)
  iff :: "[bool, bool] => bool"  (infixr "<->" 25) where
  "A <-> B == A = B"

notation (xsymbols)
  iff  (infixr "\<longleftrightarrow>" 25)

syntax "_The" :: "[pttrn, bool] => 'a"  ("(3THE _./ _)" [0, 10] 10)
translations "THE x. P" == "CONST The (%x. P)"
print_translation {*
  [(@{const_syntax The}, fn _ => fn [Abs abs] =>
      let val (x, t) = Syntax_Trans.atomic_abs_tr' abs
      in Syntax.const @{syntax_const "_The"} $ x $ t end)]
*}  -- {* To avoid eta-contraction of body *}

nonterminal letbinds and letbind
syntax
  "_bind"       :: "[pttrn, 'a] => letbind"              ("(2_ =/ _)" 10)
  ""            :: "letbind => letbinds"                 ("_")
  "_binds"      :: "[letbind, letbinds] => letbinds"     ("_;/ _")
  "_Let"        :: "[letbinds, 'a] => 'a"                ("(let (_)/ in (_))" [0, 10] 10)

nonterminal case_syn and cases_syn
syntax
  "_case_syntax" :: "['a, cases_syn] => 'b"  ("(case _ of/ _)" 10)
  "_case1" :: "['a, 'b] => case_syn"  ("(2_ =>/ _)" 10)
  "" :: "case_syn => cases_syn"  ("_")
  "_case2" :: "[case_syn, cases_syn] => cases_syn"  ("_/ | _")
syntax (xsymbols)
  "_case1" :: "['a, 'b] => case_syn"  ("(2_ \<Rightarrow>/ _)" 10)

notation (xsymbols)
  All  (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  Ex1  (binder "\<exists>!" 10)

notation (HTML output)
  All  (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  Ex1  (binder "\<exists>!" 10)

notation (HOL)
  All  (binder "! " 10) and
  Ex  (binder "? " 10) and
  Ex1  (binder "?! " 10)


subsubsection {* Axioms and basic definitions *}

axiomatization where
  refl: "t = (t::'a)" and
  subst: "s = t \<Longrightarrow> P s \<Longrightarrow> P t" and
  ext: "(!!x::'a. (f x ::'b) = g x) ==> (%x. f x) = (%x. g x)"
    -- {*Extensionality is built into the meta-logic, and this rule expresses
         a related property.  It is an eta-expanded version of the traditional
         rule, and similar to the ABS rule of HOL*} and

  the_eq_trivial: "(THE x. x = a) = (a::'a)"

axiomatization where
  impI: "(P ==> Q) ==> P-->Q" and
  mp: "[| P-->Q;  P |] ==> Q" and

  iff: "(P-->Q) --> (Q-->P) --> (P=Q)" and
  True_or_False: "(P=True) | (P=False)"

defs
  True_def:     "True      == ((%x::bool. x) = (%x. x))"
  All_def:      "All(P)    == (P = (%x. True))"
  Ex_def:       "Ex(P)     == !Q. (!x. P x --> Q) --> Q"
  False_def:    "False     == (!P. P)"
  not_def:      "~ P       == P-->False"
  and_def:      "P & Q     == !R. (P-->Q-->R) --> R"
  or_def:       "P | Q     == !R. (P-->R) --> (Q-->R) --> R"
  Ex1_def:      "Ex1(P)    == ? x. P(x) & (! y. P(y) --> y=x)"

definition If :: "bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("(if (_)/ then (_)/ else (_))" [0, 0, 10] 10)
  where "If P x y \<equiv> (THE z::'a. (P=True --> z=x) & (P=False --> z=y))"

definition Let :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"
  where "Let s f \<equiv> f s"

translations
  "_Let (_binds b bs) e"  == "_Let b (_Let bs e)"
  "let x = a in e"        == "CONST Let a (%x. e)"

axiomatization undefined :: 'a

class default = fixes default :: 'a


subsection {* Fundamental rules *}

subsubsection {* Equality *}

lemma sym: "s = t ==> t = s"
  by (erule subst) (rule refl)

lemma ssubst: "t = s ==> P s ==> P t"
  by (drule sym) (erule subst)

lemma trans: "[| r=s; s=t |] ==> r=t"
  by (erule subst)

lemma trans_sym [Pure.elim?]: "r = s ==> t = s ==> r = t"
  by (rule trans [OF _ sym])

lemma meta_eq_to_obj_eq: 
  assumes meq: "A == B"
  shows "A = B"
  by (unfold meq) (rule refl)

text {* Useful with @{text erule} for proving equalities from known equalities. *}
     (* a = b
        |   |
        c = d   *)
lemma box_equals: "[| a=b;  a=c;  b=d |] ==> c=d"
apply (rule trans)
apply (rule trans)
apply (rule sym)
apply assumption+
done

text {* For calculational reasoning: *}

lemma forw_subst: "a = b ==> P b ==> P a"
  by (rule ssubst)

lemma back_subst: "P a ==> a = b ==> P b"
  by (rule subst)


subsubsection {* Congruence rules for application *}

text {* Similar to @{text AP_THM} in Gordon's HOL. *}
lemma fun_cong: "(f::'a=>'b) = g ==> f(x)=g(x)"
apply (erule subst)
apply (rule refl)
done

text {* Similar to @{text AP_TERM} in Gordon's HOL and FOL's @{text subst_context}. *}
lemma arg_cong: "x=y ==> f(x)=f(y)"
apply (erule subst)
apply (rule refl)
done

lemma arg_cong2: "\<lbrakk> a = b; c = d \<rbrakk> \<Longrightarrow> f a c = f b d"
apply (erule ssubst)+
apply (rule refl)
done

lemma cong: "[| f = g; (x::'a) = y |] ==> f x = g y"
apply (erule subst)+
apply (rule refl)
done

ML {* val cong_tac = Cong_Tac.cong_tac @{thm cong} *}


subsubsection {* Equality of booleans -- iff *}

lemma iffI: assumes "P ==> Q" and "Q ==> P" shows "P=Q"
  by (iprover intro: iff [THEN mp, THEN mp] impI assms)

lemma iffD2: "[| P=Q; Q |] ==> P"
  by (erule ssubst)

lemma rev_iffD2: "[| Q; P=Q |] ==> P"
  by (erule iffD2)

lemma iffD1: "Q = P \<Longrightarrow> Q \<Longrightarrow> P"
  by (drule sym) (rule iffD2)

lemma rev_iffD1: "Q \<Longrightarrow> Q = P \<Longrightarrow> P"
  by (drule sym) (rule rev_iffD2)

lemma iffE:
  assumes major: "P=Q"
    and minor: "[| P --> Q; Q --> P |] ==> R"
  shows R
  by (iprover intro: minor impI major [THEN iffD2] major [THEN iffD1])


subsubsection {*True*}

lemma TrueI: "True"
  unfolding True_def by (rule refl)

lemma eqTrueI: "P ==> P = True"
  by (iprover intro: iffI TrueI)

lemma eqTrueE: "P = True ==> P"
  by (erule iffD2) (rule TrueI)


subsubsection {*Universal quantifier*}

lemma allI: assumes "!!x::'a. P(x)" shows "ALL x. P(x)"
  unfolding All_def by (iprover intro: ext eqTrueI assms)

lemma spec: "ALL x::'a. P(x) ==> P(x)"
apply (unfold All_def)
apply (rule eqTrueE)
apply (erule fun_cong)
done

lemma allE:
  assumes major: "ALL x. P(x)"
    and minor: "P(x) ==> R"
  shows R
  by (iprover intro: minor major [THEN spec])

lemma all_dupE:
  assumes major: "ALL x. P(x)"
    and minor: "[| P(x); ALL x. P(x) |] ==> R"
  shows R
  by (iprover intro: minor major major [THEN spec])


subsubsection {* False *}

text {*
  Depends upon @{text spec}; it is impossible to do propositional
  logic before quantifiers!
*}

lemma FalseE: "False ==> P"
  apply (unfold False_def)
  apply (erule spec)
  done

lemma False_neq_True: "False = True ==> P"
  by (erule eqTrueE [THEN FalseE])


subsubsection {* Negation *}

lemma notI:
  assumes "P ==> False"
  shows "~P"
  apply (unfold not_def)
  apply (iprover intro: impI assms)
  done

lemma False_not_True: "False ~= True"
  apply (rule notI)
  apply (erule False_neq_True)
  done

lemma True_not_False: "True ~= False"
  apply (rule notI)
  apply (drule sym)
  apply (erule False_neq_True)
  done

lemma notE: "[| ~P;  P |] ==> R"
  apply (unfold not_def)
  apply (erule mp [THEN FalseE])
  apply assumption
  done

lemma notI2: "(P \<Longrightarrow> \<not> Pa) \<Longrightarrow> (P \<Longrightarrow> Pa) \<Longrightarrow> \<not> P"
  by (erule notE [THEN notI]) (erule meta_mp)


subsubsection {*Implication*}

lemma impE:
  assumes "P-->Q" "P" "Q ==> R"
  shows "R"
by (iprover intro: assms mp)

(* Reduces Q to P-->Q, allowing substitution in P. *)
lemma rev_mp: "[| P;  P --> Q |] ==> Q"
by (iprover intro: mp)

lemma contrapos_nn:
  assumes major: "~Q"
      and minor: "P==>Q"
  shows "~P"
by (iprover intro: notI minor major [THEN notE])

(*not used at all, but we already have the other 3 combinations *)
lemma contrapos_pn:
  assumes major: "Q"
      and minor: "P ==> ~Q"
  shows "~P"
by (iprover intro: notI minor major notE)

lemma not_sym: "t ~= s ==> s ~= t"
  by (erule contrapos_nn) (erule sym)

lemma eq_neq_eq_imp_neq: "[| x = a ; a ~= b; b = y |] ==> x ~= y"
  by (erule subst, erule ssubst, assumption)


subsubsection {*Existential quantifier*}

lemma exI: "P x ==> EX x::'a. P x"
apply (unfold Ex_def)
apply (iprover intro: allI allE impI mp)
done

lemma exE:
  assumes major: "EX x::'a. P(x)"
      and minor: "!!x. P(x) ==> Q"
  shows "Q"
apply (rule major [unfolded Ex_def, THEN spec, THEN mp])
apply (iprover intro: impI [THEN allI] minor)
done


subsubsection {*Conjunction*}

lemma conjI: "[| P; Q |] ==> P&Q"
apply (unfold and_def)
apply (iprover intro: impI [THEN allI] mp)
done

lemma conjunct1: "[| P & Q |] ==> P"
apply (unfold and_def)
apply (iprover intro: impI dest: spec mp)
done

lemma conjunct2: "[| P & Q |] ==> Q"
apply (unfold and_def)
apply (iprover intro: impI dest: spec mp)
done

lemma conjE:
  assumes major: "P&Q"
      and minor: "[| P; Q |] ==> R"
  shows "R"
apply (rule minor)
apply (rule major [THEN conjunct1])
apply (rule major [THEN conjunct2])
done

lemma context_conjI:
  assumes "P" "P ==> Q" shows "P & Q"
by (iprover intro: conjI assms)


subsubsection {*Disjunction*}

lemma disjI1: "P ==> P|Q"
apply (unfold or_def)
apply (iprover intro: allI impI mp)
done

lemma disjI2: "Q ==> P|Q"
apply (unfold or_def)
apply (iprover intro: allI impI mp)
done

lemma disjE:
  assumes major: "P|Q"
      and minorP: "P ==> R"
      and minorQ: "Q ==> R"
  shows "R"
by (iprover intro: minorP minorQ impI
                 major [unfolded or_def, THEN spec, THEN mp, THEN mp])


subsubsection {*Classical logic*}

lemma classical:
  assumes prem: "~P ==> P"
  shows "P"
apply (rule True_or_False [THEN disjE, THEN eqTrueE])
apply assumption
apply (rule notI [THEN prem, THEN eqTrueI])
apply (erule subst)
apply assumption
done

lemmas ccontr = FalseE [THEN classical]

(*notE with premises exchanged; it discharges ~R so that it can be used to
  make elimination rules*)
lemma rev_notE:
  assumes premp: "P"
      and premnot: "~R ==> ~P"
  shows "R"
apply (rule ccontr)
apply (erule notE [OF premnot premp])
done

(*Double negation law*)
lemma notnotD: "~~P ==> P"
apply (rule classical)
apply (erule notE)
apply assumption
done

lemma contrapos_pp:
  assumes p1: "Q"
      and p2: "~P ==> ~Q"
  shows "P"
by (iprover intro: classical p1 p2 notE)


subsubsection {*Unique existence*}

lemma ex1I:
  assumes "P a" "!!x. P(x) ==> x=a"
  shows "EX! x. P(x)"
by (unfold Ex1_def, iprover intro: assms exI conjI allI impI)

text{*Sometimes easier to use: the premises have no shared variables.  Safe!*}
lemma ex_ex1I:
  assumes ex_prem: "EX x. P(x)"
      and eq: "!!x y. [| P(x); P(y) |] ==> x=y"
  shows "EX! x. P(x)"
by (iprover intro: ex_prem [THEN exE] ex1I eq)

lemma ex1E:
  assumes major: "EX! x. P(x)"
      and minor: "!!x. [| P(x);  ALL y. P(y) --> y=x |] ==> R"
  shows "R"
apply (rule major [unfolded Ex1_def, THEN exE])
apply (erule conjE)
apply (iprover intro: minor)
done

lemma ex1_implies_ex: "EX! x. P x ==> EX x. P x"
apply (erule ex1E)
apply (rule exI)
apply assumption
done


subsubsection {*THE: definite description operator*}

lemma the_equality:
  assumes prema: "P a"
      and premx: "!!x. P x ==> x=a"
  shows "(THE x. P x) = a"
apply (rule trans [OF _ the_eq_trivial])
apply (rule_tac f = "The" in arg_cong)
apply (rule ext)
apply (rule iffI)
 apply (erule premx)
apply (erule ssubst, rule prema)
done

lemma theI:
  assumes "P a" and "!!x. P x ==> x=a"
  shows "P (THE x. P x)"
by (iprover intro: assms the_equality [THEN ssubst])

lemma theI': "EX! x. P x ==> P (THE x. P x)"
apply (erule ex1E)
apply (erule theI)
apply (erule allE)
apply (erule mp)
apply assumption
done

(*Easier to apply than theI: only one occurrence of P*)
lemma theI2:
  assumes "P a" "!!x. P x ==> x=a" "!!x. P x ==> Q x"
  shows "Q (THE x. P x)"
by (iprover intro: assms theI)

lemma the1I2: assumes "EX! x. P x" "\<And>x. P x \<Longrightarrow> Q x" shows "Q (THE x. P x)"
by(iprover intro:assms(2) theI2[where P=P and Q=Q] ex1E[OF assms(1)]
           elim:allE impE)

lemma the1_equality [elim?]: "[| EX!x. P x; P a |] ==> (THE x. P x) = a"
apply (rule the_equality)
apply  assumption
apply (erule ex1E)
apply (erule all_dupE)
apply (drule mp)
apply  assumption
apply (erule ssubst)
apply (erule allE)
apply (erule mp)
apply assumption
done

lemma the_sym_eq_trivial: "(THE y. x=y) = x"
apply (rule the_equality)
apply (rule refl)
apply (erule sym)
done


subsubsection {*Classical intro rules for disjunction and existential quantifiers*}

lemma disjCI:
  assumes "~Q ==> P" shows "P|Q"
apply (rule classical)
apply (iprover intro: assms disjI1 disjI2 notI elim: notE)
done

lemma excluded_middle: "~P | P"
by (iprover intro: disjCI)

text {*
  case distinction as a natural deduction rule.
  Note that @{term "~P"} is the second case, not the first
*}
lemma case_split [case_names True False]:
  assumes prem1: "P ==> Q"
      and prem2: "~P ==> Q"
  shows "Q"
apply (rule excluded_middle [THEN disjE])
apply (erule prem2)
apply (erule prem1)
done

(*Classical implies (-->) elimination. *)
lemma impCE:
  assumes major: "P-->Q"
      and minor: "~P ==> R" "Q ==> R"
  shows "R"
apply (rule excluded_middle [of P, THEN disjE])
apply (iprover intro: minor major [THEN mp])+
done

(*This version of --> elimination works on Q before P.  It works best for
  those cases in which P holds "almost everywhere".  Can't install as
  default: would break old proofs.*)
lemma impCE':
  assumes major: "P-->Q"
      and minor: "Q ==> R" "~P ==> R"
  shows "R"
apply (rule excluded_middle [of P, THEN disjE])
apply (iprover intro: minor major [THEN mp])+
done

(*Classical <-> elimination. *)
lemma iffCE:
  assumes major: "P=Q"
      and minor: "[| P; Q |] ==> R"  "[| ~P; ~Q |] ==> R"
  shows "R"
apply (rule major [THEN iffE])
apply (iprover intro: minor elim: impCE notE)
done

lemma exCI:
  assumes "ALL x. ~P(x) ==> P(a)"
  shows "EX x. P(x)"
apply (rule ccontr)
apply (iprover intro: assms exI allI notI notE [of "\<exists>x. P x"])
done


subsubsection {* Intuitionistic Reasoning *}

lemma impE':
  assumes 1: "P --> Q"
    and 2: "Q ==> R"
    and 3: "P --> Q ==> P"
  shows R
proof -
  from 3 and 1 have P .
  with 1 have Q by (rule impE)
  with 2 show R .
qed

lemma allE':
  assumes 1: "ALL x. P x"
    and 2: "P x ==> ALL x. P x ==> Q"
  shows Q
proof -
  from 1 have "P x" by (rule spec)
  from this and 1 show Q by (rule 2)
qed

lemma notE':
  assumes 1: "~ P"
    and 2: "~ P ==> P"
  shows R
proof -
  from 2 and 1 have P .
  with 1 show R by (rule notE)
qed

lemma TrueE: "True ==> P ==> P" .
lemma notFalseE: "~ False ==> P ==> P" .

lemmas [Pure.elim!] = disjE iffE FalseE conjE exE TrueE notFalseE
  and [Pure.intro!] = iffI conjI impI TrueI notI allI refl
  and [Pure.elim 2] = allE notE' impE'
  and [Pure.intro] = exI disjI2 disjI1

lemmas [trans] = trans
  and [sym] = sym not_sym
  and [Pure.elim?] = iffD1 iffD2 impE


subsubsection {* Atomizing meta-level connectives *}

axiomatization where
  eq_reflection: "x = y \<Longrightarrow> x \<equiv> y" (*admissible axiom*)

lemma atomize_all [atomize]: "(!!x. P x) == Trueprop (ALL x. P x)"
proof
  assume "!!x. P x"
  then show "ALL x. P x" ..
next
  assume "ALL x. P x"
  then show "!!x. P x" by (rule allE)
qed

lemma atomize_imp [atomize]: "(A ==> B) == Trueprop (A --> B)"
proof
  assume r: "A ==> B"
  show "A --> B" by (rule impI) (rule r)
next
  assume "A --> B" and A
  then show B by (rule mp)
qed

lemma atomize_not: "(A ==> False) == Trueprop (~A)"
proof
  assume r: "A ==> False"
  show "~A" by (rule notI) (rule r)
next
  assume "~A" and A
  then show False by (rule notE)
qed

lemma atomize_eq [atomize, code]: "(x == y) == Trueprop (x = y)"
proof
  assume "x == y"
  show "x = y" by (unfold `x == y`) (rule refl)
next
  assume "x = y"
  then show "x == y" by (rule eq_reflection)
qed

lemma atomize_conj [atomize]: "(A &&& B) == Trueprop (A & B)"
proof
  assume conj: "A &&& B"
  show "A & B"
  proof (rule conjI)
    from conj show A by (rule conjunctionD1)
    from conj show B by (rule conjunctionD2)
  qed
next
  assume conj: "A & B"
  show "A &&& B"
  proof -
    from conj show A ..
    from conj show B ..
  qed
qed

lemmas [symmetric, rulify] = atomize_all atomize_imp
  and [symmetric, defn] = atomize_all atomize_imp atomize_eq


subsubsection {* Atomizing elimination rules *}

setup AtomizeElim.setup

lemma atomize_exL[atomize_elim]: "(!!x. P x ==> Q) == ((EX x. P x) ==> Q)"
  by rule iprover+

lemma atomize_conjL[atomize_elim]: "(A ==> B ==> C) == (A & B ==> C)"
  by rule iprover+

lemma atomize_disjL[atomize_elim]: "((A ==> C) ==> (B ==> C) ==> C) == ((A | B ==> C) ==> C)"
  by rule iprover+

lemma atomize_elimL[atomize_elim]: "(!!B. (A ==> B) ==> B) == Trueprop A" ..


subsection {* Package setup *}

ML_file "Tools/hologic.ML"


subsubsection {* Sledgehammer setup *}

text {*
Theorems blacklisted to Sledgehammer. These theorems typically produce clauses
that are prolific (match too many equality or membership literals) and relate to
seldom-used facts. Some duplicate other rules.
*}

ML {*
structure No_ATPs = Named_Thms
(
  val name = @{binding no_atp}
  val description = "theorems that should be filtered out by Sledgehammer"
)
*}

setup {* No_ATPs.setup *}


subsubsection {* Classical Reasoner setup *}

lemma imp_elim: "P --> Q ==> (~ R ==> P) ==> (Q ==> R) ==> R"
  by (rule classical) iprover

lemma swap: "~ P ==> (~ R ==> P) ==> R"
  by (rule classical) iprover

lemma thin_refl:
  "\<And>X. \<lbrakk> x=x; PROP W \<rbrakk> \<Longrightarrow> PROP W" .

ML {*
structure Hypsubst = Hypsubst
(
  val dest_eq = HOLogic.dest_eq
  val dest_Trueprop = HOLogic.dest_Trueprop
  val dest_imp = HOLogic.dest_imp
  val eq_reflection = @{thm eq_reflection}
  val rev_eq_reflection = @{thm meta_eq_to_obj_eq}
  val imp_intr = @{thm impI}
  val rev_mp = @{thm rev_mp}
  val subst = @{thm subst}
  val sym = @{thm sym}
  val thin_refl = @{thm thin_refl};
);
open Hypsubst;

structure Classical = Classical
(
  val imp_elim = @{thm imp_elim}
  val not_elim = @{thm notE}
  val swap = @{thm swap}
  val classical = @{thm classical}
  val sizef = Drule.size_of_thm
  val hyp_subst_tacs = [Hypsubst.hyp_subst_tac]
);

structure Basic_Classical: BASIC_CLASSICAL = Classical; 
open Basic_Classical;
*}

setup Classical.setup

setup {*
let
  fun non_bool_eq (@{const_name HOL.eq}, Type (_, [T, _])) = T <> @{typ bool}
    | non_bool_eq _ = false;
  fun hyp_subst_tac' ctxt =
    SUBGOAL (fn (goal, i) =>
      if Term.exists_Const non_bool_eq goal
      then Hypsubst.hyp_subst_tac ctxt i
      else no_tac);
in
  Hypsubst.hypsubst_setup
  (*prevent substitution on bool*)
  #> Context_Rules.addSWrapper (fn ctxt => fn tac => hyp_subst_tac' ctxt ORELSE' tac)
end
*}

declare iffI [intro!]
  and notI [intro!]
  and impI [intro!]
  and disjCI [intro!]
  and conjI [intro!]
  and TrueI [intro!]
  and refl [intro!]

declare iffCE [elim!]
  and FalseE [elim!]
  and impCE [elim!]
  and disjE [elim!]
  and conjE [elim!]

declare ex_ex1I [intro!]
  and allI [intro!]
  and the_equality [intro]
  and exI [intro]

declare exE [elim!]
  allE [elim]

ML {* val HOL_cs = claset_of @{context} *}

lemma contrapos_np: "~ Q ==> (~ P ==> Q) ==> P"
  apply (erule swap)
  apply (erule (1) meta_mp)
  done

declare ex_ex1I [rule del, intro! 2]
  and ex1I [intro]

declare ext [intro]

lemmas [intro?] = ext
  and [elim?] = ex1_implies_ex

(*Better then ex1E for classical reasoner: needs no quantifier duplication!*)
lemma alt_ex1E [elim!]:
  assumes major: "\<exists>!x. P x"
      and prem: "\<And>x. \<lbrakk> P x; \<forall>y y'. P y \<and> P y' \<longrightarrow> y = y' \<rbrakk> \<Longrightarrow> R"
  shows R
apply (rule ex1E [OF major])
apply (rule prem)
apply (tactic {* ares_tac @{thms allI} 1 *})+
apply (tactic {* etac (Classical.dup_elim @{thm allE}) 1 *})
apply iprover
done

ML {*
  structure Blast = Blast
  (
    structure Classical = Classical
    val Trueprop_const = dest_Const @{const Trueprop}
    val equality_name = @{const_name HOL.eq}
    val not_name = @{const_name Not}
    val notE = @{thm notE}
    val ccontr = @{thm ccontr}
    val hyp_subst_tac = Hypsubst.blast_hyp_subst_tac
  );
  val blast_tac = Blast.blast_tac;
*}

setup Blast.setup


subsubsection {* Simplifier *}

lemma eta_contract_eq: "(%s. f s) = f" ..

lemma simp_thms:
  shows not_not: "(~ ~ P) = P"
  and Not_eq_iff: "((~P) = (~Q)) = (P = Q)"
  and
    "(P ~= Q) = (P = (~Q))"
    "(P | ~P) = True"    "(~P | P) = True"
    "(x = x) = True"
  and not_True_eq_False [code]: "(\<not> True) = False"
  and not_False_eq_True [code]: "(\<not> False) = True"
  and
    "(~P) ~= P"  "P ~= (~P)"
    "(True=P) = P"
  and eq_True: "(P = True) = P"
  and "(False=P) = (~P)"
  and eq_False: "(P = False) = (\<not> P)"
  and
    "(True --> P) = P"  "(False --> P) = True"
    "(P --> True) = True"  "(P --> P) = True"
    "(P --> False) = (~P)"  "(P --> ~P) = (~P)"
    "(P & True) = P"  "(True & P) = P"
    "(P & False) = False"  "(False & P) = False"
    "(P & P) = P"  "(P & (P & Q)) = (P & Q)"
    "(P & ~P) = False"    "(~P & P) = False"
    "(P | True) = True"  "(True | P) = True"
    "(P | False) = P"  "(False | P) = P"
    "(P | P) = P"  "(P | (P | Q)) = (P | Q)" and
    "(ALL x. P) = P"  "(EX x. P) = P"  "EX x. x=t"  "EX x. t=x"
  and
    "!!P. (EX x. x=t & P(x)) = P(t)"
    "!!P. (EX x. t=x & P(x)) = P(t)"
    "!!P. (ALL x. x=t --> P(x)) = P(t)"
    "!!P. (ALL x. t=x --> P(x)) = P(t)"
  by (blast, blast, blast, blast, blast, iprover+)

lemma disj_absorb: "(A | A) = A"
  by blast

lemma disj_left_absorb: "(A | (A | B)) = (A | B)"
  by blast

lemma conj_absorb: "(A & A) = A"
  by blast

lemma conj_left_absorb: "(A & (A & B)) = (A & B)"
  by blast

lemma eq_ac:
  shows eq_commute: "(a=b) = (b=a)"
    and eq_left_commute: "(P=(Q=R)) = (Q=(P=R))"
    and eq_assoc: "((P=Q)=R) = (P=(Q=R))" by (iprover, blast+)
lemma neq_commute: "(a~=b) = (b~=a)" by iprover

lemma conj_comms:
  shows conj_commute: "(P&Q) = (Q&P)"
    and conj_left_commute: "(P&(Q&R)) = (Q&(P&R))" by iprover+
lemma conj_assoc: "((P&Q)&R) = (P&(Q&R))" by iprover

lemmas conj_ac = conj_commute conj_left_commute conj_assoc

lemma disj_comms:
  shows disj_commute: "(P|Q) = (Q|P)"
    and disj_left_commute: "(P|(Q|R)) = (Q|(P|R))" by iprover+
lemma disj_assoc: "((P|Q)|R) = (P|(Q|R))" by iprover

lemmas disj_ac = disj_commute disj_left_commute disj_assoc

lemma conj_disj_distribL: "(P&(Q|R)) = (P&Q | P&R)" by iprover
lemma conj_disj_distribR: "((P|Q)&R) = (P&R | Q&R)" by iprover

lemma disj_conj_distribL: "(P|(Q&R)) = ((P|Q) & (P|R))" by iprover
lemma disj_conj_distribR: "((P&Q)|R) = ((P|R) & (Q|R))" by iprover

lemma imp_conjR: "(P --> (Q&R)) = ((P-->Q) & (P-->R))" by iprover
lemma imp_conjL: "((P&Q) -->R)  = (P --> (Q --> R))" by iprover
lemma imp_disjL: "((P|Q) --> R) = ((P-->R)&(Q-->R))" by iprover

text {* These two are specialized, but @{text imp_disj_not1} is useful in @{text "Auth/Yahalom"}. *}
lemma imp_disj_not1: "(P --> Q | R) = (~Q --> P --> R)" by blast
lemma imp_disj_not2: "(P --> Q | R) = (~R --> P --> Q)" by blast

lemma imp_disj1: "((P-->Q)|R) = (P--> Q|R)" by blast
lemma imp_disj2: "(Q|(P-->R)) = (P--> Q|R)" by blast

lemma imp_cong: "(P = P') ==> (P' ==> (Q = Q')) ==> ((P --> Q) = (P' --> Q'))"
  by iprover

lemma de_Morgan_disj: "(~(P | Q)) = (~P & ~Q)" by iprover
lemma de_Morgan_conj: "(~(P & Q)) = (~P | ~Q)" by blast
lemma not_imp: "(~(P --> Q)) = (P & ~Q)" by blast
lemma not_iff: "(P~=Q) = (P = (~Q))" by blast
lemma disj_not1: "(~P | Q) = (P --> Q)" by blast
lemma disj_not2: "(P | ~Q) = (Q --> P)"  -- {* changes orientation :-( *}
  by blast
lemma imp_conv_disj: "(P --> Q) = ((~P) | Q)" by blast

lemma iff_conv_conj_imp: "(P = Q) = ((P --> Q) & (Q --> P))" by iprover


lemma cases_simp: "((P --> Q) & (~P --> Q)) = Q"
  -- {* Avoids duplication of subgoals after @{text split_if}, when the true and false *}
  -- {* cases boil down to the same thing. *}
  by blast

lemma not_all: "(~ (! x. P(x))) = (? x.~P(x))" by blast
lemma imp_all: "((! x. P x) --> Q) = (? x. P x --> Q)" by blast
lemma not_ex: "(~ (? x. P(x))) = (! x.~P(x))" by iprover
lemma imp_ex: "((? x. P x) --> Q) = (! x. P x --> Q)" by iprover
lemma all_not_ex: "(ALL x. P x) = (~ (EX x. ~ P x ))" by blast

declare All_def [no_atp]

lemma ex_disj_distrib: "(? x. P(x) | Q(x)) = ((? x. P(x)) | (? x. Q(x)))" by iprover
lemma all_conj_distrib: "(!x. P(x) & Q(x)) = ((! x. P(x)) & (! x. Q(x)))" by iprover

text {*
  \medskip The @{text "&"} congruence rule: not included by default!
  May slow rewrite proofs down by as much as 50\% *}

lemma conj_cong:
    "(P = P') ==> (P' ==> (Q = Q')) ==> ((P & Q) = (P' & Q'))"
  by iprover

lemma rev_conj_cong:
    "(Q = Q') ==> (Q' ==> (P = P')) ==> ((P & Q) = (P' & Q'))"
  by iprover

text {* The @{text "|"} congruence rule: not included by default! *}

lemma disj_cong:
    "(P = P') ==> (~P' ==> (Q = Q')) ==> ((P | Q) = (P' | Q'))"
  by blast


text {* \medskip if-then-else rules *}

lemma if_True [code]: "(if True then x else y) = x"
  by (unfold If_def) blast

lemma if_False [code]: "(if False then x else y) = y"
  by (unfold If_def) blast

lemma if_P: "P ==> (if P then x else y) = x"
  by (unfold If_def) blast

lemma if_not_P: "~P ==> (if P then x else y) = y"
  by (unfold If_def) blast

lemma split_if: "P (if Q then x else y) = ((Q --> P(x)) & (~Q --> P(y)))"
  apply (rule case_split [of Q])
   apply (simplesubst if_P)
    prefer 3 apply (simplesubst if_not_P, blast+)
  done

lemma split_if_asm: "P (if Q then x else y) = (~((Q & ~P x) | (~Q & ~P y)))"
by (simplesubst split_if, blast)

lemmas if_splits [no_atp] = split_if split_if_asm

lemma if_cancel: "(if c then x else x) = x"
by (simplesubst split_if, blast)

lemma if_eq_cancel: "(if x = y then y else x) = x"
by (simplesubst split_if, blast)

lemma if_bool_eq_conj:
"(if P then Q else R) = ((P-->Q) & (~P-->R))"
  -- {* This form is useful for expanding @{text "if"}s on the RIGHT of the @{text "==>"} symbol. *}
  by (rule split_if)

lemma if_bool_eq_disj: "(if P then Q else R) = ((P&Q) | (~P&R))"
  -- {* And this form is useful for expanding @{text "if"}s on the LEFT. *}
  apply (simplesubst split_if, blast)
  done

lemma Eq_TrueI: "P ==> P == True" by (unfold atomize_eq) iprover
lemma Eq_FalseI: "~P ==> P == False" by (unfold atomize_eq) iprover

text {* \medskip let rules for simproc *}

lemma Let_folded: "f x \<equiv> g x \<Longrightarrow>  Let x f \<equiv> Let x g"
  by (unfold Let_def)

lemma Let_unfold: "f x \<equiv> g \<Longrightarrow>  Let x f \<equiv> g"
  by (unfold Let_def)

text {*
  The following copy of the implication operator is useful for
  fine-tuning congruence rules.  It instructs the simplifier to simplify
  its premise.
*}

definition simp_implies :: "[prop, prop] => prop"  (infixr "=simp=>" 1) where
  "simp_implies \<equiv> op ==>"

lemma simp_impliesI:
  assumes PQ: "(PROP P \<Longrightarrow> PROP Q)"
  shows "PROP P =simp=> PROP Q"
  apply (unfold simp_implies_def)
  apply (rule PQ)
  apply assumption
  done

lemma simp_impliesE:
  assumes PQ: "PROP P =simp=> PROP Q"
  and P: "PROP P"
  and QR: "PROP Q \<Longrightarrow> PROP R"
  shows "PROP R"
  apply (rule QR)
  apply (rule PQ [unfolded simp_implies_def])
  apply (rule P)
  done

lemma simp_implies_cong:
  assumes PP' :"PROP P == PROP P'"
  and P'QQ': "PROP P' ==> (PROP Q == PROP Q')"
  shows "(PROP P =simp=> PROP Q) == (PROP P' =simp=> PROP Q')"
proof (unfold simp_implies_def, rule equal_intr_rule)
  assume PQ: "PROP P \<Longrightarrow> PROP Q"
  and P': "PROP P'"
  from PP' [symmetric] and P' have "PROP P"
    by (rule equal_elim_rule1)
  then have "PROP Q" by (rule PQ)
  with P'QQ' [OF P'] show "PROP Q'" by (rule equal_elim_rule1)
next
  assume P'Q': "PROP P' \<Longrightarrow> PROP Q'"
  and P: "PROP P"
  from PP' and P have P': "PROP P'" by (rule equal_elim_rule1)
  then have "PROP Q'" by (rule P'Q')
  with P'QQ' [OF P', symmetric] show "PROP Q"
    by (rule equal_elim_rule1)
qed

lemma uncurry:
  assumes "P \<longrightarrow> Q \<longrightarrow> R"
  shows "P \<and> Q \<longrightarrow> R"
  using assms by blast

lemma iff_allI:
  assumes "\<And>x. P x = Q x"
  shows "(\<forall>x. P x) = (\<forall>x. Q x)"
  using assms by blast

lemma iff_exI:
  assumes "\<And>x. P x = Q x"
  shows "(\<exists>x. P x) = (\<exists>x. Q x)"
  using assms by blast

lemma all_comm:
  "(\<forall>x y. P x y) = (\<forall>y x. P x y)"
  by blast

lemma ex_comm:
  "(\<exists>x y. P x y) = (\<exists>y x. P x y)"
  by blast

ML_file "Tools/simpdata.ML"
ML {* open Simpdata *}

setup {* map_theory_simpset (put_simpset HOL_basic_ss) *}

simproc_setup defined_Ex ("EX x. P x") = {* fn _ => Quantifier1.rearrange_ex *}
simproc_setup defined_All ("ALL x. P x") = {* fn _ => Quantifier1.rearrange_all *}

setup {*
  Simplifier.method_setup Splitter.split_modifiers
  #> Splitter.setup
  #> clasimp_setup
  #> EqSubst.setup
*}

text {* Simproc for proving @{text "(y = x) == False"} from premise @{text "~(x = y)"}: *}

simproc_setup neq ("x = y") = {* fn _ =>
let
  val neq_to_EQ_False = @{thm not_sym} RS @{thm Eq_FalseI};
  fun is_neq eq lhs rhs thm =
    (case Thm.prop_of thm of
      _ $ (Not $ (eq' $ l' $ r')) =>
        Not = HOLogic.Not andalso eq' = eq andalso
        r' aconv lhs andalso l' aconv rhs
    | _ => false);
  fun proc ss ct =
    (case Thm.term_of ct of
      eq $ lhs $ rhs =>
        (case find_first (is_neq eq lhs rhs) (Simplifier.prems_of ss) of
          SOME thm => SOME (thm RS neq_to_EQ_False)
        | NONE => NONE)
     | _ => NONE);
in proc end;
*}

simproc_setup let_simp ("Let x f") = {*
let
  val (f_Let_unfold, x_Let_unfold) =
    let val [(_ $ (f $ x) $ _)] = prems_of @{thm Let_unfold}
    in (cterm_of @{theory} f, cterm_of @{theory} x) end
  val (f_Let_folded, x_Let_folded) =
    let val [(_ $ (f $ x) $ _)] = prems_of @{thm Let_folded}
    in (cterm_of @{theory} f, cterm_of @{theory} x) end;
  val g_Let_folded =
    let val [(_ $ _ $ (g $ _))] = prems_of @{thm Let_folded}
    in cterm_of @{theory} g end;
  fun count_loose (Bound i) k = if i >= k then 1 else 0
    | count_loose (s $ t) k = count_loose s k + count_loose t k
    | count_loose (Abs (_, _, t)) k = count_loose  t (k + 1)
    | count_loose _ _ = 0;
  fun is_trivial_let (Const (@{const_name Let}, _) $ x $ t) =
   case t
    of Abs (_, _, t') => count_loose t' 0 <= 1
     | _ => true;
in fn _ => fn ctxt => fn ct => if is_trivial_let (Thm.term_of ct)
  then SOME @{thm Let_def} (*no or one ocurrence of bound variable*)
  else let (*Norbert Schirmer's case*)
    val thy = Proof_Context.theory_of ctxt;
    val t = Thm.term_of ct;
    val ([t'], ctxt') = Variable.import_terms false [t] ctxt;
  in Option.map (hd o Variable.export ctxt' ctxt o single)
    (case t' of Const (@{const_name Let},_) $ x $ f => (* x and f are already in normal form *)
      if is_Free x orelse is_Bound x orelse is_Const x
      then SOME @{thm Let_def}
      else
        let
          val n = case f of (Abs (x, _, _)) => x | _ => "x";
          val cx = cterm_of thy x;
          val {T = xT, ...} = rep_cterm cx;
          val cf = cterm_of thy f;
          val fx_g = Simplifier.rewrite ctxt (Thm.apply cf cx);
          val (_ $ _ $ g) = prop_of fx_g;
          val g' = abstract_over (x,g);
          val abs_g'= Abs (n,xT,g');
        in (if (g aconv g')
             then
                let
                  val rl =
                    cterm_instantiate [(f_Let_unfold, cf), (x_Let_unfold, cx)] @{thm Let_unfold};
                in SOME (rl OF [fx_g]) end
             else if (Envir.beta_eta_contract f) aconv (Envir.beta_eta_contract abs_g') then NONE (*avoid identity conversion*)
             else let
                   val g'x = abs_g'$x;
                   val g_g'x = Thm.symmetric (Thm.beta_conversion false (cterm_of thy g'x));
                   val rl = cterm_instantiate
                             [(f_Let_folded, cterm_of thy f), (x_Let_folded, cx),
                              (g_Let_folded, cterm_of thy abs_g')]
                             @{thm Let_folded};
                 in SOME (rl OF [Thm.transitive fx_g g_g'x])
                 end)
        end
    | _ => NONE)
  end
end *}

lemma True_implies_equals: "(True \<Longrightarrow> PROP P) \<equiv> PROP P"
proof
  assume "True \<Longrightarrow> PROP P"
  from this [OF TrueI] show "PROP P" .
next
  assume "PROP P"
  then show "PROP P" .
qed

lemma ex_simps:
  "!!P Q. (EX x. P x & Q)   = ((EX x. P x) & Q)"
  "!!P Q. (EX x. P & Q x)   = (P & (EX x. Q x))"
  "!!P Q. (EX x. P x | Q)   = ((EX x. P x) | Q)"
  "!!P Q. (EX x. P | Q x)   = (P | (EX x. Q x))"
  "!!P Q. (EX x. P x --> Q) = ((ALL x. P x) --> Q)"
  "!!P Q. (EX x. P --> Q x) = (P --> (EX x. Q x))"
  -- {* Miniscoping: pushing in existential quantifiers. *}
  by (iprover | blast)+

lemma all_simps:
  "!!P Q. (ALL x. P x & Q)   = ((ALL x. P x) & Q)"
  "!!P Q. (ALL x. P & Q x)   = (P & (ALL x. Q x))"
  "!!P Q. (ALL x. P x | Q)   = ((ALL x. P x) | Q)"
  "!!P Q. (ALL x. P | Q x)   = (P | (ALL x. Q x))"
  "!!P Q. (ALL x. P x --> Q) = ((EX x. P x) --> Q)"
  "!!P Q. (ALL x. P --> Q x) = (P --> (ALL x. Q x))"
  -- {* Miniscoping: pushing in universal quantifiers. *}
  by (iprover | blast)+

lemmas [simp] =
  triv_forall_equality (*prunes params*)
  True_implies_equals  (*prune asms `True'*)
  if_True
  if_False
  if_cancel
  if_eq_cancel
  imp_disjL
  (*In general it seems wrong to add distributive laws by default: they
    might cause exponential blow-up.  But imp_disjL has been in for a while
    and cannot be removed without affecting existing proofs.  Moreover,
    rewriting by "(P|Q --> R) = ((P-->R)&(Q-->R))" might be justified on the
    grounds that it allows simplification of R in the two cases.*)
  conj_assoc
  disj_assoc
  de_Morgan_conj
  de_Morgan_disj
  imp_disj1
  imp_disj2
  not_imp
  disj_not1
  not_all
  not_ex
  cases_simp
  the_eq_trivial
  the_sym_eq_trivial
  ex_simps
  all_simps
  simp_thms

lemmas [cong] = imp_cong simp_implies_cong
lemmas [split] = split_if

ML {* val HOL_ss = simpset_of @{context} *}

text {* Simplifies x assuming c and y assuming ~c *}
lemma if_cong:
  assumes "b = c"
      and "c \<Longrightarrow> x = u"
      and "\<not> c \<Longrightarrow> y = v"
  shows "(if b then x else y) = (if c then u else v)"
  using assms by simp

text {* Prevents simplification of x and y:
  faster and allows the execution of functional programs. *}
lemma if_weak_cong [cong]:
  assumes "b = c"
  shows "(if b then x else y) = (if c then x else y)"
  using assms by (rule arg_cong)

text {* Prevents simplification of t: much faster *}
lemma let_weak_cong:
  assumes "a = b"
  shows "(let x = a in t x) = (let x = b in t x)"
  using assms by (rule arg_cong)

text {* To tidy up the result of a simproc.  Only the RHS will be simplified. *}
lemma eq_cong2:
  assumes "u = u'"
  shows "(t \<equiv> u) \<equiv> (t \<equiv> u')"
  using assms by simp

lemma if_distrib:
  "f (if c then x else y) = (if c then f x else f y)"
  by simp

text{*As a simplification rule, it replaces all function equalities by
  first-order equalities.*}
lemma fun_eq_iff: "f = g \<longleftrightarrow> (\<forall>x. f x = g x)"
  by auto


subsubsection {* Generic cases and induction *}

text {* Rule projections: *}

ML {*
structure Project_Rule = Project_Rule
(
  val conjunct1 = @{thm conjunct1}
  val conjunct2 = @{thm conjunct2}
  val mp = @{thm mp}
)
*}

definition induct_forall where
  "induct_forall P == \<forall>x. P x"

definition induct_implies where
  "induct_implies A B == A \<longrightarrow> B"

definition induct_equal where
  "induct_equal x y == x = y"

definition induct_conj where
  "induct_conj A B == A \<and> B"

definition induct_true where
  "induct_true == True"

definition induct_false where
  "induct_false == False"

lemma induct_forall_eq: "(!!x. P x) == Trueprop (induct_forall (\<lambda>x. P x))"
  by (unfold atomize_all induct_forall_def)

lemma induct_implies_eq: "(A ==> B) == Trueprop (induct_implies A B)"
  by (unfold atomize_imp induct_implies_def)

lemma induct_equal_eq: "(x == y) == Trueprop (induct_equal x y)"
  by (unfold atomize_eq induct_equal_def)

lemma induct_conj_eq: "(A &&& B) == Trueprop (induct_conj A B)"
  by (unfold atomize_conj induct_conj_def)

lemmas induct_atomize' = induct_forall_eq induct_implies_eq induct_conj_eq
lemmas induct_atomize = induct_atomize' induct_equal_eq
lemmas induct_rulify' [symmetric] = induct_atomize'
lemmas induct_rulify [symmetric] = induct_atomize
lemmas induct_rulify_fallback =
  induct_forall_def induct_implies_def induct_equal_def induct_conj_def
  induct_true_def induct_false_def


lemma induct_forall_conj: "induct_forall (\<lambda>x. induct_conj (A x) (B x)) =
    induct_conj (induct_forall A) (induct_forall B)"
  by (unfold induct_forall_def induct_conj_def) iprover

lemma induct_implies_conj: "induct_implies C (induct_conj A B) =
    induct_conj (induct_implies C A) (induct_implies C B)"
  by (unfold induct_implies_def induct_conj_def) iprover

lemma induct_conj_curry: "(induct_conj A B ==> PROP C) == (A ==> B ==> PROP C)"
proof
  assume r: "induct_conj A B ==> PROP C" and A B
  show "PROP C" by (rule r) (simp add: induct_conj_def `A` `B`)
next
  assume r: "A ==> B ==> PROP C" and "induct_conj A B"
  show "PROP C" by (rule r) (simp_all add: `induct_conj A B` [unfolded induct_conj_def])
qed

lemmas induct_conj = induct_forall_conj induct_implies_conj induct_conj_curry

lemma induct_trueI: "induct_true"
  by (simp add: induct_true_def)

text {* Method setup. *}

ML {*
structure Induct = Induct
(
  val cases_default = @{thm case_split}
  val atomize = @{thms induct_atomize}
  val rulify = @{thms induct_rulify'}
  val rulify_fallback = @{thms induct_rulify_fallback}
  val equal_def = @{thm induct_equal_def}
  fun dest_def (Const (@{const_name induct_equal}, _) $ t $ u) = SOME (t, u)
    | dest_def _ = NONE
  val trivial_tac = match_tac @{thms induct_trueI}
)
*}

ML_file "~~/src/Tools/induction.ML"

setup {*
  Induct.setup #> Induction.setup #>
  Context.theory_map (Induct.map_simpset (fn ss => ss
    addsimprocs
      [Simplifier.simproc_global @{theory} "swap_induct_false"
         ["induct_false ==> PROP P ==> PROP Q"]
         (fn _ =>
            (fn _ $ (P as _ $ @{const induct_false}) $ (_ $ Q $ _) =>
                  if P <> Q then SOME Drule.swap_prems_eq else NONE
              | _ => NONE)),
       Simplifier.simproc_global @{theory} "induct_equal_conj_curry"
         ["induct_conj P Q ==> PROP R"]
         (fn _ =>
            (fn _ $ (_ $ P) $ _ =>
                let
                  fun is_conj (@{const induct_conj} $ P $ Q) =
                        is_conj P andalso is_conj Q
                    | is_conj (Const (@{const_name induct_equal}, _) $ _ $ _) = true
                    | is_conj @{const induct_true} = true
                    | is_conj @{const induct_false} = true
                    | is_conj _ = false
                in if is_conj P then SOME @{thm induct_conj_curry} else NONE end
              | _ => NONE))]
    |> Simplifier.set_mksimps (fn ss => Simpdata.mksimps Simpdata.mksimps_pairs ss #>
      map (rewrite_rule (map Thm.symmetric @{thms induct_rulify_fallback})))))
*}

text {* Pre-simplification of induction and cases rules *}

lemma [induct_simp]: "(!!x. induct_equal x t ==> PROP P x) == PROP P t"
  unfolding induct_equal_def
proof
  assume R: "!!x. x = t ==> PROP P x"
  show "PROP P t" by (rule R [OF refl])
next
  fix x assume "PROP P t" "x = t"
  then show "PROP P x" by simp
qed

lemma [induct_simp]: "(!!x. induct_equal t x ==> PROP P x) == PROP P t"
  unfolding induct_equal_def
proof
  assume R: "!!x. t = x ==> PROP P x"
  show "PROP P t" by (rule R [OF refl])
next
  fix x assume "PROP P t" "t = x"
  then show "PROP P x" by simp
qed

lemma [induct_simp]: "(induct_false ==> P) == Trueprop induct_true"
  unfolding induct_false_def induct_true_def
  by (iprover intro: equal_intr_rule)

lemma [induct_simp]: "(induct_true ==> PROP P) == PROP P"
  unfolding induct_true_def
proof
  assume R: "True \<Longrightarrow> PROP P"
  from TrueI show "PROP P" by (rule R)
next
  assume "PROP P"
  then show "PROP P" .
qed

lemma [induct_simp]: "(PROP P ==> induct_true) == Trueprop induct_true"
  unfolding induct_true_def
  by (iprover intro: equal_intr_rule)

lemma [induct_simp]: "(!!x. induct_true) == Trueprop induct_true"
  unfolding induct_true_def
  by (iprover intro: equal_intr_rule)

lemma [induct_simp]: "induct_implies induct_true P == P"
  by (simp add: induct_implies_def induct_true_def)

lemma [induct_simp]: "(x = x) = True" 
  by (rule simp_thms)

hide_const induct_forall induct_implies induct_equal induct_conj induct_true induct_false

ML_file "~~/src/Tools/induct_tacs.ML"
setup Induct_Tacs.setup


subsubsection {* Coherent logic *}

ML {*
structure Coherent = Coherent
(
  val atomize_elimL = @{thm atomize_elimL}
  val atomize_exL = @{thm atomize_exL}
  val atomize_conjL = @{thm atomize_conjL}
  val atomize_disjL = @{thm atomize_disjL}
  val operator_names =
    [@{const_name HOL.disj}, @{const_name HOL.conj}, @{const_name Ex}]
);
*}

setup Coherent.setup


subsubsection {* Reorienting equalities *}

ML {*
signature REORIENT_PROC =
sig
  val add : (term -> bool) -> theory -> theory
  val proc : morphism -> Proof.context -> cterm -> thm option
end;

structure Reorient_Proc : REORIENT_PROC =
struct
  structure Data = Theory_Data
  (
    type T = ((term -> bool) * stamp) list;
    val empty = [];
    val extend = I;
    fun merge data : T = Library.merge (eq_snd op =) data;
  );
  fun add m = Data.map (cons (m, stamp ()));
  fun matches thy t = exists (fn (m, _) => m t) (Data.get thy);

  val meta_reorient = @{thm eq_commute [THEN eq_reflection]};
  fun proc phi ctxt ct =
    let
      val thy = Proof_Context.theory_of ctxt;
    in
      case Thm.term_of ct of
        (_ $ t $ u) => if matches thy u then NONE else SOME meta_reorient
      | _ => NONE
    end;
end;
*}


subsection {* Other simple lemmas and lemma duplicates *}

lemma ex1_eq [iff]: "EX! x. x = t" "EX! x. t = x"
  by blast+

lemma choice_eq: "(ALL x. EX! y. P x y) = (EX! f. ALL x. P x (f x))"
  apply (rule iffI)
  apply (rule_tac a = "%x. THE y. P x y" in ex1I)
  apply (fast dest!: theI')
  apply (fast intro: the1_equality [symmetric])
  apply (erule ex1E)
  apply (rule allI)
  apply (rule ex1I)
  apply (erule spec)
  apply (erule_tac x = "%z. if z = x then y else f z" in allE)
  apply (erule impE)
  apply (rule allI)
  apply (case_tac "xa = x")
  apply (drule_tac [3] x = x in fun_cong, simp_all)
  done

lemmas eq_sym_conv = eq_commute

lemma nnf_simps:
  "(\<not>(P \<and> Q)) = (\<not> P \<or> \<not> Q)" "(\<not> (P \<or> Q)) = (\<not> P \<and> \<not>Q)" "(P \<longrightarrow> Q) = (\<not>P \<or> Q)" 
  "(P = Q) = ((P \<and> Q) \<or> (\<not>P \<and> \<not> Q))" "(\<not>(P = Q)) = ((P \<and> \<not> Q) \<or> (\<not>P \<and> Q))" 
  "(\<not> \<not>(P)) = P"
by blast+

subsection {* Basic ML bindings *}

ML {*
val FalseE = @{thm FalseE}
val Let_def = @{thm Let_def}
val TrueI = @{thm TrueI}
val allE = @{thm allE}
val allI = @{thm allI}
val all_dupE = @{thm all_dupE}
val arg_cong = @{thm arg_cong}
val box_equals = @{thm box_equals}
val ccontr = @{thm ccontr}
val classical = @{thm classical}
val conjE = @{thm conjE}
val conjI = @{thm conjI}
val conjunct1 = @{thm conjunct1}
val conjunct2 = @{thm conjunct2}
val disjCI = @{thm disjCI}
val disjE = @{thm disjE}
val disjI1 = @{thm disjI1}
val disjI2 = @{thm disjI2}
val eq_reflection = @{thm eq_reflection}
val ex1E = @{thm ex1E}
val ex1I = @{thm ex1I}
val ex1_implies_ex = @{thm ex1_implies_ex}
val exE = @{thm exE}
val exI = @{thm exI}
val excluded_middle = @{thm excluded_middle}
val ext = @{thm ext}
val fun_cong = @{thm fun_cong}
val iffD1 = @{thm iffD1}
val iffD2 = @{thm iffD2}
val iffI = @{thm iffI}
val impE = @{thm impE}
val impI = @{thm impI}
val meta_eq_to_obj_eq = @{thm meta_eq_to_obj_eq}
val mp = @{thm mp}
val notE = @{thm notE}
val notI = @{thm notI}
val not_all = @{thm not_all}
val not_ex = @{thm not_ex}
val not_iff = @{thm not_iff}
val not_not = @{thm not_not}
val not_sym = @{thm not_sym}
val refl = @{thm refl}
val rev_mp = @{thm rev_mp}
val spec = @{thm spec}
val ssubst = @{thm ssubst}
val subst = @{thm subst}
val sym = @{thm sym}
val trans = @{thm trans}
*}

ML_file "Tools/cnf_funcs.ML"

subsection {* Code generator setup *}

subsubsection {* Generic code generator preprocessor setup *}

lemma conj_left_cong:
  "P \<longleftrightarrow> Q \<Longrightarrow> P \<and> R \<longleftrightarrow> Q \<and> R"
  by (fact arg_cong)

lemma disj_left_cong:
  "P \<longleftrightarrow> Q \<Longrightarrow> P \<or> R \<longleftrightarrow> Q \<or> R"
  by (fact arg_cong)

setup {*
  Code_Preproc.map_pre (put_simpset HOL_basic_ss)
  #> Code_Preproc.map_post (put_simpset HOL_basic_ss)
  #> Code_Simp.map_ss (put_simpset HOL_basic_ss
    #> Simplifier.add_cong @{thm conj_left_cong} #> Simplifier.add_cong @{thm disj_left_cong})
*}


subsubsection {* Equality *}

class equal =
  fixes equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes equal_eq: "equal x y \<longleftrightarrow> x = y"
begin

lemma equal: "equal = (op =)"
  by (rule ext equal_eq)+

lemma equal_refl: "equal x x \<longleftrightarrow> True"
  unfolding equal by rule+

lemma eq_equal: "(op =) \<equiv> equal"
  by (rule eq_reflection) (rule ext, rule ext, rule sym, rule equal_eq)

end

declare eq_equal [symmetric, code_post]
declare eq_equal [code]

setup {*
  Code_Preproc.map_pre (fn ctxt =>
    ctxt addsimprocs [Simplifier.simproc_global_i @{theory} "equal" [@{term HOL.eq}]
      (fn _ => fn Const (_, Type ("fun", [Type _, _])) => SOME @{thm eq_equal} | _ => NONE)])
*}


subsubsection {* Generic code generator foundation *}

text {* Datatype @{typ bool} *}

code_datatype True False

lemma [code]:
  shows "False \<and> P \<longleftrightarrow> False"
    and "True \<and> P \<longleftrightarrow> P"
    and "P \<and> False \<longleftrightarrow> False"
    and "P \<and> True \<longleftrightarrow> P" by simp_all

lemma [code]:
  shows "False \<or> P \<longleftrightarrow> P"
    and "True \<or> P \<longleftrightarrow> True"
    and "P \<or> False \<longleftrightarrow> P"
    and "P \<or> True \<longleftrightarrow> True" by simp_all

lemma [code]:
  shows "(False \<longrightarrow> P) \<longleftrightarrow> True"
    and "(True \<longrightarrow> P) \<longleftrightarrow> P"
    and "(P \<longrightarrow> False) \<longleftrightarrow> \<not> P"
    and "(P \<longrightarrow> True) \<longleftrightarrow> True" by simp_all

text {* More about @{typ prop} *}

lemma [code nbe]:
  shows "(True \<Longrightarrow> PROP Q) \<equiv> PROP Q" 
    and "(PROP Q \<Longrightarrow> True) \<equiv> Trueprop True"
    and "(P \<Longrightarrow> R) \<equiv> Trueprop (P \<longrightarrow> R)" by (auto intro!: equal_intr_rule)

lemma Trueprop_code [code]:
  "Trueprop True \<equiv> Code_Generator.holds"
  by (auto intro!: equal_intr_rule holds)

declare Trueprop_code [symmetric, code_post]

text {* Equality *}

declare simp_thms(6) [code nbe]

instantiation itself :: (type) equal
begin

definition equal_itself :: "'a itself \<Rightarrow> 'a itself \<Rightarrow> bool" where
  "equal_itself x y \<longleftrightarrow> x = y"

instance proof
qed (fact equal_itself_def)

end

lemma equal_itself_code [code]:
  "equal TYPE('a) TYPE('a) \<longleftrightarrow> True"
  by (simp add: equal)

setup {*
  Sign.add_const_constraint (@{const_name equal}, SOME @{typ "'a\<Colon>type \<Rightarrow> 'a \<Rightarrow> bool"})
*}

lemma equal_alias_cert: "OFCLASS('a, equal_class) \<equiv> ((op = :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<equiv> equal)" (is "?ofclass \<equiv> ?equal")
proof
  assume "PROP ?ofclass"
  show "PROP ?equal"
    by (tactic {* ALLGOALS (rtac (Thm.unconstrainT @{thm eq_equal})) *})
      (fact `PROP ?ofclass`)
next
  assume "PROP ?equal"
  show "PROP ?ofclass" proof
  qed (simp add: `PROP ?equal`)
qed
  
setup {*
  Sign.add_const_constraint (@{const_name equal}, SOME @{typ "'a\<Colon>equal \<Rightarrow> 'a \<Rightarrow> bool"})
*}

setup {*
  Nbe.add_const_alias @{thm equal_alias_cert}
*}

text {* Cases *}

lemma Let_case_cert:
  assumes "CASE \<equiv> (\<lambda>x. Let x f)"
  shows "CASE x \<equiv> f x"
  using assms by simp_all

setup {*
  Code.add_case @{thm Let_case_cert}
  #> Code.add_undefined @{const_name undefined}
*}

code_abort undefined


subsubsection {* Generic code generator target languages *}

text {* type @{typ bool} *}

code_printing
  type_constructor bool \<rightharpoonup>
    (SML) "bool" and (OCaml) "bool" and (Haskell) "Bool" and (Scala) "Boolean"
| constant True \<rightharpoonup>
    (SML) "true" and (OCaml) "true" and (Haskell) "True" and (Scala) "true"
| constant False \<rightharpoonup>
    (SML) "false" and (OCaml) "false" and (Haskell) "False" and (Scala) "false" 

code_reserved SML
  bool true false

code_reserved OCaml
  bool

code_reserved Scala
  Boolean

code_printing
  constant Not \<rightharpoonup>
    (SML) "not" and (OCaml) "not" and (Haskell) "not" and (Scala) "'! _"
| constant HOL.conj \<rightharpoonup>
    (SML) infixl 1 "andalso" and (OCaml) infixl 3 "&&" and (Haskell) infixr 3 "&&" and (Scala) infixl 3 "&&"
| constant HOL.disj \<rightharpoonup>
    (SML) infixl 0 "orelse" and (OCaml) infixl 2 "||" and (Haskell) infixl 2 "||" and (Scala) infixl 1 "||"
| constant HOL.implies \<rightharpoonup>
    (SML) "!(if (_)/ then (_)/ else true)"
    and (OCaml) "!(if (_)/ then (_)/ else true)"
    and (Haskell) "!(if (_)/ then (_)/ else True)"
    and (Scala) "!(if ((_))/ (_)/ else true)"
| constant If \<rightharpoonup>
    (SML) "!(if (_)/ then (_)/ else (_))"
    and (OCaml) "!(if (_)/ then (_)/ else (_))"
    and (Haskell) "!(if (_)/ then (_)/ else (_))"
    and (Scala) "!(if ((_))/ (_)/ else (_))"

code_reserved SML
  not

code_reserved OCaml
  not

code_identifier
  code_module Pure \<rightharpoonup>
    (SML) HOL and (OCaml) HOL and (Haskell) HOL and (Scala) HOL

text {* using built-in Haskell equality *}

code_printing
  type_class equal \<rightharpoonup> (Haskell) "Eq"
| constant HOL.equal \<rightharpoonup> (Haskell) infix 4 "=="
| constant HOL.eq \<rightharpoonup> (Haskell) infix 4 "=="

text {* undefined *}

code_printing
  constant undefined \<rightharpoonup>
    (SML) "!(raise/ Fail/ \"undefined\")"
    and (OCaml) "failwith/ \"undefined\""
    and (Haskell) "error/ \"undefined\""
    and (Scala) "!sys.error(\"undefined\")"


subsubsection {* Evaluation and normalization by evaluation *}

ML {*
fun eval_tac ctxt =
  let val conv = Code_Runtime.dynamic_holds_conv (Proof_Context.theory_of ctxt)
  in CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1 conv)) ctxt) THEN' rtac TrueI end
*}

method_setup eval = {* Scan.succeed (SIMPLE_METHOD' o eval_tac) *}
  "solve goal by evaluation"

method_setup normalization = {*
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD'
      (CHANGED_PROP o
        (CONVERSION (Nbe.dynamic_conv (Proof_Context.theory_of ctxt))
          THEN_ALL_NEW (TRY o rtac TrueI))))
*} "solve goal by normalization"


subsection {* Counterexample Search Units *}

subsubsection {* Quickcheck *}

quickcheck_params [size = 5, iterations = 50]


subsubsection {* Nitpick setup *}

ML {*
structure Nitpick_Unfolds = Named_Thms
(
  val name = @{binding nitpick_unfold}
  val description = "alternative definitions of constants as needed by Nitpick"
)
structure Nitpick_Simps = Named_Thms
(
  val name = @{binding nitpick_simp}
  val description = "equational specification of constants as needed by Nitpick"
)
structure Nitpick_Psimps = Named_Thms
(
  val name = @{binding nitpick_psimp}
  val description = "partial equational specification of constants as needed by Nitpick"
)
structure Nitpick_Choice_Specs = Named_Thms
(
  val name = @{binding nitpick_choice_spec}
  val description = "choice specification of constants as needed by Nitpick"
)
*}

setup {*
  Nitpick_Unfolds.setup
  #> Nitpick_Simps.setup
  #> Nitpick_Psimps.setup
  #> Nitpick_Choice_Specs.setup
*}

declare if_bool_eq_conj [nitpick_unfold, no_atp]
        if_bool_eq_disj [no_atp]


subsection {* Preprocessing for the predicate compiler *}

ML {*
structure Predicate_Compile_Alternative_Defs = Named_Thms
(
  val name = @{binding code_pred_def}
  val description = "alternative definitions of constants for the Predicate Compiler"
)
structure Predicate_Compile_Inline_Defs = Named_Thms
(
  val name = @{binding code_pred_inline}
  val description = "inlining definitions for the Predicate Compiler"
)
structure Predicate_Compile_Simps = Named_Thms
(
  val name = @{binding code_pred_simp}
  val description = "simplification rules for the optimisations in the Predicate Compiler"
)
*}

setup {*
  Predicate_Compile_Alternative_Defs.setup
  #> Predicate_Compile_Inline_Defs.setup
  #> Predicate_Compile_Simps.setup
*}


subsection {* Legacy tactics and ML bindings *}

ML {*
(* combination of (spec RS spec RS ...(j times) ... spec RS mp) *)
local
  fun wrong_prem (Const (@{const_name All}, _) $ Abs (_, _, t)) = wrong_prem t
    | wrong_prem (Bound _) = true
    | wrong_prem _ = false;
  val filter_right = filter (not o wrong_prem o HOLogic.dest_Trueprop o hd o Thm.prems_of);
in
  fun smp i = funpow i (fn m => filter_right ([spec] RL m)) ([mp]);
  fun smp_tac j = EVERY'[dresolve_tac (smp j), atac];
end;

local
  val nnf_ss =
    simpset_of (put_simpset HOL_basic_ss @{context} addsimps @{thms simp_thms nnf_simps});
in
  fun nnf_conv ctxt = Simplifier.rewrite (put_simpset nnf_ss ctxt);
end
*}

hide_const (open) eq equal

end

