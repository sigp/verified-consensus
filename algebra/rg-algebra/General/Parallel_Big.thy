section \<open>Parallel and weak conjunction over finite sets of commands\<close>

theory Parallel_Big
  
imports CRA (* Rely_Quotient*)
begin

subsection \<open>Generalized weak conjunction over a set\<close>

locale big_conjunction = conj_distrib +
  constrains conj :: "'a::refinement_lattice \<Rightarrow> 'a \<Rightarrow> 'a"
  constrains lib :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a"
  constrains lib_first :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a"
  constrains lib_last :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a"
begin

definition setconj :: "('c \<Rightarrow> 'a::refinement_lattice) \<Rightarrow> 'c set \<Rightarrow> 'a"
where
  "setconj = comm_monoid_set.F conj chaos"

print_facts
sublocale setconj: comm_monoid_set conj chaos
rewrites
  "comm_monoid_set.F conj chaos = setconj"
proof -
  show "comm_monoid_set conj chaos" by standard
  then interpret setconj: comm_monoid_set conj chaos .
  from setconj_def show "comm_monoid_set.F conj chaos = setconj" by rule
qed

abbreviation
  Setconj ("\<iinter>\<iinter>_" [1000] 999) where
  "\<iinter>\<iinter>A \<equiv> setconj (%x. x) A"

(* Using a big hack-ish abbreviation instead of proper syntax translation (see commented below),
   because cannot specify translations within locales. *)
abbreviation
  Setconj_in :: "'c set \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<iinter>\<iinter>\<in>_./ _" [51, 10] 10) where
  "\<iinter>\<iinter>\<in>A. b \<equiv> setconj (%x. b x) A"

lemma setconj_idem: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<iinter>\<iinter>\<in>A. (\<lambda>x. c)) = c"
apply (induct set: finite)
apply simp
using conj_idem by force

end


(* Syntax and translations cannot be defined within locales, however outside the locale the term
   'setconj' is not visible. So I cannot define it like that. Using classes also does not work.

text{* Now: lot's of fancy syntax. First, @{term "setconj (%x. e) A"} is
written @{text"\<iinter>\<iinter>x\<in>A. e"}. *}

syntax
  "_setconj" :: "pttrn => 'a set => 'b => 'b"    ("(3CONJ _:_. _)" [0, 51, 10] 10)
syntax (xsymbols)
  "_setconj" :: "pttrn => 'a set => 'b => 'b"    ("(3\<iinter>\<iinter>_\<in>_. _)" [0, 51, 10] 10)
syntax (HTML output)
  "_setconj" :: "pttrn => 'a set => 'b => 'b"    ("(3\<iinter>\<iinter>_\<in>_. _)" [0, 51, 10] 10)

translations -- {* Beware of argument permutation! *}
  "CONJ i:A. b" == "CONST setconj (%i. b) A"
  "\<iinter>\<iinter>i\<in>A. b" == "CONST setconj (%i. b) A"

*)


subsection \<open>Generalized parallel over a set\<close>


locale big_parallel = par_distrib (* should contain par *)  +
  constrains par :: "'a::refinement_lattice \<Rightarrow> 'a \<Rightarrow> 'a"
  constrains conj :: "'a::refinement_lattice \<Rightarrow> 'a \<Rightarrow> 'a"
  constrains lib :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a"
  constrains lib_first :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a"
  constrains lib_last :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a"
begin

definition setpar :: "('c \<Rightarrow> 'a) \<Rightarrow> 'c set \<Rightarrow> 'a"
where
  "setpar = comm_monoid_set.F par skip"


sublocale setpar: comm_monoid_set par skip
rewrites
  "comm_monoid_set.F par skip = setpar"
proof -
  show "comm_monoid_set par skip" by standard
  then interpret setpar: comm_monoid_set par skip .
  from setpar_def show "comm_monoid_set.F par skip = setpar" by rule
qed

abbreviation
  Setpar ("\<parallel>\<parallel>_" [1000] 999) where
  "\<parallel>\<parallel>A \<equiv> setpar (%x. x) A"


(* Using a big hack-ish abbreviation instead of proper syntax translation, because cannot
specify translations within locales. *)
abbreviation
  Setpar_in :: "'c set \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<parallel>\<parallel>\<in>_./ _" [51, 10] 10) where
  "\<parallel>\<parallel>\<in>A. b \<equiv> setpar (%x. b x) A"

(* Testing the abbreviation Setpar_in *)
theorem "a \<noteq> b \<Longrightarrow> (\<parallel>\<parallel>\<in>{[a], [b]}. (\<lambda>p. hd p)) = a \<parallel> b"
by simp

end


(* -- see similar arguments for _setconj above

text{* Now: lot's of fancy syntax. First, @{term "setpar (%x. e) A"} is
written @{text"\<parallel>\<parallel>x\<in>A. e"}. *}

syntax
  "_setpar" :: "pttrn => 'a set => 'b => 'b"    ("(3PAR _:_. _)" [0, 51, 10] 10)
syntax (xsymbols)
  "_setpar" :: "pttrn => 'a set => 'b => 'b"    ("(3\<parallel>\<parallel>_\<in>_. _)" [0, 51, 10] 10)
syntax (HTML output)
  "_setpar" :: "pttrn => 'a set => 'b => 'b"    ("(3\<parallel>\<parallel>_\<in>_. _)" [0, 51, 10] 10)

translations -- {* Beware of argument permutation! *}
  "PAR i:A. b" == "CONST setpar (%i. b) A"
  "\<parallel>\<parallel>i\<in>A. b" == "CONST setpar (%i. b) A"
*)


subsection \<open>Distributed big parallel and weak conjunction operators\<close>


text \<open>
  Defining an operator 'multi' for sets that have at least two elements.
\<close>

definition multi :: "'c set \<Rightarrow> bool"
where "multi s \<equiv> \<exists> e1 e2 . e1 \<noteq> e2 \<and> {e1, e2} \<subseteq> s"

lemma multi_non_empty: "multi A \<Longrightarrow> A \<noteq> {}"
using multi_def by fastforce

locale big_parallel_distrib = conjunction_parallel + big_conjunction + big_parallel
begin

lemma conj_setpar_absorb:
  assumes ref_to_par: "g \<ge> g \<parallel> g"
  shows "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> g \<iinter> (\<parallel>\<parallel>\<in>A. (\<lambda>x. g \<iinter> c x)) \<ge> (\<parallel>\<parallel>\<in>A. (\<lambda>x. g \<iinter> c x))"
proof (induct A rule: finite_ne_induct)
  fix x
  have "g \<iinter> (g \<iinter> c x) \<ge> g \<iinter> c x" by (metis conj_idem order.refl conj_assoc)
  then show "g \<iinter> (\<parallel>\<parallel>\<in>{x}. (\<lambda>x. g \<iinter> c x)) \<ge> (\<parallel>\<parallel>\<in>{x}. (\<lambda>x. g \<iinter> c x))" by simp
next
  fix x F
  assume finf: "finite F"
    and newx: "x \<notin> F"
    and step: "g \<iinter> (\<parallel>\<parallel>\<in>F. (\<lambda>x. g \<iinter> c x)) \<ge> (\<parallel>\<parallel>\<in>F. (\<lambda>x. g \<iinter> c x))"
  have "g \<iinter> (g \<iinter> c x \<parallel> (\<parallel>\<parallel>\<in>F. (\<lambda>x. g \<iinter> c x))) \<ge> g \<iinter> g \<iinter> c x \<parallel> g \<iinter> (\<parallel>\<parallel>\<in>F. (\<lambda>x. g \<iinter> c x))" (is "_ \<ge> ?rhs")
    by (metis conj_par_distrib conj_assoc ref_to_par)
  also have "?rhs \<ge> g \<iinter> c x \<parallel> (\<parallel>\<parallel>\<in>F. (\<lambda>x. g \<iinter> c x))"
    by (simp add: step sync_mono_right)
  finally show "g \<iinter> (\<parallel>\<parallel>\<in>insert x F. (\<lambda>x. g \<iinter> c x)) \<ge> (\<parallel>\<parallel>\<in>insert x F. (\<lambda>x. g \<iinter> c x))"
    by (simp add: finf newx)
qed
  
   
lemma conj_setpar_distrib:
  assumes ref_to_par: "g \<ge> g \<parallel> g"
  shows "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> g \<iinter> (\<parallel>\<parallel>\<in>A. (\<lambda>x. c x)) \<ge> (\<parallel>\<parallel>\<in>A. (\<lambda>x. g \<iinter> c x))"
(* Apply an induction rule for non-empty finite sets *)
proof (induct A rule: finite_ne_induct)
  case (singleton x)
  have "g \<iinter> c x \<ge> g \<iinter> c x" by simp
  then show ?case by simp
next
  fix x F
  assume finf: "finite F"
    and newx: "x \<notin> F"
    and step: "g \<iinter> (\<parallel>\<parallel>\<in>F. (\<lambda>x. c x)) \<ge> (\<parallel>\<parallel>\<in>F. (\<lambda>x. g \<iinter> c x))"  
  have "g \<iinter> ((c x) \<parallel> (\<parallel>\<parallel>\<in>F. (\<lambda>x. c x))) \<ge> (g \<iinter> c x) \<parallel> (g \<iinter> (\<parallel>\<parallel>\<in>F. (\<lambda>x. c x)))" (is "_ \<ge> ?rhs") 
    by (simp add: conj_par_distrib ref_to_par)
  (* Apply induction hypothesis, step. *)
  also have  "?rhs \<ge>  (g \<iinter> c x) \<parallel> (\<parallel>\<parallel>\<in>F. (\<lambda>x. g \<iinter> c x))"
    by (simp add: local.step sync_mono_right)
  finally show "g \<iinter> (\<parallel>\<parallel>\<in>insert x F. (\<lambda>x. c x)) \<ge> (\<parallel>\<parallel>\<in>insert x F. (\<lambda>x. g \<iinter> c x))" 
    by (simp add: finf newx)
qed

lemma finite_multi_induct [case_names multi insert, consumes 2]:
  assumes fin: "finite F"
      and is_multi: "multi F"
  assumes multi: "\<And>x y. x \<noteq> y \<Longrightarrow> P {x, y}"
  assumes insert: "\<And>x F. finite F \<Longrightarrow> multi F \<Longrightarrow> x \<notin> F \<Longrightarrow> P F  \<Longrightarrow> P (insert x F)"
  shows "P F"
using assms
proof -
  have multi_non_empty: "F \<noteq> {}" by (simp add: is_multi multi_non_empty)
  show ?thesis using fin multi_non_empty is_multi
  proof (induct F rule: finite_ne_induct)
    case singleton then show ?case by (simp add: multi_def)
  next
    fix x F
    assume step: "multi F \<Longrightarrow> P F"
    assume fin: "finite F"
    assume multii: "multi (insert x F)" and newx: "x \<notin> F"
    then obtain y where xy: "x \<noteq> y" and yinf: "y \<in> F"
      by (metis ex_in_conv insert_subset multi_def singletonD)
    then show "P (insert x F)"
    proof (cases "F = {y}")
      assume "F = {y}"
      then show "P (insert x F)" by (simp add: multi xy)
    next
      assume "F \<noteq> {y}" then have "multi F" using multi_def yinf by fastforce
      then show "P (insert x F)" using step fin insert newx by blast
    qed
  qed
qed


lemma infinite_multi_induct [case_names infinite multi insert, consumes 1]:
  assumes is_multi: "multi F"
  assumes infinite: "\<And>A. \<not> finite A \<Longrightarrow> P A"
  assumes multi: "\<And>x y. x \<noteq> y \<Longrightarrow> P {x, y}"
  assumes insert: "\<And>x F. finite F \<Longrightarrow> multi F \<Longrightarrow> x \<notin> F \<Longrightarrow> P F  \<Longrightarrow> P (insert x F)"
  shows "P F"
using assms
proof (cases "finite F")
  case False with infinite show ?thesis .
next
  case True show ?thesis using True finite_multi_induct is_multi insert multi by auto
qed

lemma setpar_mono: "(\<And>x. a x \<ge> b x) \<Longrightarrow> (\<parallel>\<parallel>\<in>A. (\<lambda>x. a x)) \<ge> (\<parallel>\<parallel>\<in>A. (\<lambda>x. b x))"
  by (induct A rule: infinite_finite_induct; simp_all add: sync_mono)

lemma setpar_mono2: "(\<forall>x\<in>A. a x \<ge> b x) \<Longrightarrow> (\<parallel>\<parallel>\<in>A. (\<lambda>x. a x)) \<ge> (\<parallel>\<parallel>\<in>A. (\<lambda>x. b x))"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case by (simp add: sync_mono)
qed  
  
end
  
  
end

