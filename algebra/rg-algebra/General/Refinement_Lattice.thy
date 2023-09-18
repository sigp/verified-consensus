section \<open>Refinement lattice \label{S:lattice}\<close>

theory Refinement_Lattice
imports
  Main
begin
unbundle lattice_syntax

unbundle lattice_syntax

text \<open>
  The underlying lattice of commands is is based on the Isabelle/HOL Lirary
  complete distributive lattice.
  The lattice is the dual of that used by the refinement calculus tradition, 
  so that @{term "c \<squnion> d"} is non-deterministic choice and 
  @{term "c \<ge> d"} means command @{term "c"} is refined (or implemented) by @{term "d"}.
\<close>
                               
class refinement_lattice = complete_distrib_lattice
begin        
print_locale refinement_lattice
text \<open>The refinement lattice supremum corresponds to non-deterministic choice for commands.
Non-deterministic choice is monotonic in both arguments\<close>

lemma nondet_mono_left: "a \<ge> b \<Longrightarrow> a \<squnion> c \<ge> b \<squnion> c"
  using sup_mono by auto

lemma nondet_mono_right: "c \<ge> d \<Longrightarrow> a \<squnion> c \<ge> a \<squnion> d"
  using sup_mono by auto

text \<open>Binary choice is a special case of choice over a set.\<close>
lemma Nondet_to_nondet: "\<Squnion>{ f x | x. x \<in> {c, d}} = f c \<squnion> f d"
proof -
  have "{ f x | x. x \<in> {c, d}} = {f c, f d}" by blast
  then have "\<Squnion>{ f x | x. x \<in> {c, d}} = \<Squnion>{f c, f d}" by simp
  also have "... = f c \<squnion> f d" by simp
  finally show ?thesis .
qed

text \<open>Helper lemma for choice over indexed set.\<close>
lemma NONDET_to_Nondet: "(\<Squnion>x\<in>X. f x) = (\<Squnion>{f x |x. x \<in> X})"
  by (simp add: Setcompr_eq_image)

lemma NONDET_absorb_args: "(\<Squnion>i j. (f::nat \<Rightarrow> 'c::complete_lattice) (i + j)) = (\<Squnion>k. f k)"
proof (rule order_class.order.antisym)
  show "(\<Squnion>k. f k) \<ge> (\<Squnion>i j. f (i + j))"
    by (simp add: complete_lattice_class.SUP_upper complete_lattice_class.SUP_le_iff)
next
  have "\<And>k. \<exists>i j. f (i + j) \<ge> f k"
    by (metis Nat.add_0_right order_class.dual_order.eq_iff)
  then have "\<And>k. \<exists>i. (\<Squnion>j. f (i + j)) \<ge> f k"
    by (meson UNIV_I complete_lattice_class.SUP_upper2)
  then show "(\<Squnion>i j. f (i + j)) \<ge> (\<Squnion>k. f k)"
    by (simp add: complete_lattice_class.SUP_mono)
qed

text \<open>A transition lemma for non-deterministic distribution properties,
  going from Nondet to NONDET,
  qualified version followed by a straightforward one.\<close>

lemma f_NONDET_distrib_Nondet_qualified:
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes qual: "P {d x |x. x \<in> X}"
  assumes f_Nondet_distrib: "\<And>c D. P D \<Longrightarrow> f c (\<Squnion> D) = \<Squnion> {f c d | d . d \<in> D }"
  shows "f c (\<Squnion>x\<in>X. d x) = (\<Squnion>x\<in>X. f c (d x))"
proof -
  have nested_Collect: "\<And>f g. {f y |y. y \<in> {g x |x. x \<in> X}} = {f (g x) |x. x \<in> X}" by blast
  have "f c (\<Squnion>x\<in>X. d x) = f c (\<Squnion>{d x |x. x \<in> X})" by (simp add: NONDET_to_Nondet)
  also have "... = (\<Squnion>{f c dx |dx. dx \<in> {d x | x. x \<in> X}})" by (simp add: qual f_Nondet_distrib)
  also have "... = (\<Squnion>{f c (d x) |x. x \<in> X})" by (simp only: nested_Collect)
  also have "... = (\<Squnion>x\<in>X. f c (d x))" by (simp add: NONDET_to_Nondet)
  finally show ?thesis .
qed

lemma f_NONDET_distrib_Nondet:
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes f_Nondet_distrib: "\<And>c D. f c (\<Squnion> D) = \<Squnion> {f c d | d . d \<in> D }"
  shows "f c (\<Squnion>x\<in>X. d x) = (\<Squnion>x\<in>X. f c (d x))"
  by (simp add: Setcompr_eq_image f_Nondet_distrib image_image)    
end

lemmas refine_trans = order.trans

text \<open>Transitivity rules to make calculational reasoning smoother.\<close>
declare ord_eq_le_trans[trans]
declare ord_le_eq_trans[trans]
declare dual_order.trans[trans]


abbreviation
  dist_over_inf :: "('a::refinement_lattice \<Rightarrow> 'a) \<Rightarrow> bool"
  where
  "dist_over_inf F \<equiv> (\<forall> X . F (\<Sqinter> X) = (\<Sqinter>x\<in>X. F (x)))"

abbreviation
  dist_over_nondet :: "('a::refinement_lattice \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "dist_over_nondet F \<equiv> (\<forall> X . F (\<Squnion> X) = (\<Squnion>x\<in>X. F (x)))"

end
