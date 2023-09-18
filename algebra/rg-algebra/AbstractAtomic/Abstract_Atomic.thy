section \<open>Abstract view of atomic commands\<close>

theory Abstract_Atomic
imports
  Main (* for Complete_Lattices *)
  "../General/Refinement_Lattice"
begin

subsection \<open>A Homorphism between a Boolean Algebra and a Refinement Lattice\<close>

locale abstract_atomic_commands = 
  fixes atomic :: "'b::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice" ("atomic") 
  assumes atomic_injective: "inj atomic"
  assumes atomic_sup [simp]: "atomic (sup p q) = atomic p \<sqinter> atomic q"
  assumes atomic_inf [simp]: "atomic (inf p q) = atomic p \<squnion> atomic q"
  assumes atomic_bot [simp]: "atomic bot = \<top>"
  assumes atomic_iso: "(less_eq p q)  \<longleftrightarrow> less_eq (atomic q) (atomic p)" 
begin

definition Atomic :: "'a"
  where "Atomic \<equiv> atomic top"

definition atomic_negate :: "'a \<Rightarrow> 'a"
  where "atomic_negate c \<equiv> (if c \<in> range(atomic) then 
                               (let p = (THE p. atomic p = c) in atomic(-p))
                             else undefined)"

lemma atomic_not[simp]:
  "atomic_negate (atomic p) = atomic (- p)"
proof -
  define P where "P \<equiv> (\<lambda>p'. atomic p' = atomic p)"
  have "P p" unfolding P_def by simp
  moreover have "\<And>p'. P p' \<Longrightarrow> p' = p"
    unfolding P_def using atomic_injective unfolding inj_def by auto
  ultimately have a1: "(THE p'. P p') = p"
    using theI by blast
  have "atomic_negate (atomic p) = (let p' = (THE p'. atomic p' = (atomic p)) in atomic(-p'))"
    unfolding atomic_negate_def by simp
  also have "... = atomic(-p)"
    using atomic_injective a1 unfolding P_def by simp
  finally show ?thesis by simp
qed

lemma atomic_top[simp]:
  shows "atomic top = Atomic"
  unfolding Atomic_def by simp

lemma atomic_iso_eq: "p = q \<longleftrightarrow> atomic p = atomic q" 
  by (metis eq_iff atomic_iso)

lemma atomic_mono: "p \<le> q \<Longrightarrow> atomic q \<le> atomic p"
  by (simp add: atomic_iso)

lemma Atomic_ref_atomic: "Atomic \<le> atomic p"   
  using atomic_mono top_greatest unfolding Atomic_def by blast 

lemma atomic_negate_iso: "(atomic p) \<le> (atomic q) \<longleftrightarrow> atomic_negate(atomic q) \<le> atomic_negate(atomic p)"
   by (metis atomic_iso atomic_not compl_le_compl_iff) 

text\<open>Some useful helper lemmas on Boolean algebras\<close>

lemma atomic_compl_inf: "atomic_negate(atomic p) \<sqinter> atomic p = Atomic"
   by (metis atomic_top atomic_not atomic_sup inf_commute sup_compl_top)

lemma atomic_compl_sup: "atomic_negate(atomic p) \<squnion> atomic p = \<top>"
   by (metis atomic_inf atomic_not atomic_bot inf_compl_bot sup.commute)

lemma atomic_negate_inf_to_sup: "atomic_negate(atomic(p) \<sqinter> atomic(q)) = atomic_negate(atomic(p)) \<squnion> atomic_negate(atomic(q))"
   by (metis (no_types) atomic_inf atomic_not atomic_sup compl_sup)

end

end
