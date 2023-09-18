section \<open>pgm and hom as Boolean subalgebras\<close>

theory Abstract_Hom
imports
  "HOL.Complete_Lattices"
  "Refinement_Lattice"
begin

subsection \<open>A Homorphism between a Boolean Algebra and a Refinement Lattice\<close>

locale abstract_hom_commands =
  fixes hom :: "'b::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice"
  assumes hom_injective: "inj hom" 
  assumes hom_sup [simp]: "hom (sup p q) = hom p \<squnion> hom q"
  assumes hom_inf [simp]: "hom (inf p q) = hom p \<sqinter> hom q"
  assumes hom_bot [simp]: "hom bot = \<bottom>"
  assumes hom_iso: "(less_eq p q)  \<longleftrightarrow> (hom p) \<le> (hom q)"
begin

definition Hom :: "'a::refinement_lattice"
  where "Hom \<equiv> hom top"

definition negate :: "'a \<Rightarrow> 'a::refinement_lattice"
  where "negate c \<equiv> (if c \<in> range(hom) then 
                            (let p = (THE p. hom p = c) in hom(-p))
                         else undefined)"

lemma hom_not[simp]:
  "negate (hom p) = hom (- p)"
proof -
  define P where "P \<equiv> (\<lambda>p'. hom p' = hom p)"
  have "P p" unfolding P_def by simp
  moreover have "\<And>p'. P p' \<Longrightarrow> p' = p"
    unfolding P_def using hom_injective unfolding inj_def by auto
  ultimately have a1: "(THE p'. P p') = p"
    using theI by blast
  have "negate (hom p) = (let p' = (THE p'. hom p' = (hom p)) in hom(-p'))"
    unfolding negate_def by simp
  also have "... = hom(-p)"
    using hom_injective a1 unfolding P_def by simp
  finally show ?thesis by simp
qed

lemma hom_iso_eq: "p = q \<longleftrightarrow> hom p = hom q" 
  by (metis eq_iff hom_iso)

lemma hom_mono: "p \<ge> q \<Longrightarrow> hom p \<ge> hom q"
  by (simp add: hom_iso)

lemma Hom_ref_hom: "Hom \<ge> hom p"   
  using Hom_def hom_mono top_greatest by (simp add: le_infI1) 

lemma hom_negate_iso: "hom p \<ge> hom q \<longleftrightarrow> negate(hom q) \<ge> negate(hom p)"
   by (metis hom_iso hom_not compl_le_compl_iff) 

text\<open>Some useful helper lemmas on Boolean algebras\<close>

lemma hom_compl_inf: "negate(hom p) \<squnion> (hom p) = Hom"
  by (metis Hom_def hom_not hom_sup sup_commute sup_compl_top)

lemma hom_compl_sup: "negate(hom p) \<sqinter> (hom p) = \<bottom>"
   by (metis hom_inf hom_not hom_bot inf_compl_bot inf.commute)

end
end
