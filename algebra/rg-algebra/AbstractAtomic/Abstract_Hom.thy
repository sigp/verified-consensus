section \<open>pgm and hom as Boolean subalgebras\<close>

theory Abstract_Hom
  imports
  "../General/Refinement_Lattice"
  "../General/Liberation"
begin

subsection \<open>A Homorphism between a Boolean Algebra and a Refinement Lattice\<close>

locale abstract_hom_commands = lib_boolean_sets _ _ _ lib
  for lib :: "'c \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("E\<^sup>C\<^sub>_ _" [999, 999] 999) +
  fixes hom :: "'b::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice"
  assumes hom_injective: "inj hom" 
  assumes hom_sup [simp]: "hom (sup p q) = hom p \<squnion> hom q"
  assumes hom_inf [simp]: "hom (inf p q) = hom p \<sqinter> hom q"
  assumes hom_bot [simp]: "hom bot = \<bottom>"
  assumes hom_iso: "(less_eq p q)  \<longleftrightarrow> (hom q) \<ge> (hom p)" 
  and hom_lib: "E\<^sup>C\<^sub>x (hom p) = hom (lib_bool x p)"
  and hom_first: "E\<^sup>C\<^sub>x (hom p) = F\<^sup>C\<^sub>x (hom p)"
  and hom_last: "E\<^sup>C\<^sub>x (hom p) = L\<^sup>C\<^sub>x (hom p)"
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

lemma hom_mono: "p \<le> q \<Longrightarrow> hom p \<le> hom q"
  by (simp add: hom_iso)

lemma Hom_ref_hom: "Hom \<ge> hom p"   
  using Hom_def hom_mono top_greatest by (simp add: le_infI1) 

lemma hom_negate_iso: "hom p \<ge> hom q \<longleftrightarrow> negate(hom q) \<ge> negate(hom p)"
   by (metis hom_iso hom_not compl_le_compl_iff) 

text\<open>Some useful helper lemmas on Boolean algebras\<close>

lemma hom_compl_sup: "negate(hom p) \<squnion> (hom p) = Hom"
  by (metis Hom_def hom_not hom_sup sup_commute sup_compl_top)

lemma hom_compl_inf: "negate(hom p) \<sqinter> (hom p) = \<bottom>"
   by (metis hom_inf hom_not hom_bot inf_compl_bot inf.commute)

(* liberating over hom steps *)

lemma hom_first_last: "F\<^sup>C\<^sub>x (L\<^sup>C\<^sub>x (hom r)) = L\<^sup>C\<^sub>x (F\<^sup>C\<^sub>x (hom r))"
  by (metis abstract_hom_commands.hom_first abstract_hom_commands.hom_lib 
      abstract_hom_commands_axioms hom_last)

lemma lib_first: "E\<^sup>C\<^sub>x (hom r) = F\<^sup>C\<^sub>x (L\<^sup>C\<^sub>x (hom r))"
  using hom_first hom_last lib_boolean_sets_axioms lib_boolean_sets_def lib_lattice.lib_idem 
    liberation_stages.axioms(2) by fastforce

lemma lib_last: "E\<^sup>C\<^sub>x (hom r) = L\<^sup>C\<^sub>x (F\<^sup>C\<^sub>x (hom r))" 
  by (simp add: hom_first_last lib_first)

end
end
