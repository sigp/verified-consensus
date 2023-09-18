section \<open>General Rules Used in Proof\<close>

text\<open>This section covers some general rules used in the proof.\<close>

theory programming_constructs_extended
  imports  "../../AbstractAtomicTest/Constrained_Atomic_Commands"
  "../../AbstractAtomicTest/Programming_Constructs"
  "../../AbstractAtomicTest/IntroPar_Big"
begin

locale programming_constructs_extended = programming_constructs 
begin

text \<open>This lemma corresponds to law 28 as described in \cite{AGTRGT}.\<close>
lemma strengthen_under_rely_guar : 
  assumes a: "p \<triangleleft> (r \<squnion> g)\<^sup>* \<sqinter> q2 \<subseteq> q1"
  shows "(rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>;\<lparr>q1\<rparr> \<ge> (rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>;\<lparr>q2\<rparr>"
proof - 
  have "p \<triangleleft> (r \<squnion> g)\<^sup>* \<sqinter> q2 = p \<triangleleft> ((r \<squnion> g)\<^sup>* \<sqinter> q2)"
    by (simp add: inf_assoc restrict_domain_def)
  then have "(rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>;\<lparr>q1\<rparr> \<ge> (rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>;\<lparr>(r \<squnion> g)\<^sup>* \<sqinter> q2\<rparr>"
    using assms conj.sync_mono_right spec_strengthen_under_pre by simp
  also have "... \<ge> (rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>;\<lparr>q2\<rparr>"
  proof -
    have "(rely r) \<iinter> (guar g) \<iinter> \<lparr>(r \<squnion> g)\<^sup>* \<sqinter> q2\<rparr> = (rely r) \<iinter> (guar g) \<iinter> \<lparr>q2\<rparr>" 
      using spec_trading by fast
    then have "\<lbrace>p\<rbrace>;((rely r) \<iinter> (guar g) \<iinter> \<lparr>(r \<squnion> g)\<^sup>* \<sqinter> q2\<rparr>) \<ge>
          \<lbrace>p\<rbrace>;((rely r) \<iinter> (guar g) \<iinter> \<lparr>q2\<rparr>)" 
      using seq_mono_right by auto
    then show ?thesis
      by (metis calculation initial_assert_rely_generic spec_trading)
  qed
  then show ?thesis .
qed

lemma rg_rtrancl_maintains_invariant:
  assumes "r \<subseteq> (P' p)" and "g \<subseteq> (P' p)"   
  shows "(x,y) \<in> (r \<squnion> g)\<^sup>* \<Longrightarrow> x \<in> p \<Longrightarrow> y \<in> p"
proof (induction rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  then show ?case using assms by auto
qed

text \<open>This lemma corresponds to law 29 as described in \cite{AGTRGT}.\<close>
lemma strengthen_under_invariant :
  assumes "r \<subseteq> (P' p)" and "g \<subseteq> (P' p)" and "p \<triangleleft> q2 \<triangleright> p \<subseteq> q1 "
  shows "(rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>;\<lparr>q1\<rparr> \<ge> (rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>;\<lparr>q2\<rparr>" 
proof -
  have "(r \<squnion> g)\<^sup>* \<subseteq> (P' p)" 
    using rg_rtrancl_maintains_invariant assms(1) assms(2) sorry
  then have "p \<triangleleft> (r \<squnion> g)\<^sup>* \<sqinter> q2 \<subseteq> p \<triangleleft> (P' p) \<sqinter> q2"
    using domain_restrict_q_mono by blast
  also have "... \<subseteq> p \<triangleleft> q2 \<triangleright> p" 
    unfolding restrict_domain_def restrict_range_def by auto
  also have "... \<subseteq> q1" using assms by simp
  finally have "p \<triangleleft> (r \<squnion> g)\<^sup>* \<sqinter> q2 \<subseteq> q1" .
  then show ?thesis using strengthen_under_rely_guar by auto
qed

lemma pre_par_distrib :
  assumes "q \<ge> q1 \<parallel> q2"
  shows "\<lbrace>p\<rbrace>;q \<ge> \<lbrace>p\<rbrace>;q1 \<parallel> \<lbrace>p\<rbrace>;q2"
  by (metis assert_galois_test assms seq_assoc seq_mono_right test_par_distrib test_seq_assert)

lemma pre_strengthen_both :
  assumes "p2 \<subseteq> p1" and "\<lbrace>p1\<rbrace>;q1 \<ge> \<lbrace>p1\<rbrace>;q2"
  shows "\<lbrace>p2\<rbrace>;q1 \<ge> \<lbrace>p2\<rbrace>;q2"
  by (meson assert_iso assert_redundant assms(1) assms(2) order_trans seq_mono_left)

lemma range_simp : "a \<triangleright> b = a \<inter> {(s, s'). s' \<in> b}"
  by (metis restrict_range_def)

lemma domain_simp : "b \<triangleleft> a = {(s, s'). s \<in> b} \<inter> a" 
  by (metis restrict_domain_def)

lemma move_pre : "d \<iinter> \<lbrace>p\<rbrace>;q = \<lbrace>p\<rbrace>;(d \<iinter> q)" 
  using conj.sync_commute conj_chaos initial_assert_rely_generic rely_top by metis

lemma spec_trading_refinement : "(rely r) \<iinter> (guar g) \<iinter> \<lparr>(r \<squnion> g)\<^sup>* \<sqinter> q\<rparr> \<ge>
      (rely r) \<iinter> (guar g) \<iinter> \<lparr>q\<rparr>"
  using spec_trading by auto

end
end