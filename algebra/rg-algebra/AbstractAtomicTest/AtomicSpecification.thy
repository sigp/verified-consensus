section \<open>Atomic Specification\<close>
theory AtomicSpecification
imports
  Expressions
begin

locale atomic_specification = expressions
begin

(* An atomic step or test with arbitrary (but finite) stuttering before and after. *)
definition atomic_spec :: "'b set \<Rightarrow> 'b rel \<Rightarrow> 'a" ("\<langle>_,_\<rangle>" [30,30])
  where "atomic_spec p q \<equiv> idle;\<lbrace>p\<rbrace>;opt(q);idle"

lemma atomic_spec_introduce:
  assumes refl: "refl g"
  assumes tolerates: "tolerates_interference p q r"
  shows "(rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> \<ge> (rely r) \<iinter> \<langle>p,g \<inter> q\<rangle>"
proof -
  have "(rely r) \<iinter> (guar g) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> = (rely r) \<iinter> ((guar g) \<iinter> idle;\<lbrace>p\<rbrace>; \<lparr>q\<rparr>;idle)"
    using tolerate_interference tolerates conj_assoc by (simp add: local.conj_commute)
  also have "... \<ge> (rely r) \<iinter> idle;((guar g) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>);idle" (is "... \<ge> ?rhs")
  proof -
    have "(rely r) \<iinter> ((guar g) \<iinter> idle;\<lbrace>p\<rbrace>; \<lparr>q\<rparr>;idle) \<ge> (rely r) \<iinter> ((guar g) \<iinter> idle;\<lbrace>p\<rbrace>; \<lparr>q\<rparr>);idle" (is "... \<ge> ?rhs")
      using guar_distrib_seq seq_mono_left guar_idle refl by (metis conj.sync_mono_right)
    also have "?rhs \<ge>  (rely r) \<iinter> idle;((guar g) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>);idle"
      using guar_distrib_seq seq_mono_left guar_idle refl
      by (metis conj.sync_mono_right guar_distrib_seq_eq seq_assoc)
    finally show ?thesis .
  qed
  also have "?rhs \<ge> (rely r) \<iinter> idle;((guar g) \<iinter> \<lbrace>p\<rbrace>;(opt q));idle" (is "... \<ge> ?rhs")
    using spec_ref_opt seq_mono_right rely_refine_within by (simp add: conj.sync_mono_right)
  also have "?rhs = (rely r) \<iinter> idle;(\<lbrace>p\<rbrace>;(opt (g \<inter> q)));idle"
    using guar_opt conj.assert_distrib refl by metis
  also have "... = (rely r) \<iinter> \<langle>p, g \<inter> q\<rangle>" unfolding atomic_spec_def using seq_assoc by simp
  finally show ?thesis .
qed

lemma atomic_spec_pre_internalise:
  shows "\<langle>p,q1\<rangle> = \<langle>p,p \<triangleleft> q1\<rangle>"
proof -
  have "idle;\<lbrace>p\<rbrace>;opt(q1);idle = idle;\<lbrace>p\<rbrace>;opt(p \<triangleleft> q1);idle" using opt_pre_internalise assert_seq_test seq_assoc by metis
  then show ?thesis unfolding atomic_spec_def by simp
qed

lemma atomic_spec_strengthen_post:
  assumes "q2 \<subseteq> q1"
  shows "\<langle>p,q1\<rangle> \<ge> \<langle>p,q2\<rangle>"
proof -
  have "idle;\<lbrace>p\<rbrace>;opt(q1);idle \<ge> idle;\<lbrace>p\<rbrace>;opt(q2);idle" using opt_strengthen assms seq_mono_right seq_mono_left by simp
  then show ?thesis unfolding atomic_spec_def by simp
qed

lemma atomic_spec_weaken_pre:
  assumes "p1 \<subseteq> p2"
  shows "\<langle>p1,q\<rangle> \<ge> \<langle>p2,q\<rangle>"
proof -
  have "idle;\<lbrace>p1\<rbrace>;opt(q);idle \<ge> idle;\<lbrace>p2\<rbrace>;opt(q);idle" using assert_iso assms seq_mono_right seq_mono_left by simp
  then show ?thesis unfolding atomic_spec_def by simp
qed

lemma strengthen_spec:
  assumes "r\<^sub>1 \<supseteq> p\<^sub>1 \<triangleleft>  r\<^sub>2" and "p\<^sub>1 \<subseteq> p\<^sub>2"
  shows "\<langle>p\<^sub>1, r\<^sub>1\<rangle> \<ge> \<langle>p\<^sub>2, r\<^sub>2\<rangle>"
proof -
  have "\<langle>p\<^sub>1, r\<^sub>1\<rangle> \<ge> \<langle>p\<^sub>1, p\<^sub>1 \<triangleleft> r\<^sub>2\<rangle>" (is "... \<ge> ?rhs") unfolding atomic_spec_def using assms
    by (simp add: opt_strengthen seq_mono_left seq_mono_right) 
  also have "?rhs = \<langle>p\<^sub>1, r\<^sub>2\<rangle>"
    using atomic_spec_pre_internalise by auto
  also have "... \<ge> \<langle>p\<^sub>2, r\<^sub>2\<rangle>" 
    using atomic_spec_weaken_pre assms(2) by simp
  finally show ?thesis.
qed


end
end