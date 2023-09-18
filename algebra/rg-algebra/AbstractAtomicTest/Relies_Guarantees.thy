section \<open>Relies combined with guarantees\<close>

theory Relies_Guarantees
imports
  "Relies"
  "Guarantees"
  "Constrained_Atomic_Commands"
begin

locale relies_guarantees = constrained_atomic + relies + guarantees +
  constrains env  :: "('state \<times> 'state) set \<Rightarrow> 'a"
  constrains pgm  :: "('state \<times> 'state) set \<Rightarrow> 'a"
  constrains test :: "'state set \<Rightarrow> 'a"
begin

lemma rely_guar_def:
  shows "(rely r) \<iinter> (guar g) = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>)"
proof -
  have "(rely r) \<iinter> (guar g) = (\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>"
    using rely_def3 guar_def pgm_restrict_def Env_def by simp
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon>(r)) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>)))\<^sup>\<omega>;((nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>)"
    using conj.atomic_iter_pre_sync_iter pgm_or_env_atomic by metis
  also have "... = ((\<pi>(\<top> \<sqinter> g) \<squnion> \<epsilon>(r \<sqinter> \<top>)))\<^sup>\<omega>;((nil \<squnion> \<epsilon>(-r);\<top>) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>))\<^sup>\<omega>)"
    using pgmenv_conj_pgmenv pgmenv_conj_env by presburger
  also have "... = ((\<pi>(\<top> \<sqinter> g) \<squnion> \<epsilon>(r \<sqinter> \<top>)))\<^sup>\<omega>;(nil \<squnion> (\<epsilon>(-r) \<iinter> (\<pi>(g) \<squnion> \<epsilon>(\<top>)));\<top>)"
    using conj.atomic_optional_sync_iter pgm_or_env_atomic env_atomic conj_abort_left by metis
  also have "... = ((\<pi>(\<top> \<sqinter> g) \<squnion> \<epsilon>(r \<sqinter> \<top>)))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r \<sqinter> \<top>);\<top>)"
    by (metis inf_top.right_neutral inf_top_left local.conj_commute pgmenv_conj_env)
  finally show ?thesis by simp
qed  

lemma rely_guar_stable_step:
  assumes p_stable_under_rg: "stable p (r \<union> g)"
  shows "(\<pi>(g) \<squnion> \<epsilon>(r));\<tau>(p) \<ge> \<tau>(p);(\<pi>(g) \<squnion> \<epsilon>(r))"
proof -
  have "\<pi>(g);\<tau>(p) \<ge> \<tau>(p);\<pi>(g)"
    using pgm_test_ref p_stable_under_rg unfolding stable_def by blast
  moreover have "\<epsilon>(r);\<tau>(p) \<ge> \<tau>(p);\<epsilon>(r)"
      using env_test_ref p_stable_under_rg unfolding stable_def by blast
  ultimately show ?thesis 
    using sup_mono nondet_seq_distrib par.seq_nondet_distrib by simp
qed

(* Lemma 18 *)
lemma rely_guar_stable: 
  assumes p_stable_under_rg: "stable p (r \<union> g)"
  shows "(rely r) \<iinter> (guar g);\<tau>(p) \<ge> (rely r) \<iinter> \<tau>(p);(guar g)"
proof -
  have "(rely r) \<iinter> (guar g);\<tau>(p) \<ge> ((rely r) \<iinter> (guar g));\<tau>(p)" (is "_ \<ge> ?rhs")
    using rely_seq_distrib test_rely_conj conj_commute by metis
  also have "?rhs = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>);\<tau>(p)"
    using rely_guar_def by simp 
  also have "... = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(\<tau>(p) \<squnion> \<epsilon>(-r);\<top>)"
     using nondet_seq_distrib seq_abort seq_assoc by simp
  also have "... \<ge> (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(\<tau>(p) \<squnion> \<tau>(p);\<epsilon>(-r);\<top>)" (is "_ \<ge> ?rhs")
    using seq_mono_right nondet_mono_right seq_mono_left 
          nil_ref_test seq_nil_left by metis
  also have "?rhs = (\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;\<tau>(p);(nil \<squnion> \<epsilon>(-r);\<top>)"
    using par.seq_nondet_distrib seq_assoc by simp
  also have "... \<ge> \<tau>(p);(\<pi>(g) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>)" (is "_ \<ge> ?rhs")
    using rely_guar_stable_step iter_test_pre
          seq_mono_left p_stable_under_rg by simp
  also have "?rhs = \<tau>(p);((rely r) \<iinter> (guar g))"
    using rely_guar_def seq_assoc by simp
  also have "... = (rely r) \<iinter> \<tau>(p);(guar g)"
    using test_pre_rely by simp
  finally show ?thesis .
qed

lemma guar_opt: 
  assumes refl: "refl g"
  shows "(guar g) \<iinter> (opt q) = opt(g \<inter> q)"
proof -
  have "(guar g) \<iinter> (opt q) = (\<pi>(g) \<squnion> \<E>)\<^sup>\<omega> \<iinter> (\<pi>(q) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>) \<in> q}))"
    unfolding opt_def guar_def pgm_restrict_def by simp
  also have "... = (nil \<squnion> (\<pi>(g) \<squnion> \<E>);(\<pi>(g) \<squnion> \<E>)\<^sup>\<omega>) \<iinter> (\<pi>(q) \<squnion> \<tau>({\<sigma>. (\<sigma>,\<sigma>) \<in> q}))"
    using iter_unfold by simp
  also have "... = \<tau>({\<sigma>. (\<sigma>,\<sigma>) \<in> q}) \<squnion> \<pi>(g \<inter> q)"
  proof -
    obtain ag where b1: "atomic ag = \<pi>(g) \<squnion> \<E>" using pgm_restrict_atomic by (metis pgm_restrict_def)
    obtain aq where b2: "atomic aq = \<pi>(q)" using pgm_atomic by metis
    have b3: "((\<pi>(g) \<squnion> \<E>);(\<pi>(g) \<squnion> \<E>)\<^sup>\<omega> \<iinter> \<tau>({\<sigma>. (\<sigma>,\<sigma>) \<in> q})) = \<bottom>" 
      by (metis (no_types, lifting) b1 conj.atomic_pre_sync_nil conj.atomic_pre_sync_test_pre seq_nil_right test_seq_magic)
    moreover have "nil \<iinter> \<pi>(q) = \<bottom>" using conj.atomic_pre_sync_nil pgm_atomic conj_commute seq_nil_right by metis
    moreover have "(\<pi>(g) \<squnion> \<E>);(\<pi>(g) \<squnion> \<E>)\<^sup>\<omega> \<iinter> \<pi>(q) = \<pi>(g \<inter> q)"  
    proof -
      have "(atomic ag)\<^sup>\<omega> \<iinter> nil = nil" using conj.atomic_iter_sync_nil by simp
      moreover have "(atomic ag) \<iinter> (atomic aq) = \<pi>(g \<inter> q)"
        unfolding b1 b2
        using conj.nondet_sync_distrib local.conj_commute pgm_conj_atomid pgm_conj_pgm by auto
      ultimately show ?thesis using conj.atomic_pre_sync_atomic_pre b1 b2 seq_nil_right by metis
    qed
    moreover have "nil \<iinter> \<tau>({\<sigma>. (\<sigma>,\<sigma>) \<in> q}) = \<tau>({\<sigma>. (\<sigma>,\<sigma>) \<in> q})"
      using conj.sync_commute conj.test_sync_nil by auto
    ultimately show ?thesis using conj.nondet_sync_product by simp
  qed
  also have "... = opt(g \<inter> q)"
  proof -
    have "{\<sigma>. (\<sigma>,\<sigma>) \<in> q} = {\<sigma>. (\<sigma>,\<sigma>) \<in> (g \<inter> q)}"
      using refl unfolding refl_on_def by auto
    then show ?thesis unfolding opt_def by (simp add: sup_commute)
  qed
  finally show ?thesis .
qed

abbreviation P' :: "'b set \<Rightarrow> 'b rel" where
"P' p \<equiv> {(k, k'). k \<in> p \<longrightarrow> k' \<in> p}"

definition
guar_inv :: "('state set) \<Rightarrow> 'a" where
"guar_inv p = (guar (P' p))"

(*

(* localise over relies and guarantees *)

text_raw \<open>\DefineSnippet{relyuniv}{\<close>
lemma localise_rely: "E\<^sup>C\<^sub>x (rely r) = rely (lib_univ x r)" (* Lemma 7 *)
text_raw \<open>}%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot 
    test.hom_iso_eq test_lib test.hom_not test_top
  by (metis (full_types))

text_raw \<open>\DefineSnippet{librely}{\<close>
lemma lib_rely: "r = (E\<^sup>R\<^sub>x r) \<Longrightarrow> (rely (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (rely r))"
text_raw \<open>}%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot 
      test.hom_iso_eq test_lib test.hom_not test_top
  by (metis (full_types))

(* Lemma 8 - localise_gdr *)
text_raw \<open>\DefineSnippet{libguar}{\<close>
lemma localise_guar: "((E\<^sup>R\<^sub>x r) = (bool_last x r)) \<Longrightarrow> (guar (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (guar r))" (* 68 *)
text_raw \<open>}%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot test.hom_iso_eq test_lib 
      test.hom_not test_top
  by (metis (full_types))

text_raw \<open>\DefineSnippet{libdem}{\<close>
lemma localise_dem: "((E\<^sup>R\<^sub>x r) = (bool_last x r)) \<Longrightarrow> (demand (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (demand r))" (* 69 *)
text_raw \<open>}%EndSnippet\<close>
  using compl_bot_eq empty_not_UNIV fun_Compl_def lib_sigma test.hom_bot test.hom_iso_eq test_lib 
      test.hom_not test_top
  by (metis (full_types))

lemma localise_relies: "((E\<^sup>R\<^sub>x r) = r) \<Longrightarrow> (rely (E\<^sup>R\<^sub>x r) = E\<^sup>C\<^sub>x (rely r))" (* 70 *)
  using lib_rely by blast

end *)

end
end
