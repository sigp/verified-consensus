section \<open>Idle\<close>

theory Idle
imports
  "Specification"
  "Trading_RG"
begin
                              
locale idle_command = spec_trade_rely_guar + 
  constrains test :: "'state :: type set \<Rightarrow> 'a"
  constrains pgm  :: "'state rel \<Rightarrow> 'a" 
  constrains env  :: "'state rel \<Rightarrow> 'a"
begin

definition idle :: "'a::refinement_lattice"
  where "idle = (guar Id) \<iinter> term"
  
lemma idle_def2: "idle = (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
  using idle_def guar_conj_term by simp

lemma idle_def3: "idle = \<epsilon>(\<top>)\<^sup>\<omega>;(\<pi>(Id);\<epsilon>(\<top>)\<^sup>\<omega>)\<^sup>\<star>"
  using idle_def2 sup_commute par.fiter_decomp_iter by metis
  
lemma idle_seq_idle:
  shows "idle;idle = idle"
  using par.fiter_iter_seq idle_def2 sup_commute by metis

lemma idle_par_idle:
  shows "idle \<parallel> idle = idle"
  using term_par_term_generic idle_def2 by simp

lemma term_ref_idle:
  shows "term \<ge> idle"
proof -
  have "\<pi>(\<top>) \<squnion> \<epsilon>(\<top>) \<ge> \<pi>(Id) \<squnion> \<epsilon>(\<top>)"
    using nondet_mono_left Pgm_def pgm.Hom_ref_hom by metis    
  then have "(\<pi>(\<top>) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<ge> (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
    using fiter_mono seq_mono_left by metis
  then show ?thesis using term_def idle_def2 by metis
qed

lemma idle_ref_nil:
  shows "idle \<ge> nil"
  unfolding idle_def using term_nil by (metis conj.sync_mono_right guar_conj_nil local.conj_commute)

lemma idle_nonaborting:
  shows "chaos \<ge> idle"
  using term_nonaborting term_ref_idle by simp

lemma guar_idle:
  assumes g_reflexive: "refl g"
  shows "(guar g) \<iinter> idle = idle"
proof - 
  have "g \<inter> Id = Id" using g_reflexive unfolding refl_on_def by auto
  then show ?thesis unfolding idle_def
    by (metis conj.comm.left_commute guar_merge conj_commute) 
qed

lemma rely_idle_stable: 
  assumes p_stable_under_r: "stable p r"
  shows "(rely r) \<iinter> idle;\<tau>(p) \<ge> (rely r) \<iinter> \<tau>(p);idle"
proof -
  have "(rely r) \<iinter> idle;\<tau>(p) = (rely r) \<iinter> ((guar Id) \<iinter> term);\<tau>(p)"
    using idle_def by simp
  also have "... = (rely r) \<iinter> (guar Id);\<tau>(p) \<iinter> term"
    using conj_assoc by (metis conj.test_sync_post conj_commute)
  also have "... \<ge> (rely r) \<iinter> \<tau>(p);(guar Id) \<iinter> term" (is "_ \<ge> ?rhs")
  proof -
    have "((r \<union> Id)`` p) \<subseteq> p" (* p is stable under (r \<union> Id). *)
      using p_stable_under_r unfolding stable_def by blast
    then have "(rely r) \<iinter> (guar Id);\<tau>(p) \<ge> (rely r) \<iinter> \<tau>(p);(guar Id)"
      using rely_guar_stable p_stable_under_r stable_def by metis
    then show ?thesis using conj.sync_mono_left conj_assoc by metis
  qed
  also have "?rhs = (rely r) \<iinter> \<tau>(p);idle"
  proof -
    have "\<tau> p ; idle = \<tau> p ; guar Id \<iinter> term"
      using term_nonaborting idle_def local.conj_commute conj.nonaborting_sync_test_pre by presburger
    then show ?thesis
      using conj_assoc by simp
  qed
  finally show ?thesis .
qed

lemma rely_idle:
  assumes p_stable_under_r: "stable p r"
  shows "(rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* \<triangleright> p\<rparr> \<ge> (rely r) \<iinter> idle"
proof -
  have "p \<triangleleft> r\<^sup>* \<subseteq> r\<^sup>* \<triangleright> p"
    using stable_rtrancl p_stable_under_r
    unfolding restrict_domain_def restrict_range_def stable_def by blast
  then have "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>r\<^sup>* \<triangleright> p\<rparr> \<ge> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>r\<^sup>*\<rparr>" (is "_ \<ge> ?rhs")
    using conj.sync_mono_right spec_seq_introduce
    by (metis seq_mono_right assert_restricts_spec spec_strengthen) 
  also have "?rhs \<ge> (rely r) \<iinter> \<lparr>r\<^sup>*\<rparr>" (is "_ \<ge> ?rhs")
    using conj.sync_mono_right
    by (simp add: assert_galois_test test_seq_refine)
  also have "?rhs \<ge> (rely r) \<iinter> (guar Id) \<iinter> term" (is "_ \<ge> ?rhs")
    using spec_trade_rely_guar rtrancl_reflcl by metis
  also have "?rhs = (rely r) \<iinter> idle"
    using idle_def conj_assoc by simp
  finally show ?thesis .
qed

lemma stable_test: 
  assumes p_stable_under_r: "stable p r"
  shows "(rely r) \<iinter> \<tau>(p);idle = (rely r) \<iinter> \<tau>(p);idle;\<tau>(p)"
proof (rule antisym)
  show "(rely r) \<iinter> \<tau>(p);idle \<ge> (rely r) \<iinter> \<tau>(p);idle;\<tau>(p)"
    by (metis nil_ref_test conj.sync_mono_right seq_mono_right seq_assoc seq_nil_right)
next
  have "(rely r) \<iinter> \<tau>(p);idle;\<tau>(p) = \<tau>(p);((rely r) \<iinter> idle;\<tau>(p))"
    using test_pre_rely seq_assoc by metis
  also have "... \<ge> \<tau>(p);((rely r) \<iinter> \<tau>(p);idle)" (is "_ \<ge> ?rhs")
    using rely_idle_stable p_stable_under_r seq_mono_right by metis
  also have "?rhs = ((rely r) \<iinter> \<tau>(p);idle)"
    using test_pre_rely seq_assoc test_seq_idem by metis
  finally show "(rely r) \<iinter> \<tau>(p);idle;\<tau>(p) \<ge> (rely r) \<iinter> \<tau>(p);idle" .
qed
  
lemma stable_negate_test:
  assumes not_p_stable_under_r: "stable (-p) r"
  shows "(rely r) \<iinter> \<tau>(-p);idle;\<tau>(p);c = (rely r) \<iinter> \<tau>(-p);idle;\<tau>(p);d"
proof -
  have "(rely r) \<iinter> (\<tau>(-p);idle);\<tau>(p);c = (rely r) \<iinter> (\<tau>(-p);idle;\<tau>(-p));\<tau>(p);c"
    using stable_test not_p_stable_under_r equal_within_rely_left by metis
  also have "... = (rely r) \<iinter> (\<tau>(-p);idle;\<tau>(-p));\<tau>(p);d"
    using seq_assoc test_compl_seq by auto
  also have "... = (rely r) \<iinter> (\<tau>(-p);idle);\<tau>(p);d"
    using stable_test not_p_stable_under_r equal_within_rely_left by metis
  finally show ?thesis using seq_assoc by simp
qed

lemma tolerates_transitive :
  assumes tolerates_interference: "tolerates_interference p q r"
  shows "p \<triangleleft> r\<^sup>* O q O r\<^sup>* \<subseteq> q"
  by (simp add: domain_restrict_relcomp q_tolerates_rtrancl 
        tolerates_interference)

lemma tolerate_interference: 
  assumes tolerates_interference: "tolerates_interference p q r"
  shows "(rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>q\<rparr> = (rely r) \<iinter> idle;\<lbrace>p\<rbrace>;\<lparr>q\<rparr>;idle"
proof (rule antisym)
  have "(rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>q\<rparr> \<ge> (rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* O q O r\<^sup>*\<rparr>" (is "_ \<ge> ?rhs")
    using spec_strengthen_under_pre tolerates_transitive by (simp add: conj.sync_mono_right 
          q_tolerates_rtrancl tolerates_interference) 
  also have "?rhs \<ge> (rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* \<triangleright> p\<rparr>;\<lbrace>p\<rbrace>;\<lparr>q\<rparr>;\<lparr>r\<^sup>*\<rparr>" (is "_ \<ge> ?rhs")
  proof -
    have "\<forall>r C ra. \<lparr>ra \<triangleright> C\<rparr> ; (\<lbrace>C\<rbrace> ; \<lparr>r\<rparr>) \<le> \<lparr>ra O r\<rparr>"
      using seq_assoc spec_seq_introduce by force
    then have "\<lparr>r\<^sup>* \<triangleright> p\<rparr> ; (\<lbrace>p\<rbrace> ; (\<lparr>q\<rparr> ; \<lparr>r\<^sup>*\<rparr>)) \<le> \<lparr>r\<^sup>* O q O r\<^sup>*\<rparr>"
      by (meson order_trans seq_mono_right spec_to_sequential)
    then show ?thesis
      by (simp add: conj.sync_mono_right seq_assoc seq_mono_right)
  qed
  also have "?rhs \<ge> (rely r) \<iinter> idle;\<lbrace>p\<rbrace>;\<lparr>q\<rparr>;idle"
  proof -
    have "(rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>r\<^sup>* \<triangleright> p\<rparr>;\<lbrace>p\<rbrace>;\<lparr>q\<rparr>;\<lparr>r\<^sup>*\<rparr> \<ge> (rely r) \<iinter> idle;\<lbrace>p\<rbrace>;\<lparr>q\<rparr>;\<lbrace>\<top>\<rbrace>;\<lparr>r\<^sup>* \<triangleright> \<top>\<rparr>" (is "_ \<ge> ?rhs") using rely_idle 
      by (metis assert_top tolerates_interference_def refine_within_rely_left 
          seq_nil_right spec_test_restricts test_top tolerates_interference)
    also have "?rhs \<ge> (rely r) \<iinter> idle;\<lbrace>p\<rbrace>;\<lparr>q\<rparr>;idle" using rely_idle
      by (metis assert_iso assert_nil assert_top refine_within_rely_right seq_nil_left seq_nil_right stable_def)
    finally show ?thesis.
  qed
  finally (xtrans) show "(rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>q\<rparr> \<ge> (rely r) \<iinter> idle;\<lbrace>p\<rbrace>;\<lparr>q\<rparr>;idle".
next
  show "(rely r) \<iinter> \<lbrace>p\<rbrace>;\<lparr>q\<rparr> \<le> (rely r) \<iinter> idle;\<lbrace>p\<rbrace>;\<lparr>q\<rparr>;idle" using idle_ref_nil
    by (metis conj.sync_mono_right seq_assoc seq_mono seq_mono_right seq_nil_left seq_nil_right)
qed
  

(*
lemma rely_idle_spec: 
  shows "(rely r) \<iinter> \<lparr>r\<^sup>*\<rparr> \<ge> (rely r) \<iinter> idle"
proof -
  have "(rely r) \<iinter> \<lparr>r\<^sup>*\<rparr> = (rely r) \<iinter> \<ltort>\<top>,r\<^sup>*\<rparr>"
    using specpre_def by (simp add: assert_top)
  also have "... =  (rely r) \<iinter> \<ltort>\<top>,r\<^sup>* \<triangleright> \<top>\<rparr>"
  proof -
    have "r\<^sup>* = r\<^sup>* \<triangleright> \<top>" using restrict_range_def by auto
    then show ?thesis by simp
  qed
  also have "... \<ge> (rely r) \<iinter> idle"
  proof -
    have "\<top> \<triangleleft> r \<subseteq> range_restrict \<top>"
      using restrict_domain_def by auto
    then show ?thesis using rely_idle by simp
  qed
  finally show ?thesis .
qed*)
  

lemma idle_nonaborting_test_idle:
  shows "chaos \<ge> (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
proof -
  have "chaos \<ge> idle;idle" (is "_ \<ge> ?rhs")
    using idle_nonaborting idle_seq_idle by simp    
  also have "?rhs \<ge> idle;\<tau>(p);idle"
    by (metis seq_mono_left seq_mono_right seq_nil_right nil_ref_test)
  finally show ?thesis using idle_def2 seq_assoc by simp
qed
  
(* Idle synchronisation over par *)
lemma idle_sync_test_helper4:
  shows "((\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) = \<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
  using par.nonaborting_sync_test_pre idle_par_idle idle_def2 idle_nonaborting seq_assoc by metis
    
lemma idle_sync_test_helper3:
  shows "(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>
       = (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
proof -
  have "(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> = 
        ((\<pi>(Id) \<squnion> \<epsilon>(\<top>)) \<parallel> \<epsilon>(\<top>))\<^sup>\<star>;(
            (\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)  \<squnion>
            ((\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
          )"
    using par.atomic_fiter_pre_sync_iter_pre2 env_atomic pgm_or_env_atomic seq_assoc by metis
  also have "... = (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;(
            (\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) \<squnion>
            (nil;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
          )"
    using pgmenv_par_env skip_def par_skip_left idle_sync_test_helper4 unfolding Env_def by simp
  also have "... = (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;(((\<epsilon>(\<top>)\<^sup>\<omega> \<squnion> nil);\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>))"
    using nondet_seq_distrib seq_assoc by simp
  also have "... = (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
    by (simp add: sup_absorb1 iter0 seq_assoc)
  finally show ?thesis .
qed
  
lemma idle_sync_test_helper2:
  shows "((\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)) = 
         \<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
proof -
  have "((\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>))
      = \<tau>(p1);(((\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>))"
    using idle_nonaborting_test_idle par.nonaborting_sync_test_pre seq_assoc par_commute by fastforce
  also have "... = \<tau>(p1);(((\<pi>(Id) \<squnion> \<epsilon>(\<top>)) \<parallel> (\<pi>(Id) \<squnion> \<epsilon>(\<top>)))\<^sup>\<star>;(
      ((\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)) \<squnion>
      (((\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>))))"
    using par.atomic_fiter_pre_sync_fiter_pre2 env_atomic pgm_or_env_atomic seq_assoc by metis
  also have "... = \<tau>(p1);((\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;(
      (((\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)) \<squnion>
      (((\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>))))"
    using pgmenv_par_pgmenv skip_def par_skip_left unfolding Env_def by simp
  also have "... = \<tau>(p1);((\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;((\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>))"
    using skip_def par_skip_left idle_sync_test_helper3 by simp
  also have "... = \<tau>(p1);((\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>);\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
     using seq_assoc by metis
  also have "... = \<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
    by simp
  finally show ?thesis .
qed
  

lemma idle_sync_test_helper3b:
  shows "(\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) = 
         \<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
proof -
  have a1: "chaos \<ge> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
  proof -
    have "chaos \<ge> idle;idle" (is "_ \<ge> ?rhs")
      using idle_nonaborting idle_seq_idle by simp
    also have "?rhs \<ge> (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>" (is "_ \<ge> ?rhs")
      using idle_def2 seq_assoc by simp
    also have "?rhs \<ge> \<epsilon>(\<top>)\<^sup>\<omega>;(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>" (is "_ \<ge> ?rhs")
      using fiter0 seq_mono_left seq_nil_left by metis
    also have "?rhs \<ge> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
      by (metis seq_mono_left seq_mono_right seq_nil_right nil_ref_test)
    finally show ?thesis .
  qed
  have "(\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
      = \<tau>(p1);((\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)"
    using a1 par.nonaborting_sync_test_pre seq_assoc par_commute by fastforce
  also have "... = \<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
    using idle_sync_test_helper3 seq_assoc by simp
  finally show ?thesis .
qed
  
  
lemma idle_sync_test_helper2b:
  shows "(\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) 
    = (\<epsilon>(\<top>))\<^sup>\<omega>;(\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) \<squnion>
      (\<epsilon>(\<top>))\<^sup>\<omega>;(\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)"
proof -
  have "(\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) =
      (\<epsilon>(\<top>)\<parallel>\<epsilon>(\<top>))\<^sup>\<omega>;(
      (\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) \<squnion>
      (\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
    )"
    using par.atomic_iter_pre_sync_iter_pre2 env_atomic pgm_or_env_atomic seq_assoc by metis
  also have "... = (\<epsilon>(\<top>))\<^sup>\<omega>;(
      (\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) \<squnion>
      (\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
    )"
    using idle_sync_test_helper3b par_commute env_par_env_axiom by simp
  also have "... = 
      (\<epsilon>(\<top>))\<^sup>\<omega>;(\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) \<squnion>
      (\<epsilon>(\<top>))\<^sup>\<omega>;(\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
    "
    using par.seq_nondet_distrib by simp
  finally show ?thesis .
qed
  
lemma idle_sync_test_helper1:
  shows "(\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) = 
          (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<squnion>
          (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
proof -
  have "(\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
      = (\<epsilon>(\<top>) \<parallel> (\<pi>(Id) \<squnion> \<epsilon>(\<top>)))\<^sup>\<star>;(
        ((\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)) \<squnion>
        (\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
        )"
    using par.atomic_iter_pre_sync_fiter_pre2 env_atomic pgm_or_env_atomic seq_assoc by metis
  also have "... = (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>; (
        ((\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)) \<squnion>
        (\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
      )"
    using pgmenv_par_env par_commute by simp
  also have "... = (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;(
          (nil;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) \<squnion>
          (\<epsilon>(\<top>))\<^sup>\<omega>;(\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) \<squnion>
          (\<epsilon>(\<top>))\<^sup>\<omega>;(\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
      )"
    using idle_sync_test_helper2b idle_sync_test_helper2 by (simp add: sup_assoc)
   also have "... = (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;(
          (nil \<squnion> (\<epsilon>(\<top>))\<^sup>\<omega>);(\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) \<squnion>
          (\<epsilon>(\<top>))\<^sup>\<omega>;(\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)
      )"
    using nondet_seq_distrib seq_assoc by simp
   also have "... = (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;(
          \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<squnion>
          \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>
      )"
     by (simp add: sup_absorb2 iter0 seq_assoc)
   also have "... =
          (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<squnion>
          (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>
      "
    using par.seq_nondet_distrib seq_assoc by simp
   finally show ?thesis .
qed
  
lemma idle_sync_test:
  shows "idle;\<tau>(p1);idle \<parallel> idle;\<tau>(p2);idle = idle;\<tau>(p1);idle;\<tau>(p2);idle \<squnion> idle;\<tau>(p2);idle;\<tau>(p1);idle"
proof -
  have "idle;\<tau>(p1);idle \<parallel> idle;\<tau>(p2);idle = 
      (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
    using idle_def2 seq_assoc by simp
  also have "... = (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;
        ((\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>) \<squnion>
        ((\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> \<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>))"
    using par.atomic_fiter_pre_sync_fiter_pre2  env_atomic pgm_or_env_atomic seq_assoc
          pgmenv_par_pgmenv by metis
  also have "... = (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;
        ((\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<squnion>
          (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)"
    using idle_sync_test_helper1 par_commute by (simp add: sup_commute)
  also have "... = (
          (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<squnion>
          (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>)"
    using par.seq_nondet_distrib seq_assoc by metis
  also have "... = 
          (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<squnion>
          (\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p2);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>;\<tau>(p1);(\<pi>(Id) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>"
    by simp
  also have "... = idle;\<tau>(p1);idle;\<tau>(p2);idle \<squnion> idle;\<tau>(p2);idle;\<tau>(p1);idle"
    using idle_def2 seq_assoc by simp
  finally show ?thesis .
qed

lemma guar_conj_idle_test_idle:
  assumes g_reflexive: "refl g"
  shows "(guar g) \<iinter> idle;\<tau>(p);idle \<ge> idle;\<tau>(p);idle"
proof -
  have "(guar g) \<iinter> idle;\<tau>(p);idle \<ge> ((guar g) \<iinter> idle);((guar g) \<iinter> \<tau>(p);idle)" (is "_ \<ge> ?rhs")
    using guar_distrib_seq seq_assoc by simp
  also have "?rhs \<ge> ((guar g) \<iinter> idle);((guar g) \<iinter> \<tau>(p));((guar g) \<iinter> idle)" (is "_ \<ge> ?rhs")
    using guar_distrib_seq seq_assoc seq_mono_right by simp
  also have "?rhs \<ge> ((guar g) \<iinter> idle);\<tau>(p);((guar g) \<iinter> idle)"
  proof -
    have "(guar g) \<iinter> \<tau>(p) \<ge> nil \<iinter> \<tau>(p)" (is "_ \<ge> ?rhs")
      by (simp add: iter0 conj.sync_mono_left)
    also have "?rhs = \<tau>(p)"
      using nil_inf_test test_conj_to_inf test_top by metis
    finally show ?thesis using seq_mono_left seq_mono_right seq_assoc by metis
  qed
  finally show ?thesis using guar_idle g_reflexive by simp
qed  

lemma tolerate_interference_right:
  assumes tolerates_interference: "tolerates_interference p q r"
  shows "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> = (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>;idle" 
proof (rule antisym)
  have "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> \<ge> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q O r\<^sup>*\<rparr>" (is "_ \<ge> ?rhs")
    using q_tolerates_rtrancl_right tolerates_interference conj.sync_mono_right
    by (metis seq_mono_right assert_restricts_spec spec_strengthen)
  also have "?rhs \<ge> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>; \<lbrace>\<top>\<rbrace>; \<lparr>r\<^sup>* \<triangleright> \<top>\<rparr>" (is "_ \<ge> ?rhs")
    by (simp add: assert_top conj.sync_mono_right seq_assoc seq_mono spec_to_sequential 
        spec_test_restricts test_top)
  also have "?rhs \<ge> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>;idle"
    using refine_within_rely_right rely_idle unfolding stable_def
    by (metis assert_iso assert_nil assert_top seq_nil_left seq_nil_right) 
  finally show "(rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr> \<ge> (rely r) \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>;idle" .
next
  show "rely r \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>;idle \<ge> rely r \<iinter> \<lbrace>p\<rbrace>; \<lparr>q\<rparr>"
    using idle_ref_nil conj.sync_mono_right seq_mono_right by force
qed
    
end
end