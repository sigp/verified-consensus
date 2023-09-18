section \<open>Termination\<close>

theory Termination
imports
  "ParallelFlip"
begin
  
locale term_op = parallel_flip (* lib_first
  for lib_first :: "'b \<Rightarrow> 'a::refinement_lattice \<Rightarrow> 'a" ("F\<^sup>C\<^sub>_ _" [999, 999] 999) *)
begin

definition terminate :: "'a::refinement_lattice" ("term")
  where "term = (\<pi>(\<top>) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega>" 

(* Exists only as a copy of terminate_def, with a shorter name. We cannot
   change the definition name from terminate to term because of reserved keyword issues. *)
lemmas term_def = terminate_def

lemma term_def2: "term = \<E>\<^sup>\<omega>;(Pgm;\<E>\<^sup>\<omega>)\<^sup>\<star>"
  using term_def sup_commute par.fiter_decomp_iter Env_def Env_def Pgm_def by metis

lemma term_def3: "term = \<epsilon>(\<top>)\<^sup>\<omega>;(\<pi>(\<top>);\<epsilon>(\<top>)\<^sup>\<omega>)\<^sup>\<star>"
  using term_def sup_commute par.fiter_decomp_iter by metis

lemma term_nonaborting: "chaos \<ge> term"
proof -
  have "(Pgm \<squnion> \<E>)\<^sup>\<omega> \<ge> \<E>\<^sup>\<omega>;(Pgm;\<E>\<^sup>\<omega>)\<^sup>\<star>"
    by (simp add: sup_commute par.iter_decomp iter_ref_fiter seq_mono)
  then show ?thesis using chaos_rel term_def2 by metis
qed

lemma seq_term_term: "term = term;term"
  using par.fiter_iter_seq term_def sup_commute by metis

lemma term_nil: "term \<ge> nil"
  unfolding term_def using iter0 fiter0 seq_mono by fastforce

lemma term_par_term_generic:
  shows "(\<pi>(r) \<squnion>  \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> \<parallel> (\<pi>(r) \<squnion>  \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> = (\<pi>(r) \<squnion> \<epsilon>(\<top>))\<^sup>\<star>;\<epsilon>(\<top>)\<^sup>\<omega> "
proof -
  define a0 where "a0 \<equiv> \<pi>(r) \<squnion> \<epsilon>(\<top>)"
  define a1 where "a1 \<equiv> \<epsilon>(\<top>)"
  have a1: "(a0)\<^sup>\<star>;a1\<^sup>\<omega> \<parallel> a0\<^sup>\<star>;a1\<^sup>\<omega> =(a0\<parallel>a0)\<^sup>\<star>;(a1\<parallel>a0)\<^sup>\<star>;(a1\<parallel>a1)\<^sup>\<omega>"
    unfolding  a0_def a1_def using par.atomic_fiter_iter_sync_fiter_iter_symmetric 
        env_atomic pgm_or_env_atomic by metis
  moreover have "a0\<parallel>a0 = a0" using pgmenv_par_pgmenv a0_def by simp
  moreover have "a0\<parallel>a1 = a0" using pgmenv_par_env a0_def a1_def by simp
  moreover have "a1\<parallel>a1 = a1" unfolding a1_def by (simp add: env_par_env_axiom)
  ultimately have "(a0)\<^sup>\<star>;a1\<^sup>\<omega> \<parallel> a0\<^sup>\<star>;a1\<^sup>\<omega>  = (a0)\<^sup>\<star>;a1\<^sup>\<omega>"
    by (simp add: par_commute)
  then show ?thesis unfolding term_def a0_def a1_def by metis
qed

lemma par_term_term:
  shows "term \<parallel> term = term"
  using term_par_term_generic term_def by simp
  
end
end