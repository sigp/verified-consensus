section \<open>Relies as mapping over abstract $\pgm$-steps\<close>

theory Relies
imports
  "PgmEnv_Commands"

begin

locale env_assump = pgm_env_commands + 
  constrains env :: "'step :: complete_boolean_algebra \<Rightarrow> 'a :: refinement_lattice" 
  constrains pgm :: "'step::complete_boolean_algebra \<Rightarrow> 'a ::refinement_lattice" 
begin
  
definition
  env_assump:: "'step :: complete_boolean_algebra \<Rightarrow> 'a :: refinement_lattice"
where
  env_assump_def [simp]: "env_assump r = (\<epsilon>(r) \<squnion> Pgm) \<squnion> (atomic.negate(\<epsilon>(r)) \<sqinter> \<E>);\<top>"

lemma negate_env_sup_Env: "(atomic.negate(\<epsilon>(p)) \<sqinter> \<E>) = atomic.negate(\<epsilon>(p) \<squnion> Pgm)"
  using env_negate_def2 env_negate_def3 by auto

lemma env_assump_def1: "env_assump r = (\<epsilon>(r) \<squnion> Pgm) \<squnion> atomic.negate(\<epsilon>(r) \<squnion> Pgm);\<top>"
   by (metis negate_env_sup_Env env_assump_def)

lemma env_assump_def2: "env_assump r = assump(\<epsilon>(r) \<squnion> Pgm)" 
  using pgm_or_env_atomic env_assump_def1 assump_atomic by (metis env_or_Pgm_atomic)

lemma env_assump_def3: "env_assump r = assump(atomic.negate(\<epsilon>(-r)))"
  by (metis (no_types) atomic_negate_env double_compl env.hom_not env_assump_def2)

lemma env_assump_def4: "env_assump r = atomic.negate(\<epsilon>(-r)) \<squnion> \<epsilon>(-r);\<top>"
  by (metis atomic_negate_env double_compl env_assump_def1 env_negate_def3 env.hom_not)

lemma env_assump_def5: "env_assump r = \<epsilon>(r) \<squnion> \<pi>(\<top>) \<squnion> \<epsilon>(-r);\<top>"
  using env_assump_def1 env_negate_def3 Pgm_def by simp

lemma env_assump_top:
  shows "env_assump(\<top>) = (\<epsilon> \<top> \<squnion> \<pi> \<top>)"
  using env_assump_def5 by simp
    
lemma env_assump_conj:  "env_assump(r1) \<iinter> env_assump(r2) = env_assump(r1 \<sqinter> r2)"
proof -
  have a1: "env_assump(r1) \<iinter> env_assump(r2) = assump(\<epsilon>(r1) \<squnion> Pgm) \<iinter> assump(\<epsilon>(r2) \<squnion> Pgm)"
    using env_assump_def2 by auto
  then have a2: "... = assump((\<epsilon>(r1) \<squnion> Pgm) \<sqinter> (\<epsilon>(r2) \<squnion> Pgm))" 
    using assump_conj by (metis env_or_Pgm_atomic) 
  then have a3: "... = assump((\<epsilon>(r1) \<sqinter> \<epsilon>(r2)) \<squnion> (Pgm \<sqinter> \<epsilon>(r2)) 
                       \<squnion> (\<epsilon>(r1) \<sqinter> Pgm) \<squnion> (Pgm \<sqinter> Pgm))"
    by (simp add: Pgm_def pgm_env_distinct inf.nondet_sync_product) 
  then have a4: "... = assump((\<epsilon>(r1) \<sqinter> \<epsilon>(r2)) \<squnion> Pgm)" by (simp add: sup_inf_distrib2) 
  thus ?thesis by (metis a2 env.hom_inf sup_inf_distrib2 env_assump_def2)  
qed

lemma env_assump_inter: "env_assump(r1) \<squnion> env_assump(r2) = env_assump(r1 \<sqinter> r2)" 
    using env_assump_def2 assump_inter
    by (metis env.hom_inf env_or_Pgm_atomic sup_inf_distrib2)

lemma env_assump_weaken: 
  assumes "r1 \<le> r2"  
  shows "env_assump(r1) \<ge> env_assump(r2)"
  by (metis assms env_assump_inter inf.absorb_iff2 le_iff_sup)


lemma env_assump_par_nil: "(env_assump r);c \<parallel> nil = \<bottom>"
  proof -
    have a1: "(env_assump r);c \<parallel> nil = (atomic.negate(\<epsilon>(-r));c \<squnion> \<epsilon>(-r);\<top>) \<parallel> nil"
      using env_assump_def4 nondet_seq_distrib seq_assoc by simp
   have a2: "... = (atomic.negate(\<epsilon>(-r));c  \<parallel> nil) \<squnion> (\<epsilon>(-r);\<top> \<parallel> nil)"
     by (simp add: par.nondet_sync_distrib)
   thus ?thesis
     by (metis a1 atomic.hom_not env_negate_def2 env.hom_not sup_bot_right negate_env_sup_Env_atomic 
               par.nil_sync_atomic_pre par_commute)
qed

end

(*------------------------------------------------------------------*)

locale env_restrict = env_assump +
  constrains env :: "'step :: complete_boolean_algebra \<Rightarrow> 'a :: refinement_lattice" 
  constrains pgm :: "'step::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice" 
begin
  
definition
  restrict :: "'step::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice"
where
  restrict_def [simp]: "restrict r = (\<epsilon>(r) \<squnion> Pgm)"

lemma restrict_strengthen:
  assumes "r2 \<le> r1"
  shows "restrict r1 \<ge> restrict r2" using assms nondet_mono_left restrict_def env.hom_mono by force 

lemma restrict_nonaborting: "chaos \<ge> restrict r"
     by (metis Pgm_nonaborting Atomic_nonaborting Atomic_ref_env sup.absorb_iff2 sup_mono restrict_def)

lemma restrict_iter_nonaborting: "chaos \<ge> (restrict r)\<^sup>\<omega>"
   by (metis chaos_def Atomic_ref_env iter_mono le_supI Pgm_def Atomic_ref_pgm restrict_def)  


lemma restrict_atomic: "\<exists>q. atomic(q) = restrict r" using pgm_atomic env_atomic
    using env_or_Pgm_atomic restrict_def by auto

lemma env_assump_def6: "env_assump r = restrict r \<squnion> atomic.negate(restrict(r));\<top>" 
    using env_assump_def1 restrict_def by auto 

lemma restrict_conj_to_inf: "restrict r1 \<iinter> restrict r2 = restrict(r1 \<sqinter> r2)"
   by (metis conj_to_inf_nonaborting env.hom_inf sup_inf_distrib2 restrict_def restrict_nonaborting)

lemma restrict_iter_conj_to_inf: "(restrict r1)\<^sup>\<omega> \<iinter> (restrict r2)\<^sup>\<omega> = (restrict(r1 \<sqinter> r2))\<^sup>\<omega>"
     by (metis conj.atomic_iter_sync_iter env_or_Pgm_atomic restrict_conj_to_inf restrict_def)

lemma restrict_iter_distrib_seq: 
     "(restrict r)\<^sup>\<omega> \<iinter> (c ; d) \<ge> ((restrict r)\<^sup>\<omega> \<iinter> c) ; ((restrict r)\<^sup>\<omega> \<iinter> d)"
  using conj_seq_distrib iter_seq_iter by (simp add: seq_conj_interchange)

lemma restrict_conj_env_assump: "(restrict r) \<iinter> (env_assump r) = (restrict r)"
     by (metis assump_conj_atomic conjunction.conj_commute conjunction_axioms 
           env_or_Pgm_atomic env_assump_def2 restrict_def)  

end

(*--------------------------------------------------------*)

locale relies = env_restrict + env_assump +
  constrains env :: "'step :: complete_boolean_algebra \<Rightarrow> 'a :: refinement_lattice" 
  constrains pgm :: "'step::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice" 

begin
  
definition
  rely:: "'step::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice"
where
  rely_def [simp]: "rely r = (env_assump r)\<^sup>\<omega>"

lemma rely_top:
  shows "(rely \<top>) = chaos"
  unfolding rely_def using chaos_def2 env_assump_top sup_commute by metis

lemma restrict_iter_top:
  shows "(restrict \<top>)\<^sup>\<omega> = chaos"
  unfolding restrict_def Pgm_def using chaos_def2 env_assump_top sup_commute by metis

lemma rely_def2: "(rely r) = (restrict r)\<^sup>\<omega> \<squnion> (restrict r)\<^sup>\<omega>;atomic.negate(restrict(r));\<top>"
proof -
  have f1: "(env_assump r) = restrict r \<squnion> atomic.negate (restrict r) ; \<top>"
    using env_assump_def6 by blast
  have "(atomic.negate (restrict r) ; \<top> ; (restrict r)\<^sup>\<omega>)\<^sup>\<omega> = nil \<squnion> atomic.negate (restrict r) ; \<top>"
    by (metis iter_unfold seq_assoc seq_abort)
  then show ?thesis
    using f1 by (simp add: par.iter_decomp par.seq_nondet_distrib seq_assoc) 
qed 

lemma rely_def3: "(rely r) = ((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>))"
proof -
  have "(rely r) =  ((restrict r)\<^sup>\<omega> \<squnion> (restrict r)\<^sup>\<omega>;atomic.negate(restrict(r));\<top>)"
    using rely_def2 by simp
  also have "... = ((restrict r)\<^sup>\<omega>;(nil \<squnion> atomic.negate(restrict(r));\<top>))"
    by (simp add: par.seq_nondet_distrib seq_assoc)
  also have "... = ((\<pi>(\<top>) \<squnion> \<epsilon>(r))\<^sup>\<omega>;(nil \<squnion> \<epsilon>(-r);\<top>))"
    by (metis env_negate_def3 env.hom_not sup_commute Pgm_def restrict_def)
  finally show ?thesis .
qed   
      
subsection \<open>Rely-Restrict Galois connection, Theorem 3 in [CHM16]\<close>

lemma restrict_iter_conj_rely_helper1:
    "((restrict e);(restrict e)\<^sup>\<omega>;nil \<iinter> atomic.negate(restrict(e));\<top>) = \<bottom>"
proof -
   have "((restrict e);(restrict e)\<^sup>\<omega>;nil \<iinter> atomic.negate(restrict(e));\<top>) = 
                    ((restrict e) \<iinter> atomic.negate(restrict(e)));((restrict e)\<^sup>\<omega>;nil \<iinter> \<top>)" 
     using restrict_atomic conj.atomic_pre_sync_atomic_pre by (metis atomic.hom_not seq_nil_right) 
   thus ?thesis using restrict_atomic atomic.hom_compl_sup atomic_conj_inf seq_magic_left
     by (metis atomic.hom_not inf.sync_commute)
qed

lemma restrict_iter_conj_rely_helper2:
    "(restrict r)\<^sup>\<omega> \<ge> (restrict r)\<^sup>\<omega> \<iinter> (restrict r)\<^sup>\<omega>;atomic.negate(restrict(r));\<top>" (is "?L \<ge> ?R")
proof - 
   have a1: "?R = (restrict r)\<^sup>\<omega>;nil \<iinter> (restrict r)\<^sup>\<omega>;atomic.negate(restrict(r));\<top>" by simp
   then have a2: "... = ((restrict r)\<^sup>\<omega> \<iinter> (restrict r)\<^sup>\<omega>); 
                  ((nil \<iinter> atomic.negate(restrict(r));\<top>) \<squnion> 
                   (nil \<iinter> (restrict r);(restrict r)\<^sup>\<omega>;atomic.negate(restrict(r));\<top>) \<squnion>
                   ((restrict r);(restrict r)\<^sup>\<omega>;nil \<iinter> atomic.negate(restrict(r));\<top>))"
      proof -
        have f1: "(\<epsilon>(r) \<squnion> Pgm)\<^sup>\<omega> ; nil \<iinter> (\<epsilon>(r) \<squnion> Pgm)\<^sup>\<omega> ; (atomic.negate (restrict r) ; \<top>) = 
                                   (restrict r)\<^sup>\<omega> ; nil \<iinter> (restrict r)\<^sup>\<omega> ; atomic.negate (restrict r) ; \<top>"
          using restrict_def sequential.seq_assoc sequential_axioms by fastforce
        obtain bb  where
               f2: "\<forall>d. atomic (bb d) = \<epsilon> d \<squnion> Pgm" by (meson env_or_Pgm_atomic)
        have f3: "nil \<iinter> atomic.negate(restrict r);\<top> \<squnion> 
                    nil \<iinter> (\<epsilon>(r) \<squnion> Pgm);(\<epsilon>(r) \<squnion> Pgm)\<^sup>\<omega>;(atomic.negate(restrict r) ; \<top>) \<squnion> 
                    (\<epsilon>(r) \<squnion> Pgm);(\<epsilon>(r) \<squnion> Pgm)\<^sup>\<omega>;nil \<iinter> atomic.negate(restrict r);\<top> = 
                 nil \<iinter> atomic.negate (restrict r);\<top> \<squnion> 
                    nil \<iinter> restrict r;(restrict r)\<^sup>\<omega>;atomic.negate(restrict r);\<top> \<squnion> 
                    restrict r ; (restrict r)\<^sup>\<omega> ; nil \<iinter> atomic.negate (restrict r) ; \<top>"
          using restrict_def sequential.seq_assoc sequential_axioms by fastforce
          have f4: "(restrict r)\<^sup>\<omega> \<iinter> (restrict r)\<^sup>\<omega> = (restrict r)\<^sup>\<omega>"  by auto
        have "(\<epsilon>(r) \<squnion> Pgm) \<iinter> (\<epsilon>(r) \<squnion> Pgm) = restrict r" using restrict_def by force
        then show ?thesis using f4 f3 f2 f1 by (metis conj.atomic_iter_pre_sync_iter_pre)
     qed
   then have a3: "... = (restrict r)\<^sup>\<omega>;(\<bottom> \<squnion> \<bottom> \<squnion> 
                 ((restrict r);(restrict r)\<^sup>\<omega>;nil \<iinter> atomic.negate(restrict(r));\<top>))"
    using restrict_atomic conj.nil_sync_atomic_pre by (metis atomic.hom_not conj_idem seq_assoc)
   then have a4: "... = (restrict r)\<^sup>\<omega>;\<bottom>"  using restrict_iter_conj_rely_helper1 by auto
   then have a5: "... = (restrict r)\<^sup>\<infinity>"  by (simp add: infiter_iter_magic)
   thus ?thesis using a1 a2 a3 a4 a5 by (simp add: iter_ref_infiter) 
qed

lemma restrict_iter_conj_rely:  (* Lemma 1, p.16, [CHM16] *)
  "(restrict r)\<^sup>\<omega> \<iinter> (rely r) = (restrict r)\<^sup>\<omega>"
proof -
  have a1: "(restrict r)\<^sup>\<omega> \<iinter> (rely r) = 
               (restrict r)\<^sup>\<omega> \<iinter>  ((restrict r)\<^sup>\<omega> \<squnion> (restrict r)\<^sup>\<omega>;atomic.negate(restrict(r));\<top>)"
    using rely_def2 by auto
  then have a2: "... = ((restrict r)\<^sup>\<omega> \<iinter>  (restrict r)\<^sup>\<omega>) \<squnion>
                          ((restrict r)\<^sup>\<omega> \<iinter> (restrict r)\<^sup>\<omega>;atomic.negate(restrict(r));\<top>)"
    using conj.sync_nondet_distrib by blast
  then have a3: "... = (restrict r)\<^sup>\<omega> \<squnion> ((restrict r)\<^sup>\<omega> \<iinter> (restrict r)\<^sup>\<omega>;atomic.negate(restrict(r));\<top>)"
    by simp
  then have a4: "... = (restrict r)\<^sup>\<omega>" using restrict_iter_conj_rely_helper2 by (metis sup.orderE) 
  thus ?thesis using a1 a2 a3 by simp
qed

lemma restrict_conj_com:    (* Lemma 2, p.16, [CHM16] *)
 "(restrict r) \<iinter> c \<ge> (restrict r) \<iinter> d \<longleftrightarrow> c \<ge> (restrict r) \<iinter> d" (is "?L \<longleftrightarrow> ?R")
proof -
  have a1: "?L \<Longrightarrow> ?R"
     by (metis (no_types) restrict_nonaborting conj_conjoin_non_aborting dual_order.trans 
         local.conj_commute) 
   have "?R \<Longrightarrow> ?L"
     by (metis conj.left_idem conj.sync_mono_right)
  thus ?thesis using a1 by blast 
qed


lemma rely_restrict_galois:            (* Theorem 3, p.16, [CHM16] *)
  "(rely r) \<iinter> c \<ge> d \<Longrightarrow> c \<ge> (restrict r)\<^sup>\<omega> \<iinter> d" 
proof -
  assume a1: "(rely r) \<iinter> c \<ge> d"
  then have a2: "(restrict r)\<^sup>\<omega> \<iinter> (rely r) \<iinter> c \<ge> (restrict r)\<^sup>\<omega> \<iinter> d"
    by (metis conj.sync_assoc conj.sync_mono_right)
  then have a3: "(restrict r)\<^sup>\<omega> \<iinter> c \<ge> (restrict r)\<^sup>\<omega> \<iinter> d"
    using restrict_iter_conj_rely by auto
  then have a4: "c \<ge> (restrict r)\<^sup>\<omega> \<iinter> c"
    using restrict_iter_nonaborting conj.sync_commute conj_conjoin_non_aborting by fastforce
  thus ?thesis using a3 order.trans by auto
qed

lemma restrict_iter_strengthen:
  assumes "r2 \<le> r1"
  shows "(restrict r1)\<^sup>\<omega> \<ge> (restrict r2)\<^sup>\<omega>" 
    using assms iter_mono restrict_strengthen by simp
 
lemma rely_weaken: 
  assumes "r1 \<le> r2"
  shows "rely r1 \<ge> rely r2" using env_assump_weaken iter_mono assms by simp

lemma rely_restrict_galois_reverse:            (* Theorem 3 reverse: when does it hold? *)
  assumes r_stronger: "r1 \<le> r"    (* equals the assumption "\<epsilon>(r) \<ge> \<epsilon>(r1)" *)
  assumes d_normal: "d = (restrict r1)\<^sup>\<omega> \<iinter> d"
  shows "c \<ge> (restrict r)\<^sup>\<omega> \<iinter> d \<Longrightarrow> (rely r) \<iinter> c \<ge> d"  
proof -
  assume a1: "c \<ge> (restrict r)\<^sup>\<omega> \<iinter> d"
  then have a2: "(rely r) \<iinter> c \<ge> (restrict r)\<^sup>\<omega> \<iinter> (rely r) \<iinter> d"
<<<<<<< HEAD
    by (metis (no_types, opaque_lifting) conj.sync_assoc conj.sync_commute conj.sync_mono_left) 
=======
    by (metis (no_types) conj.sync_assoc conj.sync_commute conj.sync_mono_left) 
>>>>>>> a87ff0585792b159a497ae6dae5b85c93f31726d
  then have a3: "(rely r) \<iinter> c \<ge> (restrict r)\<^sup>\<omega> \<iinter> d"
    using assms restrict_iter_conj_rely by auto
  thus ?thesis using d_normal a3 conj.sync_mono_left le_sup_iff 
      r_stronger restrict_iter_strengthen sup.absorb_iff2 by metis
qed

lemma rely_seq_idem: "(rely r) ; (rely r) = (rely r)" by simp 

(*
lemma rely_conj: "(rely r) \<iinter> (rely r) = (rely r)" by simp

lemma rely_inf_distrib: "(rely r) \<iinter> (c \<sqinter> d) = ((rely r) \<iinter> c) \<sqinter> ((rely r) \<iinter> d)"
    by (simp add: inf_conj_distrib local.conj_commute)

(*
lemma rely_distrib_sup: "(rely r) \<iinter> (c \<squnion> d) = ((rely r) \<iinter> c) \<squnion> ((rely r) \<iinter> d)"
     by (simp add: local.conj_commute sup_conj_distrib)
*)

lemma rely_conj_distrib: "(rely r) \<iinter> (c \<iinter> d) = ((rely r) \<iinter> c) \<iinter> ((rely r) \<iinter> d)"
  using conj_conj_distrib_left by auto
*)
lemma nil_conj_rely: "nil \<iinter> (rely r) = nil"
    by (metis (no_types, lifting) conj.nondet_sync_distrib3 conj.nil_sync_nil 
          conj.nil_sync_atomic_pre conj.comm.semigroup_axioms sup_bot_right iter_unfold 
          restrict_atomic restrict_iter_conj_rely semigroup.assoc) 

lemma test_rely_conj: "\<tau>(p) \<iinter> (rely r) = \<tau>(p)"
  by (metis conj.sync_assoc conj.test_sync_nil nil_conj_rely)

lemma rely_conj_rely: "(rely r1) \<iinter> (rely r2) = (rely(r1 \<sqinter> r2))"
proof -
  have "(rely r1) \<iinter> (rely r2) = (assump(\<epsilon>(r1) \<squnion> Pgm))\<^sup>\<omega> \<iinter> (assump(\<epsilon>(r2) \<squnion> Pgm))\<^sup>\<omega>"
    using env_assump_def2 by auto
  also have "\<dots> = (assump((\<epsilon>(r1) \<squnion> Pgm) \<sqinter> (\<epsilon>(r2) \<squnion> Pgm)))\<^sup>\<omega>"
    using assump_iter_conj by (metis env_or_Pgm_atomic) 
  thus ?thesis using env_assump_def2 by (metis (no_types, lifting) env.hom_inf rely_def sup_inf_distrib2)
qed

(* for equality we need lemma assump_seq_distrib which is not proven yet 
    (needs canonical form theorem) *)
lemma rely_seq_distrib: "(rely r) \<iinter> (c;d) \<ge> ((rely r) \<iinter> c);((rely r) \<iinter> d)"
  by (metis (no_types) rely_seq_idem seq_conj_interchange) 

lemma rely_ref_chaos: "(rely r) \<ge> chaos"
  using rely_weaken rely_top by (metis top.extremum)

lemma rely_remove: "(rely r) \<iinter> c \<ge> c"
  using rely_ref_chaos conj.sync_mono_left conj_chaos_left by metis

lemma test_pre_rely:
  shows "\<tau>(p);((rely r) \<iinter> c) = ((rely r) \<iinter> \<tau>(p);c)"
proof -
  have a1: "\<And>p q c. \<tau>(p) \<iinter> \<tau>(q);c = \<tau>(q);(\<tau>(p) \<iinter> c)"
    using conj.nonaborting_sync_test_pre chaos_ref_test by simp

  have "\<tau>(p);((rely r) \<iinter> c) = \<tau>(p);((nil \<squnion> (\<epsilon>(r) \<squnion> \<pi>(\<top>) \<squnion> \<epsilon>(-r);\<top>);(rely r)) \<iinter> c)"
    using iter_unfold env_assump_def5 by simp
  also have "... = \<tau>(p);(nil \<iinter> c) \<squnion> \<tau>(p);((\<epsilon>(r) \<squnion> \<pi>(\<top>));(rely r) \<iinter> c)
                                  \<squnion> \<tau>(p);(\<epsilon>(-r);\<top>;(rely r) \<iinter> c)"
    using conj.nondet_sync_distrib par.seq_nondet_distrib by (simp add: sup_assoc nondet_seq_distrib)
  also have "... = (nil \<iinter> \<tau>(p);c) \<squnion> ((\<epsilon>(r) \<squnion> \<pi>(\<top>));(rely r) \<iinter> \<tau>(p);c)
                                  \<squnion> (\<epsilon>(-r);\<top>;(rely r) \<iinter> \<tau>(p);c)" 
    using a1 test_top conj.atomic_pre_sync_test_pre pgm_or_env_atomic 
          sup_commute env_atomic seq_assoc by metis
  also have "... = ((nil \<squnion> (\<epsilon>(r) \<squnion> \<pi>(\<top>) \<squnion> \<epsilon>(-r);\<top>);(rely r)) \<iinter> \<tau>(p);c)"
    using conj.nondet_sync_distrib par.seq_nondet_distrib by (simp add: sup_assoc nondet_seq_distrib)
  also have "... = ((rely r) \<iinter> \<tau>(p);c)"
    using iter_unfold env_assump_def5 by simp
  finally show ?thesis .
qed

(* Convenience lemmas *)
lemma rely_refine_within:
  assumes refine_within: "(rely r) \<iinter> c1 \<ge> (rely r) \<iinter> d"
  shows "(rely r) \<iinter> c0;c1;c2 \<ge> (rely r) \<iinter> c0;d;c2"
proof -
  have "(rely r) \<iinter> c0;c1;c2 = (rely r) \<iinter> ((rely r) \<iinter> c0;c1;c2)"
    using conj_idem by simp
  also have "... \<ge> (rely r) \<iinter> ((rely r) \<iinter> c0);((rely r) \<iinter> c1;c2)" (is "_ \<ge> ?rhs")
    by (metis rely_seq_distrib seq_assoc conj.sync_mono_right)
  also have "?rhs \<ge> (rely r) \<iinter> ((rely r) \<iinter> c0);((rely r) \<iinter> c1);((rely r) \<iinter> c2)" (is "_ \<ge> ?rhs")
    by (metis rely_seq_distrib seq_assoc conj.sync_mono_right seq_mono_right)
  also have "?rhs \<ge> (rely r) \<iinter> ((rely r) \<iinter> c0);((rely r) \<iinter> d);((rely r) \<iinter> c2)" (is "_ \<ge> ?rhs")
    by (metis refine_within seq_mono_left seq_mono_right conj.sync_mono_right)
  also have "?rhs \<ge> (rely r) \<iinter> c0;d;c2" 
    by (metis conj.sync_mono_right seq_mono rely_remove)
  finally show ?thesis .
qed

lemma refine_within_rely_left:
  assumes refine_within: "((rely r) \<iinter> c1) \<ge> (rely r) \<iinter> d"
  shows "(rely r) \<iinter> c1;c2 \<ge> (rely r) \<iinter> d;c2"
  using rely_refine_within refine_within seq_nil_left by metis

lemma refine_within_rely_right:
  assumes refine_within: "((rely r) \<iinter> c1) \<ge> (rely r) \<iinter> d"
  shows "(rely r) \<iinter> c0;c1 \<ge> (rely r) \<iinter> c0;d"
  using rely_refine_within refine_within seq_nil_right by metis
    
lemma equal_within_rely:
  assumes equal_within: "((rely r) \<iinter> c1) = ((rely r) \<iinter> d)"
  shows "(rely r) \<iinter> c0;c1;c2 = (rely r) \<iinter> c0;d;c2"
proof (rule antisym)
  show "(rely r) \<iinter> c0;c1;c2 \<ge> (rely r) \<iinter> c0;d;c2"
    using rely_refine_within equal_within by simp
  show "(rely r) \<iinter> c0;d;c2 \<ge> (rely r) \<iinter> c0;c1;c2"
    using rely_refine_within equal_within by simp
qed
    
lemma equal_within_rely_right:
  assumes equal_within: "((rely r) \<iinter> c1) = ((rely r) \<iinter> d)"
  shows "(rely r) \<iinter> c0;c1 = (rely r) \<iinter> c0;d"
    using equal_within_rely equal_within seq_nil_right by metis

lemma equal_within_rely_left:
  assumes equal_within: "((rely r) \<iinter> c1) = ((rely r) \<iinter> d)"
  shows "(rely r) \<iinter> c1;c2 = (rely r) \<iinter> d;c2"
    using equal_within_rely equal_within seq_nil_left by metis

text_raw \<open>\DefineSnippet{demand}{\<close>
definition
  demand :: "'step::complete_boolean_algebra \<Rightarrow> 'a::refinement_lattice"
where
  dem_def [simp]: "demand r = (restrict r)\<^sup>\<omega>"
text_raw \<open>}%EndSnippet\<close>

lemma restrict_demand: "(restrict r)\<^sup>\<omega> = demand r"
  by auto

lemma rely_demand: "(demand r) \<iinter> (rely r) = (demand r)"
  using restrict_iter_conj_rely
  by simp

end
end
