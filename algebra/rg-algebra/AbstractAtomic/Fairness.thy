section \<open>Fairness for Concurrency\<close>

text \<open>This is just to replay some proofs for a lemma on fairness (circulated by Ian 24.08.) 
        It requires axioms on parallel composition and hence belongs into the flip locale.\<close>

theory Fairness
  imports
  (* "Atomic_Commands" *)
  "../AbstractAtomicTest/ParallelFlip"
  (* "IntroPar" *)

begin

locale fairness = parallel_flip + 
 fixes fair:: "'a::refinement_lattice"
 fixes fair_par:: "'a::refinement_lattice \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<parallel>\<^sub>f" 75)
 assumes fair_def: "fair = \<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>"
 assumes fair_par_def: "c \<parallel>\<^sub>f d = ((c \<iinter> fair);skip)\<parallel>((d \<iinter> fair);skip)"

begin

definition
  tterm :: "'a::refinement_lattice"
where
  tterm_def: "tterm = Atomic\<^sup>\<star>;\<E>\<^sup>\<omega>" 

lemma chaos_fair: "chaos \<ge> fair" 
proof -
  have a1: "chaos =  \<E>\<^sup>\<omega>;(Pgm;\<E>\<^sup>\<omega>)\<^sup>\<omega>" using chaos_rel par.iter_decomp
    by (simp add: sup_commute)
  have a2: "... \<ge>  \<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>"
    by (simp add: iter_mono iter_ref_fiter seq_mono)
  thus ?thesis using fair_def a1 by simp
qed

lemma introduce_fair: "c \<ge> c \<iinter> fair"
  by (simp add: chaos_fair conj_conjoin_non_aborting)

lemma fair_fair: "fair;fair = fair"
proof -
  have f1: "\<forall>a aa ab. ab ; aa ; a = ab ; (aa ; a)"
    by (meson semigroup.assoc seq.semigroup_axioms)
  then have f2: "\<E>\<^sup>\<star> ; fair = fair"
    by (metis (no_types) fair_def fiter_seq_fiter)
  have "fair ; (Pgm ; \<E>\<^sup>\<star>)\<^sup>\<omega> = fair"
    using f1 by (simp add: fair_def)
  then show ?thesis
    using f2 f1 by (simp add: fair_def par.iter_leapfrog)
qed

lemma fair_distrib_seq: "c;d \<iinter> fair \<ge> (c \<iinter> fair);(d \<iinter> fair)"
  by (metis fair_fair seq_conj_interchange)

lemma skip_fair: "fair \<iinter> skip = \<E>\<^sup>\<star>" 
proof - 
  have a1: "fair \<iinter> skip = \<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega> \<iinter> \<E>\<^sup>\<star>;\<E>\<^sup>\<omega>" 
    using fair_def fiter0 fiter_induct inf.orderE inf.right_idem inf_sup_aci(1) inf_sup_ord(4)
        iter_unfold seq_mono_left seq_nil_left skip_def sup.idem fiter_seq_iter by auto
  have a2: "... = \<E>\<^sup>\<star>;((nil \<iinter> (Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>) \<squnion> (nil \<iinter> \<E>;\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>) \<squnion> (\<E>;\<E>\<^sup>\<omega> \<iinter> (Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>))"
    using conj.atomic_fiter_pre_sync_fiter_pre a1 conj.atomic_fiter_pre_sync_iter 
      conj.nil_sync_atomic_pre conj.nondet_sync_distrib3 fair_def iter_unfold
      local.conj_commute par.syncid_atomic seq_assoc skip_def by auto
  have a3: "\<dots> = \<E>\<^sup>\<star>;(nil \<squnion> \<bottom> \<squnion> (\<E>;\<E>\<^sup>\<omega> \<iinter> (nil \<squnion> Pgm;\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>)))"
    using conj.atomic_iter_sync_nil conj.nil_sync_atomic_pre iter_unfold
    by (smt Atomic_def2 conj.idem conj.sync_nondet_distrib inf.syncid_atomic nondet_seq_distrib seq_assoc sup_assoc)
  have a4: "\<dots> = \<E>\<^sup>\<star>;(nil \<squnion> (\<E>;\<E>\<^sup>\<omega> \<iinter> nil) \<squnion> (\<E>;\<E>\<^sup>\<omega> \<iinter> Pgm;\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>))"
    using conj.sync_nondet_distrib conj_assoc by (simp add: sup_assoc)
  have a5: "\<dots> = \<E>\<^sup>\<star>;(nil \<squnion> \<bottom> \<squnion> (\<epsilon>(\<top>);\<E>\<^sup>\<omega> \<iinter> \<pi>(\<top>);\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>))"
    using conj_commute conj.nil_sync_atomic_pre par.syncid_atomic env.Hom_def pgm.Hom_def by auto 
  have a6: "\<dots> = \<E>\<^sup>\<star>;(nil \<squnion> \<bottom> \<squnion> (\<epsilon>(\<top>) \<iinter> \<pi>(\<top>));(\<E>\<^sup>\<omega> \<iinter> \<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>))"
    using  conj.atomic_pre_sync_atomic_pre
    by (metis env_atomic pgm_atomic seq_assoc) 
  have a7: "\<dots> = \<E>\<^sup>\<star>;(nil \<squnion> \<bottom>)"
    by (simp add: env_conj_pgm)
  thus ?thesis
    using a1 a2 a3 a4 a5 a6 by auto 
qed

lemma atomic_step_env_finite: "Atomic\<^sup>\<star> = Atomic\<^sup>\<star>;\<E>\<^sup>\<star>"
proof -
  have a1: "Atomic\<^sup>\<star> = Atomic\<^sup>\<star>;Atomic\<^sup>\<star>"
    by simp
  then have a2: "\<dots> \<ge> Atomic\<^sup>\<star>;\<E>\<^sup>\<star>" (is "_ \<ge> ?rhs")
    using fiter_mono par.syncid_atomic seq_mono_right atomic.Hom_ref_hom fiter_mono
      par.syncid_atomic seq_mono_right by metis
  then have a3: "?rhs \<ge> Atomic\<^sup>\<star>"
    by (metis fiter0 seq_mono_right seq_nil_right)
  thus ?thesis
    using a2 by auto 
qed

lemma term_fair: "tterm \<iinter> fair = Atomic\<^sup>\<star>" 
proof -
  define F where "F = (\<lambda> x. x \<iinter> fair)"
  define G where "G = (\<lambda> x. \<E>\<^sup>\<omega> \<squnion> Atomic;x)"
  define H where "H = (\<lambda> x. \<E>\<^sup>\<star> \<squnion> Atomic;x)"

  have FG: "F \<circ> G = (\<lambda> x.  (\<E>\<^sup>\<omega> \<squnion> Atomic;x) \<iinter> fair)"
    using F_def G_def by (metis o_apply)
  have HF: "H \<circ> F = (\<lambda> x. \<E>\<^sup>\<star> \<squnion> Atomic;(x \<iinter> fair))"
    using F_def H_def by auto

  have fusion: "F (lfp G) = lfp H"
  proof (rule fusion_lfp_eq)
    show "mono H"  by (metis H_def sup.mono monoI order_refl seq_mono)
  next
    show "mono G" by (metis G_def sup.mono monoI order_refl seq_mono)
  next
    show "dist_over_nondet F"
    proof -
      have a1: "F (\<Squnion> X) = (\<Squnion> X) \<iinter> fair"
        by (simp add: F_def)
      then have a2: "\<dots> = (\<Squnion>x\<in>X. (x \<iinter> fair))"
        using SUP_least antisym conj.Nondet_sync_distrib
            empty_iff image_empty introduce_fair by metis 
      then have a3: "\<dots> = (\<Squnion>x\<in>X. F(x))"
        using F_def by blast
      thus ?thesis using F_def SUP_cong Sup_inf conj.sync_commute
          empty_is_image introduce_fair le_iff_inf conj.sync_Nondet_distrib
        by (metis inf_aci(1))
    qed
  next
    fix x
    have "(\<E>\<^sup>\<omega> \<squnion> Atomic;x) \<iinter> fair = (\<E>\<^sup>\<omega> \<iinter> fair) \<squnion> (Atomic;x \<iinter> fair)"
      by (simp add: conj.nondet_sync_distrib)
    also have "\<dots> = \<E>\<^sup>\<star> \<squnion> (Atomic;x \<iinter> \<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>)" 
      using skip_fair fair_def
      by (simp add: conj.sync_commute skip_def)
    also have "\<dots> = \<E>\<^sup>\<star> \<squnion> (Atomic;x \<iinter> (nil \<squnion> \<E>;\<E>\<^sup>\<star>);(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>)"
      using fiter_unfold by auto
    also have "\<dots> = \<E>\<^sup>\<star> \<squnion> (Atomic;x \<iinter> (Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>) \<squnion> (Atomic;x \<iinter> \<E>;\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>)"
    proof -
      have "\<forall>f a aa ab ac. \<not> seq_distrib_right f (a::'a) \<or> f (aa \<squnion> ab) ac = f aa ac \<squnion> f ab ac"
        using seq_distrib_right.nondet_seq_distrib by blast
      then have "\<E> ; \<E>\<^sup>\<star> ; (Pgm ; \<E>\<^sup>\<star>)\<^sup>\<omega> \<squnion> (Pgm ; \<E>\<^sup>\<star>)\<^sup>\<omega> = (nil \<squnion> \<E> ; \<E>\<^sup>\<star>) ; (Pgm ; \<E>\<^sup>\<star>)\<^sup>\<omega>"
        using sup_commute seq_distrib_right_axioms by fastforce
      then have "\<E>\<^sup>\<star> \<squnion> Atomic ; x \<iinter> (nil \<squnion> \<E> ; \<E>\<^sup>\<star>) ; (Pgm ; \<E>\<^sup>\<star>)\<^sup>\<omega> = Atomic ; x \<iinter> \<E> ; \<E>\<^sup>\<star> ; (Pgm ; \<E>\<^sup>\<star>)\<^sup>\<omega> \<squnion> (Atomic ; x \<iinter> (Pgm ; \<E>\<^sup>\<star>)\<^sup>\<omega> \<squnion> \<E>\<^sup>\<star>)"
        using conj.nondet_sync_distrib4 by presburger
      then show ?thesis
        by (simp add: sup_commute)
    qed
    also have "\<dots> = \<E>\<^sup>\<star> \<squnion> (Atomic;x \<iinter> ((Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega> \<squnion> \<E>;\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>))"
      by (simp add: conj.sync_nondet_distrib sup_assoc)
    also have "\<dots> = \<E>\<^sup>\<star> \<squnion> (Atomic;x \<iinter> (nil \<squnion> Atomic;fair))"
      by (metis (no_types, lifting) Atomic_def2 fair_def iter_unfold nondet_seq_distrib seq_assoc sup_assoc)
    also have "\<dots> = \<E>\<^sup>\<star> \<squnion> (Atomic;x \<iinter> nil) \<squnion> (Atomic;x \<iinter> Atomic;fair)"
      by (simp add: conj.sync_nondet_distrib sup_assoc)
    also have "\<dots> = \<E>\<^sup>\<star> \<squnion> Atomic;(x \<iinter> fair)"
      using conj.atomic_pre_sync_atomic_pre inf.syncid_atomic conj.atomic_pre_sync_nil by auto
    finally show "(F \<circ> G) x = (H \<circ> F) x" using FG HF by simp
  qed
  have a0: "Atomic\<^sup>\<star>;\<E>\<^sup>\<omega> = lfp (\<lambda> x. Atomic;x \<squnion> \<E>\<^sup>\<omega>)"
    using fiter_induct_eq by blast 
  have ax: "lfp G = lfp (\<lambda> x. Atomic;x \<squnion> \<E>\<^sup>\<omega>)"
    using G_def lfp_mono by (simp add: sup_commute) 
  have a1: "tterm \<iinter> fair = Atomic\<^sup>\<star>;\<E>\<^sup>\<omega> \<iinter> fair"
    by (simp add: tterm_def)
  have a2: "\<dots> = F(lfp G)"
    using a0 ax F_def by simp
  have a3: "\<dots> = lfp H" using fusion
    by simp
  have ay: "\<dots> = lfp (\<lambda> x. Atomic;x \<squnion> \<E>\<^sup>\<star>)"
    by (simp add: H_def sup_commute)
  have a4: "\<dots> = Atomic\<^sup>\<star>;\<E>\<^sup>\<star>"
    using fiter_induct_eq by simp
  thus ?thesis
    using a2 atomic_step_env_finite ay fusion tterm_def by auto 
qed

theorem fair_termination: 
  assumes "tterm \<ge> c"
  shows "Atomic\<^sup>\<star> \<ge> c \<iinter> fair"
  by (metis assms conj.sync_mono_left term_fair)

lemma fair_conj_nil: "fair \<iinter> nil = nil"
  using chaos_fair conj.atomic_fiter_sync_nil conj_chaos_left
       iter0 fair_def par.syncid_atomic seq_mono_right seq_nil_right conj.left_idem
       local.conj_assoc skip_fair by metis

lemma pgm_com_par_pgm_com: "(Pgm;c)\<^sup>\<omega>\<parallel>(Pgm;d)\<^sup>\<omega> = nil" 
proof -
    have a1: "(Pgm;c)\<^sup>\<omega>\<parallel>(Pgm;d)\<^sup>\<omega> = 
              (nil \<squnion> (Pgm;c);(Pgm;c)\<^sup>\<omega>)\<parallel>(nil \<squnion> (Pgm;d);(Pgm;d)\<^sup>\<omega>)"
    using iter_unfold by auto
  then have a2: "... = nil\<parallel>nil \<squnion> nil \<parallel> (Pgm;d;(Pgm;d)\<^sup>\<omega>) \<squnion> Pgm;c;(Pgm;c)\<^sup>\<omega>\<parallel> nil \<squnion> 
                       Pgm;c;(Pgm;c)\<^sup>\<omega>\<parallel> Pgm;d;(Pgm;d)\<^sup>\<omega>"
    using par.nondet_sync_product by blast 
  then have a3: "... = nil \<squnion> Pgm;c;(Pgm;c)\<^sup>\<omega>\<parallel> Pgm;d;(Pgm;d)\<^sup>\<omega>"
    using par.nil_sync_nil par.nil_sync_atomic_pre pgm_atomic par_commute
    by (metis sup_bot.right_neutral Pgm_def seq_assoc)  
  then have a4: "... = nil \<squnion> (Pgm\<parallel>Pgm);(c;(Pgm;c)\<^sup>\<omega>\<parallel> d;(Pgm;d)\<^sup>\<omega>)"
    using par.atomic_pre_sync_atomic_pre by (metis pgm_atomic Pgm_def seq_assoc)
  thus ?thesis by (metis a1 a2 a3 sup_bot_right Pgm_def pgm_com_par_pgm_com seq_assoc)
qed


lemma fair_par_fair_expand: "fair \<parallel> fair = \<E>\<^sup>\<star>;(nil \<squnion> Pgm;(fair \<parallel> fair))"
proof -
  have a1: "fair \<parallel> fair = \<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega> \<parallel> \<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>" using fair_def by blast
  have a2: "... = (\<E>\<^sup>\<star> \<parallel> \<E>\<^sup>\<star>);(((Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega> \<parallel>(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>) \<squnion> ((Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega> \<parallel> \<E>;\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>))"
    using par.atomic_fiter_pre_sync_fiter_pre par.sync_commute par.syncid_atomic par.syncid_syncid 
          par.syncid_syncid_fiter by force
  have a3: "... = \<E>\<^sup>\<star>;(nil \<squnion> ((nil \<squnion> Pgm;\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>) \<parallel> \<E>;\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>))"
    using iter_unfold par.syncid_syncid_fiter pgm_com_par_pgm_com by auto
  have a4: "... = \<E>\<^sup>\<star>;(nil \<squnion> 
                  ((nil \<parallel> \<E>;\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>) \<squnion> (Pgm;\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega> \<parallel> \<E>;\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>)))"
    by (simp add: par.nondet_sync_distrib)
  have a5: "... = \<E>\<^sup>\<star>;(nil \<squnion> Pgm;(\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega> \<parallel> \<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>))"
    using sup_bot.right_neutral par.nil_sync_atomic_pre par.syncid_atomic 
          Pgm_def pgm_par_Env_com seq_assoc by auto
  thus ?thesis by (simp add: a2 a3 a4 fair_def)
qed

lemma fair_par_fair: "fair \<ge> fair \<parallel> fair"
proof -
  have f1: "\<forall>a aa. ((a::'a) = aa) = (a \<ge> aa \<and> aa \<ge> a)"
    using eq_iff by blast
  have "Pgm ; \<E>\<^sup>\<star> ; (nil \<squnion> Pgm ; (fair \<parallel> fair)) = 
        Pgm ; (\<E>\<^sup>\<star> ; (nil \<squnion> Pgm ; (fair \<parallel> fair)))"
    by (simp add: semigroup.assoc seq.semigroup_axioms)
  then show ?thesis
    using f1 by (metis (no_types) iter_induct_nil fair_def fair_par_fair_expand seq_mono_right)
qed

lemma fair_distrib_par_both: "(c \<parallel> d) \<iinter> fair \<ge> (c \<iinter> fair) \<parallel> (d \<iinter> fair)"
   using conj.sync_commute conj_par_distrib fair_par_fair by fastforce  

lemma fair_par_chaos_expand: "fair \<parallel> chaos = \<E>\<^sup>\<star>;(nil \<squnion> Pgm;(fair \<parallel> chaos))"
proof -
  define c where "c = (Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>"
  define d where "d = (Pgm;\<E>\<^sup>\<omega>)\<^sup>\<omega>"
  have fair_chaos: "fair \<parallel> chaos = \<E>\<^sup>\<star>;c \<parallel> \<E>\<^sup>\<omega>;d"
  proof -
    have "fair \<parallel> chaos = \<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega> \<parallel> (Pgm \<squnion> \<E>)\<^sup>\<omega>"
      by (simp add: chaos_rel fair_def)
    also have reuse: "\<dots> = \<E>\<^sup>\<star>;c \<parallel> \<E>\<^sup>\<omega>;d"
      by (simp add: c_def d_def par.iter_decomp sup_commute)
    finally show ?thesis by blast 
  qed
  have c_par_d: "c \<parallel> d = nil"
  proof -
    have cd: "(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega> \<parallel> (Pgm;\<E>\<^sup>\<omega>)\<^sup>\<omega> = (nil \<squnion> Pgm;\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega>) \<parallel> (nil \<squnion> Pgm;\<E>\<^sup>\<omega>;(Pgm;\<E>\<^sup>\<omega>)\<^sup>\<omega>)"
      using iter_unfold by auto 
    show ?thesis 
      by (simp add: c_def d_def pgm_com_par_pgm_com)  
  qed
  have ec_par_d: "\<E>;\<E>\<^sup>\<star>;c \<parallel> d = Pgm;(\<E>\<^sup>\<star>;c \<parallel> \<E>\<^sup>\<omega>;d)"
  proof -
    have "\<E>;\<E>\<^sup>\<star>;c \<parallel> d = \<E>;\<E>\<^sup>\<star>;c \<parallel> (nil \<squnion> Pgm;\<E>\<^sup>\<omega>;d)"
      using d_def iter_unfold by auto
    also have "\<dots> = (\<E>;\<E>\<^sup>\<star>;c \<parallel> nil) \<squnion> (\<E>;\<E>\<^sup>\<star>;c \<parallel> Pgm;\<E>\<^sup>\<omega>;d)"
      using par.sync_nondet_distrib by simp 
    also have "\<dots> = \<bottom> \<squnion> Pgm;(\<E>\<^sup>\<star>;c \<parallel> \<E>\<^sup>\<omega>;d)"
      using par.nil_sync_atomic_pre par_commute env.Hom_def par.syncid_atomic
        seq_assoc pgm.Hom_def pgm_par_Env_com by auto 
    finally show ?thesis using fair_chaos by simp
  qed
  have c_par_ed: "c \<parallel> \<E>;\<E>\<^sup>\<omega>;d = Pgm;(\<E>\<^sup>\<star>;c \<parallel> \<E>\<^sup>\<omega>;d)"
    proof -
    have "c \<parallel> \<E>;\<E>\<^sup>\<omega>;d = (nil \<squnion> Pgm;\<E>\<^sup>\<star>;c) \<parallel> \<E>;\<E>\<^sup>\<omega>;d"
      using c_def iter_unfold by auto
    also have "\<dots> = (nil \<parallel> \<E>;\<E>\<^sup>\<omega>;d) \<squnion> (Pgm;\<E>\<^sup>\<star>;c \<parallel> \<E>;\<E>\<^sup>\<omega>;d)"
      by (simp add: par.nondet_sync_distrib)
    also have "\<dots> = \<bottom> \<squnion> Pgm;(\<E>\<^sup>\<star>;c \<parallel> \<E>\<^sup>\<omega>;d)"
      using par.nil_sync_atomic_pre par_commute env.Hom_def par.syncid_atomic
        seq_assoc pgm.Hom_def pgm_par_Env_com by auto 
    finally show ?thesis using fair_chaos by simp
  qed
  have "fair \<parallel> chaos = \<E>\<^sup>\<star>;c \<parallel> \<E>\<^sup>\<omega>;d"
    using fair_chaos by simp
  also have "\<dots> = \<E>\<^sup>\<star>;((c \<parallel> d) \<squnion> (\<E>;\<E>\<^sup>\<star>;c \<parallel> d) \<squnion> (c \<parallel> \<E>;\<E>\<^sup>\<omega>;d))"
    using par.atomic_fiter_pre_sync_iter_pre par.syncid_atomic par.syncid_syncid by force 
  also have "\<dots> = \<E>\<^sup>\<star>;(nil \<squnion>  Pgm;(\<E>\<^sup>\<star>;c \<parallel> \<E>\<^sup>\<omega>;d))"
    using c_par_d ec_par_d c_par_ed by simp
  also have "\<dots> = \<E>\<^sup>\<star>;(nil \<squnion>  Pgm;(fair \<parallel> chaos))"
    using fair_chaos by simp
  finally show ?thesis by blast
qed

lemma fair_par_chaos: "fair \<parallel> chaos = fair"
proof -
  have a1: "fair \<ge> fair \<parallel> chaos"
  proof -
    have a1: "\<E>\<^sup>\<star> \<squnion> \<E>\<^sup>\<star>;Pgm;(fair \<parallel> chaos) \<ge> fair \<parallel> chaos"
      using fair_par_chaos_expand par.seq_nondet_distrib seq_assoc by auto
    have a2: "\<E>\<^sup>\<star>;(Pgm;\<E>\<^sup>\<star>)\<^sup>\<omega> \<ge> fair \<parallel> chaos"
      by (simp add: a1 par.iter_induct par.iter_leapfrog)
    thus ?thesis using fair_def
      by blast
  qed
  have a2: "fair \<parallel> chaos \<ge> fair"
    using skip_nonaborting par.sync_mono by fastforce
  then show ?thesis
    by (simp add: a1 eq_iff)
qed

lemma fair_distrib_par_one: "(c \<parallel> d) \<iinter> fair \<ge> (c \<iinter> fair) \<parallel> d"
  by (metis conj_chaos fair_par_chaos par_conj_interchange)

lemma fair_par_skip: "(c \<parallel>\<^sub>f d);skip = c \<parallel>\<^sub>f d"       
proof - 
  have a1: "(c \<parallel>\<^sub>f d);skip \<ge> c \<parallel>\<^sub>f d" using seq_mono_right skip_ref_nil by fastforce 
  have a2: "c \<parallel>\<^sub>f d \<ge> (c \<parallel>\<^sub>f d);skip" 
    proof -
      have b1: "c \<parallel>\<^sub>f d = ((c \<iinter> fair);skip)\<parallel>((d \<iinter> fair);skip)" using fair_par_def by blast
      then have b2: "... =  ((c \<iinter> fair);skip;skip)\<parallel>((d \<iinter> fair);skip;skip)" 
        by (simp add: seq_assoc)
      then have b3: "... \<ge> (((c \<iinter> fair);skip)\<parallel>((d \<iinter> fair);skip));(skip \<parallel> skip)"
        using seq_par_interchange by blast 
      thus ?thesis using b1 b2 b3 by auto 
    qed
  thus ?thesis by (simp add: a1 eq_iff)
qed

lemma finite_absorb_fair_skip: 
  "(((c \<iinter> Atomic\<^sup>\<star>) \<parallel>\<^sub>f (d \<iinter> Atomic\<^sup>\<star>)) \<iinter> fair);skip \<ge> (c \<iinter> Atomic\<^sup>\<star>) \<parallel>\<^sub>f (d \<iinter> Atomic\<^sup>\<star>)"
proof -
  have a1 :"(((c \<iinter> Atomic\<^sup>\<star>) \<parallel>\<^sub>f (d \<iinter> Atomic\<^sup>\<star>)) \<iinter> fair);skip = (((c \<iinter> Atomic\<^sup>\<star> \<iinter> fair);skip \<parallel> (d \<iinter> Atomic\<^sup>\<star> \<iinter> fair);skip) \<iinter> fair);skip"
    using fair_par_def by simp
  have a2: "\<dots> \<ge> ((((c \<iinter> Atomic\<^sup>\<star> \<iinter> fair);skip) \<iinter> fair) \<parallel> (((d \<iinter> Atomic\<^sup>\<star> \<iinter> fair);skip) \<iinter> fair));skip"  (is "_ \<ge> ?rhs")
    by (simp add: fair_distrib_par_both seq_mono_left)
  have a3: "?rhs \<ge> ((c \<iinter> Atomic\<^sup>\<star> \<iinter> fair);(skip \<iinter> fair) \<parallel> (d \<iinter> Atomic\<^sup>\<star> \<iinter> fair);(skip \<iinter> fair));skip" (is "_ \<ge> ?rhs")
    using conj.right_idem fair_distrib_seq seq_mono_left conj.right_idem fair_fair par.sync_mono
          seq_conj_interchange seq_mono_left by metis
  have a4: "?rhs \<ge> ((c \<iinter> Atomic\<^sup>\<star> \<iinter> fair);\<E>\<^sup>\<star> \<parallel> (d \<iinter> Atomic\<^sup>\<star> \<iinter> fair);\<E>\<^sup>\<star>);skip" (is "_ \<ge> ?rhs")
    by (simp add: conj.sync_commute seq_mono_left seq_mono_right skip_fair)
  have a5: "?rhs \<ge> (c \<iinter> Atomic\<^sup>\<star> \<iinter> fair);skip \<parallel> (d \<iinter> Atomic\<^sup>\<star> \<iinter> fair);skip"
    sorry
  thus ?thesis using fair_par_def
    using a2 a3 a4 by auto
qed

lemma infinite_annihilates_conj: "(c \<iinter> Atomic\<^sup>\<infinity>);d = c \<iinter> Atomic\<^sup>\<infinity>"
  by (metis inf.absorb_iff2 inf.sync_commute infiter_annil local.conj_commute seq_abort 
      seq_abort_conj seq_abort_right seq_assoc)

lemma infinite_absorb_fair_skip: 
  "(((c \<iinter> Atomic\<^sup>\<infinity>) \<parallel>\<^sub>f d) \<iinter> fair);skip \<ge> (c \<iinter> Atomic\<^sup>\<infinity>) \<parallel>\<^sub>f d"
proof -
  have a1: "(((c \<iinter> Atomic\<^sup>\<infinity>) \<parallel>\<^sub>f d) \<iinter> fair);skip = (((c \<iinter> Atomic\<^sup>\<infinity> \<iinter> fair);skip \<parallel> (d \<iinter> fair);skip) \<iinter> fair);skip"
    by (simp add: fair_par_def)
  have a2: "\<dots> = (((c \<iinter> Atomic\<^sup>\<infinity> \<iinter> fair) \<parallel> (d \<iinter> fair);skip) \<iinter> fair);skip"
  proof -
    have "\<forall>a aa ab. (ab \<iinter> (aa \<iinter> Atomic\<^sup>\<infinity>)) ; a = ab \<iinter> (aa \<iinter> Atomic\<^sup>\<infinity>)"
      by (metis infinite_annihilates_conj local.conj_assoc)
    then show ?thesis
      by (simp add: local.conj_commute)
  qed 
  have a3: "\<dots> \<ge> ((c \<iinter> Atomic\<^sup>\<infinity> \<iinter> fair) \<parallel> (d \<iinter> fair);skip);skip" (is "_ \<ge> ?rhs")
    by (metis conj.right_idem fair_distrib_par_one seq_mono_left) 
  have a4: "?rhs = ((c \<iinter> Atomic\<^sup>\<infinity> \<iinter> fair);skip \<parallel> (d \<iinter> fair);skip);skip"
    using infinite_annihilates_conj
  proof -
    have "\<forall>a aa ab. (ab \<iinter> (aa \<iinter> Atomic\<^sup>\<infinity>)) ; a = ab \<iinter> (aa \<iinter> Atomic\<^sup>\<infinity>)"
      by (metis infinite_annihilates_conj local.conj_assoc)
    then show ?thesis
      using local.conj_commute by force
  qed
  have a5: "\<dots> = (c \<iinter> Atomic\<^sup>\<infinity> \<parallel>\<^sub>f d);skip"
    by (simp add: fair_par_def)
  thus ?thesis using fair_par_skip
    using a1 a2 a3 a4 by auto
qed

(* subsumed
lemma par_fair_par_rl: "c \<parallel>\<^sub>f d \<sqsubseteq> ((c \<parallel>\<^sub>f d) \<iinter> fair);skip"
    by (metis chaos_fair conj_conjoin_non_aborting fair_par_skip seq_mono skip_seq_skip skip_seq_skip_weak) 
*)

lemma helper: "(c1 \<iinter> (d1 \<squnion> d2)) \<parallel>\<^sub>f (c2 \<iinter> (d1 \<squnion> d2)) = 
      (c1 \<iinter> d1) \<parallel>\<^sub>f (c2 \<iinter> d1) \<squnion> (c1 \<iinter> d1) \<parallel>\<^sub>f (c2 \<iinter> d2) \<squnion> (c1 \<iinter> d2) \<parallel>\<^sub>f (c2 \<iinter> d1) \<squnion> (c1 \<iinter> d2) \<parallel>\<^sub>f (c2 \<iinter> d2)"
  by (simp add: conj.nondet_sync_distrib conj.sync_nondet_distrib fair_par_def nondet_seq_distrib
      par.nondet_sync_product)

lemma fair_par_commute: "(c \<parallel>\<^sub>f d) = (d \<parallel>\<^sub>f c)"
  by (simp add: fair_par_def par_commute)

lemma fair_par_nil: "(c \<parallel>\<^sub>f nil) = (c \<iinter> fair);skip "
proof - 
  have a1: "(c \<parallel>\<^sub>f nil) = (c \<iinter> fair);skip \<parallel> (nil \<iinter> fair);skip" by (simp add: fair_par_def) 
  have a2: "... = (c \<iinter> fair);skip \<parallel> nil;skip" using fair_conj_nil 
    by (simp add: conj.sync_commute)
  thus ?thesis by (simp add: conj.sync_commute fair_conj_nil fair_par_def) 
qed

lemma helper2: 
  assumes cd1: "c1 \<ge> d1"
  assumes cd2: "c2 \<ge> d2"
  assumes cd3: "c3 \<ge> d3"
  assumes cd4: "c4 \<ge> d4"
  shows "c1 \<squnion> c2 \<squnion> c3 \<squnion> c4 \<ge> d1 \<squnion> d2 \<squnion> d3 \<squnion> d4"
  sorry

lemma absorb_fair_skip: "((c \<parallel>\<^sub>f d) \<iinter> fair);skip = c \<parallel>\<^sub>f d" 
proof - 
  have rl: "c \<parallel>\<^sub>f d \<ge> ((c \<parallel>\<^sub>f d) \<iinter> fair);skip"
    using fair_par_skip introduce_fair by (metis seq_mono_left) 
  have lr: "((c \<parallel>\<^sub>f d) \<iinter> fair);skip \<ge> c \<parallel>\<^sub>f d" 
  proof -
    have f_f: "((c \<iinter> Atomic\<^sup>\<star> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<star>) \<iinter> fair);skip \<ge> c \<iinter> Atomic\<^sup>\<star> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<star>"
      using finite_absorb_fair_skip by blast
    have f_i: "((c \<iinter> Atomic\<^sup>\<star> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<infinity>) \<iinter> fair);skip \<ge> c \<iinter> Atomic\<^sup>\<star> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<infinity>"
      using infinite_absorb_fair_skip fair_par_commute
      by (simp add: infinite_absorb_fair_skip)
    have i_f: "((c \<iinter> Atomic\<^sup>\<infinity> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<star>) \<iinter> fair);skip \<ge> c \<iinter> Atomic\<^sup>\<infinity> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<star>"
      using infinite_absorb_fair_skip by blast
    have i_i: "((c \<iinter> Atomic\<^sup>\<infinity> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<infinity>) \<iinter> fair);skip \<ge> c \<iinter> Atomic\<^sup>\<infinity> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<infinity>"
      using infinite_absorb_fair_skip by blast
    have "((c \<parallel>\<^sub>f d) \<iinter> fair);skip = ((c \<iinter> (Atomic\<^sup>\<star> \<squnion> Atomic\<^sup>\<infinity>) \<parallel>\<^sub>f d \<iinter> (Atomic\<^sup>\<star> \<squnion> Atomic\<^sup>\<infinity>)) \<iinter> fair);skip"
      using conj_id par.iter_isolation by auto
    also have "\<dots> = ((c \<iinter> Atomic\<^sup>\<star> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<star>) \<iinter> fair);skip \<squnion>
            ((c \<iinter> Atomic\<^sup>\<star> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<infinity>) \<iinter> fair);skip \<squnion> 
            ((c \<iinter> Atomic\<^sup>\<infinity> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<star>) \<iinter> fair);skip \<squnion> 
            ((c \<iinter> Atomic\<^sup>\<infinity> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<infinity>) \<iinter> fair);skip"
      by (simp add: helper conj.nondet_sync_distrib nondet_seq_distrib) 
    also have "\<dots> \<ge> (c \<iinter> Atomic\<^sup>\<star> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<star>) \<squnion> 
                    (c \<iinter> Atomic\<^sup>\<star> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<infinity>) \<squnion> 
                    (c \<iinter> Atomic\<^sup>\<infinity> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<star>) \<squnion> 
                    (c \<iinter> Atomic\<^sup>\<infinity> \<parallel>\<^sub>f d \<iinter> Atomic\<^sup>\<infinity>)"
      using f_f f_i i_f i_i helper2 by blast
    finally show ?thesis 
      by (metis conj_id helper par.iter_isolation)
  qed
  thus ?thesis using rl lr by auto
qed

theorem fair_parallel_associative: "(c \<parallel>\<^sub>f d) \<parallel>\<^sub>f e = c \<parallel>\<^sub>f (d \<parallel>\<^sub>f e)"
proof -
  have a1: "(c \<parallel>\<^sub>f d) \<parallel>\<^sub>f e = ((c \<parallel>\<^sub>f d) \<iinter> fair);skip \<parallel> (e \<iinter> fair);skip"
    using fair_par_def by simp 
  have a2: "\<dots> = (c \<parallel>\<^sub>f d) \<parallel> (e \<iinter> fair);skip"
    using absorb_fair_skip by auto 
  have a3: "\<dots> = ((c \<iinter> fair);skip \<parallel> (d \<iinter> fair);skip) \<parallel> (e \<iinter> fair);skip"
    using fair_par_def by auto
  have a4: "\<dots> = (c \<iinter> fair);skip \<parallel> ((d \<iinter> fair);skip \<parallel> (e \<iinter> fair);skip)"
    using par_assoc by auto 
  have a5: "\<dots> = (c \<iinter> fair);skip \<parallel> (d \<parallel>\<^sub>f e)"
    using fair_par_def by auto 
  have a6: "\<dots> = (c \<iinter> fair);skip \<parallel> ((d \<parallel>\<^sub>f e) \<iinter> fair);skip"
    using absorb_fair_skip by auto 
  have a: "\<dots> = c \<parallel>\<^sub>f (d \<parallel>\<^sub>f e)"
    using fair_par_def by auto 
  thus ?thesis
    by (simp add: a1 a2 a3 a4 a5 a6)
qed


lemma fair_par_interchange: "(c0 \<parallel>\<^sub>f d0) \<iinter> (c1 \<parallel>\<^sub>f d1) \<ge> (c0 \<iinter> c1) \<parallel>\<^sub>f (d0 \<iinter> d1)"
proof -
  have a1: "(c0 \<parallel>\<^sub>f d0) \<iinter> (c1 \<parallel>\<^sub>f d1) =  
      ((c0 \<iinter> fair);skip \<parallel> (d0 \<iinter> fair);skip) \<iinter> ((c1 \<iinter> fair);skip \<parallel> (d1 \<iinter> fair);skip)"
    by (simp add: fair_par_def)
  have a2: "\<dots> \<ge> ((c0 \<iinter> fair);skip \<iinter> (c1 \<iinter> fair);skip) \<parallel> 
                  ((d0 \<iinter> fair);skip \<iinter> (d1 \<iinter> fair);skip)" (is "_ \<ge> ?rhs")
    using par_conj_interchange by blast
  have a3: "?rhs \<ge> (((c0 \<iinter> fair) \<iinter> (c1 \<iinter> fair));(skip \<iinter> skip)) \<parallel> 
                  (((d0 \<iinter> fair) \<iinter> (d1 \<iinter> fair));(skip \<iinter> skip))" (is "_ \<ge> ?rhs")
    using seq_conj_interchange par.sync_mono by blast
  have a4: "?rhs = ((c0 \<iinter> c1) \<iinter> fair); skip \<parallel> ((d0 \<iinter> d1) \<iinter> fair); skip"
    by (simp add: conj.comm.left_commute conj_commute)
  thus ?thesis using a2 a3 fair_par_def order_trans by auto 
qed

lemma fair_par_distrib: "D \<noteq> {} \<Longrightarrow> c \<parallel>\<^sub>f (\<Squnion> D) =  (\<Squnion>d\<in>D. c \<parallel>\<^sub>f d)"
proof - 
  assume D_nonempty: "D \<noteq> {}"
  have a1: "c \<parallel>\<^sub>f (\<Squnion> D) = (c \<iinter> fair);skip \<parallel> ((\<Squnion> D) \<iinter> fair);skip" by (simp add: fair_par_def)
  have a2: "... = (c \<iinter> fair);skip \<parallel> (\<Squnion>d\<in>D. (d \<iinter> fair);skip)"
    using D_nonempty NONDET_seq_distrib conj.Nondet_sync_distrib
    by (simp add: NONDET_seq_distrib)
  have a3: "... = (\<Squnion>d\<in>D. ((c \<iinter> fair);skip \<parallel> (d \<iinter> fair);skip))" 
    using par.sync_NONDET_distrib D_nonempty by (metis D_nonempty) 
  thus ?thesis using INF_cong a2 fair_par_def by auto 
qed

end
end
