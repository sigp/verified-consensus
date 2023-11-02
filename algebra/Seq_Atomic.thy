theory Seq_Atomic
imports Seq_Obs
begin

datatype labels = Pgm | Env 


locale seq_atomic = test_seq + 
  fixes step :: "labels \<Rightarrow> ('b \<times> 'b) \<Rightarrow> 'a"
  assumes step_test: "range (step l) \<inter> range test = {}"
  assumes step_last: "x \<le> step l (a,b) \<Longrightarrow> last x \<notin> \<Omega> \<Longrightarrow>  last x \<le> test b"
  assumes test_step: "test a ; step l (a, b) \<ge>  step l (a, b)"
  assumes first_step': "first (step l (a, b); x) \<ge> test a"
  assumes last_step': "last (step l (a,b)) \<ge> test b"
  assumes test_step': " step l (a, b); test b \<ge>  step l (a, b)"
  assumes bot_not_step: "\<Omega> \<inter> range (step l) = {}"
  assumes step_le: "step l s \<ge> (step l' s' ; x) \<Longrightarrow> l = l' \<and> s = s'"
  assumes step_meet_seq: "\<And>a b.  a \<le> step l s \<Longrightarrow> b \<le> step l' s' \<Longrightarrow>  x \<le> a ; c \<Longrightarrow> x \<le> b ; d \<Longrightarrow> 
                                  \<exists>y. y \<le> a \<and> y \<le> b \<and> x \<le> y ; c \<and> x \<le> y ; d" 
  assumes ref_tail: "step l s ; c \<ge> step l s ; d \<Longrightarrow> (test (snd s) ; c) \<ge> (test (snd s) ; d)" 
  assumes step_atomic: "x \<le> step l (a, b)  \<Longrightarrow>
      ((x \<in> \<Omega>) \<or> ((x \<le> step l (a, b) ; bottom (test b)) \<and> (x \<ge>  step l (a, b) ;  bottom (test b)) ) \<or> (x \<ge> step l (a, b)))"
begin

lemma first_step: "first (step l (a, b); x) \<le> test a"
  apply (subst flip.unit_of_unit)
  by (meson dual_order.trans flip.assoc flip.mono_f order_refl test_step)
 

lemma last_step: "last (step l (a,b)) \<le> test b"
  by (metis Diff_iff omega_mono order_eq_refl rangeI seq_atomic.last_step' seq_atomic_axioms step_last test_nil)



lemma step_first: "x \<le> step l (a, b) \<Longrightarrow> first x \<le> test a"
  by (meson dual_order.trans first_test test_step)
lemma first_stepD: "first (step l (a, b) ; x) \<ge> test a' \<Longrightarrow> a = a'"
  by (metis dual_order.trans first_step test_le)

lemma last_omega_closed: "x \<le> bottom y \<Longrightarrow> last x \<in> \<Omega>" sorry

lemma  step_meet: "x \<le> step l (a, b) \<Longrightarrow> x \<le> step l' (c, d) \<Longrightarrow> last x \<in> \<Omega> \<or> (c = a \<and> d = b)"
  apply (case_tac " x \<in> \<Omega>"; clarsimp)
  apply (case_tac "c = a"; clarsimp?)
   defer
   apply (frule step_first)
   apply (frule step_first) back
  using last_omega_closed apply auto[1]
  apply (subgoal_tac "last x \<le> test b \<and> last x \<le> test d")
    apply (clarsimp)
  apply (smt (verit, ccfv_SIG) dual_order.trans in_omega le_test prod.inject seq_atomic.step_le seq_atomic_axioms step_atomic)
   apply (smt (verit, del_insts) in_omega le_test order_trans prod.inject step_atomic step_le)
  using last_omega_closed by auto
  

lemma  step_meet': "x \<le> step l (a, b) \<Longrightarrow> x \<le> step l' (c, d) \<Longrightarrow> last x \<in> \<Omega> \<or> (c = a \<and> d = b \<and> l = l')"
    apply (case_tac " x \<in> \<Omega>"; clarsimp)
  apply (case_tac "c = a"; clarsimp?)
   defer
   apply (frule step_first)
   apply (frule step_first) back
  using last_omega_closed apply auto[1]
  apply (subgoal_tac "last x \<le> test b \<and> last x \<le> test d")
    apply (clarsimp)
  apply (smt (verit, ccfv_SIG) dual_order.trans in_omega le_test prod.inject seq_atomic.step_le seq_atomic_axioms step_atomic)
   apply (smt (verit, del_insts) in_omega le_test order_trans prod.inject step_atomic step_le)
  using last_omega_closed by auto


lemma step_le_first: "step l (a, b) \<le> step l' (x, y) \<Longrightarrow> a = x"
  apply (frule first_le)
  by (metis dual_order.trans le_test prod.inject seq_atomic.step_le seq_atomic_axioms)


lemma step_le_last: "step l (a,b) \<le> step l' (x,y) \<Longrightarrow> b = y"
  apply (drule step_last)
  apply (metis Diff_iff last_step' omega_mono rangeI test_nil)
  by (meson bot_not_step disjoint_iff_not_equal dual_order.trans in_omega last_step' rangeI test_le)



lemma step_not_bot [simp]: " step l (a, b) \<notin> \<Omega>"
  by (metis Int_iff bot_not_step empty_iff rangeI)
  
lift_definition datomic :: "(labels \<times> 'b \<times> 'b) set \<Rightarrow> 'a downset"  is
                           "\<lambda>S. \<Down>((\<lambda>x. step (fst x) (snd x)) ` S) \<union> \<Omega> "
  by (clarsimp simp: down_sup_distrib down_union_distrib)

lemma step_le_bex[simp, elim!]: "(a, aa, b) \<in> p \<Longrightarrow> c \<le> step a (aa, b) \<Longrightarrow> (\<exists>x\<in>p. c \<le> step (fst x) (snd x))"
  
  by (metis fst_conv snd_conv)

lemma step_not_le_bot[simp]:  "\<not>(step l s) \<le> (bottom c)" 
  by (metis in_omega old.prod.exhaust step_not_bot)

sublocale step_atomic: abstract_atomic_commands datomic
  apply (standard)
      apply (clarsimp simp: inj_def)
  apply (transfer)
                 apply (intro set_eqI iffI; clarsimp)
                  apply (drule_tac x="step a (aa,b)" in set_eqD1[rotated]; clarsimp?)
        apply (clarsimp simp: downset_set_def'  )
       apply (clarsimp simp: in_Down_iff)
        apply (metis dual_order.trans le_test seq_atomic.step_le seq_atomic_axioms)
                 apply (drule sym, drule_tac x="step a (aa,b)" in set_eqD1[rotated]; clarsimp?)
       apply (clarsimp simp: downset_set_def')

      apply (clarsimp simp: in_Down_iff)
        apply (metis dual_order.trans le_test seq_atomic.step_le seq_atomic_axioms)


     apply (clarsimp simp: sup_downset_def, transfer)
                apply (safe; clarsimp?)[1]
                  apply (clarsimp simp: downset_set_def' in_down_iff)
                  apply (elim disjE; clarsimp?)
        apply (metis fst_conv order_refl snd_conv)

      apply (clarsimp simp: downset_set_def')+
  apply (metis Un_iff fst_conv snd_conv)
  apply (simp add: down_union_distrib image_Un)+
    apply (clarsimp simp: inf_downset_def, transfer)
 apply (safe; clarsimp?)[1]
      apply (clarsimp simp: downset_set_def')

          apply (fastforce simp: down_union_distrib image_Un down_image_iff )+
    apply (clarsimp simp: down_image_iff)
    apply (frule (1) step_meet') back
    apply (elim disjE; clarsimp?)
  apply (smt (verit, ccfv_threshold) Diff_iff IntI fst_conv in_omega last_step' order_trans rangeI seq_atomic.step_le seq_atomic_axioms snd_conv step_atomic step_meet' test_nil)

              apply (transfer; clarsimp)
             apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp)
  apply (safe; clarsimp simp: downset_set_def')[1]
  apply (metis fst_eqD snd_eqD subsetD)
  apply (drule_tac c="step a (aa,b)" in subsetD)
   apply (clarsimp)+
  by (metis le_test order_trans step_le)


sublocale seq_elem_fiter: iteration_finite_distrib convolute conv_test_pre.nil
  apply (standard)
  using conv_seq_distrib.seq_nondet_distrib by presburger

sublocale seq_elem_iter: iteration_infinite_distrib convolute conv_test_pre.nil
  apply (standard)
  using conv_seq_Distrib.seq_Nondet_distrib by presburger


end

end