theory CRA_Obs
imports Par_Obs Conj_Obs Seq_Obs
begin


locale sync = ab_ordered_semigroup + top_semigroup + sync_semigroup  

locale seq_sync = seq: test_seq + sync: sync +
  constrains seq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and unit_of :: "'a \<Rightarrow> 'a"

begin

notation f (infixl "\<otimes>" 75)

end

locale seq_sync_elem = seq_sync + exchange_semigroup_ordered seq f  +
 assumes nil_par_nil_weak: "\<And>x. test x \<otimes> test x \<ge> test x" and
          skip_ref_nil: "\<And>x. unit_of (first x) \<ge> first x" and 
         seq_subunits: "\<And>a b. (unit_of a ; unit_of b) \<le> unit_of (a ; b) " and 
       first_exchange: "\<And>x y.  first (f x y) \<le> f (first x) (first y) " 

(*
locale seq_par_elem = seq_par + exchange_semigroup_ordered seq par  +
 assumes nil_par_nil_weak: "\<And>x. test x \<parallel> test x \<ge> test x" and
          skip_ref_nil: "\<And>x. to_env (first x) \<ge> first x" and 
         seq_subunits: "\<And>a b. (to_env a ; to_env b) \<le> to_env (a ; b) " and 
       first_exchange: "\<And>x y.  first (par x y) \<le> par (first x) (first y) " 
*)
context test_seq begin

lemma not_bot_testable': "\<not> first x \<in> \<Omega> \<Longrightarrow> \<exists>t. first x \<le> test t" 
  apply (erule contrapos_np, clarsimp)
  apply (insert  test_nil)
  apply (clarsimp simp: set_eq_iff)
  apply (erule_tac x="first x" in allE, clarsimp)
  by auto

lemma not_bot_testable: "\<not>  x \<in> \<Omega> \<Longrightarrow> \<exists>t. first x \<le> test t" 
  apply (clarsimp)
  apply (insert  test_nil)
  apply (clarsimp simp: set_eq_iff)
  apply (erule_tac x="first x" in allE, clarsimp)
  apply (drule iffD2)
   apply (metis dual_order.trans bot_annihilate_seq flip.mono_f flip.unit_of_apply)
  apply (clarsimp)
  by (fastforce)

end


context seq_sync_elem begin



lemma exchange_test': "\<And>t . test t ; (a \<otimes> b) \<le> (test t ; a) \<otimes> (test t ; b)" 
  apply (rule order_trans[rotated], rule exchange)
  by (rule seq.mono_f, rule nil_par_nil_weak, clarsimp)



lemma nil_le_skip: "seq.dnil \<le> sync.dunit"
  apply (clarsimp simp: less_eq_downset_def seq.dnil_def sup_downset_def)
  apply (transfer; clarsimp; clarsimp simp: down_image_iff)

   apply (rule_tac x = "first y" in exI)
   apply (erule order_trans)
  using skip_ref_nil 
  by (metis image_iff rangeI seq.first_last)


sublocale exchange_semigroup_ordered seq f ..


lemma [simp]: "bottom x \<otimes> bottom y \<in> \<Omega>"
  by (meson in_omega order_refl sync.bot_le_unit_bot sync.down_unit sync.mono_f)

lemma test_to_env: "test x \<le> unit_of (test x)"
  by (metis seq.test_is_first skip_ref_nil)

lemma bot_test[simp]:"bottom y \<otimes> test x \<in> \<Omega>"
  by (meson in_omega order_refl sync.down_unit sync.mono_f test_to_env)
 

lemma test_bot[simp]: "test x \<otimes> bottom y \<in> \<Omega>"
  by (meson bot_test in_omega order_trans sync.commute)

lemma neq_par_test_omega:"x \<noteq> y \<Longrightarrow> f (test x) (test y) \<in> \<Omega>"
proof -
  assume a1: "x \<noteq> y"
  have "\<forall>a b. test b \<otimes> a \<le> unit_of (test b) \<otimes> a"
    using sync.mono_f test_to_env by force
  then show ?thesis
    using a1 by (smt (z3) in_omega order_trans sync.commute sync.down_unit seq.test_atom seq.test_le)
qed

lemma omega_seq: "x \<in> \<Omega> \<Longrightarrow> x;y \<in> \<Omega>"
  by (meson in_omega order_trans sync.aborting seq.bot_annihilate_seq seq.flip.mono_f)



(* 
*)

lemma le_test_par: "x \<le> test xa \<otimes> test xb \<Longrightarrow> \<not> x \<in> \<Omega> \<Longrightarrow>  x \<ge> test xa"
  by (meson dual_order.trans in_omega order_refl sync.down_unit sync.mono_f seq.test_atom test_to_env)


lemma le_bot_par: "x \<le> bottom x \<otimes> y \<Longrightarrow> x \<le> y"
  oops


(* lemma le_first_test: "x \<le> (test t ; a) \<parallel> (test t' ; b) \<Longrightarrow> first x \<le> test t \<or> first x \<le> test t'" 
  oops
  by (meson first_par order.trans seq.first_le seq.first_test_seq) *)

lemma in_Down_iff: "a \<in> \<Down> S \<longleftrightarrow> (\<exists>x\<in>S. a \<le> x)"
  by (clarsimp simp: downset_set_def)

lemma mono_on_helper: "(mono_on UNIV g) \<Longrightarrow>  (\<Union>a\<in>\<Down> S. g a) = (\<Union>a\<in>S. g a) " 
  apply (safe)
   apply (clarsimp simp: in_Down_iff)
   apply (meson in_mono monotoneD)
  using in_Down_iff by auto


lemma rewrite_sup_helper': "mono_on UNIV g  \<Longrightarrow> (\<Union>a\<in>\<Down> S. \<Union>b\<in>S'. \<Union>c\<in>S''. \<down> (g a b c)) = (\<Union>a\<in>S. \<Union>b\<in>S'. \<Union>c\<in>S'' . \<down> (g a b c))"
  apply (intro set_eqI iffI; clarsimp simp: in_down_iff)
   apply (smt (verit) downset_set_def le_fun_def mem_Collect_eq monotoneD order_trans)
  using downset_set_def by blast


lemma rewrite_sup_helper'': "mono_on UNIV g  \<Longrightarrow> (\<Union>a\<in>\<down> a. \<Union>b\<in>S'. \<Union>c\<in>S''. \<down> (g a b c)) = (\<Union>b\<in>S'. \<Union>c\<in>S'' . \<down> (g a b c))"
  apply (intro set_eqI iffI; clarsimp simp: in_down_iff)
   apply (smt (verit) downset_set_def le_fun_def mem_Collect_eq monotoneD order_trans)
  using in_down_iff by auto

lemma rewrite_sup_helper'''': "mono_on UNIV g \<Longrightarrow> (\<Union>a\<in>\<Down> S. \<down> (g a)) = (\<Union>a\<in> S. \<down> (g a))  "
apply (intro set_eqI iffI; clarsimp simp: in_down_iff)
   apply (smt (verit) downset_set_def le_fun_def mem_Collect_eq monotoneD order_trans)
  using in_Down_iff by auto

lemma rewrite_sup_helper''': "mono_on UNIV g  \<Longrightarrow> (\<Union>a\<in>\<down> a. \<Union>b\<in>S'. \<down> (g a b)) = (\<Union>b\<in>S'.  \<down> (g a b ))"
  apply (intro set_eqI iffI; clarsimp simp: in_down_iff)
   apply (smt (verit) downset_set_def le_fun_def mem_Collect_eq monotoneD order_trans)
  using in_down_iff by auto





lemma test_seq_eq: "\<not>(test t ; (test xa) \<in> \<Omega>) \<Longrightarrow> t = xa"
  by (meson \<Omega>_def dual_order.trans in_omega seq.le_test seq.test_atom seq.test_le seq.test_le')



lemma par_conv_test_inf: "sync.convolute (seq.dtest p) (seq.dtest q) = (seq.dtest p \<sqinter> seq.dtest q) "
  sorry
  apply (clarsimp simp: inf_downset_def, transfer)
  apply (case_tac "p = {}", clarsimp)
   apply (safe; clarsimp simp: in_Down_iff in_down_iff)
     apply (meson bot_test in_omega order_trans par.mono_f)
    apply (meson in_omega par.bot_le_unit_bot par.down_unit par.mono_f refine_trans)
   apply (rule_tac x="bottom y" in bexI, clarsimp)
    apply (meson in_omega order_refl order_trans par.bot_idemp)
   apply (clarsimp)
   apply (fastforce)
  apply (clarsimp simp: UN_Un)
   apply (simp add: rewrite_sup'  monotoneI seq.flip.mono_f par.mono_f le_funI
                                        seq.rewrite_sup_helper rewrite_sup_helper' mono_on_helper 
                                                       rewrite_sup_helper'' rewrite_sup_helper''')
  apply (safe; clarsimp simp: in_Down_iff in_down_iff)
  sledgehammer
        apply (meson bot_test dual_order.trans le_bot_le_any par.mono_f)
       apply (metis dual_order.trans le_bot_par par.commute)
  using le_bot_le_any in_down_iff apply blast
     apply (subst seq.nonempty_bot_union, fastforce)+
     apply (case_tac "q = {}", clarsimp)
  apply (safe; clarsimp simp: in_Down_iff in_down_iff)
        apply (meson le_bot_le_any ordered_semigroup.mono_f par.down_unit par.ordered_semigroup_axioms refine_trans)
       apply (meson par.mono_f refine_trans test_bot)
      apply (metis le_bot_le_any down_image_iff in_down_iff)
     apply (subst seq.nonempty_bot_union, fastforce)+
  apply (simp add: rewrite_sup' rewrite_sup monotoneI seq.flip.mono_f par.mono_f 
      le_funI seq.rewrite_sup_helper rewrite_sup_helper' mono_on_helper 
      rewrite_sup_helper'' rewrite_sup_helper''' rewrite_sup_helper'''')
     apply (safe; clarsimp simp: in_down_iff in_Down_iff)
    apply (smt (verit) bot_test le_bot_le_any le_test_par order_trans
                       par.commute par.down_unit par.mono_f test_to_env)
  defer
   apply (metis (no_types, opaque_lifting) dual_order.trans nil_par_nil_weak preorder_bot_class.bot_least seq.test_atom seq.test_le)
  by (meson dual_order.trans order_eq_refl par.commute par.down_unit par.mono_f test_to_env)


lemma first_le_first_iff: "first x \<le> first (c) \<longleftrightarrow> x \<le> first c ; x "
  apply (safe)
   apply (meson dual_order.trans order_refl seq.flip.unit_of_apply seq.mono_f)
  apply (case_tac "first c \<in> \<Omega>", clarsimp)
  
proof -
  fix y :: 'a
  assume a1: "x \<le> first c ; x"
  assume a2: "first c \<le> y\<^sub>\<bottom>"
  then have "c\<^sub>\<bottom> \<le> y\<^sub>\<bottom>"
    by (meson dual_order.refl dual_order.trans preorder_bot_class.bot_least seq.first_le seq.flip.bot_le_unit_bot)
  then have "c\<^sub>\<bottom> \<le> y"
    by (metis (no_types) dual_order.refl dual_order.trans preorder_bot_class.bot_least)
  then have "first c ; x \<le> c"
    using a2 by (meson dual_order.refl dual_order.trans preorder_bot_class.bot_least seq.bot_annihilate_seq seq.flip.mono_f)
  then show "first x \<le> first c"
    using a1 by (meson dual_order.trans seq.first_le)
next
  assume a1: "x \<le> first c ; x"
  assume a2: "first c \<notin> \<Omega> "
  show " first x \<le> first c"
    using a1 a2 
    by (smt (verit, ccfv_SIG) Diff_iff rangeE range_eqI seq.test_nil seq.test_seq_axioms test_seq.first_test)
qed


lemma par_conv_sub: "x \<down>\<in> sync.convolute c d \<Longrightarrow>  (\<And>a b. a \<down>\<in> c \<Longrightarrow> b \<down>\<in> d \<Longrightarrow> (f a b) \<down>\<in>S ) \<Longrightarrow> x \<down>\<in> S"
  apply (transfer; clarsimp simp: in_down_iff)
  apply (atomize)
  using local.in_Down_iff by blast


lemma seq_conv_sub: "x \<down>\<in> seq.convolute c d \<Longrightarrow>  (\<And>a b. a \<down>\<in> c \<Longrightarrow> b \<down>\<in> d \<Longrightarrow> (seq a b) \<down>\<in>S ) \<Longrightarrow> x \<down>\<in> S"
  apply (transfer; clarsimp simp: in_down_iff)
  apply (atomize)
  using local.in_Down_iff by blast


lemma seq_conv_par_sub: "x \<down>\<in> seq.convolute c d \<Longrightarrow>  (\<And>a b. a \<down>\<in> c \<Longrightarrow> b \<down>\<in> d \<Longrightarrow> f (seq a b) x' \<down>\<in>S ) \<Longrightarrow> (f x x') \<down>\<in> S"
  apply (transfer; clarsimp simp: in_down_iff)
  apply (atomize)
  apply (erule_tac x=xa in allE)
  apply (erule_tac x=xb in allE)
  apply (clarsimp)
  by (metis local.in_Down_iff order_refl sync.mono_f)






lemma test_par_join: "test t ; a \<otimes> test t ; b \<le> (test t) ; f a b "
  sorry  

lemma test_seq_in_downclosed: "x \<in> d \<Longrightarrow> \<Omega> \<subseteq> d \<Longrightarrow> \<Down>d=d \<Longrightarrow> test t ; x \<in> d"
  by (meson in_downsetI in_mono in_omega seq.test_le')

lemma first_first_le: "first (first c) \<ge> (first c)"
  by (metis order_trans seq.down_last seq.first_last_ex seq.flip.unit_of_apply)


lemma non_sync_first_omega: "a \<noteq> b \<Longrightarrow> first (test a ; c \<otimes> test b ; d) \<in> \<Omega>"
  apply (clarsimp)
  apply (drule neq_par_test_omega, clarsimp)
  apply (rule_tac x=y in exI)
  apply (rule order_trans)
   apply (rule first_exchange)
  apply (rule order_trans)
   apply (rule sync.mono_f)
    apply (rule seq.first_test_seq)
   apply (rule seq.first_test_seq, assumption)
  done  

lemma first_first_seq_le: "first (first x ; d) \<le> first x" 
  apply (case_tac "first x \<in> \<Omega>") 
  apply (clarsimp)
   apply (metis (mono_tags, opaque_lifting) dual_order.trans order_refl preorder_bot_class.bot_least seq.bot_annihilate_seq seq.first_le seq.flip.bot_le_unit_bot seq.flip.mono_f)
  apply (frule seq.not_bot_testable', clarsimp)
  by (meson refine_trans seq.aborting seq.first_test seq.flip.mono_f seq.test_atom)
 (* anot_bot_testable'"=
  find_theorems first test *)



lemma test_neq_first_in_omega:"test t \<noteq> first c \<Longrightarrow> f (test t) (first c) \<in> \<Omega>" nitpick
  apply (clarsimp)
  apply (case_tac "first c \<in> \<Omega>", clarsimp)
   apply (meson in_omega omega_mono order_refl sync.mono_f test_bot)

  apply (frule seq.not_bot_testable')
  apply (clarsimp)
  
  sorry



lemma non_sync_first_first_omega: "test t \<noteq> first x \<Longrightarrow>  first (test t; c \<otimes> first x; d) \<in> \<Omega>"
  apply (clarsimp)
  apply (drule test_neq_first_in_omega, clarsimp)
  apply (rule_tac x=y in exI)
  apply (rule order_trans)
   apply (rule first_exchange) 
  apply (rule order_trans)
   apply (rule sync.mono_f)
     apply (rule seq.first_test_seq)
    apply (rule first_first_seq_le)
  apply (assumption)
  done

lemma par_closed_omega: "x \<in> \<Omega> \<Longrightarrow> y \<in> \<Omega> \<Longrightarrow> f x y \<in> \<Omega>"
  by (metis in_omega ordered_semigroup_def sync.bot_le_unit_bot
            sync.down_unit sync.ordered_semigroup_axioms refine_trans)




lemma first_neq_first_in_omega:"first x \<noteq> first y \<Longrightarrow> f (first x)  (first y) \<in> \<Omega>"
  by (smt (verit, best) seq.not_bot_testable' omega_mono order_eq_refl sync.commute sync.mono_f par_closed_omega test_neq_first_in_omega)

lemma first_first: "first x \<noteq> first y \<Longrightarrow> first (first x ; c \<otimes> first y ; d) \<in> \<Omega>"
apply (clarsimp)
  apply (drule first_neq_first_in_omega, clarsimp)
  apply (rule_tac x=ya in exI)
  apply (rule order_trans)
   apply (rule first_exchange) 
  apply (rule order_trans)
   apply (rule sync.mono_f)
     apply (rule first_first_seq_le)
   apply (rule first_first_seq_le)
  apply (assumption)
  done

find_theorems first par

thm exchange

lemma bottom_exchange: "x \<le> bottom y ; xb \<otimes> bottom ya ; xe \<Longrightarrow> x \<le> (y\<^sub>\<bottom> \<otimes> bottom ya) ; (y\<^sub>\<bottom> ; xb \<otimes> bottom ya ; xe)"
  apply (erule order_trans)
proof -
  obtain aa :: "'a \<Rightarrow> 'a" where
    f1: "\<forall>a. (a \<in> \<Omega> \<or> (\<forall>aa. \<not> a \<le> aa\<^sub>\<bottom>)) \<and> (a \<le> bottom (aa a) \<or> a \<notin> \<Omega>)"
    by (metis in_omega le_bottom_bottom_le order_trans preorder_bot_class.bot_least)
  then have f2: "\<forall>a aa ab ac. aa\<^sub>\<bottom> ; ac \<otimes> bottom a ; ab \<in> \<Omega>"
    using par_closed_omega seq.bot_annihilate_seq by blast
  then have "\<exists>a\<ge>y\<^sub>\<bottom> \<otimes> (bottom ya). a \<le>bottom   (aa (bottom y ; xb \<otimes> bottom ya ; xe))"
    using f1 by (meson le_bottom_bottom_le sync.mono_f seq.bot_annihilate_seq)
  then show "bottom y ; xb \<otimes> bottom ya ; xe \<le> (bottom y \<otimes> bottom ya) ; (bottom y ; xb \<otimes> bottom ya ; xe)"
    using f2 f1 
     by (meson dual_order.trans le_bottom_bottom_le seq.bot_annihilate_seq seq.flip.mono_f)
qed


sublocale seq_sync_test: 
    sync_command_with_tests_aborting seq.convolute seq.dtest sync.convolute sync.dunit

  apply (standard; (clarsimp simp: par_conv_test_inf)?)
      apply (rule antisym)
  apply (rule order_trans[rotated], rule exchange_convolute.exchange, clarsimp simp: par_conv_test_inf )
     apply ( clarsimp simp: less_eq_downset_def)
      apply (case_tac "p = {}", clarsimp simp: in_down_iff)
      apply (metis less_eq_downset_def order_class.order_eq_iff par_conv_test_inf seq.conv_test.test_inf_eq_seq seq.conv_test.test_seq_idem seq.conv_test_pre.test.hom_bot)
 
     apply (transfer)
  apply (simp)
  apply (intro conjI)
      apply (simp add:rewrite_sup' rewrite_sup monotoneI 
                       seq.flip.mono_f sync.mono_f le_funI seq.rewrite_sup_helper 
                       rewrite_sup_helper' mono_on_helper rewrite_sup_helper'' rewrite_sup_helper''')
      apply ( clarsimp simp: in_down_iff)
      apply (elim disjE; clarsimp simp: down_image_iff)
       apply (subgoal_tac "x \<le> f (test y ; xb) (test xd ; xe)")

       apply (frule seq.first_le) back back back
        apply (subst (asm) first_le_first_iff) 
        apply (case_tac "y = xd"; clarsimp?)
         apply (meson order_trans test_par_join)
  apply (drule non_sync_first_omega)
         apply (erule_tac x="first (test y ; xb \<otimes> test xd ; xe)" in ballE)
  apply (erule_tac x="test y ; xb" in ballE)
           apply (erule_tac x="test xd ; xe" in ballE)
            apply (meson dual_order.trans seq.flip.unit_of_apply)
  using test_seq_in_downclosed 
           apply blast
 using test_seq_in_downclosed 
         apply blast
       apply (blast)
      apply (meson dual_order.trans order_refl sync.mono_f seq.flip.mono_f)
     apply (subgoal_tac "x \<le> f (test y ; xb) (first (bottom ya); (bottom ya ; xe))")
      apply (frule seq.first_le) back back back back
      apply (subst (asm) first_le_first_iff) 
      apply (case_tac "first (bottom ya) = test y ", clarsimp)
  apply (drule order_trans, rule test_par_join)
       apply (metis IntD2 in_omega inf.orderE seq.bot_annihilate_seq)
      apply (erule_tac x="first (test y ; xb \<otimes> first (bottom ya) ; (ya\<^sub>\<bottom> ; xe))" in ballE)
       apply (erule_tac x="test y ; xb" in ballE)
        apply (erule_tac x="first (bottom ya) ; (ya\<^sub>\<bottom> ; xe)" in ballE)
         apply (meson dual_order.trans seq.flip.unit_of_apply)
  apply (erule notE) back back
        apply (metis in_mono in_omega local.in_Down_iff omega_seq order_refl seq.flip.down_unit)
  using test_seq_in_downclosed apply blast
       apply (metis non_sync_first_first_omega)
      apply (meson order_refl order_trans sync.mono_f seq.assoc' seq.flip.mono_f seq.flip.unit_of_apply)

      apply (simp add:rewrite_sup' rewrite_sup monotoneI 
                       seq.flip.mono_f sync.mono_f le_funI seq.rewrite_sup_helper 
                       rewrite_sup_helper' mono_on_helper rewrite_sup_helper'' rewrite_sup_helper''')
     apply ( clarsimp simp: in_down_iff)
     apply (elim disjE; clarsimp)
     apply (subgoal_tac "x \<le> f (first (bottom y); (bottom y ; xb)) (test xd ; xe) ")

      apply (case_tac "first (bottom y) = test xd ", clarsimp?)
        apply (meson in_omega order_trans seq.bot_annihilate_seq subset_iff test_par_join)
       apply (erule_tac x="first (first (bottom y) ; (y\<^sub>\<bottom> ; xb) \<otimes> test xd ; xe)" in ballE)
        apply (erule_tac x="(first (bottom y); (bottom y ; xb))" in ballE)
         apply (erule_tac x="(test xd ; xe)" in ballE)
          apply (meson dual_order.trans seq.flip.unit_of_apply)
  using test_seq_in_downclosed apply auto[1]
        apply (meson dual_order.trans in_omega seq.assoc seq.assoc' seq.bot_annihilate_seq seq.flip.down_unit subset_iff)
       apply (smt (verit, ccfv_SIG) dual_order.trans in_omega non_sync_first_first_omega sync.commute seq.first_le)
      apply (erule order_trans)
  apply (rule sync.mono_f)
       apply (meson dual_order.trans first_le_first_iff order_refl seq.bot_annihilate_seq seq.first_le seq.mono_f)
      apply (rule order_refl)
     apply (subgoal_tac "x \<le> f (bottom y ; xb) (bottom ya ; xe)")
  apply (subgoal_tac "x \<le> f (bottom y) (bottom ya) ; f (bottom y ; xb) (bottom ya ; xe)")
      apply (erule_tac x="f (bottom y) (bottom ya)" in ballE)
       apply (erule_tac x="(bottom y ; xb)" in ballE)
  apply (erule_tac x="(bottom ya ; xe)" in ballE)
         apply (meson dual_order.trans seq.flip.unit_of_apply)
        apply (meson in_mono in_omega seq.bot_annihilate_seq)
        apply (meson in_mono in_omega seq.bot_annihilate_seq)
       apply (meson in_omega order_refl par_closed_omega)
  using bottom_exchange apply presburger

  apply (meson dual_order.trans order_refl sync.mono_f seq.flip.mono_f)
  using nil_le_skip seq.nil_dnil apply fastforce
  using exchange_convolute.exchange apply force
  apply (transfer)
  apply (clarsimp)
   apply (safe; clarsimp simp: in_down_iff)
  apply (meson in_omega order_eq_refl sync.aborting sync.commute refine_trans subsetD)
  done

 

end


locale seq_par = seq: test_seq + par: par_elem +
  constrains seq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and to_env :: "'a \<Rightarrow> 'a"

locale seq_par_elem = seq_par + seq_sync_elem seq last test first par to_env

begin

sublocale seq_par: sequential_parallel seq.convolute seq.dnil par.convolute par.dunit
  apply (standard; clarsimp?)
     apply (clarsimp simp: less_eq_downset_def seq.nil_dnil[symmetric] 
                           sup_downset_def seq.conv_test_pre.nil_def, transfer)

     apply (clarsimp simp: less_eq_downset_def seq.dnil_def sup_downset_def, transfer)
  apply (intro conjI; clarsimp)
      apply (clarsimp simp: down_sup_distrib down_union_distrib in_down_iff down_image_iff Bex_def)
      apply (meson dual_order.refl nil_par_nil_weak order_trans)
      apply (clarsimp simp: down_sup_distrib down_union_distrib in_down_iff down_image_iff Bex_def)
  apply (meson in_omega order_refl order_trans par.bot_idemp)
    apply (clarsimp simp: less_eq_downset_def seq.nil_dnil[symmetric] sup_downset_def
                          seq.conv_test_pre.nil_def, transfer, clarsimp, intro conjI)
     apply (clarsimp simp: down_image_iff)
  apply (meson dual_order.trans test_to_env)
    apply (clarsimp simp: downset_set_def in_down_iff)
  using order_trans par.bot_le_unit_bot apply blast
   apply (clarsimp simp: less_eq_downset_def seq.nil_dnil[symmetric] sup_downset_def 
           seq.conv_test_pre.nil_def, transfer, clarsimp simp: down_sup_distrib downset_set_def' )
  apply (meson order_trans in_down_iff seq.mono_f seq_subunits)
  by (rule exchange_convolute.exchange)

end


lemma rewrite_sup_helper': "mono_on UNIV f  \<Longrightarrow> (\<Union>a\<in>\<Down> S. \<Union>b\<in>S'. \<Union>c\<in>S''. \<down> (f a b c)) = (\<Union>a\<in>S. \<Union>b\<in>S'. \<Union>c\<in>S'' . \<down> (f a b c))"
  apply (intro set_eqI iffI; clarsimp simp: in_down_iff)
   apply (smt (verit) downset_set_def le_fun_def mem_Collect_eq monotoneD order_trans)
  using downset_set_def by blast


lemma rewrite_sup_helper'': "mono_on UNIV f  \<Longrightarrow> (\<Union>a\<in>\<down> a. \<Union>b\<in>S'. \<Union>c\<in>S''. \<down> (f a b c)) = (\<Union>b\<in>S'. \<Union>c\<in>S'' . \<down> (f a b c))"
  apply (intro set_eqI iffI; clarsimp simp: in_down_iff)
   apply (smt (verit) downset_set_def le_fun_def mem_Collect_eq monotoneD order_trans)
  using in_down_iff by auto

lemma rewrite_sup_helper'''': "mono_on UNIV f \<Longrightarrow> (\<Union>a\<in>\<Down> S. \<down> (f a)) = (\<Union>a\<in> S. \<down> (f a))  "
apply (intro set_eqI iffI; clarsimp simp: in_down_iff)
   apply (smt (verit) downset_set_def le_fun_def mem_Collect_eq monotoneD order_trans)
  using in_Down_iff by auto

lemma rewrite_sup_helper''': "mono_on UNIV f  \<Longrightarrow> (\<Union>a\<in>\<down> a. \<Union>b\<in>S'. \<down> (f a b)) = (\<Union>b\<in>S'.  \<down> (f a b ))"
  apply (intro set_eqI iffI; clarsimp simp: in_down_iff)
   apply (smt (verit) downset_set_def le_fun_def mem_Collect_eq monotoneD order_trans)
  using in_down_iff by auto

locale conj_par = conj: conj_elem + par: par_elem +
  constrains par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and to_env :: "'a \<Rightarrow> 'a"

locale conj_par_elem = conj_par + 
                       exchange_semigroup_ordered  par conj + 
                       assumes chaos_par_magic: "\<And>a b.  (unit_of a \<parallel> bottom b) \<in> \<Omega>" and
                        unit_of_par: "unit_of (a \<parallel> b) \<ge> unit_of a \<parallel> unit_of b" 
begin


  

sublocale conv_conjunction_parallel: conjunction_parallel  conj.convolute conj.dunit par.convolute par.dunit
  apply (standard; clarsimp?)
    apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: downset_set_def in_down_iff)
  apply (meson chaos_par_magic par.mono_f refine_trans)
    apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: downset_set_def in_down_iff)
  apply (smt (verit, best) dual_order.trans par.mono_f unit_of_par)
  by (meson exchange_convolute.exchange)
  
end


locale conj_seq = seq: test_seq + conj: conj_elem + 
  constrains conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and unit_of :: "'a \<Rightarrow> 'a"

locale conj_seq_elem = conj_seq  + 
                       seq_sync_elem seq last test first  conj (*+
      assumes chaos_seq_chaos_nonaborting: "\<And>a b. unit_of (a ; b) \<ge> unit_of a ; unit_of b" *)
begin


sublocale conv_conjunction_sequential: conjunction_sequential conj.convolute conj.dunit seq.convolute seq.dnil
  apply (standard)
   apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: downset_set_def in_down_iff)
  
  apply (meson order_trans seq.mono_f seq_subunits)
  by (meson exchange_convolute.exchange)
(*

lemma le_bot_conj: "x \<le> \<bottom> \<iinter> y  \<Longrightarrow> x \<le> y"
  oops
  by (meson conj.covering dual_order.trans preorder_bot_class.bot_least)

lemma le_bot_conj': "x \<le> y \<iinter> \<bottom>  \<Longrightarrow> x \<le> y"
  oops
  by (meson conj.covering dual_order.trans preorder_bot_class.bot_least)
*)

lemma unit_of_test: "unit_of (test x) \<le> test x"
  oops
  

lemma test_le_unit_of: "\<exists>c. test x \<le> unit_of c"
  apply (insert conv_conjunction_sequential.chaos_ref_nil)
  apply (clarsimp simp: less_eq_downset_def seq.nil_dnil[symmetric])
  apply (clarsimp simp: seq.conv_test_pre.nil_def)
  apply (transfer)
  apply (clarsimp simp: subset_iff down_image_iff)
  apply (erule_tac x="test x" in allE)
  apply (clarsimp)
  apply (fastforce)
  done
  

lemma conj_bot_test[simp]: "conj (bottom a) (test x) \<in> \<Omega>"
  apply (insert test_le_unit_of[where x=x], clarsimp)
  by (meson conj.down_unit conj.mono_f in_omega order_refl)

lemma conj_bot_test'[simp]: "conj (test x) (bottom a)  \<in> \<Omega>"
  by (metis \<Omega>_def conj_bot_test down_down in_downsetI local.conj.commute)

lemma exchange_test': "\<And>t . test t ; (conj a  b) \<le> conj (test t ; a) (test t ; b)" 
  apply (rule order_trans[rotated], rule exchange)
  using conj.idemp seq.flip.mono_f by auto

lemma test_conj_inf: "test t \<iinter> test t' \<le> test t "
  oops

lemma "(test t)\<^sub>1 \<ge> test t"
  oops



lemma bottom_seq_omega: "bottom x ; y \<in> \<Omega>"
  using seq.bot_annihilate_seq by auto


(* sublocale conj_seq_test: 
  sync_command_with_tests_aborting seq.convolute seq.dtest conj.convolute conj.dunit
  apply (standard)
  done
*)
end


locale cra_elem = conj_par_elem + cs: conj_seq_elem + sp: seq_par_elem
begin


sublocale conv_cra: cra cs.seq.convolute cs.seq.conv_test_pre.nil par.convolute par.dunit conj.convolute conj.dunit
  apply (standard; clarsimp?)
  using cs.seq.nil_dnil sp.seq_par.nil_par_nil_weak apply force
  apply (simp add: sp.seq_sync_test.chaos_ref_nil)
    apply (simp add: sp.exchange_convolute.exchange)
  using cs.conv_conjunction_sequential.chaos_seq_chaos_nonaborting apply auto[1]
  using cs.conv_conjunction_sequential.seq_conj_interchange by force

sublocale cra_assert: assertions cs.seq.convolute cs.seq.dtest ..

sublocale conv_cra_test: test_commands cs.seq.convolute cs.seq.dtest par.convolute par.dunit conj.convolute conj.dunit
  apply (standard)
  using sp.seq_sync_test.test_sync_distrib apply auto[1]
   apply (meson cs.seq_sync_test.test_sync_distrib)
  by (simp add: sp.seq_sync_test.test_sync_test)

end


end