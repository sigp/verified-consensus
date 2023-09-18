theory CRA_Obs
imports Par_Obs Conj_Obs Seq_Obs
begin

locale seq_par = seq: test_seq + par: par_elem +
  constrains seq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and to_env :: "'a \<Rightarrow> 'a"

locale seq_par_elem = seq_par + exchange_semigroup_ordered seq par  +
 constrains bot :: "'a :: preorder_bot" 
 assumes nil_par_nil_weak: "\<And>x. test x \<parallel> test x \<ge> test x" and
          skip_ref_nil: "\<And>x. to_env (first x) \<ge> first x" and 
         seq_subunits: "\<And>a b. (to_env a ; to_env b) \<le> to_env (a ; b) " 


context seq_par_elem begin



lemma exchange_test': "\<And>t . test t ; (a \<parallel> b) \<le> (test t ; a) \<parallel> (test t ; b)" 
  apply (rule order_trans[rotated], rule exchange)
  by (rule seq.mono_f, rule nil_par_nil_weak, clarsimp)



lemma nil_le_skip: "seq.dnil \<le> par.dunit"
  apply (clarsimp simp: less_eq_downset_def seq.dnil_def sup_downset_def)
  apply (transfer; clarsimp; clarsimp simp: down_image_iff)

   apply (rule_tac x = "first y" in exI)
   apply (erule order_trans)
  using skip_ref_nil 
  by (metis image_iff rangeI seq.first_last)


sublocale exchange_semigroup_ordered seq par ..

lemma le_bot_le_any[elim!]: "x \<le> \<bottom> \<Longrightarrow> x \<le> (y :: 'a :: preorder_bot)" 
  by (meson dual_order.trans preorder_bot_class.bot_least)

lemma [simp]: "\<bottom> \<parallel> \<bottom> \<le> \<bottom>" 
  by (meson dual_order.trans par.down_unit par.mono_f preorder_bot_class.bot_least)

lemma test_to_env: "test x \<le> to_env (test x)"
  by (metis seq.test_is_first skip_ref_nil)

lemma bot_test[simp]:"\<bottom> \<parallel> test x \<le> \<bottom>" 
  using test_to_env 
  by (meson dual_order.trans par.down_unit par.mono_f preorder_bot_class.bot_least)
 

lemma test_bot[simp]: "test x \<parallel> \<bottom>  \<le> \<bottom>" 
  by (meson bot_test dual_order.trans par.commute)





sublocale seq_par: sequential_parallel seq.convolute seq.dnil par.convolute par.dunit
  apply (standard; clarsimp?)
     apply (clarsimp simp: less_eq_downset_def seq.nil_dnil[symmetric] 
                           sup_downset_def seq.conv_test_pre.nil_def, transfer)

     apply (clarsimp simp: less_eq_downset_def seq.dnil_def sup_downset_def, transfer)
  apply (intro conjI; clarsimp)
      apply (clarsimp simp: down_sup_distrib down_union_distrib in_down_iff down_image_iff Bex_def)
     apply (meson dual_order.refl nil_par_nil_weak order_trans)
    apply (clarsimp simp: less_eq_downset_def seq.nil_dnil[symmetric] sup_downset_def
                          seq.conv_test_pre.nil_def, transfer, clarsimp, intro conjI)
     apply (clarsimp simp: down_image_iff)
  apply (meson dual_order.trans test_to_env)
    apply (clarsimp simp: downset_set_def in_down_iff)

   apply (clarsimp simp: less_eq_downset_def seq.nil_dnil[symmetric] sup_downset_def 
           seq.conv_test_pre.nil_def, transfer, clarsimp simp: down_sup_distrib downset_set_def' )
  apply (meson order_trans in_down_iff seq.mono_f seq_subunits)

  by (rule exchange_convolute.exchange)


lemma le_test_par: "x \<le> test xa \<parallel> test xb \<Longrightarrow> \<not> x \<le> \<bottom> \<Longrightarrow>  x \<ge> test xa"
  by (meson dual_order.trans order_eq_refl par.down_unit par.mono_f seq.test_atom test_to_env)


lemma le_bot_par: "x \<le> \<bottom> \<parallel> y \<Longrightarrow> x \<le> y"
  by (metis (no_types, opaque_lifting) dual_order.refl dual_order.trans par.commute
              par.down_unit par.mono_f preorder_bot_class.bot_least)


(* lemma le_first_test: "x \<le> (test t ; a) \<parallel> (test t' ; b) \<Longrightarrow> first x \<le> test t \<or> first x \<le> test t'" 
  oops
  by (meson first_par order.trans seq.first_le seq.first_test_seq) *)

lemma in_Down_iff: "a \<in> \<Down> S \<longleftrightarrow> (\<exists>x\<in>S. a \<le> x)"
  by (clarsimp simp: downset_set_def)

lemma mono_on_helper: "(mono_on UNIV f) \<Longrightarrow>  (\<Union>a\<in>\<Down> S. f a) = (\<Union>a\<in>S. f a) " 
  apply (safe)
   apply (clarsimp simp: in_Down_iff)
   apply (meson in_mono monotoneD)
  using in_Down_iff by auto


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



lemma not_bot_testable: "\<not> x \<le> \<bottom> \<Longrightarrow> \<exists>t. first x \<le> test t" 
  apply (erule contrapos_np, clarsimp)
  by (metis Diff_iff image_iff le_bot_le_any order_refl rangeI in_down_iff seq.test_nil)

lemma test_seq_eq: "\<not>(test t ; (test xa) \<le> \<bottom>) \<Longrightarrow> t = xa"
  by (meson dual_order.trans seq.le_test seq.test_atom seq.test_le seq.test_le')

lemma par_conv_test_inf: "par.convolute (seq.dtest p) (seq.dtest q) = (seq.dtest p \<sqinter> seq.dtest q) "
  apply (clarsimp simp: inf_downset_def, transfer)
     apply (case_tac "p = {}", clarsimp)
   apply (simp add: rewrite_sup'  monotoneI seq.flip.mono_f par.mono_f le_funI
                                        seq.rewrite_sup_helper rewrite_sup_helper' mono_on_helper 
                                                       rewrite_sup_helper'' rewrite_sup_helper''')
  apply (safe; clarsimp simp: in_Down_iff in_down_iff)
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


lemma "\<exists>t. first c \<le> test t"
  using le_bot_le_any not_bot_testable seq.first_test by blast

lemma firstE: "(\<And>t. first c \<le> test t \<Longrightarrow> P (first c)) \<Longrightarrow> P (first c)"
  using le_bot_le_any not_bot_testable seq.first_test by blast

lemma first_le_first_iff: "first x \<le> first (c) \<longleftrightarrow> x \<le> first c ; x "
  apply (rule firstE)
  apply (subst seq.flip.unit_of_unit, assumption)
  apply (clarsimp)
  done

sublocale seq_par_test: 
    sync_command_with_tests_aborting seq.convolute seq.dtest par.convolute par.dunit

  apply (standard; (clarsimp simp: par_conv_test_inf)?)
      apply (rule antisym)
  apply (rule order_trans[rotated], rule exchange_convolute.exchange, clarsimp simp: par_conv_test_inf )
  apply ( clarsimp simp: less_eq_downset_def)
      apply (transfer)
      apply (case_tac "p = {}", clarsimp simp: in_down_iff)
       apply (rule_tac x="\<bottom>" in bexI; clarsimp?)
  defer
      apply (subst seq.nonempty_bot_union, clarsimp)
       apply (subst seq.nonempty_bot_union, clarsimp)
       apply (subst seq.nonempty_bot_union, clarsimp)


      apply (simp add:rewrite_sup' rewrite_sup monotoneI 
                       seq.flip.mono_f par.mono_f le_funI seq.rewrite_sup_helper 
                       rewrite_sup_helper' mono_on_helper rewrite_sup_helper'' rewrite_sup_helper''')
       apply (clarsimp simp: in_down_iff)
  
       apply (frule seq.first_le)
      apply (subst (asm) first_le_first_iff)

       apply (drule order_trans) back
        apply (rule seq.mono_f, rule order_refl, assumption)
       apply (case_tac "test xa ; xb \<parallel> test xc ; xd \<le> \<bottom>")
        apply (meson dual_order.trans le_bot_le_any)
       apply (frule not_bot_testable, clarsimp)
       apply (frule order_trans) back
        apply (rule seq.mono_f, assumption, rule order_refl)
  apply (frule order_trans) back back back
        apply (rule exchange_test')
       apply (case_tac " test t ; (test xa) \<le> \<bottom>")
       apply (case_tac " test t ; (test xc) \<le> \<bottom>")
  thm seq.assoc
        apply (subgoal_tac "x \<le> \<bottom>")
  using le_bot_le_any apply blast

        apply (erule order_trans) back back back
  apply (rule order_trans[OF par.mono_f], rule seq.assoc, rule seq.assoc)
  
  apply (rule order_trans[OF par.mono_f], rule seq.mono_f, assumption, rule order_refl, rule seq.mono_f, assumption, rule order_refl)
         apply (metis le_bot_par par.mono_f seq.bot_annihilate_seq)
        apply (frule test_seq_eq, clarsimp)
  
        apply (meson in_downsetI seq.test_le')
        apply (frule test_seq_eq, clarsimp)
  apply (meson in_downsetI seq.test_le')
    apply (clarsimp simp: local.seq_par.skip_ref_nil seq.nil_dnil)
  using exchange_convolute.exchange apply force
  apply (transfer)
  apply (clarsimp)
  apply (safe; clarsimp simp: in_down_iff)
   apply (metis par.aborting par.commute dual_order.trans)
  apply (rule_tac x="\<bottom>" in bexI; clarsimp?)
   apply (rule_tac x="\<bottom>" in bexI; clarsimp?)
  apply (rule_tac x="\<bottom>" in bexI; clarsimp?)
  by (metis dual_order.trans le_bot_le_any le_bot_par par.aborting par.mono_f seq.bot_annihilate_seq seq.mono_f)

 

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
                       assumes chaos_par_magic: " \<bottom> \<ge> unit_of a \<parallel> \<bottom>" and
                        unit_of_par: "unit_of (a \<parallel> b) \<ge> unit_of a \<parallel> unit_of b" 
begin


  

sublocale conv_conjunction_parallel: conjunction_parallel  conj.convolute conj.dunit par.convolute par.dunit
  apply (standard; clarsimp?)
    apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: downset_set_def in_down_iff)
    apply (meson chaos_par_magic dual_order.trans par.mono_f)
    apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: downset_set_def in_down_iff)
  apply (smt (verit, best) dual_order.trans par.mono_f unit_of_par)
  by (meson exchange_convolute.exchange)
  
end


locale conj_seq = seq: test_seq + conj: conj_elem + 
  constrains conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and unit_of :: "'a \<Rightarrow> 'a"

locale conj_seq_elem = conj_seq  + 
                       exchange_semigroup_ordered seq conj +
      assumes chaos_seq_chaos_nonaborting: "\<And>a b. unit_of (a ; b) \<ge> unit_of a ; unit_of b"
begin


sublocale conv_conjunction_sequential: conjunction_sequential conj.convolute conj.dunit seq.convolute seq.dnil
  apply (standard)
   apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: downset_set_def in_down_iff)
  apply (meson chaos_seq_chaos_nonaborting dual_order.trans seq.mono_f)
  by (meson exchange_convolute.exchange)


lemma le_bot_conj: "x \<le> \<bottom> \<iinter> y  \<Longrightarrow> x \<le> y"
  by (meson conj.covering dual_order.trans preorder_bot_class.bot_least)

lemma le_bot_conj': "x \<le> y \<iinter> \<bottom>  \<Longrightarrow> x \<le> y"
  by (meson conj.covering dual_order.trans preorder_bot_class.bot_least)


lemma unit_of_test: "unit_of (test x) \<le> test x"
  
  by (simp add: conj.unit_of_unit)

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
  

lemma conj_bot_test[simp]: "conj \<bottom> (test x) \<le> \<bottom>"
  apply (insert test_le_unit_of[where x=x], clarsimp)
  by (meson conj.down_unit conj.mono_f dual_order.trans preorder_bot_class.bot_least)
  

lemma conj_bot_test'[simp]: "conj (test x) \<bottom>  \<le> \<bottom>"
  apply (rule order_trans, rule conj.commute)
  by (simp add: local.conj.commute)

lemma exchange_test': "\<And>t . test t ; (conj a  b) \<le> conj (test t ; a) (test t ; b)" 
  apply (rule order_trans[rotated], rule exchange)
  by (rule seq.mono_f; clarsimp)

lemma test_conj_inf: "test t \<iinter> test t' \<le> test t "
  by (meson conj.down_unit conj.mono_f dual_order.refl dual_order.trans test_le_unit_of)

lemma "(test t)\<^sub>1 \<ge> test t"
  by (metis conj.unit_of_unit conj_bot_test dual_order.trans
       local.conj.commute preorder_bot_class.bot_least seq.test_atom unit_of_test)




sublocale conj_seq_test: 
  sync_command_with_tests_aborting seq.convolute seq.dtest conj.convolute conj.dunit
  apply (standard)
       apply (rule antisym)
        apply (rule_tac y="seq.convolute (conj.convolute (seq.dtest p) (seq.dtest p)) (conj.convolute c d)" in order_trans)
         apply simp
        apply (rule order_trans, rule conv_conjunction_sequential.seq_conj_interchange)
        apply (rule order_refl)
       apply (clarsimp simp: less_eq_downset_def, transfer)
       apply (case_tac "p={}", clarsimp simp: Bex_def in_down_iff)
        apply (rule_tac x=\<bottom> in exI, clarsimp)
        defer
  apply (subst seq.nonempty_bot_union, fastforce)+
        apply (simp add: rewrite_sup' rewrite_sup monotoneI seq.flip.mono_f conj.mono_f le_funI seq.rewrite_sup_helper rewrite_sup_helper'  rewrite_sup_helper'' rewrite_sup_helper''' rewrite_sup_helper'''')
        apply (clarsimp simp: in_down_iff)
  apply (subgoal_tac "first x \<le> test xa \<or> first x \<le> test xc", elim disjE)
          apply (meson dual_order.trans seq.flip.mono_f seq.flip.unit_of_apply in_downsetI seq.test_le')
  apply (meson dual_order.trans seq.flip.mono_f seq.flip.unit_of_apply in_downsetI seq.test_le')
  using conj.covering seq.first_test apply blast
       apply (clarsimp simp: inf_downset_def, transfer)
       apply (case_tac "p={}", clarsimp simp: Bex_def in_down_iff)
        apply (simp add: rewrite_sup' rewrite_sup monotoneI seq.flip.mono_f conj.mono_f le_funI seq.rewrite_sup_helper rewrite_sup_helper'  rewrite_sup_helper'' rewrite_sup_helper''' rewrite_sup_helper'''')
        apply (safe; clarsimp simp: in_down_iff)[1]
          apply (meson conj.mono_f conj_bot_test dual_order.refl dual_order.trans)
  using conj.covering dual_order.trans apply blast
        apply (meson dual_order.trans preorder_bot_class.bot_least in_down_iff)
       apply (subst seq.nonempty_bot_union, fastforce)+
       apply (case_tac "q={}", clarsimp simp: Bex_def in_down_iff)
        apply (simp add: rewrite_sup' rewrite_sup monotoneI seq.flip.mono_f conj.mono_f le_funI seq.rewrite_sup_helper rewrite_sup_helper'  rewrite_sup_helper'' rewrite_sup_helper''' rewrite_sup_helper'''')
        apply (safe; clarsimp simp: in_down_iff in_Down_iff)[1]
  using le_bot_conj' apply blast
         apply (metis conj_bot_test dual_order.trans local.conj.commute)
       apply (subst seq.nonempty_bot_union, fastforce)+
        apply (simp add: rewrite_sup' rewrite_sup monotoneI seq.flip.mono_f conj.mono_f le_funI seq.rewrite_sup_helper rewrite_sup_helper'  rewrite_sup_helper'' rewrite_sup_helper''' rewrite_sup_helper'''')
       apply (safe; clarsimp simp: in_down_iff in_Down_iff)  
         apply (meson conj.down_unit conj.mono_f dual_order.trans order_eq_refl test_le_unit_of)
        apply (metis (no_types, lifting) conj.covering conj.unit_of_unit conj_bot_test dual_order.trans local.conj.commute local.conj.idem preorder_bot_class.bot_least seq.test_atom)
       apply (metis conj.mono_f local.conj.idem)
      apply simp
  apply (simp add: conv_conjunction_sequential.chaos_ref_nil seq.nil_dnil)
  using conv_conjunction_sequential.seq_conj_interchange apply presburger
  using conj.conj_conv.conj_abort_right apply presburger
  by (metis conj.covering preorder_bot_class.bot_least refine_trans seq.aborting seq.bot_annihilate_seq seq.flip.mono_f)
end


locale cra_elem = conj_par_elem + cs: conj_seq_elem + sp: seq_par_elem
begin


sublocale conv_cra: cra cs.seq.convolute cs.seq.conv_test_pre.nil par.convolute par.dunit conj.convolute conj.dunit
  apply (standard; clarsimp?)
       apply (metis order_refl cs.seq.conv_test_pre.test_top sp.seq_par_test.test_sync_nil)
  using sp.seq_par_test.chaos_ref_nil apply force
    apply (simp add: sp.exchange_convolute.exchange)
  using cs.conv_conjunction_sequential.chaos_seq_chaos_nonaborting apply auto[1]
  using cs.conv_conjunction_sequential.seq_conj_interchange by force

sublocale cra_assert: assertions cs.seq.convolute cs.seq.dtest ..

sublocale conv_cra_test: test_commands cs.seq.convolute cs.seq.dtest par.convolute par.dunit conj.convolute conj.dunit
  apply (standard)
    apply (simp add: sp.seq_par_test.test_sync_distrib)
  using cs.conj_seq_test.test_sync_distrib apply force
  using sp.seq_par_test.test_sync_test by fastforce

end


end