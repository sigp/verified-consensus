theory Seq_Obs
  imports
   Ordered_Semigroups
  "rg-algebra/General/Sequential"
begin


locale first = fixes first

locale last  = fixes last

locale seq =  fixes seq :: "'a  \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 90) 

locale test_semigroup = ordered_semigroup + 
  fixes unit_of :: "'a \<Rightarrow> 'a" ("(_\<^sub>1)" [1000] 999)
  fixes test :: "'b  \<Rightarrow> 'a" 
  assumes unit_of_unit: "\<And>a t. (unit_of a) \<le> test t \<longleftrightarrow> a \<le> f a (test t)"
  assumes down_unit:    "\<And> a b. x \<le> f b (unit_of a) \<Longrightarrow> x \<le> b \<or> x \<le> bottom a " 
  assumes unit_of_apply: "\<And>a. a \<le> f a (unit_of a)"
  assumes bot_le_unit_bot: "bottom x \<le> unit_of (bottom x)" 
  assumes first_test: "\<And>t. unit_of (test t) \<le> (test t)" 

begin


lift_definition dunit :: "'a downset" is "\<Down>(range unit_of) "
  apply (clarsimp)
  apply (clarsimp simp: downset_set_def')
  apply (rule_tac x="bottom y" in exI)
  using bot_le_unit_bot order_trans by blast


sublocale conv_right: right_monoid convolute dunit
  apply (standard)
  apply (transfer)
   apply (clarsimp simp:  down_sup_distrib )
  apply (safe; clarsimp simp: in_down_iff down_image_iff )
   defer
   apply (meson UNIV_I down_image_iff order_refl unit_of_apply)
  by (smt (verit, ccfv_SIG) down_unit dual_order.trans in_Down_iff in_omega order_eq_refl ordered_semigroup.mono_f ordered_semigroup_axioms subsetD)
 
end



locale seq_elem = seq + last + 
  flip: test_semigroup "\<lambda>x y. seq y x" first + first + bot_strict seq +
  constrains first :: "'a \<Rightarrow> 'a"
  constrains last :: "'a \<Rightarrow> 'a"
  assumes down_last: "\<And>a b. seq b (last a) \<le> b"
  assumes last_unit: "\<And>b. b \<le> seq b (last b)"
  assumes first_last: "range last = range first "
begin


definition "dnil = flip.dunit"

lemma first_last_ex: "\<exists>x. first y = last x"
  using first_last by auto

sublocale monoid convolute dnil
  apply (standard)
   apply (clarsimp simp: dnil_def sup_downset_def )
   apply (transfer)
  apply (intro set_eqI)
   apply (clarsimp simp: down_sup_distrib down_union_distrib down_image_iff)
   apply (safe; clarsimp simp: down_image_iff in_down_iff)
  apply (smt (verit, ccfv_SIG) flip.down_unit dual_order.trans in_Down_iff in_omega order_eq_refl ordered_semigroup.mono_f ordered_semigroup_axioms subsetD)

   apply (clarsimp simp: down_image_iff in_down_iff Bex_def)
  using flip.unit_of_apply apply blast
apply (clarsimp simp: dnil_def sup_downset_def)
   apply (transfer)
  apply (intro set_eqI)
   apply (clarsimp simp: down_sup_distrib down_union_distrib down_image_iff)
  apply (safe; clarsimp simp: down_image_iff in_down_iff)
  apply (drule order_trans, rule mono_f, rule order_refl, assumption)
  apply (metis down_last first_last_ex  in_Down_iff)
  apply (clarsimp simp: down_image_iff in_down_iff Bex_def)
  by (metis first_last last_unit order_refl rangeE rangeI)


sublocale downset_seq_distrib_left: seq_distrib_left convolute dnil
  apply (standard; clarsimp?)
   apply (simp add: conv_top_strict.top_strict_axioms top_strict.top_strict)
  apply (intro conjI)
  apply (clarsimp simp: less_eq_downset_def sup_downset_def, transfer, clarsimp)
  apply (metis)
  apply (clarsimp simp: less_eq_downset_def sup_downset_def, transfer, clarsimp)
  apply (blast)
  done

sublocale down_seq_distrib_right: seq_distrib convolute dnil
  apply (standard; transfer; clarsimp)
   apply (safe; clarsimp simp: in_down_iff)
   apply (meson aborting bot_annihilate_seq flip.mono_f order_trans)
  by (meson bot_idemp in_mono in_omega order_refl order_trans)



sublocale conv_seq_distrib: seq_nondet_distrib convolute dnil
  apply standard
  apply (clarsimp simp: sup_downset_def)
  apply (transfer, clarsimp simp: down_sup_distrib down_union_distrib)
  apply (safe; clarsimp simp: in_down_iff)
  by blast+

sublocale conv_seq_Distrib: seq_Nondet_distrib convolute dnil
  apply standard
  apply (transfer, clarsimp simp: down_sup_distrib down_union_distrib)
  apply (safe; clarsimp simp: in_down_iff)
     apply blast
  apply (metis in_mono in_omega)
   apply (meson in_downsetI)
  by (meson bot_idemp in_mono in_omega order_refl order_trans)


end


locale test_seq = seq_elem + 
  assumes test_nil:   "range test = (range first - \<Omega>)" and
          test_atom:  "\<And>x t. x \<le> test t \<Longrightarrow> x \<le> bottom x \<or>  x \<ge> test t" and
          test_le:    "\<And>(x) y. test x \<le> test y \<Longrightarrow> x = y" and
          first_le: "x \<le> y \<Longrightarrow> first x \<le> first y" and
          last_first_seq: "last x \<ge> first y \<Longrightarrow> last y \<le> last (x ; y)  "

begin


lemma test_is_first: "\<exists>c. first c = test t" 
  by (metis DiffD1 image_iff rangeI test_nil)


lemma test_is_last: "\<exists>c. last c = test t" 
  by (metis first_last image_iff rangeI test_is_first)

lemma first_le_test_iff: "(first a) \<le> test t \<longleftrightarrow> a \<le> (test t) ; a "
  by (rule flip.unit_of_unit)

lemma first_test_last_test_iff: "first (test t) \<le> test t \<longleftrightarrow> last (test t) \<le> test t"
  apply (safe)
  defer
   apply (meson first_le_test_iff flip.mono_f last_unit order_refl order_trans)
  oops
  sledgehammer
  oops
  by (simp add: flip.first_test)

lemma testE: "(\<And>c. first c = test t \<Longrightarrow> P (first c)) \<Longrightarrow> P (test t)"
  by (insert test_is_first[where t=t], clarsimp)


lemma testE': "(\<And>c. last c = test t \<Longrightarrow> P (last c)) \<Longrightarrow> P (test t)"
  by (insert test_is_last[where t=t], clarsimp)

lemma test_seq_test: "test t \<le> test t ; test t" 
  apply (subst flip.unit_of_unit[symmetric])
  by (simp add: flip.first_test)

  

lemma first_test: "x \<le> test t; y \<Longrightarrow> first x \<le> test t" 
  apply (frule first_le)
  apply (rule order_trans, assumption)
  apply (subst  first_le_test_iff)
  by (meson assoc' dual_order.trans mono_f order_refl test_seq_test)


(* lemma insert_bot_nonempty: "S \<noteq> {} \<Longrightarrow> insert \<bottom> (\<Down> S) = \<Down> (S :: 'a :: preorder_bot set)"
  oops
  apply (intro set_eqI iffI; clarsimp simp: downset_set_def')
  apply (subgoal_tac "\<exists>x. x \<in> S", clarsimp)
  by blast
 *)
  
lemma first_test_seq: "first (test t; y) \<le> test t"
  using first_test by blast

lift_definition dtest :: "'b set \<Rightarrow> 'a downset"  is "\<lambda>S. \<Down>(test ` S) \<union> \<Omega>"
  apply (clarsimp)
  by (clarsimp simp: down_sup_distrib down_union_distrib)



lemma set_eqD1: "x \<in> S \<Longrightarrow> S = S' \<Longrightarrow> x \<in> S'"
  by (blast)

lemma no_bot_test: "bottom x \<notin> range test "
  using test_nil by auto

sublocale conv_test_pre: test_sequential_pre convolute dtest
  apply (standard)                    
  apply (transfer)
       apply (clarsimp simp: Sup_downset_def down_sup_distrib)
  apply (simp add: image_Union)
       apply (intro set_eqI iffI; clarsimp?)
        apply (clarsimp simp: down_image_iff down_sup_distrib)
  apply (clarsimp simp: down_image_iff down_sup_distrib)
       apply (blast)
      apply (rule injI) 
      apply (transfer)
      apply (intro set_eqI; clarsimp)
  apply (rule iffI)
       apply (drule_tac x="test xa" in set_eqD1[rotated])
        apply (clarsimp simp: down_image_iff in_down_iff)
  apply (rule_tac x=xa in bexI)
         apply (meson UnCI down_image_iff dual_order.refl)
        apply (clarsimp simp: in_Down_iff)
  apply (clarsimp)
       apply (elim disjE; clarsimp?)
        apply (clarsimp simp: down_image_iff in_Down_iff)

  using test_le apply blast
  apply (metis DiffD2 in_omega rangeI test_nil)
  apply (drule sym)
       apply (drule_tac x="test xa" in set_eqD1[rotated])
  apply (simp add: test_nil)
        apply (meson UnCI down_image_iff dual_order.refl)
  apply (clarsimp)
       apply (elim disjE; clarsimp?)
  apply (clarsimp simp: down_image_iff)
  using test_le apply blast
  apply (metis DiffD2 in_omega rangeI test_nil)

           apply (clarsimp simp: sup_downset_def, transfer)
     apply (simp add: down_union_distrib image_Un)
     apply (clarsimp simp: inf_downset_def, transfer, clarsimp)

     apply (safe; clarsimp?)
          apply (clarsimp simp: inf_downset_def, transfer, clarsimp)
     apply (safe; clarsimp?)
      apply (clarsimp simp: down_image_iff in_down_iff)
      apply (metis)
      apply (clarsimp simp: down_image_iff in_down_iff)
     apply (metis)
    apply (clarsimp simp: down_image_iff in_down_iff) 

  apply (metis IntI dual_order.trans test_atom test_le)
         apply (transfer, clarsimp)
        apply (clarsimp simp: less_eq_downset_def, transfer, intro iffI; clarsimp simp: down_image_iff)
   apply blast
  apply (clarsimp simp: subset_iff down_image_iff)
  apply (erule_tac x="test x" in allE)
  by (metis DiffD2 in_omega order_refl rangeI test_le test_nil)
  

lemma nil_dnil: "conv_test_pre.nil= dnil" 
  apply (clarsimp simp: conv_test_pre.nil_def, rule antisym; clarsimp simp: less_eq_downset_def dnil_def sup_downset_def)
   apply (transfer)
   apply (subst test_nil)
   apply (clarsimp)
   apply (intro conjI; clarsimp?)
    apply (metis Diff_subset down_image_iff iso_tuple_UNIV_I subset_image_iff)
  apply (meson UNIV_I down_image_iff flip.bot_le_unit_bot order_trans)
  apply (transfer; clarsimp)
  apply (clarsimp simp: downset_set_def')
  by (metis (mono_tags, lifting) Diff_iff down_image_iff downset_set_def in_omega mem_Collect_eq order_trans range_eqI test_nil)

lemma test_inf: "test ` p \<inter> test ` q = test ` (p \<inter> q)"
  apply (safe; clarsimp)
  apply (clarsimp simp: image_iff)
  by (metis Int_iff dual_order.refl test_le)

lemma test_le': "test x ; y \<le> y \<or> test x ; y \<le> bottom (test x)"
  apply (clarsimp)
  by (smt (verit, del_insts) down_last flip.down_unit flip.unit_of_apply mono_f order_refl order_trans test_is_last)

lemma le_test: "y ; test x \<le> y"
  by (metis down_last test_is_last)

lemma first_test_test: "first (test t) \<le> test t" 
  by (simp add: first_le_test_iff test_seq_test)

lemma first_test_test': "first (test t) \<ge> test t" 
  using flip.unit_of_apply le_test order_trans by blast

(* lemma last_unit: "x ; last x \<ge> x"
  using unit_of_apply by blast *)

lemma rewrite_sup_helper: "mono_on UNIV f \<Longrightarrow> (\<Union>a\<in>\<Down>S. \<Union>b\<in>S'. \<down> (f a b)) = (\<Union>a\<in>S. \<Union>b\<in>S'. \<down> (f a b)) "
  apply (safe; clarsimp simp: in_down_iff)
   apply (smt (verit) downset_set_def dual_order.trans le_fun_def mem_Collect_eq monotoneD)
  apply (rule_tac x=a in bexI)
   apply (smt (verit) downset_set_def dual_order.trans le_fun_def mem_Collect_eq monotoneD)
  apply (clarsimp simp: downset_set_def)
  by (fastforce )

(* lemma nonempty_bot_union: "S \<noteq> {} \<Longrightarrow> \<Down> (S) \<union> \<Down> {\<bottom>} = \<Down>(S :: 'a :: preorder_bot set)"
  by (metis Un_empty_right Un_insert_right down_down
            down_union_distrib test_seq.insert_bot_nonempty
            test_seq_axioms)


lemma nonempty_bot_union': "S \<noteq> {} \<Longrightarrow> \<Down> (S) \<union> \<down>\<bottom> = \<Down>(S :: 'a :: preorder_bot set)" 
  apply (safe; clarsimp simp: in_down_iff)
  apply (rule in_downsetI, clarsimp)
  apply (rule_tac x=x in bexI)
  using order_trans preorder_bot_class.bot_least apply blast
  using downset_set_def by blast *)

sublocale conv_test: test_sequential convolute dtest
  apply (standard)
  using left_neutral nil_dnil  apply presburger
  using right_neutral nil_dnil apply presburger
  using down_seq_distrib_right.Nondet_seq_distrib apply presburger
  using downset_seq_distrib_left.seq_nondet_distrib_weak apply presburger
   apply (simp add: conv_seq_distrib.seq_nondet_distrib) 
  apply (rule antisym)
   defer
   apply (simp add: down_seq_distrib_right.seq_mono)
  apply (clarsimp simp: inf_downset_def less_eq_downset_def, transfer)
  apply (case_tac "p = {}", clarsimp)
   apply (clarsimp simp: down_sup_distrib down_union_distrib in_down_iff test_inf Bex_def down_image_iff) 
  apply (elim disjE; clarsimp)
  
    apply (metis bot_annihilate_seq bot_idemp in_mono in_omega mono_f order_refl order_trans)
  apply (metis (no_types, opaque_lifting) IntD2 bot_annihilate_seq bot_idemp dual_order.trans in_omega inf.orderE mono_f order_eq_refl)

  apply (case_tac "q = {}", clarsimp)

   apply (clarsimp simp: down_sup_distrib down_union_distrib in_down_iff test_inf Bex_def down_image_iff) 
    apply (metis bot_annihilate_seq bot_idemp in_mono in_omega mono_f order_refl order_trans)

   apply (meson aborting bot_annihilate_seq dual_order.trans flip.mono_f preorder_bot_class.bot_least)
  apply (simp add: rewrite_sup_helper flip.mono_f le_fun_def monotone_onI)
  apply (clarsimp simp: down_sup_distrib down_union_distrib in_down_iff test_inf Bex_def down_image_iff) 
  apply (elim disjE; clarsimp?)
  apply (metis IntD2 first_test flip.unit_of_apply in_Down_iff in_omega inf.orderE test_le')

    apply (metis bot_annihilate_seq bot_idemp in_mono in_omega mono_f order_refl order_trans)
   apply (metis (mono_tags, opaque_lifting) bot_annihilate_seq bot_idemp dual_order.trans flip.mono_f in_mono in_omega order_refl)
  by (metis (mono_tags, opaque_lifting) bot_annihilate_seq bot_idemp dual_order.trans in_mono in_omega mono_f order_refl)
  
sublocale conv_assert: assertions convolute dtest ..  


lemma down_bot_seq_bot[simp]: " (\<down> (bottom x ; y)) = \<down>(bottom x)"
  apply (safe; clarsimp simp: in_down_iff)
  using bot_strict.bot_annihilate_seq bot_strict_axioms dual_order.trans apply blast
  by (meson bot_annihilate_seq dual_order.refl preorder_bot_class.bot_least refine_trans)


lemma mono_seq_down:"(\<Union>x\<in>\<down> (a). (\<Union>x\<in>\<down> ((seq :: 'a \<Rightarrow> 'a \<Rightarrow> 'a) b x). f a b x)) = (\<Union>x\<in>\<down> (seq b a). f a b x)"
  apply (safe; clarsimp)
  apply (meson dual_order.trans order_refl in_down_iff mono_f)
  by (meson order_refl in_down_iff)


lemma mono_seq_down':"(\<Union>x\<in>\<down> (a). (\<Union>x\<in>\<down> ((seq :: 'a \<Rightarrow> 'a \<Rightarrow> 'a) x b). f a b x)) = (\<Union>x\<in>\<down> (seq a b). f a b x)"
  apply (safe; clarsimp)
   apply (meson dual_order.trans order_refl in_down_iff mono_f)
  using in_down_iff by blast

lemma sup_down_sup:"(\<Union>x\<in>\<down> (c). \<Union>y\<in>x'. \<down> (x ; y)) = (\<Union>y\<in>x'. \<down>(c ; y))"
  apply (safe; clarsimp simp: in_down_iff Bex_def)
   apply (meson dual_order.trans order_refl mono_f)
  by blast
  

end

end