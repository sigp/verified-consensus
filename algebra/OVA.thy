theory OVA
imports Ordered_Semigroups
begin

locale ova = ordered_semigroup +
  fixes d :: "'a \<Rightarrow> ('b :: complete_lattice)" and phi :: "('b \<times> 'b) \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes labeling: "\<And>a b. d (f a b) = d a \<squnion> d b" and
          d_antitone: "\<And>a b. a \<le> b \<Longrightarrow> d b \<le> d a" and
          phi_functor: "\<And>a b c x. c \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a \<le> d x \<Longrightarrow> phi (b, c) (phi (a, b) x) \<le> phi (a, c) x" and
          phi_functor': "c \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a \<le> d x \<Longrightarrow> phi (a, c) x \<le> phi (b, c) (phi (a, b) x)  " and
          phi_id: "phi (d x, d x) x \<le> x" and
          phi_id': "x \<le> phi (d x, d x) x" and
          phi_antitone: "A \<le> d y \<Longrightarrow> x \<le> y \<Longrightarrow> phi (d x, A) x \<le> phi (d y, A) y" and
          phi_monotone: "B \<le> A \<Longrightarrow> A \<le> d x \<Longrightarrow> phi (d x, A) x \<le> phi (d x, B) x"



begin

definition "restrict b a = phi (d b, a) b"


lemma restrict_id: "restrict x (d x) \<le> x" 
  unfolding restrict_def
  by (rule phi_id)

lemma restrict_id': "x \<le> restrict x (d x) " 
  unfolding restrict_def
  by (rule phi_id')


lemma d_restrict[simp]: " A \<le> d x \<Longrightarrow> d (restrict x A) = A"
  apply (clarsimp simp: restrict_def)
  sorry


lemma d_phi[simp]: " A \<le> d x \<Longrightarrow> d (phi (d x, A) x) = A"
  apply (clarsimp simp: restrict_def)
  sorry


lemma restrict_functor: "B \<le> A \<Longrightarrow> A \<le> d x \<Longrightarrow> restrict (restrict x A) B \<le> restrict x B"
  apply (clarsimp simp: restrict_def)
  apply (rule order_trans)
  thm phi_functor[where a=A and b=B]
   apply (rule )
  by (meson order_refl phi_functor)
  apply (rule phi_antitone)

lemma restrict_monotone: "A \<le> d y \<Longrightarrow> x \<le> y \<Longrightarrow> restrict x A \<le> restrict y A"
  apply (clarsimp simp: restrict_def) sorry

lemma restrict_antitone': "B \<le> A \<Longrightarrow> A \<le> d x \<Longrightarrow> restrict x A \<le> restrict x B"
  apply (clarsimp simp: restrict_def)
  sorry

lemma grothendieckD: "x \<le> y \<Longrightarrow> d y \<le> d x \<and> restrict x (d y) \<le> y"
  apply (intro conjI)
   apply (erule d_antitone)
  apply (rule order_trans[rotated], rule restrict_id, rule restrict_monotone; clarsimp)
  done

lemma grothendieckI: "d y \<le> d x \<Longrightarrow> restrict x (d y) \<le> y \<Longrightarrow> x \<le> y" 
  apply (rule order_trans)
   apply (rule restrict_id')
  apply (rule order_trans[rotated], assumption)
  by (rule restrict_antitone', assumption, rule order_refl)


lift_definition restrict_command :: "'b \<Rightarrow> 'a downset \<Rightarrow> 'a downset" is "\<lambda>d S. \<Squnion>x\<in>S. \<down>(restrict x d)"
  apply (clarsimp)
  apply (safe)
    apply (clarsimp simp: down_sup_distrib in_down_iff)+
   apply (blast)
  apply (blast)
  done


lift_definition domain :: "'a downset \<Rightarrow> 'b set" is "\<lambda>S. (d ` S)"
  done

lemma d_bot_top[simp]: "d \<bottom> = \<top>" sorry

lemma domain_bot: "domain \<bottom> = {\<top>}"
  apply (transfer, safe, clarsimp simp: in_down_iff)
   apply (drule grothendieckD, clarsimp simp: labeling)
   defer
   apply (clarsimp simp: in_down_iff image_iff)
  sorry



lemma "A \<in> domain (\<Squnion>S) \<Longrightarrow>   restrict_command A (\<Squnion>S) = \<Squnion>(restrict_command A ` S)"
  apply (case_tac "S = {}"; clarsimp?)
  apply (clarsimp simp: domain_bot)
   apply (transfer, clarsimp)
   apply (safe; clarsimp simp: in_down_iff)
  apply (drule grothendieckD, clarsimp)
    apply (clarsimp simp: restrict_def)
    apply (erule order_trans, clarsimp)
  apply (blast)
   apply (transfer, clarsimp)
   apply (safe; clarsimp simp: in_down_iff)
   apply (meson in_downsetI)
  by (meson in_downsetI)


lemma in_up_iff: "x \<in> \<up> y \<longleftrightarrow> y \<in> \<down>x  " 
  apply (safe; clarsimp simp: in_down_iff)
  by (clarsimp simp: upset_def upset_set_def eta_def)+ 

lemma in_Up_iff: "x \<in> \<Up>Y \<longleftrightarrow> (\<exists>y\<in>Y. y \<in> \<down>x)"

  apply (safe; clarsimp simp: in_down_iff)
   apply (clarsimp simp: upset_def upset_set_def eta_def)+ 
  apply (blast)
  done

lemma "domain S = domain \<top>"
  apply (transfer, safe; clarsimp simp: in_Down_iff)
  oops
   apply (blast)
  apply (rule_tac x="\<bottom>" in bexI; clarsimp?)
  apply (erule order_trans)
  using d_antitone preorder_bot_class.bot_least by blast
  oops

lemma restrict_increasing: "A \<le> d b \<Longrightarrow> b \<le> restrict b A"
  by (rule grothendieckI; clarsimp)

lift_definition cyl :: "'b \<Rightarrow> 'a downset \<Rightarrow> 'a downset" is "\<lambda>b S. \<Down>(\<Squnion>x\<in>S. {y. d y = b \<and> x \<ge> restrict y (d x) }) \<union> \<down>\<bottom>"
  apply (clarsimp)
  by (simp add: down_union_distrib)

lemma domain_means_bot_restrict: "d ` y = {A} \<Longrightarrow> \<Down>y = y \<Longrightarrow> restrict \<bottom> A \<in> y"
  apply (case_tac "y = {}"; clarsimp)
  apply (subgoal_tac "\<exists>x\<in>y. True", clarsimp)
  sorry

lemma galois: "domain x = {B} \<Longrightarrow> A \<le> B \<Longrightarrow> domain y = {A} \<Longrightarrow> restrict_command A x \<le> y \<longleftrightarrow> x \<le> cyl B y"
  apply (safe)
   apply (clarsimp simp: less_eq_downset_def)
   apply (transfer, clarsimp simp: in_Down_iff)
   apply (rule_tac x="restrict xa A" in bexI)
    apply (rule_tac x=xa in exI, clarsimp)
  apply (metis d_restrict insert_image order_refl singleton_insert_inj_eq)

   apply (erule_tac c=" restrict xa A" in subsetD, clarsimp simp: in_down_iff)
   apply (blast)
   apply (clarsimp simp: less_eq_downset_def)
  apply (transfer, clarsimp simp: in_Down_iff in_down_iff down_sup_distrib)
  apply (drule_tac c=xb in subsetD; clarsimp)
  apply (elim disjE; clarsimp simp: in_down_iff)
   defer
   apply (frule domain_means_bot_restrict, assumption)back
  
   apply (metis d_bot_top in_Down_iff order_top_class.top_greatest restrict_monotone)
  apply (clarsimp simp: in_Down_iff)
  by (metis SUP_upper2 Sup_empty Sup_insert antisym d_bot_top grothendieckD grothendieckI in_downsetI order_top_class.top_greatest sup_bot.right.right_neutral)
  oops
  by (metis imageI in_Down_iff phi_id restrict_def restrict_id' singletonD)

lemma cyl_mono: "domain c = {A}  \<Longrightarrow> domain D = {B} \<Longrightarrow> B \<le> A \<Longrightarrow> c \<le> D \<Longrightarrow>
 cyl A c \<le> cyl A D"
  apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp)
  apply (clarsimp simp: in_Down_iff in_down_iff)
  apply (rule_tac x=y in bexI)
   apply blast
  apply (erule_tac c=y in subsetD)
  apply (clarsimp)
  done

lemma cyl_idemp: "domain P = {A} \<Longrightarrow> cyl A P = P"
  apply (transfer)
  apply (safe; clarsimp simp: in_Down_iff in_down_iff)
    apply (metis imageI in_downsetI restrict_id' singleton_iff)
  using in_downsetI apply blast
  apply (rule_tac x=x in bexI; clarsimp?)
  apply (rule_tac x=x in exI, clarsimp)
  by (metis image_eqI restrict_id singletonD)

lemma conv_monotone:  "P \<le> Q \<Longrightarrow> A \<le> B \<Longrightarrow> convolute P A \<le> convolute Q B"
  apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: in_down_iff)
  apply (blast)
  done

lemma restrict_decreasing: "domain Q = {A} \<Longrightarrow> D \<le> A \<Longrightarrow> Q \<le> restrict_command D Q"
  apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: in_down_iff)
  by (metis ball_imageD restrict_increasing singletonD)

lemma "domain P = {A} \<Longrightarrow> domain Q = {B} \<Longrightarrow> restrict_command A (convolute P Q) = (convolute P (restrict_command (A \<sqinter> B) Q))"
  apply (rule antisym)
   apply (subst galois[where B="A \<squnion> B"])
      defer
      apply (clarsimp)
     defer
     apply (subst cyl_idemp[symmetric, where A="A \<squnion> B"]) back
      defer
      apply (rule cyl_mono[where B=A])
         prefer 4
  find_theorems  convolute
         apply (rule conv_monotone, rule order_refl)
         apply (rule restrict_decreasing, assumption, clarsimp)
        prefer 4
        apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: in_down_iff)
  apply (drule grothendieckD, clarsimp) back
  sledgehammer[isar_proofs]
 

  oops
  apply (transfer; safe; clarsimp simp: in_down_iff)
   apply (rule_tac x=a in bexI, rule_tac x=b in bexI)
     apply (rule_tac x="restrict b (A \<sqinter> B)" in bexI)
      apply (erule order_trans)
      apply (rule grothendieckI, clarsimp simp: labeling)
       apply (subst d_restrict)
        defer
        apply (clarsimp)
        apply (intro conjI)
         apply (metis empty_iff image_eqI insert_iff order_refl)
        apply (metis d_restrict grothendieckD imageI labeling preorder_bot_class.bot_least singletonD sup.order_iff)
  thm phi_functor
       apply (rule order_trans, rule restrict_functor)
         apply (metis SUP_upper2 Sup_empty Sup_insert d_bot_top order_top_class.top_greatest sup_bot.right.right_neutral)
        apply (smt (verit) doubleton_eq_iff insert_absorb2 insert_image order_eq_refl ova.grothendieckD ova.labeling ova_axioms sup_absorb1)
       apply (clarsimp simp: labeling)
       apply (subst d_restrict)
        apply (metis ball_imageD inf_le2 singletonD)
  apply (subgoal_tac "d a = A")
        apply (clarsimp)
        apply (rule order_trans[rotated])
  find_theorems f
         apply (rule mono_f, rule order_refl)
         apply (rule restrict_increasing)
         apply (metis ball_imageD inf_le2 singletonD)
  apply (rule order_trans)
  apply (metis)
  apply (rule grothendieckI)

  

lemma "domain (convolute P Q) = domain P \<squnion> domain Q"
  apply (transfer)
  apply (clarsimp)
  apply (rule antisym; clarsimp?)
   apply (clarsimp simp: in_up_iff in_down_iff image_iff in_Up_iff in_Down_iff) 
  sorry
  
   apply (clarsimp simp: Sup_le_iff in_down_iff)
   apply (drule grothendieckD, clarsimp simp: labeling)
  apply (rule_tac x=xa in 
   apply (rule_tac x=y in bexI, fastforce, clarsimp)
  apply (safe; clarsimp?) nitpick
   apply (clarsimp simp: in_up_iff in_down_iff image_iff in_Up_iff)
   apply (rule_tac x=y in bexI; clarsimp?)
   apply (rule_tac x=\<bottom> in bexI; clarsimp?)
  apply (rule_tac x="(y \<^bold>* \<bottom>)" in bexI; clarsimp?)
   apply (rule le_supI1)
   apply (subst le_Inf_iff; clarsimp)
   apply (rule INF_lower)
  apply (clarsimp simp: in_down_iff image_iff)
  oops
  thm SUP_upper2
   apply (rule_tac i=\<bottom> in SUP_upper2, clarsimp)
  using d_antitone preorder_bot_class.bot_least apply blast
  apply (meson SUP_upper2 grothendieckD le_supI1 preorder_bot_class.bot_least)
   apply (clarsimp simp: Sup_le_iff in_down_iff)
   apply (rule_tac i=\<bottom> in SUP_upper2, clarsimp)
    apply (blast)
  using d_antitone preorder_bot_class.bot_least apply blast

  find_theorems 
   apply (rule INF_lower2)
  apply (clarsimp simp: in_down_iff)
  thm le_Inf_iff
  apply (clarsimp simp: le_Inf_iff)

end

end