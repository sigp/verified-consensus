theory Conj_Obs
imports Ordered_Semigroups
begin

locale conj =
  fixes conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "\<iinter>" 80)
                                                                               
locale conj_elem = conj   + sync_semigroup conj + ab_ordered_semigroup conj + top_semigroup conj +
  assumes covering: "x \<le> conj a b \<Longrightarrow> x \<le> a \<or> x \<le> b \<or> x \<in> \<Omega>"
  assumes idemp: "x \<le> conj x x"
begin

sublocale top_semigroup conj ..

lemma conv_idemp: "convolute a a = a"
 apply (rule antisym)
   apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: down_sup_distrib in_down_iff)
  using covering in_downsetI apply blast
  apply (clarsimp simp: less_eq_downset_def, transfer, clarsimp simp: down_sup_distrib in_down_iff) 
  using idemp by blast

sublocale conj_conv: conjunction convolute dunit
  apply (standard)   
  using conv_sync.sync_commute conv_top_strict.top_strict apply presburger
   apply (rule conv_idemp)
  by (fastforce)

sublocale conj_distrib convolute dunit ..

lemma mono_down:"(\<Union>x\<in>\<down> (a). (\<Union>x\<in>\<down> ((conj :: 'a \<Rightarrow> 'a \<Rightarrow> 'a) b x). f a b x)) = (\<Union>x\<in>\<down> (conj b a). f a b x)"
  apply (safe; clarsimp)
   apply (meson mono_f dual_order.trans order_refl in_down_iff)
  by (meson order_refl in_down_iff)

lemma mono_down':"(\<Union>x\<in>\<down> (a). (\<Union>x\<in>\<down> ((conj :: 'a \<Rightarrow> 'a \<Rightarrow> 'a) x b). f a b x)) = (\<Union>x\<in>\<down> (conj a b). f a b x)"
  apply (safe; clarsimp)
   apply (meson mono_f dual_order.trans order_refl in_down_iff)
  by (meson order_refl in_down_iff)


end

end