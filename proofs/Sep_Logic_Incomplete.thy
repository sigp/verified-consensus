theory Sep_Logic_Incomplete
  imports Hoare_VCG ProcessEpoch_O
begin


lemma "valid_lens ref \<Longrightarrow> valid_lens l \<Longrightarrow>set (lens_ocomp l ref) s (get (lens_ocomp l ref) s) = s"
  apply (clarsimp simp: lens_ocomp_def)
  apply (case_tac "get ref s"; clarsimp)
   apply (metis set_get_def valid_lens_def)
  apply (metis set_get_def valid_lens_def)
  done

lemma valid_lens_ocomp: "valid_lens ref \<Longrightarrow> valid_lens l \<Longrightarrow> valid_lens (lens_ocomp l ref)" sorry


definition "lens_pset_fix l ref v \<equiv> Abs_p_set (Pair ({f. (\<exists>v. (\<lambda>s. case (get (lens_ocomp l ref) s) of (Some x) \<Rightarrow> (set (lens_ocomp l ref) (set ref s (Some v))) (Some x) |
                                                                    None \<Rightarrow> set ref s (Some v) )  = f)  } \<union> {id})
                                              (\<lambda>s. case (get (lens_ocomp l ref) s) of (Some x) \<Rightarrow> (set (lens_ocomp l ref) (set ref s (Some v))) (Some x) |
                                                                    None \<Rightarrow> set ref s (Some v) ))"

lemma set_of_lens_pset_fix: "set_of (lens_pset_fix l ref v) = {f. (\<exists>v. (\<lambda>s. case (get (lens_ocomp l ref) s) of (Some x) \<Rightarrow> (set (lens_ocomp l ref) (set ref s (Some v))) (Some x) |
                                                                    None \<Rightarrow> set ref s (Some v) )  = f)  } \<union> {id} "
  apply (clarsimp simp: lens_pset_fix_def set_of_def)
  apply (subst Abs_p_set_inverse)
   apply (simp)
   apply (rule disjI2)
   apply (blast)
  apply (clarsimp)
  done

lemma point_of_lens_pset_fix: "point_of (lens_pset_fix l ref v) = (\<lambda>s. case (get (lens_ocomp l ref) s) of (Some x) \<Rightarrow> (set (lens_ocomp l ref) (set ref s (Some v))) (Some x) |
                                                                    None \<Rightarrow> set ref s (Some v) ) "
  apply (clarsimp simp: lens_pset_fix_def point_of_def)
  apply (subst Abs_p_set_inverse)
   apply (clarsimp)
   apply (blast)
  apply (clarsimp)
  done

lemma valid_get_set_simp[simp]: "valid_lens ref \<Longrightarrow> get ref (lens.set ref x v) = v"
  by (simp add: get_set_def valid_lens_def)


lemma valid_set_set_simp[simp]: "valid_lens ref \<Longrightarrow> set ref (lens.set ref x v) v' = set ref x v'"
  by (simp add: set_set_def valid_lens_def)

definition "lens_pset_option l v  = Abs_p_set (Pair ({f. (\<exists>v. (\<lambda>s. set l s (Some v)) = f)} \<union> {id}) (\<lambda>s. set l s (Some v)))"



lemma set_of_lens_pset_option: "set_of (lens_pset_option l v) = {f. (\<exists>v. (\<lambda>s. set l s (Some v)) = f)} \<union> {id} "
  apply (clarsimp simp: lens_pset_option_def set_of_def)
  apply (subst Abs_p_set_inverse)
   apply (clarsimp)
   apply (blast)
  apply (clarsimp)
  done

lemma point_of_lens_pset_option: "point_of (lens_pset_option l v) = (\<lambda>s. set l s (Some v)) "
  apply (clarsimp simp: lens_pset_option_def point_of_def)
  apply (subst Abs_p_set_inverse)
   apply (clarsimp)
   apply (blast)
  apply (clarsimp)
  done

lemma split_maps_to_lens:  "(ref \<mapsto>\<^sub>l v) s \<Longrightarrow> valid_lens l \<Longrightarrow>
                            (lens_ocomp l ref \<mapsto>\<^sub>l (get l v) \<and>* (ALLS x. lcomp l ref \<mapsto>\<^sub>l x \<longrightarrow>* ref \<mapsto>\<^sub>l (set l v x))) s"
  apply (clarsimp simp: sep_conj_def maps_to_def)
  apply (intro conjI)
   apply (simp add: valid_lens_ocomp)
  apply (subgoal_tac "valid_lens (lcomp l ref)")
   apply (rule_tac x="lens_pset_option (lens_ocomp l ref) (get l v)" in exI)
   apply (rule_tac x="lens_pset_fix l ref v" in exI)
   apply (intro conjI)
       apply (clarsimp simp: sep_disj_p_set_def)
       apply (clarsimp simp: disj_cylindric_set_def)
       apply (clarsimp simp: set_of_lens_pset_option set_of_lens_pset_fix)
       apply (elim disjE; clarsimp)
       apply (intro ext; clarsimp split: option.splits)
       apply (intro conjI impI; clarsimp?)
        apply (clarsimp simp: lens_ocomp_def)
       apply (clarsimp simp: lens_ocomp_def)
      apply (rule p_set_eqI)
       apply (clarsimp simp: set_of_plus_domain_iff)
       apply (intro set_eqI iffI; clarsimp?)
        apply (elim disjE; clarsimp)
  apply (clarsimp simp: Bex_def)
       apply (clarsimp simp: set_of_lens_pset_option set_of_lens_pset_fix)
         apply (rule_tac x=id in exI; clarsimp)
        apply (case_tac va; clarsimp)
         apply (rule_tac x="(\<lambda>s. set (lcomp l ref) s None)" in bexI)
          apply (rule_tac x=id in bexI; clarsimp?)
          apply (intro ext; clarsimp simp: lens_ocomp_def)
       apply (clarsimp simp: set_of_lens_pset_option set_of_lens_pset_fix)
  sorry

lemma maps_to_is_valid:"(maps_to l v \<and>* R) s \<Longrightarrow> valid (l) (Some v)"
  apply (clarsimp simp: sep_conj_def maps_to_def )
  sorry


lemma valid_validator_some_simp[simp]: 
"valid validators (Some xs) =  (let ys = Invariants.var_list_inner xs in sum_list (map (unat o Validator.effective_balance_f) ys) < 2^(64) \<and> distinct ys \<and> length ys < 2^64 )"
  apply (clarsimp simp: validators_def lens_ocomp_def valid_def first_def lens_comp_def split: lens.splits)
  sorry


lemma split_validator:  "(vref \<mapsto>\<^sub>l v) s \<Longrightarrow> 
                            (lens_ocomp exit_epoch vref \<mapsto>\<^sub>l (get exit_epoch v) \<and>* lens_ocomp withdrawable_epoch vref \<mapsto>\<^sub>l (get withdrawable_epoch v) \<and>* lens_ocomp activation_epoch vref \<mapsto>\<^sub>l (get activation_epoch v) \<and>*
                            (ALLS x y z. lens_ocomp exit_epoch vref \<mapsto>\<^sub>l x \<longrightarrow>* lens_ocomp withdrawable_epoch vref \<mapsto>\<^sub>l y  \<longrightarrow>* lens_ocomp activation_epoch vref \<mapsto>\<^sub>l z \<longrightarrow>* 
                                vref \<mapsto>\<^sub>l v\<lparr>exit_epoch_f := x, withdrawable_epoch_f := y, activation_epoch_f := z\<rparr>)) s" sorry


lemma slashings_wf: "(slashings \<mapsto>\<^sub>l ss \<and>* R) s \<Longrightarrow> 
sum_list (map unat (vector_inner ss)) \<le> 2 ^ 64 - 1 \<and> 
PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX = sum_list (vector_inner ss) *
PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX div sum_list (vector_inner ss)"
  sorry

lemma val_length_wf:  "(validators \<mapsto>\<^sub>l vs \<and>* R) s \<Longrightarrow> length (var_list_inner vs) \<le> 2 ^ 64 - 1"
  sorry

context hoare_logic begin
lemma ref_varlist_split: "(ref \<mapsto>\<^sub>l VariableList (a # x)) s \<Longrightarrow> (lens_oocomp (v_list_lens 0) ref \<mapsto>\<^sub>l a \<and>* lens_ocomp (offset 1) ref \<mapsto>\<^sub>l VariableList x) s" sorry


lemma is_split: "(inactivity_scores \<mapsto>\<^sub>l is) h \<Longrightarrow> (inactivity_scores \<mapsto>\<^sub>l VariableList (map (unsafe_var_list_index is o word_of_nat) [0..<(length (var_list_inner is))])) h" sorry


lemma restore_variablelist: "foldr (\<and>*) (map (\<lambda>x. lens_oocomp (v_list_lens (word_of_nat x)) ll \<mapsto>\<^sub>l f x) xs) sep_empty = 
       (ll \<mapsto>\<^sub>l VariableList (map f xs)) "
  sorry

lemma restore_variablelist': "foldr (\<and>*) (map (\<lambda>x. lcomp (v_list_lens (fst x)) ll \<mapsto>\<^sub>l f x) (enumerate xs)) sep_empty = 
       (ll \<mapsto>\<^sub>l VariableList (map f (enumerate xs))) "
  sorry

lemma split_var_list: 
  "(ls \<mapsto>\<^sub>l vs \<and>* R) s \<Longrightarrow> 
         (lens_oocomp (v_list_lens n) ls \<mapsto>\<^sub>l (unsafe_var_list_index vs n) \<and>* 
           ((ALLS x. (lens_oocomp (v_list_lens n) ls \<mapsto>\<^sub>l x) \<longrightarrow>* 
                     ls \<mapsto>\<^sub>l VariableList (list_update (var_list_inner vs) (unat n) x))) \<and>* R) s " sorry



definition 
 "index_var_list vs n \<equiv> unsafe_var_list_index vs (word_of_nat n) " 


definition index_var_list_lens_comp :: "('c, 'd VariableList option) lens \<Rightarrow> nat \<Rightarrow> ('c, 'd option) lens" where
 "index_var_list_lens_comp vs n \<equiv> lcomp (v_list_lens (word_of_nat n) ) vs" 


notation index_var_list ("_[_]!")

notation index_var_list_lens_comp ("_[_]\<^sub>l")

lemma slice_vl: "vl = VariableList (map id (var_list_inner vl))" 
  by (cases vl; clarsimp simp: var_list_inner_def)

lemma slice_vl': "vl = VariableList (map snd (enumerate (var_list_inner vl)))" 
  by (cases vl; clarsimp simp: enumerate_def var_list_inner_def)

definition "update_var_list_by domain f vs \<equiv> VariableList (map (\<lambda>x. if x \<in> domain then f x else (vs[x]!)) [0..<length (var_list_inner vs)])"

lemma split_vars_by_list: 
       "(l \<mapsto>\<^sub>l vars) s \<Longrightarrow> (\<And>x. x \<in> list.set xs \<Longrightarrow> unsafe_var_list_index vars x = f x) \<Longrightarrow>
        (foldr (\<and>*) (map (\<lambda>x. lens_oocomp (v_list_lens x) l \<mapsto>\<^sub>l f x) xs) \<box> \<and>*
        (ALLS g. (foldr (\<and>*) (map (\<lambda>x. lens_oocomp (v_list_lens x) l \<mapsto>\<^sub>l g x) xs) \<box>) \<longrightarrow>* 
                 (l \<mapsto>\<^sub>l update_var_list_by (unat ` list.set xs) (g o word_of_nat) vars ))) s"
  sorry

definition "slash_balance total_balance curr_epoch adjusted_total_slashing_balance b v \<equiv> 
        if slashed_f b \<and> Epoch (epoch_to_u64 curr_epoch + EPOCHS_PER_SLASHINGS_VECTOR config div 2) = withdrawable_epoch_f b then
        v - Validator.effective_balance_f b div (EFFECTIVE_BALANCE_INCREMENT config * adjusted_total_slashing_balance) div (total_balance * EFFECTIVE_BALANCE_INCREMENT config) else v"

lemma [simp]: 
      "length (var_list_inner bls) = length (var_list_inner vs) \<Longrightarrow> 
       foldr (\<and>*) (map (\<lambda>x. lens_oocomp (v_list_lens (fst x)) balances \<mapsto>\<^sub>l unsafe_var_list_index bls (fst x)) (local.enumerate (local.var_list_inner vs))) \<box> = 
       (balances \<mapsto>\<^sub>l bls) " sorry

lemma [simp]: 
      "
       foldr (\<and>*) (map (\<lambda>x. lens_oocomp (v_list_lens (fst x)) validators \<mapsto>\<^sub>l unsafe_var_list_index vs (fst x)) (local.enumerate (local.var_list_inner vs))) \<box> = 
       (validators \<mapsto>\<^sub>l vs) " sorry

lemma another_helper: "foldr (\<and>*) (map (\<lambda>x. lens_oocomp (v_list_lens (fst x)) l \<mapsto>\<^sub>l f (fst x) (snd x)) (local.enumerate (local.var_list_inner vs))) \<box> =
        (l \<mapsto>\<^sub>l VariableList (map (\<lambda>x. f (word_of_nat x) (unsafe_var_list_index vs (word_of_nat x))) [0..<length (var_list_inner vs)])) " sorry

lemma slash_balance_restore: 
     "foldr (\<and>*) (map (\<lambda>x. lcomp (v_list_lens (fst x)) balances \<mapsto>\<^sub>l slash_balance total_balance curr_epoch adjusted_total_slashing_balance 
                                                                     (unsafe_var_list_index vs (fst x)) (unsafe_var_list_index bls (fst x))) (local.enumerate (local.var_list_inner vs))) \<box> = 
      (balances \<mapsto>\<^sub>l VariableList (map (\<lambda>x. slash_balance total_balance curr_epoch adjusted_total_slashing_balance (vs[x]!) (bls[x]!)) [0..< length (local.var_list_inner vs)]))"
  sorry 
end

end

