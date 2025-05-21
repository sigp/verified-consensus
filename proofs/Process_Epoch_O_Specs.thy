theory Process_Epoch_O_Specs
imports ProcessEpoch_O sqrt_proof Hoare_VCG Sep_Logic_Incomplete
begin


locale extended_hl_pre =  extended_vc  + hoare_logic +
  assumes churn_limit_quotient_config_nonempty[simp]: "CHURN_LIMIT_QUOTIENT config \<noteq> 0" 
  and effective_balance_safe[simp]:
 "MAX_EFFECTIVE_BALANCE \<le> MAX_EFFECTIVE_BALANCE + EFFECTIVE_BALANCE_INCREMENT config"

  and EBI_ge_zero[intro]: "EFFECTIVE_BALANCE_INCREMENT config > 0"
  and  SLOTS_PER_EPOCH_ATLEAST[simp]: "1 < SLOTS_PER_EPOCH config" 
  and  EPOCHS_PER_ETH1_VOTING_PERIOD_ATLEAST[simp]: "EPOCHS_PER_ETH1_VOTING_PERIOD config \<noteq> 0" 
  and  EBI_nonzero[simp]: "EFFECTIVE_BALANCE_INCREMENT config \<noteq> 0" 
  and  brf_ebi_times_bounded[simp]: 
      "EFFECTIVE_BALANCE_INCREMENT config * 
       BASE_REWARD_FACTOR config div EFFECTIVE_BALANCE_INCREMENT config = 
       BASE_REWARD_FACTOR config" 
  and EBI_multiple_of_HYSTERESIS_QUOTIENT: 
  "\<exists>n. HYSTERESIS_QUOTIENT * n div n = HYSTERESIS_QUOTIENT \<and> EFFECTIVE_BALANCE_INCREMENT config = HYSTERESIS_QUOTIENT * n" 
   and  ISB_not_zero[simp]:  "INACTIVITY_SCORE_BIAS config \<noteq> 0" 

   and brf_not_zero: "BASE_REWARD_FACTOR config \<noteq> 0" 

  and upward_threshold_safe: "((EFFECTIVE_BALANCE_INCREMENT config div HYSTERESIS_QUOTIENT) * HYSTERESIS_UPWARD_MULTIPLIER)
         div (EFFECTIVE_BALANCE_INCREMENT config div HYSTERESIS_QUOTIENT) = HYSTERESIS_UPWARD_MULTIPLIER"


begin

declare [[show_sorts=false]]
declare [[show_types=false]]

term free


lemma read_beacon_wp[wp]: "(\<And>x. x = v \<Longrightarrow> hoare_triple ( lift (P x)) (c x) (Q )) \<Longrightarrow> hoare_triple (lift (maps_to l v \<and>* (maps_to l v \<longrightarrow>*  (P v )))) (do {v <- read_beacon l ; c v}) (Q  )"
  apply (clarsimp simp: hoare_triple_def bindCont_def run_def read_beacon_def getState_def )
  apply (clarsimp simp: Sup_le_iff)
  apply (safe)
   apply (clarsimp simp: fail_def assert_galois_test)
   defer
   apply (clarsimp simp: fail_def assert_galois_test return_def)
   apply (case_tac "y = v"; clarsimp?)
    apply (subst seq_assoc[symmetric])
    apply (subst test_seq_test)
    apply (rule order_trans, rule seq_mono_left)
     apply (rule test.hom_mono[where p="Collect (lift (P v))"])
     apply (clarsimp)
  apply (sep_solve)
    apply (blast)
  apply (subst seq_assoc[symmetric])
   apply (subst test_seq_test)
 apply (rule order_trans, rule seq_mono_left)
    apply (rule test.hom_mono[where p="{}"])
    apply (clarsimp)
    defer
    apply (clarsimp)
  apply (subst seq_assoc[symmetric])
   apply (subst test_seq_test)
 apply (rule order_trans, rule seq_mono_left)
    apply (rule test.hom_mono[where p="{}"])
    apply (clarsimp)
    defer
    apply (clarsimp)
   apply (drule maps_to_get_wf, clarsimp)
  apply (drule maps_to_get_wf, clarsimp)
  done




lemma get_current_epoch_wp[wp]: "hoare_triple (lift (P (slot_to_epoch config v))) (f (slot_to_epoch config v)) Q \<Longrightarrow>
hoare_triple (lift (maps_to beacon_slots v \<and>* (maps_to beacon_slots v \<longrightarrow>* P (slot_to_epoch config v)))) (bindCont get_current_epoch f) Q"
  apply (clarsimp simp: get_current_epoch_def)
  apply (rule hoare_weaken_pre)
  apply (clarsimp simp: bindCont_assoc[symmetric] bindCont_return')
   apply (rule read_beacon_wp, fastforce)
  apply (rule order_refl)
  done

lemma valid_lens_withdrawable_epoch[simp]:"valid_lens withdrawable_epoch" 
  by (clarsimp simp: valid_lens_def withdrawable_epoch_def get_set_def set_get_def set_set_def)



lemma get_previous_epoch_wp':"(\<And>x. hoare_triple (lift (P x)) (f x) Q) \<Longrightarrow> hoare_triple (lift (maps_to beacon_slots v \<and>*
          (maps_to beacon_slots v \<longrightarrow>*
           (if slot_to_epoch config v = GENESIS_EPOCH then P GENESIS_EPOCH
            else (\<lambda>s. 1 \<le> epoch_to_u64 (slot_to_epoch config v) \<and>
                 (1 \<le> epoch_to_u64 (slot_to_epoch config v) \<longrightarrow> P (Epoch (epoch_to_u64 (slot_to_epoch config v) - 1)) s)))))) (bindCont get_previous_epoch f) Q"
  apply (simp only: get_previous_epoch_def, rule hoare_weaken_pre)
  apply (subst bindCont_assoc[symmetric])
   apply (rule get_current_epoch_wp)
  apply (rule if_wp)
    apply (rule return_triple', assumption)
  apply (simp add: epoch_unsigned_sub_def, wp)
  apply (rule order_refl)
  done



lemma previous_genesis[simp]: "previous_epoch GENESIS_EPOCH = GENESIS_EPOCH"
  by (clarsimp simp: previous_epoch_def)

lemma previous_is_self_simp[simp]: "previous_epoch e = e \<longleftrightarrow> e = GENESIS_EPOCH"
  apply (clarsimp simp: previous_epoch_def GENESIS_EPOCH_def) 
  by (metis diff_0_right diff_left_imp_eq epoch_to_u64.simps zero_neq_one)


lemma get_previous_epoch_wp[wp]:"hoare_triple (lift (P (previous_epoch (slot_to_epoch config v)))) (f (previous_epoch (slot_to_epoch config v))) Q \<Longrightarrow>
   hoare_triple (lift (maps_to beacon_slots v \<and>* (maps_to beacon_slots v \<longrightarrow>*
               P (previous_epoch (slot_to_epoch config v)) ))) (bindCont get_previous_epoch f) Q"
  apply (simp only: get_previous_epoch_def, rule hoare_weaken_pre)
   apply (wp)
    apply (clarsimp simp: bindCont_assoc[symmetric])
  apply (drule sym[where s="slot_to_epoch config v"], drule sym, clarsimp, assumption)
   apply (simp add: epoch_unsigned_sub_def, wp)
   apply (clarsimp simp: previous_epoch_def split: if_splits, assumption)
  apply (clarsimp)
  apply (sep_cancel)+
  apply (intro conjI impI allI; clarsimp)
     apply (sep_mp)
   apply (clarsimp simp: GENESIS_EPOCH_def)
   apply (clarsimp simp: slot_to_epoch_def)
  using lt1_neq0 apply blast
  apply (sep_mp)
   apply (clarsimp simp: previous_epoch_def split: if_splits)
  done




lemma get_active_validator_indices_wp[wp]:
  "hoare_triple (lift (P (active_validator_indices epoch v))) (f (active_validator_indices epoch v)) Q \<Longrightarrow> 
     hoare_triple (lift (maps_to validators v \<and>* (maps_to validators v \<longrightarrow>* P (active_validator_indices epoch v)))) (bindCont (get_active_validator_indices epoch) f) Q"
  apply (unfold get_active_validator_indices_def, rule hoare_weaken_pre)
  apply (clarsimp simp: liftM_def)
   apply (wp)
   apply (clarsimp simp: comp_def)
   apply (erule hoare_eqI')
  apply (clarsimp)
  apply (rule exI, sep_cancel)+
  apply (sep_cancel)+
  apply (sep_mp)
  apply (clarsimp)
  done

lemma if_refl: "(if (P = P) then Q else R) = Q"
  by (clarsimp)


lemma get_current_unslashed_participating_indices_wp[wp]:"  hoare_triple (lift (pre {x \<in> list.set (active_validator_indices (slot_to_epoch config current_slot) valids). has_flag (unsafe_var_list_index cep x) flag_index \<and> \<not> slashed_f (unsafe_var_list_index valids x)})) (f {x \<in> list.set (active_validator_indices (slot_to_epoch config current_slot) valids). has_flag (unsafe_var_list_index cep x) flag_index \<and> \<not> slashed_f (unsafe_var_list_index valids x)}) Q \<Longrightarrow>
 hoare_triple 
(lift (maps_to beacon_slots current_slot \<and>* maps_to current_epoch_participation cep \<and>* maps_to validators valids \<and>* 
((maps_to beacon_slots current_slot \<and>* maps_to current_epoch_participation cep \<and>* maps_to validators valids) \<longrightarrow>* pre ({x \<in> list.set (active_validator_indices (slot_to_epoch config current_slot) valids). has_flag (unsafe_var_list_index cep x) flag_index \<and> \<not> slashed_f (unsafe_var_list_index valids x)})) ))   (bindCont (get_unslashed_participating_indices flag_index (slot_to_epoch config current_slot)) f) Q"
  apply (unfold get_unslashed_participating_indices_def, rule hoare_weaken_pre)
   apply (simp only: bindCont_assoc[symmetric])
   apply (rule get_previous_epoch_wp)
   apply (rule get_current_epoch_wp)
   apply (rule assert_wp')
   apply (simp)
  apply (rule read_beacon_wp[where v=cep], simp)

   apply (clarsimp, wp, clarsimp)
  apply (assumption)
  apply (clarsimp)
  apply (sep_cancel)
  apply (sep_cancel)+
  apply (simp)
  apply (sep_mp)
  apply (clarsimp)
  done

lemma get_previous_unslashed_participating_indices_wp[wp]:" (\<And>x. hoare_triple (lift (pre {x \<in> list.set (active_validator_indices (previous_epoch (slot_to_epoch config current_slot)) valids). has_flag (unsafe_var_list_index pep x) flag_index \<and> \<not> slashed_f (unsafe_var_list_index valids x)})) (f {x \<in> list.set (active_validator_indices (previous_epoch (slot_to_epoch config current_slot)) valids). has_flag (unsafe_var_list_index pep x) flag_index \<and> \<not> slashed_f (unsafe_var_list_index valids x)}) Q) \<Longrightarrow> (slot_to_epoch config current_slot) \<noteq> GENESIS_EPOCH \<Longrightarrow> hoare_triple 
(lift (maps_to beacon_slots current_slot \<and>* maps_to previous_epoch_participation pep \<and>* maps_to current_epoch_participation cep \<and>* maps_to validators valids \<and>* 
((maps_to beacon_slots current_slot \<and>* maps_to previous_epoch_participation pep \<and>* maps_to current_epoch_participation cep \<and>* maps_to validators valids) \<longrightarrow>* pre ({x \<in> list.set (active_validator_indices (previous_epoch (slot_to_epoch config current_slot)) valids). has_flag (unsafe_var_list_index pep x) flag_index \<and> \<not> slashed_f (unsafe_var_list_index valids x)})) )) 
   (bindCont (get_unslashed_participating_indices flag_index (previous_epoch (slot_to_epoch config current_slot))) f) Q"
  apply (unfold get_unslashed_participating_indices_def, rule hoare_weaken_pre)
    apply (simp only: bindCont_assoc[symmetric])
   apply (rule get_previous_epoch_wp)
   apply (rule get_current_epoch_wp)
   apply (rule assert_wp')
   apply (simp)
  apply (rule read_beacon_wp[where v=pep], simp)
   apply (clarsimp, wp, clarsimp)
  apply (assumption)
  apply (clarsimp)
  apply (sep_cancel)
  apply (sep_cancel)+
  apply (simp)
  apply (sep_mp)
  apply (clarsimp)
  done




  
lemma unat_sum_list_simp:"sum_list (map unat xs) \<le> 2^64 - 1 \<Longrightarrow> unat (sum_list (xs :: u64 list)) = sum_list (map unat xs)"
  apply (induct xs; clarsimp)
  apply (unat_arith; clarsimp)
  done

lemma  safe_sum_distinct_wb: " (sum_list (map unat xs)) \<le> 2^64 - 1 \<Longrightarrow> safe_sum xs = return (sum_list xs)" 
  apply (induct xs; clarsimp simp: safe_sum_def)
  apply (subst foldrM_shift)
  apply (clarsimp)
  apply (clarsimp simp: word_unsigned_add_def Let_unfold, safe; (clarsimp simp: bindCont_return split: if_splits)?)
   apply (metis add.commute)
  apply (erule notE)
  apply (unat_arith; clarsimp)
  apply (clarsimp simp: unat_sum_list_simp)
  done



lemma sum_list_wp[wp]: "hoare_triple (lift (P (sum_list xs))) (f (sum_list xs)) Q \<Longrightarrow>
    hoare_triple (lift (\<lambda>s. (sum_list (map unat xs)) \<le> 2^64 - 1 \<and> ((sum_list (map unat xs)) \<le> 2^64 - 1 \<longrightarrow> P (sum_list xs) s))) (do {b <- safe_sum xs; f b}) Q"
  apply ( rule hoare_assert_stateI, clarsimp)
  apply (subst safe_sum_distinct_wb, clarsimp)
  apply (clarsimp)
  apply (rule hoare_weaken_pre, assumption)
  apply (clarsimp)
  done



  

lemma plus_one_helper_nat[elim!]:
  "x < n + (1 :: nat) \<Longrightarrow> x \<le> n"
  by (simp add: word_less_nat_alt word_le_nat_alt field_simps)


lemma count_list_remove1: "Suc n \<le> count_list ys a \<Longrightarrow> n \<le> count_list (remove1 a ys) a"
  apply (induct ys; clarsimp)
  by (metis Suc_eq_plus1 add.commute nat_add_left_cancel_le)


lemma count_ge_suc_in_set: "Suc n \<le> count_list ys a \<Longrightarrow> a \<in> list.set ys"
  apply (induct ys; clarsimp)
  using linorder_not_le by fastforce

lemma count_neq_remove1[simp]: "x \<noteq> a \<Longrightarrow> count_list (remove1 a ys) x = count_list ys x"
  by (induct ys; clarsimp)

lemma sum_list_map_leI:"(\<And>x. count_list ys x \<ge> count_list xs x) \<Longrightarrow> (\<Sum>a\<leftarrow>xs. (f a) :: nat) \<le> sum_list (map f ys)"
  apply (induct xs arbitrary: ys ; clarsimp)
  apply (atomize)
  apply (erule_tac x="remove1 a ys" in allE)
  apply (drule mp)
   apply (clarsimp)
   apply (erule_tac x=x in allE)
   apply (clarsimp split: if_splits)
    apply (erule count_list_remove1)
   apply (subst sum_list_map_remove1) back
    apply (erule_tac x=a in allE; clarsimp)
  apply (erule count_ge_suc_in_set)
  using add_left_mono apply blast
  done

lemma sum_map_map:"(\<Sum>a\<leftarrow>xs. f (g a)) = (\<Sum>a\<leftarrow>(map g xs). (f a))"
  apply (clarsimp)
  apply (clarsimp simp: comp_def)
  done


lemma lists_of_set_reduce_count: "xs \<in> lists_of ys' \<Longrightarrow> ys' \<subseteq> list.set ys \<Longrightarrow> count_list xs a \<le> count_list ys a"
  apply (induct ys arbitrary: ys'; clarsimp simp: lists_of_def)
  apply (safe)
   apply (metis Diff_insert_absorb Set.set_insert count_ge_suc_in_set count_list_remove1 not_less_eq_eq set_remove1_eq)
  by (metis Diff_iff count_ge_suc_in_set count_list_0_iff count_list_remove1 insert_iff not_less_eq_eq order_antisym_conv set_remove1_eq subset_code(1))

lemma [simp]: "var_list_inner (VariableList vs) = vs"
  by (simp add: var_list_inner_def)

lemma map_unsafe_var_list[simp]: "(map (unsafe_var_list_index (VariableList vs)) xs) = map (\<lambda>v. vs ! unat v) xs"
  by (clarsimp simp: unsafe_var_list_index_def)

lemma distinct_index_list_map: "distinct (Invariants.var_list_inner v) \<Longrightarrow>
       distinct xs \<Longrightarrow> \<forall>x\<in>(list.set xs). x < var_list_len v \<Longrightarrow>
       distinct (map (unsafe_var_list_index v) xs)"
  apply (induct xs; clarsimp)
  apply (case_tac v; clarsimp simp: unsafe_var_list_index_def)
  by (metis distinct_the_index_is_index unat_less_helper word_unat.Rep_inverse)

lemma nth_mem' [intro]: "n < length xs \<Longrightarrow> xs ! n  = a \<Longrightarrow> a \<in> list.set xs"
  by (auto simp add: set_conv_nth)

lemma in_set_zip_iff: "(a,b) \<in> list.set (zip xs ys) \<longleftrightarrow> (\<exists>n. n < length xs \<and> n < length ys \<and> xs ! n = a \<and> ys ! n = b)"
  apply (safe; clarsimp?)
   apply (induct xs arbitrary: ys ; clarsimp)
   apply (case_tac ys; clarsimp)
   apply (safe)
    apply auto[1]
   apply (metis Suc_less_eq nth_Cons_Suc)
  apply (rule_tac n=n in nth_mem', clarsimp)
  apply (clarsimp)
  done

lemma bounded_enumerate: "(i, v) \<in> list.set (local.enumerate (local.var_list_inner vs)) \<Longrightarrow> length (var_list_inner vs) \<le> 2^64 - 1 \<Longrightarrow> i < var_list_len vs"
  apply (case_tac vs; clarsimp)
  apply (clarsimp simp: enumerate_def)
  apply (clarsimp simp: in_set_zip_iff)
  apply (rule of_nat_mono_maybe, clarsimp)
  apply (clarsimp)
  done
  

lemma index_in_length_in_set[intro!]: "xb < var_list_len v \<Longrightarrow> local.var_list_inner v ! unat xb \<in> list.set (Invariants.var_list_inner v)"
  apply (case_tac v; clarsimp)
  by (simp add: unat_less_helper)


declare range.simps[simp del ]

lemma get_total_balance_wp[wp]:"(\<And>x xs (v :: Validator VariableList). distinct xs \<Longrightarrow> list.set xs = S \<Longrightarrow> x = max (EFFECTIVE_BALANCE_INCREMENT config) (sum_list (map (Validator.effective_balance_f \<circ> unsafe_var_list_index v) xs)) \<Longrightarrow>
    hoare_triple (lift (P x)) (f x) Q) 
  \<Longrightarrow> hoare_triple (lift ((maps_to validators v \<and>* (maps_to validators v \<longrightarrow>* (\<lambda>s. (\<forall>x\<in>S. x < var_list_len v) \<and>  ((\<forall>x\<in>S. x < var_list_len v) \<longrightarrow> (\<forall>xs\<in>lists_of S. P (max (EFFECTIVE_BALANCE_INCREMENT config) (sum_list (map (Validator.effective_balance_f \<circ> unsafe_var_list_index v) xs))) s)  )))) ))
   (do {b <- get_total_balance S; f b}) Q"
  apply (clarsimp simp: get_total_balance_def, rule hoare_weaken_pre)
   apply (wp)
   apply (clarsimp)
   apply (atomize)
   apply (erule_tac allE)
   apply (erule_tac x=a in allE)
   apply (fastforce)
  apply (clarsimp)
  apply (rule exI)
  apply (sep_cancel)
  apply (sep_cancel)
  apply (clarsimp)
  apply (intro conjI impI)

   apply (clarsimp simp: lists_of_def)
 apply (sep_frule (direct) maps_to_is_valid[where l=validators])
     apply (clarsimp)
     apply (rule plus_one_helper_nat, clarsimp)
  apply (clarsimp simp: Let_unfold)
     apply (erule le_less_trans[rotated])
     apply (clarsimp simp: comp_def)
     apply (subst sum_map_map, rule sum_list_map_leI[where ys="Invariants.var_list_inner v"])
  apply (clarsimp simp: unsafe_var_list_index_def)
     apply (rule order_trans, rule lists_of_set_reduce_count[where ys="Invariants.var_list_inner v"])
      apply (clarsimp simp: lists_of_def)
      apply (intro conjI)
      apply (rule distinct_index_list_map, assumption, assumption)
      apply (sep_mp, clarsimp)
       apply (rule refl)
      apply (clarsimp)
    apply (clarsimp simp: unsafe_var_list_index_def)
    apply (sep_mp, clarsimp, rule order_refl)
  apply (sep_mp, clarsimp)
  apply (erule_tac x=x in ballE, clarsimp)
  by (clarsimp simp: lists_of_def)

(* TODO add in real spec *)                                                                                                  
lemma weigh_justification_and_finalization_wp[wp]: "(hoare_triple (lift (P ())) (f ()) Q) \<Longrightarrow> 
  hoare_triple (lift (P ())) (do {b <- weigh_justification_and_finalization total_b previous current ; f b}) Q"
  sorry

lemma gen_epoch_add_zero[simp]:" epoch_unsigned_add GENESIS_EPOCH x = return x" 
  apply (clarsimp simp: GENESIS_EPOCH_def)
  apply (intro ext, clarsimp simp: return_def epoch_unsigned_add_def bindCont_def word_unsigned_add_def)
  by (metis Epoch.collapse epoch_to_u64.simps)



lemma [simp]: "((\<lambda>a. the (u64_of a)) \<circ> u64) = id "
  by (intro ext; clarsimp)


lemma [simp]: "ProgressiveBalancesCache.fields (total_active_balance_f pbc) (previous_epoch_flag_attesting_balances_f pbc) (current_epoch_flag_attesting_balances_f pbc) = pbc"
  by (clarsimp simp: ProgressiveBalancesCache.defs)


lemma process_fast_spec: "hoare_triple (lift (maps_to beacon_slots b \<and>* maps_to progressive_balances_cache pbc \<and>* R)) process_justification_and_finalization_fast
   (lift (maps_to beacon_slots b \<and>* maps_to progressive_balances_cache pbc \<and>* R))"
  apply (unfold process_justification_and_finalization_fast_def, rule hoare_weaken_pre, wp)
   apply (simp only: gen_epoch_add_zero)
   apply (wp)
  apply (clarsimp, safe)
   apply (sep_cancel)+
  apply (rule exI)
  by (sep_cancel)+




lemma active_validator_indices_are_bound: "x \<in> list.set (active_validator_indices e v) \<Longrightarrow> length (local.var_list_inner v) \<le> 2 ^ 64 - 1 \<Longrightarrow> x < var_list_len v"
  apply (clarsimp simp: active_validator_indices_def)
  apply (erule bounded_enumerate)
  apply (clarsimp)
  done


lemma "hoare_triple (lift (maps_to beacon_slots b \<and>* maps_to previous_epoch_participation pep \<and>*  maps_to current_epoch_participation cep \<and>*  maps_to validators v \<and>*  R \<and>* R')) process_justification_and_finalization 
    (lift (maps_to beacon_slots b \<and>* maps_to validators v \<and>*  maps_to previous_epoch_participation pep \<and>* maps_to current_epoch_participation cep \<and>* R \<and>* R'))"
    apply (subgoal_tac "epoch_to_u64 GENESIS_EPOCH \<le> epoch_to_u64 GENESIS_EPOCH + 1")
  apply (unfold process_justification_and_finalization_def)
   apply (rule hoare_weaken_pre)
    apply (clarsimp simp: bindCont_assoc[symmetric])
    apply (rule get_previous_epoch_wp[where v=b])
  apply (rule get_current_epoch_wp[where v=b])
    apply (wp)
     apply (clarsimp simp: get_total_active_balance_def, wp)
  using less_eq_Epoch_def apply force
  apply (rule le_funI)
   apply (simp)
    apply (safe)
     apply (sep_cancel)+
   apply (clarsimp)
    apply (safe)
    defer
    apply (sep_cancel)+
    apply (clarsimp)
     apply (intro conjI impI)
  apply (clarsimp)
     defer
      apply (clarsimp)
     apply (sep_cancel)+
      apply (intro conjI)
       apply (clarsimp)
      apply (safe; clarsimp?)
  apply (sep_solve)
      defer
     defer
     apply (erule active_validator_indices_are_bound)
 apply (sep_frule (direct) maps_to_is_valid[where l=validators])
     apply (clarsimp simp: Let_unfold)
    apply (case_tac v; clarsimp)
  apply (clarsimp)
     apply (erule active_validator_indices_are_bound)
 apply (sep_frule (direct) maps_to_is_valid[where l=validators])
     apply (clarsimp simp: Let_unfold)
  apply (case_tac v; clarsimp)
  done



lemma get_validator_churn_limit_fast_spec: "hoare_triple (\<lless>num_active_validators \<mapsto>\<^sub>l n \<and>* R\<then>) get_validator_churn_limit_fast (lift (num_active_validators \<mapsto>\<^sub>l n \<and>* R))"
  apply (clarsimp simp: get_validator_churn_limit_fast_def, rule hoare_weaken_pre)
   apply (wp)
  apply (clarsimp)
  apply (rule exI)
  apply (sep_solve)
  done

lemma get_validator_churn_limit_fast_wp[wp]: "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow> 
     hoare_triple (\<lless>num_active_validators \<mapsto>\<^sub>l n \<and>* (num_active_validators \<mapsto>\<^sub>l n \<longrightarrow>* P (max (MIN_PER_EPOCH_CHURN_LIMIT config) (n div CHURN_LIMIT_QUOTIENT config)))\<then>) 
      (bindCont get_validator_churn_limit_fast c) (Q)"
  apply (clarsimp simp: get_validator_churn_limit_fast_def, rule hoare_weaken_pre)
   apply (wp)
  by (fastforce)

lemma get_validator_churn_limit_spec: "hoare_triple (\<lless>beacon_slots \<mapsto>\<^sub>l v \<and>* validators \<mapsto>\<^sub>l vs \<and>*  R\<then>) get_validator_churn_limit (lift (beacon_slots \<mapsto>\<^sub>l v \<and>* validators \<mapsto>\<^sub>l vs \<and>* R))"
  apply (clarsimp simp: get_validator_churn_limit_def, rule hoare_weaken_pre)
   apply (wp)
  apply (clarsimp)
  apply (sep_cancel)+
  done

lemma get_validator_churn_limit_spec': "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
   hoare_triple (\<lless>beacon_slots \<mapsto>\<^sub>l v \<and>* validators \<mapsto>\<^sub>l vs \<and>* (beacon_slots \<mapsto>\<^sub>l v \<and>* validators \<mapsto>\<^sub>l vs \<longrightarrow>* P (max (MIN_PER_EPOCH_CHURN_LIMIT config) (word_of_nat (length (active_validator_indices (slot_to_epoch config v) vs)) div CHURN_LIMIT_QUOTIENT config))) \<then>) (bindCont get_validator_churn_limit c) (Q)"
  apply (clarsimp simp: get_validator_churn_limit_def, rule hoare_weaken_pre)
   apply (wp)
  apply (clarsimp)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (sep_cancel)+
  done

definition "next_epoch b_slots \<equiv> epoch_to_u64 (slot_to_epoch config b_slots) + 1"



lemma process_eth1_data_reset: "hoare_triple (lift (beacon_slots \<mapsto>\<^sub>l b \<and>* eth1_data_votes \<mapsto>\<^sub>l data_votes \<and>*  R))
         process_eth1_data_reset 
      (lift (beacon_slots \<mapsto>\<^sub>l b \<and>* 
   eth1_data_votes \<mapsto>\<^sub>l (if (next_epoch b) mod (EPOCHS_PER_ETH1_VOTING_PERIOD config) = 0 then (VariableList []) else data_votes) \<and>*  R))"
  apply (unfold process_eth1_data_reset_def epoch_unsigned_add_def, rule hoare_weaken_pre)
   apply (wp)
  apply (safe)
  apply (sep_cancel)+
  apply (intro conjI impI)
    apply (clarsimp)
    apply (clarsimp simp: slot_to_epoch_def)
    apply (subgoal_tac "SLOTS_PER_EPOCH config > 1")
  apply (metis (no_types, opaque_lifting) div_by_0 div_less_dividend_word div_word_self less_is_non_zero_p1 lt1_neq0 olen_add_eqv word_div_lt_eq_0)
    apply (clarsimp)
  apply (clarsimp)
  apply (clarsimp simp: next_epoch_def)
  apply (rule exI)
  by (sep_cancel)+

definition "previous_epochs bs = {e. e \<le> previous_epoch (slot_to_epoch config bs)}"

lemma raw_epoch_simp: "raw_epoch = epoch_to_u64"
  by (intro ext, case_tac x; clarsimp)

lemma get_finality_delay_wp[wp]:
"hoare_triple (lift (P (raw_epoch (previous_epoch (slot_to_epoch config bs)) - raw_epoch (epoch_f f_c))))
       (c ((raw_epoch (previous_epoch (slot_to_epoch config bs)) - raw_epoch (epoch_f f_c)))) R \<Longrightarrow>
           hoare_triple (lift (\<lambda>s. epoch_f f_c \<in> previous_epochs bs \<and> (epoch_f f_c \<in> previous_epochs bs \<longrightarrow>
           (beacon_slots \<mapsto>\<^sub>l bs \<and>* finalized_checkpoint \<mapsto>\<^sub>l f_c \<and>* (beacon_slots \<mapsto>\<^sub>l bs \<and>*  finalized_checkpoint \<mapsto>\<^sub>l f_c \<longrightarrow>* P (raw_epoch (previous_epoch (slot_to_epoch config bs)) - raw_epoch (epoch_f f_c)))) s) ) ) 
(bindCont get_finality_delay c) ( R )"
  apply (unfold get_finality_delay_def, rule hoare_weaken_pre)
   apply (wp)
   apply (clarsimp simp: raw_epoch_simp)
   apply (erule hoare_eqI')
  apply (clarsimp)
  apply (sep_cancel)+
  apply (rule exI, sep_cancel)+
  apply (clarsimp)
   apply (clarsimp simp: previous_epochs_def)
  using less_eq_Epoch_def 
   apply (clarsimp)
   apply (sep_mp)
  by (clarsimp simp: raw_epoch_simp)



abbreviation (input) "sep_wp pre post P \<equiv> (lift (pre \<and>* (post \<longrightarrow>* P)))"



schematic_goal is_in_activity_leak[wp]:
 "hoare_triple (lift (pre ?x)) (c ?x) post \<Longrightarrow>
   hoare_triple
    (sep_wp (beacon_slots \<mapsto>\<^sub>l b_s \<and>* finalized_checkpoint \<mapsto>\<^sub>l c_f)
  (beacon_slots \<mapsto>\<^sub>l b_s \<and>* finalized_checkpoint \<mapsto>\<^sub>l c_f)
 (\<lambda>s. Checkpoint.epoch_f c_f \<in> previous_epochs b_s \<and> (Checkpoint.epoch_f c_f \<in> previous_epochs b_s \<longrightarrow> pre ?x s)))
  (bindCont is_in_inactivity_leak c) post"
  apply (unfold is_in_inactivity_leak_def, rule hoare_weaken_pre)
   apply (wp)
  apply (rule lift_mono')
  apply (clarsimp)
  apply (intro conjI impI)
   apply (clarsimp simp: sep_conj_assoc)
   defer
   apply (clarsimp simp: sep_conj_assoc)
   apply (sep_cancel)+
  apply (sep_mp)
   apply (clarsimp)
  apply (sep_mp)
  apply (clarsimp)
  done

lemma epoch_always_bounded[simp]: "epoch_to_u64 (slot_to_epoch config v) \<le> epoch_to_u64 (slot_to_epoch config v) + 1"
  apply (clarsimp simp: slot_to_epoch_def)
  by (metis (no_types, opaque_lifting) SLOTS_PER_EPOCH_ATLEAST div_0 div_by_1 div_less_dividend_word 
         less_is_non_zero_p1 lt1_neq0 olen_add_eqv word_div_less zero_neq_one)


lemma subst_in_impl: "(x = y \<longrightarrow> f y) = (x = y \<longrightarrow> f x)"
  by (safe)

schematic_goal new_state_context_wp[simplified subst_in_impl, wp]: 
 "hoare_triple (lift (pre ?x)) (c ?x) post \<Longrightarrow> hoare_triple (lift ?P) (bindCont new_state_context c) (post)"
  apply (unfold new_state_context_def epoch_unsigned_add_def, rule hoare_weaken_pre)
   apply (wp)
  apply (erule hoare_eqI')
  apply (clarsimp simp: subst_in_impl)
  apply (sep_cancel)+
  done




lemma new_slashings_context_wp[wp]: 
  "hoare_triple (lift (P x)) (c x) Q \<Longrightarrow> hoare_triple (lift (slashings \<mapsto>\<^sub>l ss \<and>*
       (slashings \<mapsto>\<^sub>l ss \<longrightarrow>*
        (\<lambda>s. safe_mul PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX (sum_list (vector_inner ss)) \<and>
              (safe_mul PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX (sum_list (vector_inner ss)) \<longrightarrow>
               raw_epoch (current_epoch_f st_ctxt) \<le> raw_epoch (current_epoch_f st_ctxt) + EPOCHS_PER_SLASHINGS_VECTOR config \<and>
               (raw_epoch (current_epoch_f st_ctxt) \<le> raw_epoch (current_epoch_f st_ctxt) + EPOCHS_PER_SLASHINGS_VECTOR config \<longrightarrow>
                SlashingsContext.fields (min (sum_list (vector_inner ss) * PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX) (total_active_balance_f pbc))
                 (Epoch ((raw_epoch (current_epoch_f st_ctxt) + EPOCHS_PER_SLASHINGS_VECTOR config) div 2)) =
                x \<and>
                (SlashingsContext.fields (min (sum_list (vector_inner ss) * PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX) (total_active_balance_f pbc))
                  (Epoch ((raw_epoch (current_epoch_f st_ctxt) + EPOCHS_PER_SLASHINGS_VECTOR config) div 2)) =
                 x \<longrightarrow>
                 P x s))))))) (bindCont (new_slashings_context st_ctxt pbc) c) ( Q)"
  apply (clarsimp simp: new_slashings_context_def, rule hoare_weaken_pre , wp)
   apply (erule hoare_eqI')
  apply (clarsimp)
  apply (rule exI)

  apply (frule slashings_wf)
  apply (erule sep_conj_impl, assumption)
  apply (clarsimp)
  apply (sep_cancel)+
  apply (clarsimp)
  apply (sep_mp)
  apply (safe; clarsimp?)
  by (case_tac ss; clarsimp simp: vector_inner_def)



schematic_goal new_activation_queue_wp[wp]:
  "hoare_triple (lift (P x)) (c x) Q \<Longrightarrow> 
   hoare_triple (lift (beacon_slots \<mapsto>\<^sub>l b_s \<and>* validators \<mapsto>\<^sub>l vs \<and>* 
  (validators \<mapsto>\<^sub>l vs \<and>* beacon_slots \<mapsto>\<^sub>l b_s \<longrightarrow>*
    (\<lambda>sc. fold (\<lambda>(i, v) q. add_if_could_be_eligible_for_activation q i v (Epoch (next_epoch b_s))) (local.enumerate (local.var_list_inner vs)) (ActivationQueue.fields []) = x \<and>
(fold (\<lambda>(i, v) q. add_if_could_be_eligible_for_activation q i v (Epoch (next_epoch b_s))) (local.enumerate (local.var_list_inner vs)) (ActivationQueue.fields []) = x \<longrightarrow> P x sc))) ))
   (bindCont new_activation_queue c) Q"
  apply (clarsimp simp: new_activation_queue_def epoch_unsigned_add_def, rule hoare_weaken_pre, wp)
   apply (erule hoare_eqI')
  apply (clarsimp)
  apply (fold next_epoch_def)
  apply (sep_cancel)+
  apply (rule exI, sep_cancel+)
  by (sep_mp, clarsimp)
 

abbreviation "map_varlist f xs \<equiv> map f (local.var_list_inner xs)"

definition "frequency_map xs = Some(0 := None) o of_nat o (count_list xs)"

lemma exit_cache_eq_iff: "(x :: ExitCache) = y \<longleftrightarrow> exit_epoch_counts_f x = exit_epoch_counts_f y"
  by (case_tac x; case_tac y; clarsimp)

lemma  new_exit_cache_wp[wp]: "
  hoare_triple (lift (P x)) (c x) Q \<Longrightarrow> 
  hoare_triple (lift (validators \<mapsto>\<^sub>l vs \<and>*
                     (validators \<mapsto>\<^sub>l vs \<longrightarrow>* 
                       (\<lambda>s. exit_epoch_counts_f x = frequency_map (map_varlist exit_epoch_f vs) \<and> 
                       (exit_epoch_counts_f x = frequency_map (map_varlist exit_epoch_f vs) \<longrightarrow> P x s)))))
                (bindCont new_exit_cache c) Q"
  apply (clarsimp simp: new_exit_cache_def Let_unfold, rule hoare_weaken_pre, wp)
     apply (erule hoare_eqI')
  apply (clarsimp)
  apply (rule exI)
  apply (sep_cancel)+
  apply (intro conjI impI)
  apply (sep_mp)
  apply (clarsimp)
   apply (clarsimp simp: frequency_map_def exit_cache_eq_iff ExitCache.defs)
   apply (intro ext, clarsimp)
  apply (sep_mp, clarsimp)
  done




lemma sqrt_eq_zero_iff[simp]: "sqrt' x = 0 \<longleftrightarrow> x = 0"
  by (metis div_by_1 lt1_neq0 mult.right_neutral sqrt_le_eqI word_coorder.extremum zero_sqrt_zero)



schematic_goal get_base_reward_fast_wp[wp]:
 "hoare_triple (lift (P x)) (c x) Q \<Longrightarrow> hoare_triple (lift (\<lambda>s. total_active_balance_f pbc < total_active_balance_f pbc + 1 \<and>
          (total_active_balance_f pbc < total_active_balance_f pbc + 1 \<longrightarrow>
           total_active_balance_f pbc \<noteq> 0 \<and>
           (total_active_balance_f pbc \<noteq> 0 \<longrightarrow>
            safe_mul (effective_balance div EFFECTIVE_BALANCE_INCREMENT config) (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config div sqrt' (total_active_balance_f pbc)) \<and>
            (safe_mul (effective_balance div EFFECTIVE_BALANCE_INCREMENT config) (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config div sqrt' (total_active_balance_f pbc)) \<longrightarrow>
             effective_balance div EFFECTIVE_BALANCE_INCREMENT config * (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config div sqrt' (total_active_balance_f pbc)) = x \<and>
             (effective_balance div EFFECTIVE_BALANCE_INCREMENT config * (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config div sqrt' (total_active_balance_f pbc)) = x \<longrightarrow> P x s ))))))
        (bindCont (get_base_reward_fast effective_balance pbc) c) Q"
  apply (clarsimp simp: get_base_reward_fast_def, rule hoare_weaken_pre, wp)
   apply (clarsimp simp: get_base_reward_per_increment_fast_def, wp)
   apply (erule hoare_eqI')
  apply (clarsimp)
  apply (intro conjI impI; clarsimp?)
   apply (metis brf_ebi_times_bounded mult.commute safe_mul_def)
  using safe_mul_commute by blast



schematic_goal compute_base_rewards_wp[wp]:
 "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow> 
 hoare_triple 
  (lift (progressive_balances_cache \<mapsto>\<^sub>l pbc \<and>* (progressive_balances_cache \<mapsto>\<^sub>l pbc \<longrightarrow>*
        (\<lambda>s. total_active_balance_f pbc < total_active_balance_f pbc + 1 \<and>
              (total_active_balance_f pbc < total_active_balance_f pbc + 1 \<longrightarrow>
               total_active_balance_f pbc \<noteq> 0 \<and>
               (total_active_balance_f pbc \<noteq> 0 \<longrightarrow>
                (\<forall>f\<in>list.set (local.range 0 (unat (MAX_EFFECTIVE_BALANCE + EFFECTIVE_BALANCE_INCREMENT config)) (unat (EFFECTIVE_BALANCE_INCREMENT config))).
                    safe_mul (word_of_nat f div EFFECTIVE_BALANCE_INCREMENT config) (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config div sqrt' (total_active_balance_f pbc)) \<and>
                    (safe_mul (word_of_nat f div EFFECTIVE_BALANCE_INCREMENT config) (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config div sqrt' (total_active_balance_f pbc)) \<longrightarrow>
                   
                      P ((map (\<lambda>effective_balance.
                        word_of_nat effective_balance div EFFECTIVE_BALANCE_INCREMENT config * (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config div sqrt' (total_active_balance_f pbc)))
                       (local.range 0 (unat (MAX_EFFECTIVE_BALANCE + EFFECTIVE_BALANCE_INCREMENT config)) (unat (EFFECTIVE_BALANCE_INCREMENT config))))) s))))) ))) 
       (bindCont compute_base_rewards c) Q"
  apply (clarsimp simp: compute_base_rewards_def, rule hoare_weaken_pre)
  apply (simp only: bindCont_assoc[symmetric])
   apply (rule read_beacon_wp)
  apply (rule add_wp')
  apply (rule mapM_wp'[where g="(\<lambda>effective_balance. of_nat effective_balance div EFFECTIVE_BALANCE_INCREMENT config * (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config div sqrt' (total_active_balance_f pbc)))" for f])
    apply (erule get_base_reward_fast_wp)
    apply (intro conjI impI; clarsimp?)
  apply (fastforce)
  apply (clarsimp)
  apply (erule sep_conj_impl, assumption)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (subgoal_tac "list.set (local.range 0 (unat (MAX_EFFECTIVE_BALANCE + EFFECTIVE_BALANCE_INCREMENT config)) (unat (EFFECTIVE_BALANCE_INCREMENT config))) \<noteq> {}")
   apply (clarsimp simp: nonempty_ball_conj_lift nonempty_ball_imp_lift)
   apply (erule_tac x=0 in ballE; clarsimp?)
  apply (clarsimp simp: range_empty_iff)
  by (metis EBI_ge_zero add_0 effective_balance_safe neq_0_no_wrap unat_0 unat_gt_0 unat_mono)




abbreviation "map_var f vs \<equiv> map f (var_list_inner vs)"




definition "base_rewards_from_cache pbc \<equiv>
map (\<lambda>effective_balance. word_of_nat effective_balance div EFFECTIVE_BALANCE_INCREMENT config *
      (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config div sqrt' (total_active_balance_f pbc)))
       (local.range 0 (unat (MAX_EFFECTIVE_BALANCE + EFFECTIVE_BALANCE_INCREMENT config)) (unat (EFFECTIVE_BALANCE_INCREMENT config)))"

schematic_goal new_base_rewards_cache_wp: 
  "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow> 
hoare_triple (lift (validators \<mapsto>\<^sub>l vs \<and>* progressive_balances_cache \<mapsto>\<^sub>l pbc \<and>* 
(validators \<mapsto>\<^sub>l vs \<and>* progressive_balances_cache \<mapsto>\<^sub>l pbc \<longrightarrow>*
  (\<lambda>s. total_active_balance_f pbc < total_active_balance_f pbc + 1 \<and>
       (total_active_balance_f pbc < total_active_balance_f pbc + 1 \<longrightarrow>
        total_active_balance_f pbc \<noteq> 0 \<and>
        (total_active_balance_f pbc \<noteq> 0 \<longrightarrow>
         (\<forall>f\<in>list.set (local.range 0 (unat (MAX_EFFECTIVE_BALANCE + EFFECTIVE_BALANCE_INCREMENT config)) (unat (EFFECTIVE_BALANCE_INCREMENT config))).
             safe_mul (word_of_nat f div EFFECTIVE_BALANCE_INCREMENT config) (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config div sqrt' (total_active_balance_f pbc)) \<and>
             (safe_mul (word_of_nat f div EFFECTIVE_BALANCE_INCREMENT config) (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config div sqrt' (total_active_balance_f pbc)) \<longrightarrow>
              P \<lparr>effective_balances_f = map_var Validator.effective_balance_f vs,
                   base_rewards_f = base_rewards_from_cache pbc \<rparr> s)))))))) 
       (bindCont new_base_rewards_cache c) Q"
  apply (clarsimp simp: new_base_rewards_cache_def)
  apply (rule hoare_weaken_pre, simp only: bindCont_assoc[symmetric])
  apply (wp)

  apply (clarsimp)
  apply (rule exI)
  apply (sep_cancel)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (clarsimp)
  apply (clarsimp simp: base_rewards_from_cache_def)
  done


lemma get_total_active_balance_wp[wp]:"(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow> 
 hoare_triple (lift (beacon_slots \<mapsto>\<^sub>l b_s \<and>* validators \<mapsto>\<^sub>l vs \<and>*
 (beacon_slots \<mapsto>\<^sub>l b_s \<and>* validators \<mapsto>\<^sub>l vs \<longrightarrow>* 
(\<lambda>s. (\<forall>x\<in>list.set (active_validator_indices (slot_to_epoch config b_s) vs). x < var_list_len vs) \<and>
       ((\<forall>x\<in>list.set (active_validator_indices (slot_to_epoch config b_s) vs). x < var_list_len vs) \<longrightarrow>
        (\<forall>xs\<in>lists_of (list.set (active_validator_indices (slot_to_epoch config b_s) vs)).
  P (max (EFFECTIVE_BALANCE_INCREMENT config)
     (\<Sum>a\<leftarrow>xs. Validator.effective_balance_f (unsafe_var_list_index vs a))) s)  )))))
 (bindCont get_total_active_balance c) Q"
  apply (clarsimp simp: get_total_active_balance_def, rule hoare_weaken_pre, wp, clarsimp)
  apply (sep_cancel)+
  apply (sep_mp, clarsimp)
  done

abbreviation "current_epoch bs \<equiv> slot_to_epoch config bs"

definition "unslashed_participating_indices flag_index epoch epoch_participation vs  \<equiv>
            {x \<in> list.set (active_validator_indices epoch vs). 
             has_flag (unsafe_var_list_index epoch_participation x) flag_index \<and> 
             \<not> slashed_f (unsafe_var_list_index vs x)}  "

lemma get_flag_attesting_balance_current_epoch_wp: 
  "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
   hoare_triple (lift (beacon_slots \<mapsto>\<^sub>l b_s \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<and>* 
                       validators \<mapsto>\<^sub>l vs \<and>*
                       (beacon_slots \<mapsto>\<^sub>l b_s \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<and>* 
                         validators \<mapsto>\<^sub>l vs \<longrightarrow>*
                         (\<lambda>s. epoch = current_epoch b_s \<and>
                       (\<forall>x\<in>(unslashed_participating_indices flag_index epoch cep vs ). x < var_list_len vs) \<and>
                        (epoch = current_epoch b_s \<longrightarrow>
                        (\<forall>x\<in>(unslashed_participating_indices flag_index epoch cep vs ). x < var_list_len vs) \<longrightarrow> 
        (\<forall>xs\<in>lists_of (unslashed_participating_indices flag_index epoch cep vs).
         P (max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>xs. Validator.effective_balance_f (unsafe_var_list_index vs a))) s))))))
      (bindCont (get_flag_attesting_balance flag_index epoch) c) Q"
  apply (clarsimp simp: get_flag_attesting_balance_def, rule hoare_weaken_pre)
  apply (clarsimp simp: bindCont_assoc[symmetric])
   apply (rule hoare_eqI'[where v=epoch], rule get_current_unslashed_participating_indices_wp, wp)
  apply (rule lift_mono')
  apply (clarsimp)
  apply (intro conjI)
   apply (sep_mp)
   apply (blast)
  apply (clarsimp)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (clarsimp simp: unslashed_participating_indices_def)
  done

lemma get_flag_attesting_balance_previous_epoch_wp: 
  "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow> current_epoch b_s \<noteq> GENESIS_EPOCH \<Longrightarrow>
   hoare_triple (lift (beacon_slots \<mapsto>\<^sub>l b_s \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<and>*
                       validators \<mapsto>\<^sub>l vs \<and>*
                       (beacon_slots \<mapsto>\<^sub>l b_s \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<and>* 
                         validators \<mapsto>\<^sub>l vs \<longrightarrow>*
                         (\<lambda>s. epoch = previous_epoch (slot_to_epoch config b_s) \<and>
                       (\<forall>x\<in>(unslashed_participating_indices flag_index epoch pep vs). x < var_list_len vs) \<and>
                        (epoch = previous_epoch (slot_to_epoch config b_s) \<longrightarrow>
                        (\<forall>x\<in>(unslashed_participating_indices flag_index epoch pep vs). x < var_list_len vs) \<longrightarrow> 
        (\<forall>xs\<in>lists_of (unslashed_participating_indices flag_index epoch pep vs).
         P (max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>xs. Validator.effective_balance_f (unsafe_var_list_index vs a))) s))))))
      (bindCont (get_flag_attesting_balance flag_index epoch) c) Q"
  apply (clarsimp simp: get_flag_attesting_balance_def, rule hoare_weaken_pre)
  apply (clarsimp simp: bindCont_assoc[symmetric])
   apply (rule hoare_eqI'[where v=epoch], rule get_previous_unslashed_participating_indices_wp, wp)
  apply (rule lift_mono')
  apply (clarsimp)
  apply (intro conjI)
   apply (sep_mp)
   apply (blast)
  apply (clarsimp)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (clarsimp simp: unslashed_participating_indices_def)
  done

lemma [simp]: "(Invariants.var_list_inner vs) = (var_list_inner vs)"
  by (case_tac vs; clarsimp)


lemma new_progressive_balances_wp: "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
  hoare_triple (lift (beacon_slots \<mapsto>\<^sub>l b_s \<and>* validators \<mapsto>\<^sub>l vs \<and>*
                     current_epoch_participation \<mapsto>\<^sub>l cep \<and>*
                     previous_epoch_participation \<mapsto>\<^sub>l pep \<and>* 
                    (beacon_slots \<mapsto>\<^sub>l b_s \<and>* validators \<mapsto>\<^sub>l vs \<and>*
                     current_epoch_participation \<mapsto>\<^sub>l cep \<and>*
                     previous_epoch_participation \<mapsto>\<^sub>l pep  \<longrightarrow>*
 (\<lambda>s.(\<exists>ep. ep = (if (current_epoch b_s) = GENESIS_EPOCH then cep else pep) \<and>  
     (\<forall>xs \<in> lists_of (list.set (active_validator_indices (current_epoch b_s) vs)).
     \<forall>xsa \<in> lists_of (unslashed_participating_indices TIMELY_SOURCE_FLAG_INDEX (previous_epoch (current_epoch b_s)) ep vs).
     \<forall>xsb \<in> lists_of (unslashed_participating_indices TIMELY_TARGET_FLAG_INDEX (previous_epoch (current_epoch b_s)) ep vs).
     \<forall>xsc \<in> lists_of (unslashed_participating_indices TIMELY_HEAD_FLAG_INDEX   (previous_epoch (current_epoch b_s)) ep vs).
     \<forall>xsd \<in> lists_of (unslashed_participating_indices TIMELY_SOURCE_FLAG_INDEX (current_epoch b_s) cep vs).
     \<forall>xse \<in> lists_of (unslashed_participating_indices TIMELY_TARGET_FLAG_INDEX (current_epoch b_s) cep vs).
     \<forall>xsf \<in> lists_of (unslashed_participating_indices TIMELY_HEAD_FLAG_INDEX (current_epoch b_s) cep vs).
      P (ProgressiveBalancesCache.fields (max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>xs. Validator.effective_balance_f (unsafe_var_list_index vs a)))
           [max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>xsa. Validator.effective_balance_f (unsafe_var_list_index vs a)),
            max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>xsb. Validator.effective_balance_f (unsafe_var_list_index vs a)),
            max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>xsc. Validator.effective_balance_f (unsafe_var_list_index vs a))]
           [max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>xsd. Validator.effective_balance_f (unsafe_var_list_index vs a)),
            max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>xse. Validator.effective_balance_f (unsafe_var_list_index vs a)),
            max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>xsf. Validator.effective_balance_f (unsafe_var_list_index vs a))]) s))))))
 (bindCont new_progressive_balances c) Q"
  apply (case_tac "current_epoch b_s = GENESIS_EPOCH")
defer
  apply (clarsimp simp: new_progressive_balances_def, rule hoare_weaken_pre)
  apply (clarsimp simp: bindCont_assoc[symmetric])
   apply (rule get_total_active_balance_wp[where b_s=b_s])
   apply (rule get_previous_epoch_wp[where v=b_s])
   apply (rule get_current_epoch_wp[where v=b_s])
   apply (rule get_flag_attesting_balance_previous_epoch_wp[where b_s=b_s])
   apply (rule get_flag_attesting_balance_previous_epoch_wp[where b_s=b_s])
   apply (rule get_flag_attesting_balance_previous_epoch_wp[where b_s=b_s])
   apply (rule get_flag_attesting_balance_current_epoch_wp[where b_s=b_s])+
   apply (fastforce)
     apply (clarsimp)
     prefer 3
  apply (clarsimp)
  apply (sep_cancel)+
  apply (safe; clarsimp?)
  apply (erule active_validator_indices_are_bound)
   apply (clarsimp simp: sep_conj_assoc)
   apply (sep_drule (direct) val_length_wf)
   apply (clarsimp)
  apply (clarsimp simp: sep_conj_assoc)
  apply (sep_cancel)+
     apply (intro conjI)
      apply (clarsimp simp: unslashed_participating_indices_def)
 apply (erule active_validator_indices_are_bound)
   apply (clarsimp simp: sep_conj_assoc)
   apply (sep_drule (direct) val_length_wf)
      apply (clarsimp)
     apply (intro conjI impI ballI)
     apply (sep_cancel)+
     apply (intro conjI impI ballI)
      apply (clarsimp simp: unslashed_participating_indices_def)

apply (erule active_validator_indices_are_bound)
   apply (clarsimp simp: sep_conj_assoc)
   apply (sep_drule (direct) val_length_wf)
      apply (clarsimp)
     apply (sep_cancel)+
 apply (intro conjI impI ballI)
      apply (clarsimp simp: unslashed_participating_indices_def)

apply (erule active_validator_indices_are_bound)
   apply (clarsimp simp: sep_conj_assoc)
   apply (sep_drule (direct) val_length_wf)
      apply (clarsimp)
     apply (sep_cancel)+
 apply (intro conjI impI ballI)
      apply (clarsimp simp: unslashed_participating_indices_def)

     apply (sep_cancel)+
  apply (intro conjI impI)
      apply (clarsimp simp: unslashed_participating_indices_def)
     apply (intro conjI impI ballI)
     apply (sep_cancel)+
     apply (intro conjI impI ballI)
      apply (clarsimp simp: unslashed_participating_indices_def)
   apply (clarsimp simp: sep_conj_assoc)
     apply (sep_mp)
  apply (erule_tac x=xs in ballE)
      apply (erule_tac x=xsa in ballE)
       apply (erule_tac x=xsb in ballE)
        apply (erule_tac x=xsc in ballE)
         apply (erule_tac x=xsd in ballE)
          apply (erule_tac x=xse in ballE)
  apply (erule_tac x=xsf in ballE)
            apply (assumption)
           apply (clarsimp)+
  apply (clarsimp simp: new_progressive_balances_def, rule hoare_weaken_pre)
   apply (clarsimp simp: bindCont_assoc[symmetric])
apply (rule get_total_active_balance_wp[where b_s=b_s])
   apply (rule get_previous_epoch_wp[where v=b_s])
  apply (rule get_current_epoch_wp[where v=b_s])
   apply (rule get_flag_attesting_balance_current_epoch_wp[where b_s=b_s])+
   apply (fastforce)
apply (clarsimp)
  apply (sep_cancel)+
  apply (safe; clarsimp?)
  apply (erule active_validator_indices_are_bound)
   apply (clarsimp simp: sep_conj_assoc)
   apply (sep_drule (direct) val_length_wf)
   apply (clarsimp)
  apply (clarsimp simp: sep_conj_assoc)
  apply (sep_cancel)+
     apply (intro conjI impI ballI)
   apply (clarsimp simp: unslashed_participating_indices_def)
  apply (sep_cancel)+

  apply (intro conjI impI ballI)
   apply (clarsimp simp: unslashed_participating_indices_def)
  apply (sep_cancel)+
  apply (intro conjI impI ballI)
   apply (clarsimp simp: unslashed_participating_indices_def)
  apply (sep_cancel)+
  apply (intro conjI impI ballI)
   apply (clarsimp simp: unslashed_participating_indices_def)
  apply (sep_cancel)+
 apply (intro conjI impI ballI)
   apply (clarsimp simp: unslashed_participating_indices_def)
apply (sep_cancel)+
 apply (intro conjI impI ballI)
   apply (clarsimp simp: unslashed_participating_indices_def)
  apply (clarsimp simp: sep_conj_assoc)
  apply (sep_mp)
  apply (clarsimp)
  done  



lemma new_rewards_and_penalties_context_wp[wp]:"(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
   hoare_triple 
          (lift (progressive_balances_cache \<mapsto>\<^sub>l pbc \<and>* 
          (\<lambda>s. (\<forall>x\<in>list.set (local.range 0 (unat NUM_FLAG_INDICES) (Suc 0)). x < length (previous_epoch_flag_attesting_balances_f pbc)) \<and>
         ((\<forall>x\<in>list.set (local.range 0 (unat NUM_FLAG_INDICES) (Suc 0)). x < length (previous_epoch_flag_attesting_balances_f pbc)) \<longrightarrow>
          (progressive_balances_cache \<mapsto>\<^sub>l pbc \<longrightarrow>*
           P (RewardsAndPenaltiesContext.fields (map (\<lambda>a. previous_epoch_flag_attesting_balances_f pbc ! a div EFFECTIVE_BALANCE_INCREMENT config) (local.range 0 (unat NUM_FLAG_INDICES) (Suc 0)))
               (total_active_balance_f pbc div EFFECTIVE_BALANCE_INCREMENT config)))s
           )))) 
   (bindCont (new_rewards_and_penalties_context pbc) c) Q"
  apply (unfold new_rewards_and_penalties_context_def)
  apply (rule hoare_weaken_pre)
   apply (simp only: bindCont_assoc[symmetric])
   apply (rule mapM_wp_foldr')
    apply (clarsimp simp: unslashed_participating_increment_def liftM_def comp_def)
   apply (simp only: bindCont_assoc[symmetric])
  apply (rule read_beacon_wp[where v=pbc])
    apply (wp)
    apply (clarsimp)
  apply (rule factor_foldr_sep)
    prefer 2
    apply (clarsimp simp: mono_def)
    apply blast
   defer
   apply (intro ext iffI; clarsimp)
  apply (sep_cancel)
  apply (rule factor_foldr_pure)
   apply (clarsimp)
  by (clarsimp)



lemma safe_mul_one[simp]: "safe_mul 1 (x :: u64)"
  apply (clarsimp simp: safe_mul_def)
  using div_word_self by blast

lemma new_effective_balances_ctxt_wp[wp]: 
"(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
  hoare_triple 
    (lift (P \<lparr> downward_threshold_f = 
                (EFFECTIVE_BALANCE_INCREMENT config div HYSTERESIS_QUOTIENT), 
              upward_threshold_f = 
                (EFFECTIVE_BALANCE_INCREMENT config div HYSTERESIS_QUOTIENT * HYSTERESIS_UPWARD_MULTIPLIER)\<rparr>)) 
     (bindCont new_effective_balances_ctxt c) Q "
  apply (unfold new_effective_balances_ctxt_def, rule hoare_weaken_pre, wp)
  apply (clarsimp simp: HYSTERESIS_QUOTIENT_def HYSTERESIS_DOWNWARD_MULTIPLIER_def HYSTERESIS_UPWARD_MULTIPLIER_def)
  apply (intro conjI impI)
  using EBI_multiple_of_HYSTERESIS_QUOTIENT 
    apply (insert EBI_multiple_of_HYSTERESIS_QUOTIENT)[1]
   apply (clarsimp simp: HYSTERESIS_QUOTIENT_def)
   apply (clarsimp simp: safe_mul_def)
  apply (metis HYSTERESIS_QUOTIENT_def HYSTERESIS_UPWARD_MULTIPLIER_def mult.commute upward_threshold_safe)
  by (clarsimp simp: EffectiveBalancesContext.defs)



lemma new_next_epoch_progressive_balances_wp[wp]: "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
  hoare_triple 
    (lift (\<lambda>s. P \<lparr> total_active_balance_f = 0, 
                   previous_epoch_flag_attesting_balances_f = current_epoch_flag_attesting_balances_f pbc,
                   current_epoch_flag_attesting_balances_f = [0,0,0]\<rparr> s)) 
   (bindCont (new_next_epoch_progressive_balances pbc) c) Q"
  by (clarsimp simp: new_next_epoch_progressive_balances_def ProgressiveBalancesCache.defs)

term "effective_balances_f brc ! unat n div EFFECTIVE_BALANCE_INCREMENT config = (effective_balances_f brc ! unat n) div EFFECTIVE_BALANCE_INCREMENT config"

lemma get_cached_base_reward_wp[wp]:"(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
  hoare_triple 
   (lift (\<lambda>s. (length (base_rewards_f brc) \<le> 2 ^ 64 - 1) \<and> n < word_of_nat (length (effective_balances_f brc)) \<and>  effective_balances_f brc ! unat n div EFFECTIVE_BALANCE_INCREMENT config < word_of_nat (length (base_rewards_f brc))
              \<and>  (n < word_of_nat (length (effective_balances_f brc)) \<longrightarrow> effective_balances_f brc ! unat n div EFFECTIVE_BALANCE_INCREMENT config < word_of_nat (length (base_rewards_f brc)) \<longrightarrow> length (base_rewards_f brc) \<le> 2 ^ 64 - 1 \<longrightarrow>
    (P (base_rewards_f brc ! unat (effective_balances_f brc ! unat n div EFFECTIVE_BALANCE_INCREMENT config)) s))))
   (bindCont (get_cached_base_reward brc n) c)
    Q"
  apply (clarsimp simp: get_cached_base_reward_def, rule hoare_weaken_pre, wp)
  by (clarsimp)


definition single_inactivity_update:: "u64 \<Rightarrow> ValidatorInfo \<Rightarrow> StateContext \<Rightarrow> u64"
  where "single_inactivity_update inactivity_score val_info state_ctxt \<equiv> 
  if \<not>(is_eligible_f val_info) then inactivity_score
  else 
  (let new_inactivity_score = inactivity_score in
   let new_inactivity_score = (if (is_unslashed_participating_index val_info TIMELY_TARGET_FLAG_INDEX)
                              then (new_inactivity_score - (min new_inactivity_score 1))
                              else (new_inactivity_score + INACTIVITY_SCORE_BIAS config)) in
   let new_inactivity_score = (if \<not>(is_in_inactivity_leak_f state_ctxt)
                              then (new_inactivity_score - (min new_inactivity_score (INACTIVITY_SCORE_RECOVERY_RATE config)))
                              else (new_inactivity_score))
  in new_inactivity_score)
"

lemma process_single_inactivity_update_wp[wp]: "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. inactivity_score \<le> inactivity_score + INACTIVITY_SCORE_BIAS config \<and>
                          (inactivity_score \<le> inactivity_score + INACTIVITY_SCORE_BIAS config \<longrightarrow> 
                             P (single_inactivity_update inactivity_score validator_info state_ctxt) s )))
   (bindCont (process_single_inactivity_update inactivity_score validator_info state_ctxt) c)
   Q"
  apply (unfold process_single_inactivity_update_def, rule hoare_weaken_pre, wp)
    apply (clarsimp)
  apply (fastforce)
   apply (simp only: Let_unfold)
   apply (wp)
    apply (clarsimp, wp)
   apply (clarsimp ,wp)
  apply (clarsimp)
  apply (safe)
         apply (clarsimp simp: single_inactivity_update_def Let_unfold)+
  done




definition "rewardable (v_info :: ValidatorInfo) flag_index state_ctxt \<equiv> 
              (is_unslashed_participating_index v_info flag_index) \<and>
              \<not>(is_in_inactivity_leak_f state_ctxt)"




lemma get_flag_index_delta_TIMELY_SOURCE_WEIGHT_wp[wp]: "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
   hoare_triple (lift (\<lambda>s. let unslashed_participating_increment = (unslashed_participating_increments_array_f rewards_ctxt ! 0) in
                            safe_mul TIMELY_SOURCE_WEIGHT (base_reward_f v_info) \<and> 
                            safe_mul (TIMELY_SOURCE_WEIGHT * base_reward_f v_info) unslashed_participating_increment \<and>
                            safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR \<and> 
                            active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0 \<and> 
                           (safe_mul TIMELY_SOURCE_WEIGHT (base_reward_f v_info) \<and> 
                            safe_mul (TIMELY_SOURCE_WEIGHT * base_reward_f v_info) unslashed_participating_increment \<and>
                            safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR \<and> 
                            active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0 \<longrightarrow> 
              (if rewardable v_info 0 state_ctxt then 
                 P (base_reward_f v_info * TIMELY_SOURCE_WEIGHT * unslashed_participating_increment div (active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR), 0) s
            else P (0, base_reward_f v_info * TIMELY_SOURCE_WEIGHT div WEIGHT_DENOMINATOR) s)) )) 
                (bindCont (get_flag_index_delta v_info 0 rewards_ctxt state_ctxt) c) Q"
  apply (clarsimp simp: get_flag_index_delta_def, rule hoare_weaken_pre)
   apply (wp)
   apply (clarsimp simp: , assumption)
  apply (subst if_lift)+
  apply (rule lift_mono')
  apply (simp add: TIMELY_HEAD_FLAG_INDEX_def PARTICIPATION_FLAG_WEIGHTS_def) 
  apply (intro conjI impI; clarsimp simp: Let_unfold)
   apply (clarsimp simp: rewardable_def)
   apply (intro conjI impI)
    apply (fastforce simp: safe_mul_commute mult.commute)
  apply (fastforce simp: safe_mul_commute mult.commute)
   apply (clarsimp simp: rewardable_def)
  done

lemma get_flag_index_delta_TIMELY_TARGET_WEIGHT_wp[wp]: "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
   hoare_triple (lift (\<lambda>s. let unslashed_participating_increment = (unslashed_participating_increments_array_f rewards_ctxt ! 1) in
                            safe_mul TIMELY_TARGET_WEIGHT (base_reward_f v_info) \<and> 
                            safe_mul (TIMELY_TARGET_WEIGHT * base_reward_f v_info) unslashed_participating_increment \<and>
                            safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR \<and> 
                            active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0 \<and> 
                           (safe_mul TIMELY_TARGET_WEIGHT (base_reward_f v_info) \<and> 
                            safe_mul (TIMELY_TARGET_WEIGHT * base_reward_f v_info) unslashed_participating_increment \<and>
                            safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR \<and> 
                            active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0 \<longrightarrow> 
              (if rewardable v_info 1 state_ctxt then 
                 P (base_reward_f v_info * TIMELY_TARGET_WEIGHT * unslashed_participating_increment div (active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR), 0) s
            else P (0, base_reward_f v_info * TIMELY_TARGET_WEIGHT div WEIGHT_DENOMINATOR) s)) )) 
                (bindCont (get_flag_index_delta v_info 1 rewards_ctxt state_ctxt) c) Q"
  apply (clarsimp simp: get_flag_index_delta_def, rule hoare_weaken_pre)
   apply (wp)
   apply (clarsimp simp: , assumption)
  apply (subst if_lift)+
  apply (rule lift_mono')
  apply (simp add: TIMELY_HEAD_FLAG_INDEX_def PARTICIPATION_FLAG_WEIGHTS_def) 
  apply (intro conjI impI; clarsimp simp: Let_unfold)
   apply (clarsimp simp: rewardable_def)
   apply (intro conjI impI)
    apply (fastforce simp: safe_mul_commute mult.commute)
  apply (fastforce simp: safe_mul_commute mult.commute)
   apply (clarsimp simp: rewardable_def)
  done

thm get_flag_index_delta_def

lemma get_flag_index_delta_wp_gen: "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
   hoare_triple (lift (\<lambda>s. let unslashed_participating_increment = (unslashed_participating_increments_array_f rewards_ctxt ! flag_index) in
                           let weight = PARTICIPATION_FLAG_WEIGHTS ! flag_index in
                            flag_index < length PARTICIPATION_FLAG_WEIGHTS \<and> 
                            flag_index < length (unslashed_participating_increments_array_f rewards_ctxt) \<and>
                            safe_mul weight (base_reward_f v_info) \<and> 
                            safe_mul (weight * base_reward_f v_info) unslashed_participating_increment \<and>
                            safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR \<and> 
                            active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0 \<and> 
                           (flag_index < length PARTICIPATION_FLAG_WEIGHTS \<and> 
                            flag_index < length (unslashed_participating_increments_array_f rewards_ctxt) \<and>
                            safe_mul weight (base_reward_f v_info) \<and> 
                            safe_mul (weight * base_reward_f v_info) unslashed_participating_increment \<and>
                            safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR \<and> 
                            active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0 \<longrightarrow> 
              (if rewardable v_info flag_index state_ctxt then 
                 P (base_reward_f v_info * weight * unslashed_participating_increment div (active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR), 0) s
            else (if flag_index = TIMELY_HEAD_FLAG_INDEX then P (0, 0) s else P (0, base_reward_f v_info * weight div WEIGHT_DENOMINATOR) s))) )) 
                (bindCont (get_flag_index_delta v_info flag_index rewards_ctxt state_ctxt) c) Q"
  apply (clarsimp simp: get_flag_index_delta_def, rule hoare_weaken_pre)
   apply (wp)
   apply (clarsimp simp: , assumption)
  apply (subst if_lift)+
  apply (rule lift_mono')
  apply (simp add: TIMELY_HEAD_FLAG_INDEX_def PARTICIPATION_FLAG_WEIGHTS_def) 
  apply (intro conjI impI; clarsimp simp: Let_unfold)
   apply (clarsimp simp: rewardable_def)
   apply (intro conjI impI)
    apply (fastforce simp: safe_mul_commute mult.commute)
     apply (fastforce simp: safe_mul_commute mult.commute)
    apply (clarsimp simp: rewardable_def)
   apply (clarsimp simp: rewardable_def)
   apply (fastforce simp: safe_mul_commute mult.commute)
 apply (clarsimp simp: rewardable_def)
  done

lemma get_flag_index_delta_TIMELY_HEAD_WEIGHT_wp[wp]: "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
   hoare_triple (lift (\<lambda>s. let unslashed_participating_increment = (unslashed_participating_increments_array_f rewards_ctxt ! 2) in
                            safe_mul TIMELY_HEAD_WEIGHT (base_reward_f v_info) \<and> 
                            safe_mul (TIMELY_HEAD_WEIGHT * base_reward_f v_info) unslashed_participating_increment \<and>
                            safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR \<and> 
                            active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0 \<and> 
                           (safe_mul TIMELY_HEAD_WEIGHT (base_reward_f v_info) \<and> 
                            safe_mul (TIMELY_HEAD_WEIGHT * base_reward_f v_info) unslashed_participating_increment \<and>
                            safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR \<and> 
                            active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0 \<longrightarrow> 
              (if rewardable v_info 2 state_ctxt then 
                 P (base_reward_f v_info * TIMELY_HEAD_WEIGHT * unslashed_participating_increment div (active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR), 0) s
            else P (0, 0) s)) )) 
                (bindCont (get_flag_index_delta v_info 2 rewards_ctxt state_ctxt) c) Q"
  apply (clarsimp simp: get_flag_index_delta_def, rule hoare_weaken_pre)
   apply (wp)
   apply (clarsimp simp: , assumption)
  apply (subst if_lift)+
  apply (rule lift_mono')
  apply (simp add: TIMELY_HEAD_FLAG_INDEX_def PARTICIPATION_FLAG_WEIGHTS_def) 
  apply (intro conjI impI; clarsimp simp: Let_unfold)
   apply (clarsimp simp: rewardable_def)
   apply (intro conjI impI)
    apply (fastforce simp: safe_mul_commute mult.commute)
  apply (fastforce simp: safe_mul_commute mult.commute)
   apply (clarsimp simp: rewardable_def)
  done
 

lemma range_participation_flag_weights_simp:"(local.range 0 (length PARTICIPATION_FLAG_WEIGHTS) 1) = [0,1,2]"
  apply (clarsimp simp: PARTICIPATION_FLAG_WEIGHTS_def)
  by (clarsimp simp: range.simps)


lemma hoare_case_prod[intro, wp]: "hoare_triple P (bindCont (f (fst x) (snd x)) c) Q \<Longrightarrow> 
  hoare_triple P (bindCont (case_prod f x) c) Q"
  by (clarsimp split: prod.splits)




lemma safe_mul_not_zeroI:"safe_mul (x :: u64) y \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x * y \<noteq> 0"
  by (clarsimp simp: safe_mul_def)

lemma get_inactivity_penalty_delta_wp[wp]: "
 (\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow> 
  hoare_triple (lift (\<lambda>s. let effective_balance = ValidatorInfo.effective_balance_f val_info in
                          safe_mul inactivity_score effective_balance \<and>
                          safe_mul INACTIVITY_PENALTY_QUOTIENT_ALTAIR (INACTIVITY_SCORE_BIAS config) \<and>
                   (safe_mul inactivity_score effective_balance \<longrightarrow>
                    safe_mul INACTIVITY_PENALTY_QUOTIENT_ALTAIR (INACTIVITY_SCORE_BIAS config) \<longrightarrow>
                    P (0, (if (\<not> is_unslashed_participating_index val_info TIMELY_TARGET_FLAG_INDEX) 
                             then (inactivity_score * effective_balance) div
                                  (INACTIVITY_PENALTY_QUOTIENT_ALTAIR * INACTIVITY_SCORE_BIAS config)
                          else 0)) s  ))) 
   (bindCont (get_inactivity_penalty_delta val_info inactivity_score state_ctxt) c)
   Q "
  apply (unfold get_inactivity_penalty_delta_def, rule hoare_weaken_pre, wp)
   apply (clarsimp, fastforce)
  apply (simp only: if_lift, rule lift_mono')
  apply (case_tac "\<not> is_unslashed_participating_index val_info TIMELY_TARGET_FLAG_INDEX"; clarsimp simp: Let_unfold)
  apply (intro conjI)
  apply (rule safe_mul_not_zeroI)
  using safe_mul_commute apply blast
    apply (clarsimp)
   apply (clarsimp simp: INACTIVITY_PENALTY_QUOTIENT_ALTAIR_def)
  by (clarsimp simp: mult.commute)




lemma drop_maps_to_lift: "lift (maps_to l v \<and>* R) s \<Longrightarrow> lift R s"
  apply (clarsimp simp: lift_def)
  apply (clarsimp simp: sep_conj_def maps_to_def)
  apply (rule_tac x=y in exI)
  apply (clarsimp)
  apply (clarsimp simp: point_of_plus_domain_iff)
  by (metis comp_apply point_of_plus_domain_iff sep_add_commute valid_write_write)

lemma case_simplifier_0: "(0 = TIMELY_HEAD_FLAG_INDEX \<longrightarrow> P) = True"
  by (clarsimp simp: TIMELY_HEAD_FLAG_INDEX_def)


lemma case_simplifier_1: "(1 = TIMELY_HEAD_FLAG_INDEX \<longrightarrow> P) = True"
  by (clarsimp simp: TIMELY_HEAD_FLAG_INDEX_def)


lemma case_simplifier_1': "(Suc 0 = TIMELY_HEAD_FLAG_INDEX \<longrightarrow> P) = True"
  by (clarsimp simp: TIMELY_HEAD_FLAG_INDEX_def)


lemma case_simplifier_2: "(2 = TIMELY_HEAD_FLAG_INDEX \<longrightarrow> P) = P"
  by (clarsimp simp: TIMELY_HEAD_FLAG_INDEX_def)

lemmas case_flag_simplifiers = case_simplifier_0 case_simplifier_1 case_simplifier_2 case_simplifier_1'

definition "assuming P R \<equiv> P \<and> (P \<longrightarrow> R)"





lemma rewardable_is_unslashed[simp]: "rewardable x y z \<Longrightarrow> is_unslashed_participating_index x y"
  by (clarsimp simp: rewardable_def)

lemma unrewardable_is_slashed: "\<not>rewardable x y z \<Longrightarrow> \<not>is_in_inactivity_leak_f z \<Longrightarrow> \<not>is_unslashed_participating_index x y"
  by (clarsimp simp: rewardable_def)


lemma unrewardable_is_leaking: "\<not>rewardable x y z \<Longrightarrow> is_unslashed_participating_index x y \<Longrightarrow> is_in_inactivity_leak_f z"
  apply (simp only: rewardable_def)
  by (clarsimp)

lemmas unrewardable_simps = unrewardable_is_slashed unrewardable_is_leaking

lemma rewardable_not_in_inactivity_leak[simp]: "rewardable x y z \<Longrightarrow> \<not>is_in_inactivity_leak_f z"
  apply (simp only: rewardable_def)
  by (clarsimp)

lemma par_index_zero[simp]: "PARTICIPATION_FLAG_WEIGHTS ! 0 = TIMELY_SOURCE_WEIGHT"
  by (clarsimp simp: PARTICIPATION_FLAG_WEIGHTS_def)

lemma par_index_one[simp]: "PARTICIPATION_FLAG_WEIGHTS ! (Suc 0) = TIMELY_TARGET_WEIGHT"
  by (clarsimp simp: PARTICIPATION_FLAG_WEIGHTS_def)


lemma par_index_two[simp]: "PARTICIPATION_FLAG_WEIGHTS ! 2 = TIMELY_HEAD_WEIGHT"
  by (clarsimp simp: PARTICIPATION_FLAG_WEIGHTS_def)

lemma sum_bounded_l: "x \<le> x + (y :: u64) \<longleftrightarrow> unat x + unat y < 2 ^ 64"
  apply (safe)
   apply (unat_arith, simp)
  apply (unat_arith, simp)
  done

lemma sum_bounded_r: "y \<le> x + (y :: u64) \<longleftrightarrow> unat x + unat y < 2 ^ 64"
  apply (safe)
   apply (unat_arith, simp)
  apply (unat_arith, simp)
  done

lemma unat_plus_distrib_bounded: "unat (x + y) = unat x + unat (y :: u64) \<longleftrightarrow> unat x + unat y < 2 ^ 64"
  apply (safe)
   apply (unat_arith, simp)
  using sum_bounded_l unat_plus_simple by blast


lemmas sum_bounded = sum_bounded_l sum_bounded_r

lemma chain_safe: "x \<le> x + z \<Longrightarrow> z \<ge> y \<Longrightarrow> x \<le> x + (y :: u64)"
  by (unat_arith)

lemmas safe_sum_iff = unat_plus_distrib_bounded[THEN iffD2]




lemma saturating_sub_simp1[simp]: "b \<le> a \<Longrightarrow> saturating_sub a b = a - b"
  by (clarsimp simp: saturating_sub_def)


lemma saturating_sub_simp2[simp]: "b \<ge> (a :: u64) \<Longrightarrow> saturating_sub a b = 0"
  by (clarsimp simp: saturating_sub_def)

lemma process_single_reward_and_penalty_wp[wp]: "
 (\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. let eff_balance = (ValidatorInfo.effective_balance_f validator_info);
                              rewards = map (\<lambda>n. if rewardable validator_info n state_ctxt then base_reward_f validator_info * PARTICIPATION_FLAG_WEIGHTS ! n * unslashed_participating_increments_array_f rewards_ctxt ! n div
                                                                      (active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR) else 0) [0, 1, 2];
                                          penalties = map (\<lambda>n. if \<not>(rewardable validator_info n state_ctxt) then base_reward_f validator_info * PARTICIPATION_FLAG_WEIGHTS ! n div WEIGHT_DENOMINATOR 
                                                                                                             else 0) [0,1];
                                          inactivity_penalty_delta = (if \<not> is_unslashed_participating_index validator_info TIMELY_TARGET_FLAG_INDEX then 
                                                                           inactivity_score * eff_balance div 
                                                                           (INACTIVITY_PENALTY_QUOTIENT_ALTAIR * INACTIVITY_SCORE_BIAS config) else 0);
                                          result = (if is_eligible_f validator_info then saturating_sub (balance + sum_list rewards) (sum_list penalties + inactivity_penalty_delta) else balance)
                           in  \<forall>n\<in>{0,1,2}. let unslashed_participating_increment = unslashed_participating_increments_array_f rewards_ctxt ! n;
                                                weight = PARTICIPATION_FLAG_WEIGHTS ! n              
                                         in n < length PARTICIPATION_FLAG_WEIGHTS \<and>
                                            n < length (unslashed_participating_increments_array_f rewards_ctxt) \<and>
                                            balance \<le> balance + sum_list rewards \<and>
                                            sum_list (map unat rewards) + unat inactivity_penalty_delta  < 2^64 \<and> 
                                            (sum_list (map unat penalties) + unat inactivity_penalty_delta) < 2 ^ 64 \<and>
                                            safe_mul weight (base_reward_f validator_info) \<and>
                                            safe_mul inactivity_score eff_balance \<and>
                                            safe_mul (weight * base_reward_f validator_info) unslashed_participating_increment \<and>
                                            safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR \<and>
                                            safe_mul INACTIVITY_PENALTY_QUOTIENT_ALTAIR (INACTIVITY_SCORE_BIAS config) \<and>
                                            active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0 \<and>
                                            (n < length PARTICIPATION_FLAG_WEIGHTS \<and> safe_mul inactivity_score eff_balance \<and>
                                             n < length (unslashed_participating_increments_array_f rewards_ctxt) \<and>
                                             safe_mul weight (base_reward_f validator_info) \<and> safe_mul INACTIVITY_PENALTY_QUOTIENT_ALTAIR (INACTIVITY_SCORE_BIAS config) \<and>
                                             safe_mul (weight * base_reward_f validator_info) unslashed_participating_increment \<and>
                                             safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR \<and> active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0 \<longrightarrow> (P (result)) s)))
  (bindCont (process_single_reward_and_penalty balance inactivity_score validator_info rewards_ctxt state_ctxt) c)
   Q"
  apply (unfold process_single_reward_and_penalty_def, rule hoare_weaken_pre)
   apply (simp only: bindCont_assoc[symmetric])
   apply (rule if_wp)
   apply (simp only: bindCont_assoc[symmetric])
    apply (rule alloc_wp)
  apply (rule alloc_wp)
    apply (simp only: Let_unfold)
    apply (clarsimp simp: bindCont_return)
    apply (simp only: bindCont_assoc[symmetric])
    apply (rule mapM_wp_foldr'[where g="\<lambda>_. ()"])
     apply (simp only: bindCont_assoc[symmetric])
     apply (rule get_flag_index_delta_wp_gen)
     apply (simp only: bindCont_assoc[symmetric] | rule read_beacon_wp_ex add_wp' write_beacon_wp' wp | assumption)+
  apply (simp only: if_lift TIMELY_TARGET_FLAG_INDEX_def TIMELY_HEAD_FLAG_INDEX_def TIMELY_SOURCE_FLAG_INDEX_def)
  apply (simp only: Let_unfold)
  apply (clarsimp)
   apply (unfold range_participation_flag_weights_simp[simplified])
   apply (simp only: foldr.simps case_flag_simplifiers)
  apply (intro conjI impI; clarsimp simp: Let_unfold)
  apply ( (sep_cancel | intro conjI impI allI | clarsimp simp:  | (rule exI, sep_cancel+) | (erule sep_curry[rotated, where P="P result" for result]))+,
       (fastforce simp: sum_bounded safe_sum_iff add.assoc | fastforce simp: sum_bounded safe_sum_iff | (rule exI, intro conjI impI) | clarsimp simp: unrewardable_simps )?)+
  done


lemma process_single_inactivity_update_wp'[wp]:
   "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
   hoare_triple (lift (\<lambda>s. let result = (if (is_unslashed_participating_index validator_info TIMELY_TARGET_FLAG_INDEX)
                                             then (saturating_sub score 1)
                                             else (score + INACTIVITY_SCORE_BIAS config));
                               result = (if \<not>(is_in_inactivity_leak_f state_ctxt) 
                                             then (saturating_sub result (INACTIVITY_SCORE_RECOVERY_RATE config))
                                             else (result));
                               result = (if \<not>(is_eligible_f validator_info) then score else result) in
                               score \<le> score + INACTIVITY_SCORE_BIAS config \<and>  P result s)) 
    (bindCont (process_single_inactivity_update score validator_info state_ctxt) c) Q"
  apply (unfold process_single_inactivity_update_def, rule hoare_weaken_pre, wp)
    apply (fastforce)
   apply (wp)
    apply (fastforce)
   apply (wp)
   apply (fastforce)
  apply (clarsimp simp: Let_unfold)
  apply (intro conjI impI allI; clarsimp simp: saturating_sub_def)
    apply (intro conjI impI allI; clarsimp simp: saturating_sub_def)
  apply (intro conjI impI allI; clarsimp simp: saturating_sub_def)
  apply (intro conjI impI allI; clarsimp simp: saturating_sub_def)
  done

lemma process_single_slashing[wp]:
   "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
   hoare_triple (lift (\<lambda>s. let effective_balance = Validator.effective_balance_f validator in
                           let effective_balance_increment = (effective_balance div EFFECTIVE_BALANCE_INCREMENT config) in
                           let result = (if Validator.slashed_f validator \<and> 
                                            target_withdrawable_epoch_f slashings_ctxt = withdrawable_epoch_f validator
                                          then
                                             saturating_sub balance (effective_balance_increment * adjusted_total_slashing_balance_f slashings_ctxt div total_active_balance_f progressive_balances *
                                             EFFECTIVE_BALANCE_INCREMENT config)
                                          else balance) in 
                        safe_mul (adjusted_total_slashing_balance_f slashings_ctxt) effective_balance_increment \<and>
                        total_active_balance_f progressive_balances \<noteq> 0  \<and>
                         safe_mul (EFFECTIVE_BALANCE_INCREMENT config)
                         (effective_balance_increment * adjusted_total_slashing_balance_f slashings_ctxt div total_active_balance_f progressive_balances) \<and>
                        
                         (safe_mul (adjusted_total_slashing_balance_f slashings_ctxt) effective_balance_increment \<and>
                           total_active_balance_f progressive_balances \<noteq> 0  \<and>
                           safe_mul (EFFECTIVE_BALANCE_INCREMENT config)
                          (effective_balance_increment * adjusted_total_slashing_balance_f slashings_ctxt div total_active_balance_f progressive_balances) \<longrightarrow>
                          P result s)))
    (bindCont (process_single_slashing balance validator slashings_ctxt progressive_balances) c) Q"
  apply (unfold process_single_slashing_def, rule hoare_weaken_pre, wp)
   apply (fastforce)
  apply (clarsimp simp:  Let_unfold)
  apply (intro conjI impI allI; clarsimp simp: saturating_sub_def)
    apply (intro conjI impI allI; clarsimp simp: saturating_sub_def)
  done


definition "(total_active_balance :: (ProgressiveBalancesCache, u64) lens) = Lens total_active_balance_f (\<lambda>x v. x\<lparr>total_active_balance_f := v\<rparr>) (\<lambda>_. True)"


definition "updated_nepb epb val flags future_epoch n =
          (let new_effective_balance = Validator.effective_balance_f val in
           epb\<lparr>total_active_balance_f :=
           if (is_active_validator val future_epoch) then total_active_balance_f epb + new_effective_balance else total_active_balance_f epb ,
           previous_epoch_flag_attesting_balances_f :=
             if slashed_f val then previous_epoch_flag_attesting_balances_f epb else
             map (\<lambda>x. if has_flag flags x  then
                         if (new_effective_balance > n) then previous_epoch_flag_attesting_balances_f epb ! x + (new_effective_balance - n)
                                                        else previous_epoch_flag_attesting_balances_f epb ! x - (n - new_effective_balance)
                      else previous_epoch_flag_attesting_balances_f epb ! x)
              (local.range 0 (length (participation_flag_weights flags)) 1) \<rparr>)"


lemma get_dom_inter_none: "get l x = None \<Longrightarrow> dom (get l) \<inter> {x} = {}"
  by (safe; clarsimp?)

lemma if_app: "(if B then f else g) x = (if B then f x else g x)"
  apply (clarsimp)
  done

lemma state_splitI: "(\<Squnion>x. \<tau> {x} ; a) \<le> b \<Longrightarrow> a \<le> b"
  by (metis NONDET_seq_distrib Nondet_test_nil seq_nil_left)

lemma get_dom_inter: "get l x = Some y \<Longrightarrow> dom (get l) \<inter> {x} = {x}"
  by (safe; clarsimp?)



lemma inter_collect_r: "A \<inter> Collect B = Collect (\<lambda>x. x \<in> A \<and> B x)"
  by (safe; clarsimp)

lemma neg_collect: "- Collect P = Collect (- P)"
  by (safe; clarsimp?)




lemma set_of_range_simp[simp]: "list.set (local.range m n (Suc 0)) = {i. i \<ge> m \<and> i < n}"
  apply (induct \<open>n - m\<close> arbitrary: m n; clarsimp? )
    apply (subst range.simps(2))
   apply (clarsimp)
  apply (case_tac n; clarsimp)
    apply (subst range.simps(2))
  apply (clarsimp)
  apply (atomize)
  apply (erule_tac x=m in allE)
  apply (erule_tac x=nat in allE)
  apply (drule mp)
   apply (simp add: Suc_diff_le)
  apply (intro set_eqI iffI; clarsimp)
  apply (elim disjE; clarsimp?)
  done
  

lemma update_next_epoch_progressive_balances_wp[wp]: 
  defines pre_def: "precondition old_effective_balance cep validator v \<equiv> total_active_balance_f v \<le> total_active_balance_f v + Validator.effective_balance_f validator \<and> 
                           (\<forall>n\<in>{n. n < length (participation_flag_weights cep) \<and> has_flag cep n}.
   (if Validator.effective_balance_f validator > old_effective_balance
     then previous_epoch_flag_attesting_balances_f v ! n \<le> previous_epoch_flag_attesting_balances_f v ! n + (Validator.effective_balance_f validator - old_effective_balance)
     else old_effective_balance - Validator.effective_balance_f validator \<le> previous_epoch_flag_attesting_balances_f v ! n)) "
  shows "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>                                                 
   hoare_triple (lift (\<lambda>s. precondition old_effective_balance cep validator v \<and> (precondition old_effective_balance cep validator v \<longrightarrow>
  (next_epoch_progressive_balances \<mapsto>\<^sub>l v \<and>* ((next_epoch_progressive_balances \<mapsto>\<^sub>l updated_nepb v validator cep future_epoch old_effective_balance)  \<longrightarrow>* P ())) s)))
       (bindCont (update_next_epoch_progressive_balances future_epoch next_epoch_progressive_balances validator cep old_effective_balance) next) Q"
  apply (clarsimp simp: word_unsigned_add_def Let_unfold ) 
  apply (clarsimp simp: update_next_epoch_progressive_balances_def , rule hoare_weaken_pre)
   apply (wp | fastforce)+
  apply (intro lift_mono' le_funI)
  apply (clarsimp, intro exI conjI impI; clarsimp simp: pre_def)
  apply (sep_cancel)+
         apply (intro conjI impI exI; clarsimp simp: pre_def)
  apply (sep_cancel)+
     apply (intro exI conjI impI; clarsimp?)
       apply order
     apply (subst mapM_is_sequence_map)

  apply (rule_tac I="(next_epoch_progressive_balances \<mapsto>\<^sub>l v\<lparr>total_active_balance_f := total_active_balance_f v + Validator.effective_balance_f validator\<rparr>)"
           and P="\<lambda>x s. sep_empty s \<and> (has_flag cep x \<longrightarrow> previous_epoch_flag_attesting_balances_f v ! x \<le> previous_epoch_flag_attesting_balances_f v ! x + (Validator.effective_balance_f validator - old_effective_balance))"
           and Q="\<lambda>x s. sep_empty s \<and>  (has_flag cep x \<longrightarrow> previous_epoch_flag_attesting_balances_f v ! x \<le> previous_epoch_flag_attesting_balances_f v ! x + (Validator.effective_balance_f validator - old_effective_balance))"
           and g="\<lambda>x. if has_flag cep x then previous_epoch_flag_attesting_balances_f v ! x + (Validator.effective_balance_f validator - old_effective_balance)
                      else previous_epoch_flag_attesting_balances_f v ! x " in sequenceI_rewriting)
  apply (intro exI conjI impI exI)
       apply (sep_cancel)+
       apply (clarsimp simp: foldr_pure)
        apply (sep_mp, assumption)
apply (sep_cancel)+
       apply (clarsimp simp: foldr_pure)
         apply (sep_mp, assumption)
       apply (clarsimp simp: foldr_pure)
      apply (sep_cancel)+
  apply (rule exI, sep_cancel)+
         apply (clarsimp simp: updated_nepb_def Let_unfold split: if_splits cong: if_cong)
      apply (sep_cancel)+
         apply (clarsimp simp: updated_nepb_def Let_unfold split: if_splits cong: if_cong)
     apply (sep_mp, assumption)
  apply (sep_cancel)+
     apply (subst mapM_is_sequence_map)
       apply (intro conjI impI)
        apply order
  apply (clarsimp)
apply (rule_tac I="(next_epoch_progressive_balances \<mapsto>\<^sub>l v\<lparr>total_active_balance_f := total_active_balance_f v + Validator.effective_balance_f validator\<rparr>)"
           and P="\<lambda>x s. sep_empty s \<and> (has_flag cep x \<longrightarrow> old_effective_balance - Validator.effective_balance_f validator  \<le> previous_epoch_flag_attesting_balances_f v ! x)"
           and Q="\<lambda>x s. sep_empty s \<and> (has_flag cep x \<longrightarrow> old_effective_balance - Validator.effective_balance_f validator \<le> previous_epoch_flag_attesting_balances_f v ! x)"
           and g="\<lambda>x. if has_flag cep x then previous_epoch_flag_attesting_balances_f v ! x - (old_effective_balance - Validator.effective_balance_f validator)
                      else previous_epoch_flag_attesting_balances_f v ! x " in sequenceI_rewriting)
      apply (clarsimp)
  apply (intro exI conjI impI; clarsimp?)
       apply (sep_cancel)+
  apply (intro conjI impI; clarsimp?)
  apply (sep_mp)
       apply (clarsimp)
      apply (clarsimp)
     apply (clarsimp simp: foldr_pure)
    apply (sep_cancel)+
  apply (rule exI, sep_cancel+)
  apply (clarsimp)
    apply (clarsimp simp: updated_nepb_def Let_unfold split: if_splits cong: if_cong, sep_mp, clarsimp)
   apply (sep_cancel)+
    apply (clarsimp simp: updated_nepb_def Let_unfold split: if_splits cong: if_cong, sep_mp, clarsimp)
  apply (sep_cancel+)
  apply (rule_tac x=v in exI, (sep_cancel+)?)
  apply (intro conjI impI)
     apply (sep_cancel)+
  apply (intro conjI impI; clarsimp)
  apply (order)
     apply (subst mapM_is_sequence_map)
apply (rule_tac I="(next_epoch_progressive_balances \<mapsto>\<^sub>l v)"
           and P="\<lambda>x s. sep_empty s \<and> (has_flag cep x \<longrightarrow> previous_epoch_flag_attesting_balances_f v ! x \<le> previous_epoch_flag_attesting_balances_f v ! x + (Validator.effective_balance_f validator - old_effective_balance))"
           and Q="\<lambda>x s. sep_empty s \<and>  (has_flag cep x \<longrightarrow> previous_epoch_flag_attesting_balances_f v ! x \<le> previous_epoch_flag_attesting_balances_f v ! x + (Validator.effective_balance_f validator - old_effective_balance))"
           and g="\<lambda>x. if has_flag cep x then previous_epoch_flag_attesting_balances_f v ! x + (Validator.effective_balance_f validator - old_effective_balance)
                      else previous_epoch_flag_attesting_balances_f v ! x " in sequenceI_rewriting)
       apply (intro exI impI conjI,  (sep_cancel)+)
      apply (clarsimp simp: foldr_pure)
      apply (sep_mp)
      apply (simp add: add_diff_eq diff_diff_eq2)
     apply (clarsimp simp: foldr_pure)
     apply (clarsimp simp: foldr_pure pre_def)

  apply (sep_cancel)+

     apply (intro conjI impI ballI exI allI)
     apply (sep_cancel)+
         apply (clarsimp simp: updated_nepb_def Let_unfold split: if_splits cong: if_cong, sep_mp, clarsimp)
    apply (sep_cancel)+
         apply (clarsimp simp: updated_nepb_def Let_unfold split: if_splits cong: if_cong, sep_mp, clarsimp)
   apply (sep_cancel)+
   apply (intro conjI impI; clarsimp)
    apply (order)
     apply (subst mapM_is_sequence_map)

apply (rule_tac I="(next_epoch_progressive_balances \<mapsto>\<^sub>l v)"
           and P="\<lambda>x s. sep_empty s \<and> (has_flag cep x \<longrightarrow> old_effective_balance - Validator.effective_balance_f validator  \<le> previous_epoch_flag_attesting_balances_f v ! x)"
           and Q="\<lambda>x s. sep_empty s \<and> (has_flag cep x \<longrightarrow> old_effective_balance - Validator.effective_balance_f validator \<le> previous_epoch_flag_attesting_balances_f v ! x)"
           and g="\<lambda>x. if has_flag cep x then previous_epoch_flag_attesting_balances_f v ! x - (old_effective_balance - Validator.effective_balance_f validator)
                      else previous_epoch_flag_attesting_balances_f v ! x " in sequenceI_rewriting)
      apply (clarsimp)
      apply (intro exI conjI impI; clarsimp?)
       apply (sep_cancel)+
       apply (intro conjI impI; clarsimp)

       apply (sep_mp)
  apply (simp add: add.commute diff_add_eq diff_diff_eq2)
      apply (clarsimp)
   apply (clarsimp simp: foldr_pure)
   apply (sep_cancel)+
  apply (rule exI, sep_cancel+)
         apply (clarsimp simp: updated_nepb_def Let_unfold split: if_splits cong: if_cong, sep_mp, clarsimp)
     apply (sep_cancel)+
  by (clarsimp simp: updated_nepb_def Let_unfold split: if_splits cong: if_cong, sep_mp, clarsimp)

lemma x_mod_y_le_x[simp]:
  "x mod y \<le> (x :: u64)"
  by (metis (no_types, lifting) linorder_le_cases mod_by_0 mod_word_less order_le_less_trans word_gt_0 word_mod_less_divisor)

lemma compute_activation_exit_epoch[wp]:
"(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> hoare_triple (\<lless>\<lambda>s.  epoch_to_u64 epoch \<le> epoch_to_u64 epoch + 1 \<and> (epoch_to_u64 epoch + 1) \<le> (epoch_to_u64 epoch + 1) + epoch_to_u64 MAX_SEED_LOOKAHEAD \<and>
             (epoch_to_u64 epoch \<le> epoch_to_u64 epoch + 1 \<longrightarrow>
              (epoch_to_u64 epoch + 1) \<le>  (epoch_to_u64 epoch + 1) + epoch_to_u64 MAX_SEED_LOOKAHEAD \<longrightarrow>
               P (Epoch (epoch_to_u64 epoch + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD)) s)\<then>) (bindCont (compute_activation_exit_epoch epoch) next) Q"
  apply (clarsimp simp: compute_activation_exit_epoch_def epoch_unsigned_add_def, rule hoare_weaken_pre)
  by (simp only: bindCont_assoc[symmetric] epoch_unsigned_add_def | rule read_beacon_wp_ex add_wp' write_beacon_wp' wp | fastforce)+


definition "record_exit x epoch v\<equiv> x\<lparr>exit_epoch_counts_f := (exit_epoch_counts_f x)(epoch \<mapsto> v + 1)\<rparr>"
                              

lemma record_validator_exit_wp[wp]:"(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> 
         hoare_triple (lift (\<lambda>s. let v = case_option 0 id (exit_epoch_counts_f x epoch)
  in v \<le> v + 1 \<and>
  (exit_cache \<mapsto>\<^sub>l x \<and>* (exit_cache \<mapsto>\<^sub>l record_exit x epoch v \<longrightarrow>* P ())) s)) (bindCont (record_validator_exit exit_cache epoch) next) Q "
  apply (unfold record_validator_exit_def)
  apply (rule hoare_weaken_pre)
   apply (simp only: bindCont_assoc[symmetric] record_exit_def epoch_unsigned_add_def | rule read_beacon_wp_ex add_wp' write_beacon_wp' wp | fastforce)+
  apply (clarsimp)
  apply (rule_tac x=x in exI)
  apply (intro conjI impI; clarsimp?)
   apply (sep_cancel)+
   apply (rule exI, sep_cancel+)
   apply (sep_mp; clarsimp)
  apply (erule contrapos_np; clarsimp)
  apply (sep_cancel)+
  apply (rule exI, sep_cancel+)
   apply (sep_mp; clarsimp)
  done


definition "new_exit_epoch ec state_ctxt \<equiv>
         let next_epoch = (current_epoch_f state_ctxt) + 1 in
         let exit_queue_epoch = max (get_max_exit_epoch ec) (next_epoch + MAX_SEED_LOOKAHEAD) in
         let exit_queue_churn = get_exit_queue_churn ec exit_queue_epoch in
         exit_queue_epoch  + (if exit_queue_churn \<ge> churn_limit_f state_ctxt then 1 else Epoch 0)"

lemma epoch_simp[simp]: "Epoch (epoch_to_u64 e) = e"
  by (case_tac e; clarsimp?)

definition "initiate_exit_when_far_future ex state_ctxt ec we vref \<equiv> if ex \<noteq> FAR_FUTURE_EPOCH then  (lcomp withdrawable_epoch vref \<mapsto>\<^sub>l we \<and>* lcomp exit_epoch vref \<mapsto>\<^sub>l ex \<and>* exit_cache \<mapsto>\<^sub>l ec) else
                                               (lcomp exit_epoch vref \<mapsto>\<^sub>l new_exit_epoch  ec state_ctxt \<and>* lcomp withdrawable_epoch vref \<mapsto>\<^sub>l new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) \<and>* 
  exit_cache \<mapsto>\<^sub>l record_exit ec (new_exit_epoch ec state_ctxt) (case_option 0 id (exit_epoch_counts_f ec (new_exit_epoch ec state_ctxt))))"
lemma initiate_validator_exit_fast_wp[wp]:
  defines precon: "pre state_ctxt x \<equiv> (\<forall>e\<in>dom(exit_epoch_counts_f x). the (exit_epoch_counts_f x e) \<le> the(exit_epoch_counts_f x e) + 1 ) \<and>
                                     epoch_to_u64 (current_epoch_f state_ctxt) \<le> epoch_to_u64 (current_epoch_f state_ctxt) + 1 \<and>
                                     epoch_to_u64 (current_epoch_f state_ctxt) + 1 \<le> epoch_to_u64 (current_epoch_f state_ctxt) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD \<and>
                                     epoch_to_u64 (max (get_max_exit_epoch x) (Epoch (epoch_to_u64 (current_epoch_f state_ctxt) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD))) \<le> epoch_to_u64 (max (get_max_exit_epoch x) (Epoch (epoch_to_u64 (current_epoch_f state_ctxt) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD))) + 1 \<and>
                                     epoch_to_u64 (max (get_max_exit_epoch x) (Epoch (epoch_to_u64 (current_epoch_f state_ctxt) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD))) + 1 \<le> epoch_to_u64 (max (get_max_exit_epoch x) (Epoch (epoch_to_u64 (current_epoch_f state_ctxt) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD))) + 1 + MIN_VALIDATOR_WITHDRAWABILITY_DELAY config"
  shows
"(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> hoare_triple (lift (\<lambda>s. pre state_ctxt ec \<and> 
  (lcomp withdrawable_epoch vref \<mapsto>\<^sub>l we \<and>* lcomp exit_epoch vref \<mapsto>\<^sub>l ex \<and>* exit_cache \<mapsto>\<^sub>l ec \<and>* 
 (initiate_exit_when_far_future ex state_ctxt ec we vref \<longrightarrow>* P ())  ) s))
 (bindCont (initiate_validator_exit_fast vref exit_cache state_ctxt) next) Q"
  apply (clarsimp simp: initiate_validator_exit_fast_def precon, rule hoare_weaken_pre)
   apply (simp only: bindCont_assoc[symmetric] epoch_unsigned_add_def | rule read_beacon_wp_ex add_wp' write_beacon_wp' wp | fastforce)+
  apply (clarsimp)
  apply (rule exI, sep_cancel+)
  apply (rule_tac x=ec in exI)
  apply (intro impI conjI; clarsimp simp: initiate_exit_when_far_future_def)
     apply (sep_cancel)+
  apply (rule exI, sep_cancel+)
  apply (rule exI)

     apply (sep_cancel)+
  apply (rule_tac x=we in exI)

      apply (sep_cancel)+
     apply (intro impI conjI; clarsimp?)
      apply (sep_cancel)+
       apply (clarsimp simp: Let_unfold)
     apply (intro impI conjI; clarsimp?)
        defer
       apply (sep_cancel)+
       apply (clarsimp)
       apply (subgoal_tac "Epoch (epoch_to_u64 (max (get_max_exit_epoch ec) (Epoch (epoch_to_u64 (current_epoch_f state_ctxt) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD))) + 1 ) = new_exit_epoch ec state_ctxt")
       apply (subgoal_tac "Epoch (epoch_to_u64 (max (get_max_exit_epoch ec) (Epoch (epoch_to_u64 (current_epoch_f state_ctxt) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD))) + 1 +  MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) =new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config)")

  apply (clarsimp)
         apply (sep_mp, clarsimp)
        apply (clarsimp)
        apply (drule sym, clarsimp) back
  apply (clarsimp simp: plus_Epoch_def one_Epoch_def)

        apply (clarsimp simp: new_exit_epoch_def)
       apply (clarsimp simp: plus_Epoch_def one_Epoch_def)
      apply (sep_cancel)+
      defer
      apply (sep_cancel)+
  apply (rule exI, sep_cancel+)
  apply (rule exI, sep_cancel+)
  apply (rule exI, sep_cancel+)
      apply (intro conjI impI; clarsimp?)
       defer
      apply (sep_cancel)+
       apply (clarsimp simp: Let_unfold)
     apply (intro impI conjI; clarsimp?)
        defer
        apply (sep_cancel)+
        apply (subgoal_tac "max (get_max_exit_epoch ec) (Epoch (epoch_to_u64 (current_epoch_f state_ctxt) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD)) = new_exit_epoch ec state_ctxt "; clarsimp)
         apply (subgoal_tac "Epoch (epoch_to_u64 (new_exit_epoch ec state_ctxt) + MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) = new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config)"; clarsimp?)
          apply (sep_mp, clarsimp)
         apply (clarsimp simp: plus_Epoch_def)
 apply (clarsimp simp: new_exit_epoch_def)
        apply (clarsimp simp: plus_Epoch_def one_Epoch_def)
       apply (sep_cancel)+
       apply (sep_mp)
      defer
  apply (clarsimp split: option.splits)
       apply (simp add: new_exit_epoch_def one_Epoch_def plus_Epoch_def)
      apply (metis domI option.sel)
     apply (sep_mp, clarsimp)
    apply (smt (verit, ccfv_threshold) add.commute olen_add_eqv word_plus_mono_right2)

  apply (clarsimp split: option.splits)
       apply (simp add: new_exit_epoch_def one_Epoch_def plus_Epoch_def)
   apply (metis domI option.sel)
  by (assumption)



lemma sep_expand_allS: "((ALLS x. P x) \<and>* Q) s \<Longrightarrow> (ALLS x. (P x \<and>* Q)) s"
  apply (clarsimp simp: sep_conj_def)
  by (blast)


abbreviation "maybe m d \<equiv> (case_option d id m)"

lemma get_exit_epoch_simp: "get exit_epoch val = exit_epoch_f val"
  by (clarsimp simp: exit_epoch_def)


lemma get_withdrawable_epoch_simp: "get withdrawable_epoch val = withdrawable_epoch_f val"
  by (clarsimp simp: withdrawable_epoch_def)



lemma get_activation_epoch_simp: "get activation_epoch val = activation_epoch_f val"
  by (clarsimp simp:activation_epoch_def)

lemmas get_val_fields_simps = get_exit_epoch_simp get_activation_epoch_simp get_withdrawable_epoch_simp


abbreviation (input) "queued val_info aq \<equiv> index_f val_info \<in> List.set aq"
abbreviation (input) "ready_to_eject validator state_ctxt \<equiv> exit_epoch_f validator = FAR_FUTURE_EPOCH \<and>
  (is_active_validator validator (current_epoch_f state_ctxt) \<and> Validator.effective_balance_f validator \<le> EJECTION_BALANCE config)"



lemma exit_epoch_get_simp[simp]: "get exit_epoch val = exit_epoch_f val"
  by (clarsimp simp: exit_epoch_def)

lemma process_single_registry_update_wp[wp]:
"(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> 
  hoare_triple (lift (\<lambda>s.  (current_epoch_f state_ctxt) \<le> (current_epoch_f state_ctxt) + 1 \<and>
                           (current_epoch_f state_ctxt) + 1 \<le> (current_epoch_f state_ctxt) + 1 +  MAX_SEED_LOOKAHEAD \<and>                         
       (\<exists>val ec x.  max (get_max_exit_epoch ec) ((current_epoch_f state_ctxt) + 1 +  MAX_SEED_LOOKAHEAD) \<le> max (get_max_exit_epoch ec) ((current_epoch_f state_ctxt) + 1 +  MAX_SEED_LOOKAHEAD) + 1 \<and>
                     max (get_max_exit_epoch ec) ((current_epoch_f state_ctxt) + 1 +  MAX_SEED_LOOKAHEAD) + 1 \<le> max (get_max_exit_epoch ec) ((current_epoch_f state_ctxt) + 1 +  MAX_SEED_LOOKAHEAD) + 1 + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) \<and> 
         (\<forall>n\<in>ran(exit_epoch_counts_f ec). n \<le> n + 1) \<and> 
        (vref \<mapsto>\<^sub>l val \<and>* exit_cache \<mapsto>\<^sub>l ec \<and>* next_epoch_aq \<mapsto>\<^sub>l x \<and>*
        (let val' = val\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue val then (current_epoch_f state_ctxt) + 1 else activation_eligibility_epoch_f val\<rparr> in 
            vref \<mapsto>\<^sub>l val'\<lparr>exit_epoch_f := (if ready_to_eject val' state_ctxt then new_exit_epoch ec state_ctxt else exit_epoch_f val') ,
              withdrawable_epoch_f := if ready_to_eject val' state_ctxt then new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) else  withdrawable_epoch_f val',
              activation_epoch_f := if queued val_info aq then (current_epoch_f state_ctxt) + 1 +  MAX_SEED_LOOKAHEAD else activation_epoch_f val' \<rparr> \<and>*
         next_epoch_aq \<mapsto>\<^sub>l 
             add_if_could_be_eligible_for_activation x (index_f val_info) (val') (next_epoch_f state_ctxt) \<and>* 
         exit_cache \<mapsto>\<^sub>l 
             (if ready_to_eject val' state_ctxt then record_exit ec (new_exit_epoch ec state_ctxt) (maybe (exit_epoch_counts_f ec (new_exit_epoch ec state_ctxt)) 0) else ec) \<longrightarrow>* P ()))s))) 
     (bindCont (process_single_registry_update vref val_info ex_cache aq 
                                         next_epoch_aq state_ctxt) next) Q"
  apply (rule hoare_assert_stateI)
  apply (simp only: lift_pure_conj)
  apply (elim conjE)
  apply (drule lift_exE, clarsimp)+

  apply (unfold process_single_registry_update_def epoch_unsigned_add_def,  rule hoare_weaken_pre, 
    (simp only: bindCont_assoc[symmetric] epoch_unsigned_add_def | rule read_beacon_wp_ex add_wp' write_beacon_wp' wp | fastforce)+)
  apply ( intro le_funI)
  apply (clarsimp)
  apply (rule_tac x=val in exI)

   apply (intro conjI impI; clarsimp?)
    apply (sep_cancel)+
          apply (intro conjI impI; (clarsimp simp: less_eq_Epoch_def one_Epoch_def plus_Epoch_def)?)
    apply (rule_tac x=val in exI)
    apply (sep_cancel)+


 apply (rule_tac x="val\<lparr>activation_eligibility_epoch_f := Epoch (epoch_to_u64 (current_epoch_f state_ctxt) + 1)\<rparr>" in exI)
    apply (intro conjI impI; clarsimp?)
           apply (sep_cancel)+
           apply (intro conjI impI; (clarsimp simp: less_eq_Epoch_def one_Epoch_def plus_Epoch_def)?)
            defer
          apply (clarsimp simp: Let_unfold plus_Epoch_def one_Epoch_def)
         defer
  defer
         apply (clarsimp simp only: sep_conj_ac)
         apply (sep_drule split_validator)

      apply (sep_cancel)+
    apply (rule exI, sep_cancel+)
          apply (rule exI, sep_cancel+)
         apply (clarsimp simp: Let_unfold plus_Epoch_def one_Epoch_def)

  apply (sep_drule (direct) sep_expand_allS)+
          apply (erule_tac x="if exit_epoch_f val = FAR_FUTURE_EPOCH then new_exit_epoch ec state_ctxt else exit_epoch_f val" in allE)
  apply (sep_drule (direct) sep_expand_allS)+
  apply (erule_tac x="if exit_epoch_f val = FAR_FUTURE_EPOCH then new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) else withdrawable_epoch_f val" in allE)
  apply (sep_drule (direct) sep_expand_allS)+
           apply (erule_tac x="Epoch (epoch_to_u64 (current_epoch_f state_ctxt) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD)" in allE)

         apply (clarsimp simp: initiate_exit_when_far_future_def)
         apply (clarsimp split: if_splits)
          apply (clarsimp simp: get_exit_epoch_simp get_withdrawable_epoch_simp)

          apply (sep_mp, assumption)

  apply (sep_mp, assumption)
               apply (sep_cancel)+
          apply (clarsimp simp: Let_unfold plus_Epoch_def one_Epoch_def)

      apply (sep_drule split_validator[where vref=vref], clarsimp simp: sep_conj_ac)
  apply (sep_select_asm 3)
  apply (clarsimp simp only: sep_conj_ac)
            apply (rule exI, sep_cancel+)
         apply (rule exI, sep_cancel+)
          apply (sep_drule spec[where x="(if ready_to_eject val state_ctxt then new_exit_epoch ec state_ctxt else exit_epoch_f val)" for val ec])
          apply (sep_drule spec[where x="if ready_to_eject val state_ctxt then new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) else  withdrawable_epoch_f val" for val ec])
          apply (sep_drule spec[where x="Epoch (epoch_to_u64 (current_epoch_f state_ctxt) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD)"])
          apply (clarsimp simp: get_exit_epoch_simp get_withdrawable_epoch_simp)
      apply (sep_mp)
      apply (clarsimp split: if_splits)
           apply (sep_mp)
           apply (drule mp)
  apply blast
           apply (erule notE)
           apply (blast)
          apply (clarsimp)
          apply (clarsimp simp: get_exit_epoch_simp get_withdrawable_epoch_simp)
         apply (sep_mp)
         apply (fastforce simp: is_active_validator_def)

          apply (clarsimp simp: get_exit_epoch_simp get_withdrawable_epoch_simp)
         apply (sep_mp, assumption)
               apply (clarsimp)
     apply (sep_cancel)+
       apply (intro conjI impI; (clarsimp simp: one_Epoch_def plus_Epoch_def)?)
  defer
      apply (metis epoch_to_u64.simps max_def)
               apply (sep_cancel)+

     apply (clarsimp simp: Let_unfold)
  apply (sep_drule split_validator[where vref=vref], clarsimp simp: sep_conj_ac)

        apply (sep_cancel)+

     apply (rule_tac x=x in exI)
        apply (sep_cancel)+
  apply (clarsimp split: if_splits)
       apply (sep_drule spec[where x="( new_exit_epoch ec state_ctxt)" for val ec])
          apply (sep_drule spec[where x="new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config)" for val ec])
     apply (sep_drule spec)+
         apply (clarsimp simp: sep_conj_ac)

     apply (sep_mp)

        apply (clarsimp simp: get_activation_epoch_simp)
 apply (clarsimp simp: initiate_exit_when_far_future_def)
         apply (clarsimp simp: sep_conj_ac)
  apply (sep_mp)
          apply (clarsimp simp: get_exit_epoch_simp get_withdrawable_epoch_simp)

          apply (sep_mp, assumption)

        apply (sep_mp, clarsimp)
   apply (clarsimp simp: get_activation_epoch_simp)
        apply (clarsimp simp: initiate_exit_when_far_future_def)
  apply (sep_drule spec)+
          apply (clarsimp simp: get_exit_epoch_simp get_withdrawable_epoch_simp sep_conj_ac)
        apply (sep_mp, clarsimp)
  apply (sep_mp, assumption)
      apply (sep_cancel)+
    apply (rule_tac x=x in exI)
  apply (clarsimp simp: Let_unfold)
    apply (sep_cancel)+
    apply (clarsimp split: if_splits)
    apply (sep_mp, assumption)
  apply (sep_cancel)+

              apply (rule_tac x=val in exI)
              apply (intro conjI impI)
          apply (clarsimp)
          apply (sep_cancel)+
      apply (intro conjI impI; (clarsimp simp: one_Epoch_def plus_Epoch_def less_eq_Epoch_def)?)
             defer
        defer
           apply (sep_cancel)+
  apply (sep_drule split_validator[where vref=vref], clarsimp simp: sep_conj_ac)
           apply (sep_cancel)+
         apply (rule exI, sep_cancel+)
            apply (rule exI, sep_cancel+)
 apply (sep_drule spec[where x="(if ready_to_eject val state_ctxt then new_exit_epoch ec state_ctxt else exit_epoch_f val)" for val ec])
          apply (sep_drule spec[where x="if ready_to_eject val state_ctxt then new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) else  withdrawable_epoch_f val" for val ec])
          apply (sep_drule spec[where x="Epoch (epoch_to_u64 (current_epoch_f state_ctxt) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD)"])
            apply (sep_mp)
            apply (clarsimp simp: initiate_exit_when_far_future_def)
            apply (clarsimp split: if_splits; fastforce?)
             apply (sep_mp)
          apply (clarsimp simp: get_exit_epoch_simp get_withdrawable_epoch_simp)
             apply (sep_mp)

             apply (clarsimp)
          apply (clarsimp simp: get_exit_epoch_simp get_withdrawable_epoch_simp)
             apply (sep_mp, assumption)

          apply (sep_cancel)+
  apply (sep_drule split_validator[where vref=vref], clarsimp simp: sep_conj_ac)


          apply (rule exI, sep_cancel+)

      apply (intro conjI impI; (clarsimp simp: less_eq_Epoch_def one_Epoch_def plus_Epoch_def)?)
           apply (sep_cancel)+
          apply (rule exI, sep_cancel+)
           apply (clarsimp simp: Let_unfold)
           apply (sep_drule spec[where x="if exit_epoch_f val = FAR_FUTURE_EPOCH \<and> is_active_validator val (current_epoch_f state_ctxt) \<and>
                                             Validator.effective_balance_f val \<le> EJECTION_BALANCE config then new_exit_epoch ec state_ctxt else exit_epoch_f val" for ec val])
           apply (sep_drule spec[where x="if exit_epoch_f val = FAR_FUTURE_EPOCH \<and> is_active_validator val (current_epoch_f state_ctxt) \<and>
                                             Validator.effective_balance_f val \<le> EJECTION_BALANCE config then new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) else 
                                             withdrawable_epoch_f val" for ec val])
           apply (sep_drule spec)
          apply (clarsimp simp: get_exit_epoch_simp get_withdrawable_epoch_simp)
  apply (sep_mp)
apply (clarsimp split: if_splits simp: get_val_fields_simps)
              apply (sep_mp)
              apply (fastforce)
  apply (fastforce)
  apply (fastforce)

           apply (clarsimp simp: get_activation_epoch_simp)
           apply (sep_mp, clarsimp)
          apply (sep_cancel)+
           apply (clarsimp simp: Let_unfold)
          apply (intro conjI impI; (clarsimp simp: less_eq_Epoch_def one_Epoch_def plus_Epoch_def)?)
  defer
            apply (metis (no_types, lifting) max.coboundedI2 max.orderE olen_add_eqv)
           apply (sep_drule split_validator[where vref=vref])
  apply (clarsimp)
           apply (sep_cancel)+
          apply (rule exI, sep_cancel+)
           apply (clarsimp simp: Let_unfold)
 apply (sep_drule spec[where x=" if exit_epoch_f val = FAR_FUTURE_EPOCH then new_exit_epoch ec state_ctxt else exit_epoch_f val" for ec val])
           apply (sep_drule spec[where x="if exit_epoch_f val = FAR_FUTURE_EPOCH then new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) else withdrawable_epoch_f val" for ec val])
           apply (sep_drule spec)
         apply (sep_mp)
           apply (clarsimp simp: get_activation_epoch_simp)
          apply (clarsimp simp: get_exit_epoch_simp get_withdrawable_epoch_simp initiate_exit_when_far_future_def split: if_splits; fastforce?)
            apply (clarsimp)
  apply (clarsimp simp: sep_conj_ac)
            apply (sep_mp)
            apply (clarsimp)
            apply (sep_mp, clarsimp)
  apply (clarsimp simp: sep_conj_ac)
  apply (sep_mp, clarsimp)
    apply (sep_cancel)+
  apply (clarsimp split: if_splits)
    apply (rule exI, sep_cancel+)
          apply (sep_mp, assumption)
  defer
   apply (metis (no_types, lifting) max.coboundedI2 max.orderE olen_add_eqv)
        apply (metis (no_types, lifting) max.coboundedI2 max.orderE olen_add_eqv)
       apply (erule_tac x=y in ballE; fastforce?)
       apply (fastforce simp: ran_def)
apply (erule_tac x=y in ballE; fastforce?)
      apply (fastforce simp: ran_def)
        apply (metis (no_types, lifting) max.coboundedI2 max.orderE olen_add_eqv)

apply (erule_tac x=y in ballE; fastforce?)
    apply (fastforce simp: ran_def)
apply (erule_tac x=y in ballE; fastforce?)
  by (fastforce simp: ran_def)

  







lemma process_single_effective_balance_update_wp[wp]: defines updated_balance_def: "updated_balance b eb_ctxt v \<equiv> (let eff_balance = Validator.effective_balance_f v in 
                 if (b + downward_threshold_f eb_ctxt < eff_balance) \<or>  (eff_balance + upward_threshold_f eb_ctxt < b) 
                    then min (b - b mod EFFECTIVE_BALANCE_INCREMENT config) MAX_EFFECTIVE_BALANCE
                    else eff_balance)" shows 

"(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> hoare_triple (lift (\<lambda>s. b \<le> b + downward_threshold_f eb_ctxt \<and>
                                                                              total_active_balance_f epb \<le> total_active_balance_f epb + min (b - b mod EFFECTIVE_BALANCE_INCREMENT config) MAX_EFFECTIVE_BALANCE \<and>
                                                                             
                                                                               Validator.effective_balance_f v \<le> Validator.effective_balance_f v + upward_threshold_f eb_ctxt \<and>
  total_active_balance_f epb \<le> total_active_balance_f epb + Validator.effective_balance_f v \<and>
  ValidatorInfo.effective_balance_f val_info < MAX_EFFECTIVE_BALANCE \<and>
 (\<forall>n\<in>{n. n \<le> length (participation_flag_weights cep) \<and> has_flag cep n}.  
       (ValidatorInfo.effective_balance_f val_info \<ge> b - b mod EFFECTIVE_BALANCE_INCREMENT config \<longrightarrow>
       ValidatorInfo.effective_balance_f val_info - (b - b mod EFFECTIVE_BALANCE_INCREMENT config) \<le> previous_epoch_flag_attesting_balances_f epb ! n) \<and>
     (Validator.effective_balance_f v \<ge> ValidatorInfo.effective_balance_f val_info \<longrightarrow>
      previous_epoch_flag_attesting_balances_f epb ! n \<le> previous_epoch_flag_attesting_balances_f epb ! n + (Validator.effective_balance_f v - ValidatorInfo.effective_balance_f val_info)) \<and>
      ValidatorInfo.effective_balance_f val_info - Validator.effective_balance_f v \<le> previous_epoch_flag_attesting_balances_f epb ! n  \<and>
         
       previous_epoch_flag_attesting_balances_f epb ! n
       \<le> previous_epoch_flag_attesting_balances_f epb ! n + (min (b - b mod EFFECTIVE_BALANCE_INCREMENT config) MAX_EFFECTIVE_BALANCE - ValidatorInfo.effective_balance_f val_info)) \<and>
 (balance \<mapsto>\<^sub>l b \<and>* validator \<mapsto>\<^sub>l v \<and>* next_epb \<mapsto>\<^sub>l epb \<and>* next_ebrc \<mapsto>\<^sub>l ebrc \<and>*
 (next_ebrc \<mapsto>\<^sub>l ebrc\<lparr>effective_balances_f := effective_balances_f ebrc @ [updated_balance b eb_ctxt v]\<rparr> \<and>*
           validator \<mapsto>\<^sub>l v\<lparr>Validator.effective_balance_f := updated_balance b eb_ctxt v\<rparr> \<and>*
           next_epb \<mapsto>\<^sub>l updated_nepb epb (v\<lparr>Validator.effective_balance_f := updated_balance b eb_ctxt v\<rparr>) cep (next_epoch_f state_ctxt) (ValidatorInfo.effective_balance_f val_info) \<and>*
           balance \<mapsto>\<^sub>l b \<longrightarrow>* P ()))s ))         
     (bindCont (process_single_effective_balance_update balance validator 
                   val_info next_epb next_ebrc eb_ctxt state_ctxt cep) next) Q"
  apply (clarsimp simp: process_single_effective_balance_update_def liftM_def comp_def updated_balance_def , rule hoare_weaken_pre)
   apply (simp only: bindCont_assoc[symmetric] | rule update_next_epoch_progressive_balances_wp[where v=epb] read_beacon_wp_ex add_wp' write_beacon_wp' wp | fastforce)+
  apply (intro lift_mono' le_funI)
  apply (clarsimp)
  apply (intro exI impI conjI | sep_cancel | clarsimp )+
    apply (sep_mp, clarsimp)
  apply (intro exI impI conjI | sep_cancel | clarsimp )+
    apply (sep_mp, clarsimp)
  apply (intro exI impI conjI allI ballI | sep_cancel | clarsimp)+
  by (sep_mp, clarsimp)


lemma new_state_context_wp': "(\<And>x. \<lblot>\<lless>pre x\<then>\<rblot> c x \<lblot>post\<rblot>) \<Longrightarrow>
\<lblot>\<lless>beacon_slots \<mapsto>\<^sub>l v \<and>*
   (beacon_slots \<mapsto>\<^sub>l v \<longrightarrow>*
    (beacon_slots \<mapsto>\<^sub>l v \<and>* finalized_checkpoint \<mapsto>\<^sub>l c_f) \<and>*
    (beacon_slots \<mapsto>\<^sub>l v \<and>* finalized_checkpoint \<mapsto>\<^sub>l c_f \<longrightarrow>*
     (\<lambda>s. Checkpoint.epoch_f c_f \<in> previous_epochs v \<and>
           (Checkpoint.epoch_f c_f \<in> previous_epochs v \<longrightarrow>
            (num_active_validators \<mapsto>\<^sub>l n \<and>*
             (num_active_validators \<mapsto>\<^sub>l n \<longrightarrow>*
              (\<lambda>a. StateContext.fields (current_epoch v) (Epoch (epoch_to_u64 (current_epoch v) + 1))
                     (MIN_EPOCHS_TO_INACTIVITY_PENALTY config < raw_epoch (previous_epoch (current_epoch v)) - raw_epoch (Checkpoint.epoch_f c_f))
                     (max (MIN_PER_EPOCH_CHURN_LIMIT config) (n div CHURN_LIMIT_QUOTIENT config)) =
                    x \<and>
                    (StateContext.fields (current_epoch v) (Epoch (epoch_to_u64 (current_epoch v) + 1))
                      (MIN_EPOCHS_TO_INACTIVITY_PENALTY config < raw_epoch (previous_epoch (current_epoch v)) - raw_epoch (Checkpoint.epoch_f c_f))
                      (max (MIN_PER_EPOCH_CHURN_LIMIT config) (n div CHURN_LIMIT_QUOTIENT config)) =
                     x \<longrightarrow>
                     pre x a))))
             s))))\<then>\<rblot> bindCont (new_state_context) c \<lblot>post\<rblot>"
  apply (rule hoare_weaken_pre, rule new_state_context_wp, fastforce)
  apply (clarsimp)
  by (sep_cancel)+

lemma new_slashings_context_wp': "(\<And>x. \<lblot>\<lless>P x\<then>\<rblot> c x \<lblot>Q\<rblot>) \<Longrightarrow>
\<lblot>\<lless>slashings \<mapsto>\<^sub>l ss \<and>*
   (slashings \<mapsto>\<^sub>l ss \<longrightarrow>*
    (\<lambda>s. safe_mul PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX (sum_list (local.vector_inner ss)) \<and>
          (safe_mul PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX (sum_list (local.vector_inner ss)) \<longrightarrow>
           raw_epoch (current_epoch_f st_ctxt) \<le> raw_epoch (current_epoch_f st_ctxt) + EPOCHS_PER_SLASHINGS_VECTOR config \<and>
           (raw_epoch (current_epoch_f st_ctxt) \<le> raw_epoch (current_epoch_f st_ctxt) + EPOCHS_PER_SLASHINGS_VECTOR config \<longrightarrow>
            SlashingsContext.fields (min (sum_list (local.vector_inner ss) * PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX) (total_active_balance_f pbc))
             (Epoch ((raw_epoch (current_epoch_f st_ctxt) + EPOCHS_PER_SLASHINGS_VECTOR config) div 2)) =
            x \<and>
            (SlashingsContext.fields (min (sum_list (local.vector_inner ss) * PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX) (total_active_balance_f pbc))
              (Epoch ((raw_epoch (current_epoch_f st_ctxt) + EPOCHS_PER_SLASHINGS_VECTOR config) div 2)) =
             x \<longrightarrow>
             P x s)))))\<then>\<rblot> bindCont (new_slashings_context st_ctxt pbc) c \<lblot>Q\<rblot>"
  apply (rule hoare_weaken_pre, wp)
  by (clarsimp, sep_cancel+)




lemma get_current_epoch_wp'[wp]: "(\<And>x. hoare_triple (lift (P x)) (f x) Q) \<Longrightarrow>
hoare_triple (lift (maps_to beacon_slots v \<and>* (maps_to beacon_slots v \<longrightarrow>* P (slot_to_epoch config v)))) (bindCont get_current_epoch f) Q"
  apply (clarsimp simp: get_current_epoch_def)
  apply (rule hoare_weaken_pre)
  apply (clarsimp simp: bindCont_assoc[symmetric] bindCont_return')
   apply (rule read_beacon_wp, fastforce)
  apply (rule order_refl)
  done

lemma get_previous_epoch_wp''[wp]:"(\<And>x. hoare_triple (lift (P x)) (f x) Q) \<Longrightarrow>
   hoare_triple (lift (maps_to beacon_slots v \<and>* (maps_to beacon_slots v \<longrightarrow>*
               P (previous_epoch (slot_to_epoch config v)) ))) (bindCont get_previous_epoch f) Q"
  apply (rule hoare_weaken_pre)
   apply (wp)
  by (fastforce)




lemma var_list_index_lens_wp[wp]: 
"(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow> 
  hoare_triple (\<lless>\<lambda>s. \<exists>x. 
       (lens_oocomp (v_list_lens i) ls \<mapsto>\<^sub>l x \<and>* (lcomp (v_list_lens i) ls \<mapsto>\<^sub>l x \<longrightarrow>* P (lcomp (v_list_lens i) ls))) s\<then>) 
   (bindCont (var_list_index_lens ls i) c) Q"
  apply (rule hoare_weaken_pre)
  apply (unfold var_list_index_lens_def)
   apply (simp only: bindCont_assoc[symmetric])
   apply (rule read_beacon_wp_ex)
    apply (clarsimp)
    apply (fastforce)
   apply (clarsimp)
  done


lemma unify_helper: "(\<And>g'. g = g' \<Longrightarrow> P (bindCont f g')) \<Longrightarrow> P (bindCont f g)"
  by (blast)



lemma commute_index_offset: "(take (Suc 0) (local.var_list_inner aa) @ take (length (local.var_list_inner aa) - Suc 0) (local.var_list_inner aaa))[0 := ab] =
       take (Suc 0) ((local.var_list_inner aa)[0 := ab]) @ take (length (local.var_list_inner aa) - Suc 0) (local.var_list_inner aaa)"
  apply (rule nth_equalityI; clarsimp?)
  by (clarsimp simp: nth_append nth_list_update  split: if_splits)


definition lens_ocomp' :: "('f , 'e option) lens \<Rightarrow> ('g, 'f option) lens \<Rightarrow> ('g, 'e option) lens" (infixl "|o>" 54) where 
"lens_ocomp' l l' \<equiv> Lens (\<lambda>s. Option.bind (get l' s) (\<lambda>s'. get l s')  ) 
                     (\<lambda>(s :: 'g) (a :: 'e option). 
                        set l' s (do {b <- get l' s; Some (set l b a)}) ) (\<lambda>_. True) "


lemma hd_upto: "[0..<length (a # x)] = 0#[1..<length (a#x)]"
  apply (case_tac x; clarsimp?)
  apply (intro conjI impI ; clarsimp?)
  using Suc_le_lessD upt_conv_Cons apply presburger
  by (simp add: linorder_not_le)


lemma maps_to_impl: "maps_to l v s \<Longrightarrow> set l = set l' \<Longrightarrow> v = v' \<Longrightarrow> valid_lens l' \<Longrightarrow> maps_to l' v' s"
  by (clarsimp simp: maps_to_def)


lemma nth_update_iff: "xs[i := v] ! j = (if i = j \<and> i < length xs then v else xs ! j)"
  apply (clarsimp)
  by (case_tac "i = j"; clarsimp)


lemma nth_update_iff': "i \<ge> length xs \<Longrightarrow> xs[i := v] = xs"
  by (clarsimp)

lemma unat_of_nat64_suc: "xa + 1 < 2 ^ 64 \<Longrightarrow> unat (1 + (word_of_nat :: nat \<Rightarrow> 64 word) xa) = Suc xa"
  apply (unat_arith, clarsimp)
  apply (intro conjI impI)
   apply (clarsimp simp:  unat_of_nat64'; clarsimp?)
  by (clarsimp simp:  unat_of_nat64'; clarsimp?)



lemma idk_helper: "i < length (local.var_list_inner aa) \<Longrightarrow> 0 < i \<Longrightarrow> length (local.var_list_inner aa) < 2^64 \<Longrightarrow> xa + 1 < 2^64 \<Longrightarrow>
    (drop (Suc 0) (local.var_list_inner aa))[unat ((word_of_nat :: nat \<Rightarrow> 64 word) xa) := ab] ! (i - Suc 0) =
    (local.var_list_inner aa)[unat (1 + (word_of_nat :: nat \<Rightarrow> 64 word) xa) := ab] ! i"
  apply (case_tac "xa + 1 < length (local.var_list_inner aa)"; clarsimp?)
  apply (subst nth_update_iff)
  apply (clarsimp split: if_splits)
  apply (intro conjI impI; clarsimp?)
  apply (subst nth_update_iff)

   apply (clarsimp split: if_splits)
   apply (subgoal_tac "unat ((word_of_nat :: nat \<Rightarrow> 64 word) xa) = xa \<and> unat (1 + (word_of_nat :: nat \<Rightarrow> 64 word) xa) = xa + 1")
    apply (clarsimp simp: unat_of_nat64_suc unat_of_nat64')
   apply (clarsimp)
    apply (intro conjI)
     apply (subst (asm) unat_of_nat64'; clarsimp?)
  apply (rule unat_of_nat64_suc; clarsimp)
  apply (smt (verit, best) add_diff_inverse_nat diff_Suc_1' diff_add_0 diff_is_0_eq diff_less_mono not_less_eq nth_update_iff unatSuc unat_gt_0)

   apply (subgoal_tac "unat ((word_of_nat :: nat \<Rightarrow> 64 word) xa) = xa \<and> unat (1 + (word_of_nat :: nat \<Rightarrow> 64 word) xa) = xa + 1")
   apply (clarsimp)
  apply (clarsimp)
    apply (intro conjI)
     apply (subst unat_of_nat64'; clarsimp?)
  by (rule unat_of_nat64_suc; clarsimp)
  
  
   



  
lemma ifI: "P \<longrightarrow> Q \<Longrightarrow> \<not>P \<longrightarrow> R \<Longrightarrow> (if P then Q else R)"
  by (clarsimp)


lemma ifI': "P \<longrightarrow> Q s \<Longrightarrow> \<not>P \<longrightarrow> R s \<Longrightarrow> (if P then Q else R) s"
  by (clarsimp)

lemma base_reward_fields[simp]: "base_reward_f (ValidatorInfo.fields a b c d e f g h i) = c"
  by (clarsimp simp: ValidatorInfo.fields_def)

lemma effective_balance_fields[simp]: "effective_balance_f (ValidatorInfo.fields a b c d e f g h i) = b"
  by (clarsimp simp: ValidatorInfo.fields_def)


lemma index_fields[simp]: "index_f (ValidatorInfo.fields a b c d e f g h i) = a"
  by (clarsimp simp: ValidatorInfo.fields_def)


lemma is_eligible_fields[simp]: "is_eligible_f (ValidatorInfo.fields a b c d e f g h i) = d"
  by (clarsimp simp: ValidatorInfo.fields_def)

lemma rewardable_simp: 
   "rewardable
         (ValidatorInfo.fields a b c d e f g h i)
         n state_ctxt = (g \<and> \<not> e \<and> has_flag h n \<and> \<not> is_in_inactivity_leak_f state_ctxt)"
  apply (subst rewardable_def)
  apply (subst is_unslashed_participating_index_def)
  by (simp add: ValidatorInfo.fields_def )

definition "reward rewards_ctxt state_ctxt validator_info n \<equiv> if rewardable validator_info n state_ctxt then base_reward_f validator_info * PARTICIPATION_FLAG_WEIGHTS ! n * unslashed_participating_increments_array_f rewards_ctxt ! n div
                                                                      (active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR) else 0"
definition "penalise state_ctxt validator_info \<equiv> (\<lambda>n. if \<not>(rewardable validator_info n state_ctxt) then base_reward_f validator_info * PARTICIPATION_FLAG_WEIGHTS ! n div WEIGHT_DENOMINATOR 
                                                                                                             else 0)"
definition "inactive_penalty_delta eff_balance inactivity_score validator_info
                       \<equiv> (if \<not> is_unslashed_participating_index validator_info TIMELY_TARGET_FLAG_INDEX then 
                                                                           inactivity_score * eff_balance div 
                                                                           (INACTIVITY_PENALTY_QUOTIENT_ALTAIR * INACTIVITY_SCORE_BIAS config) else 0)"

definition "processed_reward inactivity_penalty_delta penalties rewards balance validator_info \<equiv> 
     (if is_eligible_f validator_info then saturating_sub (balance + sum_list rewards) (sum_list penalties + inactivity_penalty_delta) else balance)"

lemma process_single_reward_and_penalty_wp'[wp]: "
 (\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. let eff_balance = (ValidatorInfo.effective_balance_f validator_info);
                              rewards = map (reward rewards_ctxt state_ctxt validator_info) [0, 1, 2];
                                          penalties = map (penalise state_ctxt validator_info) [0,1];
                                          inactivity_penalty_delta = inactive_penalty_delta eff_balance inactivity_score validator_info;
                                          result = processed_reward inactivity_penalty_delta penalties rewards balance validator_info
                           in  \<forall>n\<in>{0,1,2}. let unslashed_participating_increment = unslashed_participating_increments_array_f rewards_ctxt ! n;
                                                weight = PARTICIPATION_FLAG_WEIGHTS ! n              
                                         in n < length PARTICIPATION_FLAG_WEIGHTS \<and>
                                            n < length (unslashed_participating_increments_array_f rewards_ctxt) \<and>
                                            balance \<le> balance + sum_list rewards \<and>
                                            sum_list (map unat rewards) + unat inactivity_penalty_delta  < 2^64 \<and> 
                                            (sum_list (map unat penalties) + unat inactivity_penalty_delta) < 2 ^ 64 \<and>
                                            safe_mul weight (base_reward_f validator_info) \<and>
                                            safe_mul inactivity_score eff_balance \<and>
                                            safe_mul (weight * base_reward_f validator_info) unslashed_participating_increment \<and>
                                            safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR \<and>
                                            safe_mul INACTIVITY_PENALTY_QUOTIENT_ALTAIR (INACTIVITY_SCORE_BIAS config) \<and>
                                            active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0 \<and>
                                            (n < length PARTICIPATION_FLAG_WEIGHTS \<and> safe_mul inactivity_score eff_balance \<and>
                                             n < length (unslashed_participating_increments_array_f rewards_ctxt) \<and>
                                             safe_mul weight (base_reward_f validator_info) \<and> safe_mul INACTIVITY_PENALTY_QUOTIENT_ALTAIR (INACTIVITY_SCORE_BIAS config) \<and>
                                             safe_mul (weight * base_reward_f validator_info) unslashed_participating_increment \<and>
                                             safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR \<and> active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0 \<longrightarrow> (P (result)) s)))
  (bindCont (process_single_reward_and_penalty balance inactivity_score validator_info rewards_ctxt state_ctxt) c)
   Q"
  apply (rule hoare_weaken_pre)
   apply (wp)
  by (clarsimp simp: reward_def penalise_def inactive_penalty_delta_def processed_reward_def)


definition single_effective_balance_updated :: "64 word \<Rightarrow> EffectiveBalancesContext \<Rightarrow> Validator \<Rightarrow> 64 word"
  where  "single_effective_balance_updated b eb_ctxt v \<equiv> 
            (let eff_balance = Validator.effective_balance_f v in 
                 if (b + downward_threshold_f eb_ctxt < eff_balance) \<or>  (eff_balance + upward_threshold_f eb_ctxt < b) 
                    then min (b - b mod EFFECTIVE_BALANCE_INCREMENT config) MAX_EFFECTIVE_BALANCE
                    else eff_balance)"


lemma process_single_effective_balance_update_wp'[wp]:

"(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> 
  hoare_triple (lift (\<lambda>s. \<exists>b v epb ebrc.  b \<le> b + downward_threshold_f eb_ctxt \<and>
                                          total_active_balance_f epb \<le> total_active_balance_f epb + single_effective_balance_updated b eb_ctxt v \<and>                                                                           
                                          Validator.effective_balance_f v \<le> Validator.effective_balance_f v + upward_threshold_f eb_ctxt \<and>
                                          total_active_balance_f epb \<le> total_active_balance_f epb + Validator.effective_balance_f v \<and>
                                          ValidatorInfo.effective_balance_f val_info < MAX_EFFECTIVE_BALANCE \<and>
                                          (\<forall>previous_epoch_flag_attesting_balance\<in>{ (previous_epoch_flag_attesting_balances_f epb ! n) | n. n \<le> length (participation_flag_weights cep) \<and> has_flag cep n}.
                                               previous_epoch_flag_attesting_balance \<le> 
                                               previous_epoch_flag_attesting_balance +
                                                   (single_effective_balance_updated b eb_ctxt v - ValidatorInfo.effective_balance_f val_info) \<and>
                                               ValidatorInfo.effective_balance_f val_info - single_effective_balance_updated b eb_ctxt v \<le> previous_epoch_flag_attesting_balance) \<and>

 (balance \<mapsto>\<^sub>l b \<and>* validator \<mapsto>\<^sub>l v \<and>* next_epb \<mapsto>\<^sub>l epb \<and>* next_ebrc \<mapsto>\<^sub>l ebrc \<and>*
 (next_ebrc \<mapsto>\<^sub>l ebrc\<lparr>effective_balances_f := effective_balances_f ebrc @ [single_effective_balance_updated b eb_ctxt v]\<rparr> \<and>*
           validator \<mapsto>\<^sub>l v\<lparr>Validator.effective_balance_f := single_effective_balance_updated b eb_ctxt v\<rparr> \<and>*
           next_epb \<mapsto>\<^sub>l updated_nepb epb (v\<lparr>Validator.effective_balance_f := single_effective_balance_updated b eb_ctxt v\<rparr>) cep (next_epoch_f state_ctxt) (ValidatorInfo.effective_balance_f val_info) \<and>*
           balance \<mapsto>\<^sub>l b \<longrightarrow>* P ()))s ))         
     (bindCont (process_single_effective_balance_update balance validator 
                   val_info next_epb next_ebrc eb_ctxt state_ctxt cep) next) Q"
  apply (rule hoare_assert_stateI)
  apply (drule lift_exE, clarsimp)+
  apply (simp add: process_single_effective_balance_update_def)
  apply (rule hoare_weaken_pre, wp)
  apply (safe)
  apply (intro exI, sep_cancel+)+
  apply (intro conjI impI; clarsimp?)
  apply (intro conjI impI; clarsimp?)
  apply (intro exI, sep_cancel+)+
     apply (intro conjI impI)
  defer
      defer
  apply (sep_cancel)+
  apply (intro exI, sep_cancel+)+
    apply (clarsimp simp: Let_unfold single_effective_balance_updated_def)
  apply (sep_mp)
       apply (clarsimp split: if_splits)
  apply (intro exI, sep_cancel+)+
  apply (intro conjI impI; clarsimp?)
       apply (clarsimp simp: single_effective_balance_updated_def)
      apply (intro conjI impI)
       apply (clarsimp simp: Let_unfold single_effective_balance_updated_def)
  using less_imp_le_nat apply blast
      apply (clarsimp simp: Let_unfold single_effective_balance_updated_def)
  using less_imp_le_nat apply blast
     apply (sep_cancel)+
  apply (intro exI, sep_cancel+)+
 apply (clarsimp simp: Let_unfold single_effective_balance_updated_def)
  apply (sep_mp)
     apply (clarsimp split: if_splits)
  apply (intro exI, sep_cancel+)+
     apply (intro conjI impI)
      defer
      defer
      apply (sep_cancel)+
  apply (intro exI, sep_cancel+)+
apply (clarsimp simp: Let_unfold single_effective_balance_updated_def)
  apply (sep_mp)
      apply (clarsimp split: if_splits)
     apply (clarsimp simp: Let_unfold single_effective_balance_updated_def)
 apply (clarsimp simp: Let_unfold single_effective_balance_updated_def)
    apply (intro conjI impI)
  using less_imp_le_nat apply blast
    apply (clarsimp simp: Let_unfold single_effective_balance_updated_def)
  using less_imp_le_nat apply blast
 apply (clarsimp simp: Let_unfold single_effective_balance_updated_def)
  apply (intro conjI impI allI)
 apply (clarsimp simp: Let_unfold single_effective_balance_updated_def)
  using less_imp_le_nat apply blast
 apply (clarsimp simp: Let_unfold single_effective_balance_updated_def)
  using less_imp_le_nat apply blast
  done




definition make_validator_info :: "Validator \<Rightarrow> Epoch \<Rightarrow> Epoch \<Rightarrow> ParticipationFlags \<Rightarrow> ParticipationFlags \<Rightarrow> BaseRewardsCache \<Rightarrow> nat \<Rightarrow> ValidatorInfo"
  where "make_validator_info v curr_epoch prev_epoch ce p brc n =
  (ValidatorInfo.fields (word_of_nat n) (Validator.effective_balance_f v) (base_rewards_f brc ! unat (effective_balances_f brc ! unat ((word_of_nat n) :: 64 word) div EFFECTIVE_BALANCE_INCREMENT config))
                          (is_active_validator v prev_epoch \<or> slashed_f v \<and> Epoch (epoch_to_u64 prev_epoch + 1) < withdrawable_epoch_f v) (slashed_f v) (is_active_validator v curr_epoch) (is_active_validator v prev_epoch) p ce)"


lemma cond_helper_simp: "slashed_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v,
                  exit_epoch_f :=
                    if is_active_validator (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) (current_epoch_f state_ctxt) \<and>
                       Validator.effective_balance_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) \<le> EJECTION_BALANCE config
                    then new_exit_epoch ec state_ctxt else exit_epoch_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>),
                  withdrawable_epoch_f :=
                    if is_active_validator (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) (current_epoch_f state_ctxt) \<and>
                       Validator.effective_balance_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) \<le> EJECTION_BALANCE config
                    then new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) else withdrawable_epoch_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>),
                  activation_epoch_f :=
                    if index_f (make_validator_info v curr_epoch prev_epoch ce p brc xa) \<in> list.set final_activation_queue then current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD
                    else activation_epoch_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>)\<rparr>) \<and>
            target_withdrawable_epoch_f slashings_ctxt =
            withdrawable_epoch_f
             (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v,
                  exit_epoch_f :=
                    if is_active_validator (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) (current_epoch_f state_ctxt) \<and>
                       Validator.effective_balance_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) \<le> EJECTION_BALANCE config
                    then new_exit_epoch ec state_ctxt else exit_epoch_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>),
                  withdrawable_epoch_f :=
                    if is_active_validator (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) (current_epoch_f state_ctxt) \<and>
                       Validator.effective_balance_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) \<le> EJECTION_BALANCE config
                    then new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) else withdrawable_epoch_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>),
                  activation_epoch_f :=
                    if index_f (make_validator_info v curr_epoch prev_epoch ce p brc xa) \<in> list.set final_activation_queue then current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD
                    else activation_epoch_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>)\<rparr>) \<longleftrightarrow> slashed_f v \<and> 
  target_withdrawable_epoch_f slashings_ctxt =
                    (if is_active_validator v (current_epoch_f state_ctxt) \<and>
                       Validator.effective_balance_f v \<le> EJECTION_BALANCE config
                    then new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) else withdrawable_epoch_f v )"
  apply (intro iffI conjI impI)
     apply (clarsimp)
    apply (clarsimp)
    apply (intro conjI impI; clarsimp)
     apply (clarsimp simp: is_active_validator_def)
  apply (clarsimp simp: is_active_validator_def)
  apply (clarsimp)
  apply (clarsimp)
  apply (clarsimp simp: is_active_validator_def)
  done

definition "updated_validator (v :: Validator) ec state_ctxt final_activation_queue brc p ce prev_epoch curr_epoch n \<equiv>
   v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v,
           exit_epoch_f :=
             if is_active_validator (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) (current_epoch_f state_ctxt) \<and>
                Validator.effective_balance_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) \<le> EJECTION_BALANCE config
             then new_exit_epoch ec state_ctxt else exit_epoch_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>),
           withdrawable_epoch_f :=
             if is_active_validator (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) (current_epoch_f state_ctxt) \<and>
                Validator.effective_balance_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) \<le> EJECTION_BALANCE config
             then new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) else withdrawable_epoch_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>),
           activation_epoch_f :=
             if index_f (make_validator_info v curr_epoch prev_epoch ce p brc n) \<in> list.set final_activation_queue then current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD
             else activation_epoch_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>)\<rparr>"

definition "updated_balance val_info v v' i slashings_ctxt progressive_balances rewards_ctxt state_ctxt b \<equiv> (if slashed_f v' \<and> target_withdrawable_epoch_f slashings_ctxt = withdrawable_epoch_f v'
         then saturating_sub
               (processed_reward (inactive_penalty_delta (Validator.effective_balance_f v) i val_info) (map (penalise state_ctxt val_info) [0, 1])
                 (map (reward rewards_ctxt state_ctxt val_info) [0, 1, 2]) b val_info)
               (Validator.effective_balance_f v' div EFFECTIVE_BALANCE_INCREMENT config * adjusted_total_slashing_balance_f slashings_ctxt div total_active_balance_f progressive_balances * EFFECTIVE_BALANCE_INCREMENT config)
         else processed_reward (inactive_penalty_delta (Validator.effective_balance_f v) i val_info) (map (penalise state_ctxt val_info) [0, 1])
               (map (reward rewards_ctxt state_ctxt val_info) [0, 1, 2]) b val_info)"

lemma effective_balance_simp_helper: "(Validator.effective_balance_f
                 (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v,
                      exit_epoch_f :=
                        if is_active_validator (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) (current_epoch_f state_ctxt) \<and>
                           Validator.effective_balance_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) \<le> EJECTION_BALANCE config
                        then new_exit_epoch ec state_ctxt else exit_epoch_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>),
                      withdrawable_epoch_f :=
                        if is_active_validator (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) (current_epoch_f state_ctxt) \<and>
                           Validator.effective_balance_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) \<le> EJECTION_BALANCE config
                        then new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) else withdrawable_epoch_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>),
                      activation_epoch_f :=
                        if index_f (make_validator_info v curr_epoch prev_epoch ce p brc xa) \<in> list.set final_activation_queue then current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD
                        else activation_epoch_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>)\<rparr>)) = 
       Validator.effective_balance_f v"
  by clarsimp


definition "update_effective_balance v balance effective_balances_ctxt \<equiv> (v
           \<lparr>Validator.effective_balance_f :=
              if balance + downward_threshold_f effective_balances_ctxt
                 < Validator.effective_balance_f v \<or>
                 Validator.effective_balance_f v + upward_threshold_f effective_balances_ctxt
                 < balance
              then min (balance -
                        balance mod EFFECTIVE_BALANCE_INCREMENT config)
                    MAX_EFFECTIVE_BALANCE
              else Validator.effective_balance_f v\<rparr>)"


  

definition "new_effective_balance effective_balances_ctxt new_balance old_balance \<equiv> [if new_balance + downward_threshold_f effective_balances_ctxt
               < old_balance \<or>
               old_balance + upward_threshold_f effective_balances_ctxt
               < new_balance
            then min (new_balance -
                      new_balance mod EFFECTIVE_BALANCE_INCREMENT config)
                  MAX_EFFECTIVE_BALANCE
            else old_balance]"

lemma effective_balance_f_simp[simp]:"ValidatorInfo.effective_balance_f (make_validator_info a b c d e f g) = Validator.effective_balance_f a"
  by (clarsimp simp: make_validator_info_def)


lemma effective_balance_f_updated_validator_simp[simp]:" Validator.effective_balance_f (updated_validator v a b c d e f g h i) = Validator.effective_balance_f v"
  by (clarsimp simp: updated_validator_def)

definition "update_exit_cache state_ctxt v ec \<equiv> (if is_active_validator v (current_epoch_f state_ctxt) \<and> Validator.effective_balance_f v \<le> EJECTION_BALANCE config \<and> exit_epoch_f v = FAR_FUTURE_EPOCH
         then record_exit ec (new_exit_epoch ec state_ctxt) (case exit_epoch_counts_f ec (new_exit_epoch ec state_ctxt) of None \<Rightarrow> 0 | Some a \<Rightarrow> id a) else ec)"

lemma update_exit_cache_fold: 
  "update_exit_cache state_ctxt v ec = (if is_active_validator (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) (current_epoch_f state_ctxt) \<and>
            Validator.effective_balance_f (v\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue v then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f v\<rparr>) \<le> EJECTION_BALANCE config \<and> 
            exit_epoch_f v = FAR_FUTURE_EPOCH
         then record_exit ec (new_exit_epoch ec state_ctxt) (case exit_epoch_counts_f ec (new_exit_epoch ec state_ctxt) of None \<Rightarrow> 0 | Some a \<Rightarrow> id a) else ec)"
  by (clarsimp simp: update_exit_cache_def is_active_validator_def)


lemma activation_updated_simp: "activation_epoch_f (updated_validator v ec state_ctxt final_activation_queue brc p ce prev_epoch curr_epoch n) \<le> epoch \<longleftrightarrow> 
       (if word_of_nat n \<in> list.set final_activation_queue then current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD else activation_epoch_f v) \<le> epoch  "
  by (clarsimp simp: updated_validator_def make_validator_info_def)


lemma is_active_upd: "is_active_validator (v\<lparr>activation_eligibility_epoch_f := current_epoch_f state_ctxt + 1\<rparr>) epoch = is_active_validator v epoch"
  by (clarsimp simp: is_active_validator_def)




definition "active_next_epoch v ec state_ctxt final_activation_queue n = (word_of_nat n \<notin> list.set final_activation_queue \<and> activation_epoch_f v \<le> current_epoch_f state_ctxt + 1 \<and>
   current_epoch_f state_ctxt + 1 < (if (is_active_validator v (current_epoch_f state_ctxt) \<and>
    Validator.effective_balance_f v \<le> EJECTION_BALANCE config) then new_exit_epoch ec state_ctxt else exit_epoch_f v))"

lemma is_active_next_epoch_active_next_epoch: 
  "\<not>(current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD \<le> current_epoch_f state_ctxt + 1) \<Longrightarrow> (next_epoch_f state_ctxt) = (current_epoch_f state_ctxt + 1) \<Longrightarrow> is_active_validator
           (update_effective_balance (updated_validator v ec state_ctxt final_activation_queue brc p ce prev_epoch curr_epoch xa)
             (updated_balance (make_validator_info v curr_epoch prev_epoch ce p brc xa) v 
              (updated_validator v ec state_ctxt final_activation_queue brc p ce prev_epoch curr_epoch xa) i slashings_ctxt progressive_balances rewards_ctxt state_ctxt b) effective_balances_ctxt)  (next_epoch_f state_ctxt) = 
  active_next_epoch v ec state_ctxt final_activation_queue xa"
  apply (clarsimp simp: is_active_validator_def active_next_epoch_def update_effective_balance_def activation_updated_simp)
  apply (clarsimp simp: updated_validator_def is_active_upd)
  apply (intro conjI impI; clarsimp?)
  using is_active_validator_def apply blast
  using is_active_validator_def by blast

lemma sep_not_true: "((P \<longrightarrow>* Q) \<and>* R) s \<Longrightarrow> (\<And>s. R s \<Longrightarrow> P s) \<Longrightarrow> Q s"
  by (drule sep_mp_gen; fastforce)



lemma n_le_flag_weights: " n \<in> {0, 1, 2} \<Longrightarrow> n < length PARTICIPATION_FLAG_WEIGHTS"
  apply (clarsimp simp: PARTICIPATION_FLAG_WEIGHTS_def)
  by (linarith)

lemma split_foldr_map_sep_conj: "foldr (\<and>*) (map (\<lambda>x. P x \<and>* Q x) xs) sep_empty = (foldr (\<and>*) (map (\<lambda>x. P x) xs) sep_empty  \<and>* foldr (\<and>*) (map (\<lambda>x. Q x) xs) sep_empty)" 
  apply (induct xs; clarsimp)
  apply (intro ext iffI; clarsimp?)
   apply (sep_cancel)+
  done

lemma split_foldr_map_conj: "foldr (\<and>*) (map (\<lambda>x s. P x \<and> Q x s) xs) sep_empty = (\<lambda>s. foldr (\<and>) (map (\<lambda>x. P x) xs) True  \<and> foldr (\<and>*) (map (\<lambda>x. Q x) xs) sep_empty s)" 
  by (induct xs; clarsimp)

lemma [simp]:"foldr (\<and>) (map (\<lambda>x. P x) xs) True \<longleftrightarrow> (\<forall>x\<in>(list.set xs). P x)"
  by (induct xs; clarsimp)



lemma var_map_index_id: "xs = [0..<n] \<Longrightarrow> n = length (var_list_inner vs) \<Longrightarrow> n < 2^64 \<Longrightarrow> VariableList (map (\<lambda>x. unsafe_var_list_index vs (word_of_nat x)) xs) = vs"
  apply (clarsimp)
  apply (case_tac vs)
  apply (clarsimp)
  apply (rule nth_equalityI)
   apply (clarsimp)
  apply (clarsimp)
  apply (clarsimp simp: unsafe_var_list_index_def)
  apply (subgoal_tac "unat ((word_of_nat :: nat \<Rightarrow> 64 word) i) = i")
   apply (clarsimp)
  apply (unat_arith, clarsimp)
  apply (rule unat_of_nat64')
  apply (clarsimp)
  done

term process_epoch_single_pass

lemma maxI: "(a \<le> b \<Longrightarrow> P b) \<Longrightarrow> (\<not>a \<le> b \<Longrightarrow> P a) \<Longrightarrow> P (max a b)"
  by (clarsimp simp: max_def)        





definition "registered_validator val ec (aq :: 64 word list) (state_ctxt :: StateContext) n \<equiv>
  (let  val' = val\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue val then (current_epoch_f state_ctxt) + 1 else activation_eligibility_epoch_f val\<rparr> in 
              val'\<lparr>exit_epoch_f := (if ready_to_eject val' state_ctxt then new_exit_epoch ec state_ctxt else exit_epoch_f val') ,
              withdrawable_epoch_f := if ready_to_eject val' state_ctxt then new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) else  withdrawable_epoch_f val',
              activation_epoch_f := if n \<in> List.set aq then (current_epoch_f state_ctxt) + 1 +  MAX_SEED_LOOKAHEAD else activation_epoch_f val' \<rparr>)"



lemma is_active_update_activation[simp]: "is_active_validator (val\<lparr>activation_eligibility_epoch_f := b\<rparr>) epoch =
      is_active_validator (val) epoch "
  by (clarsimp simp: is_active_validator_def)


lemma register_validator_fold1: 
 "is_eligible_for_activation_queue val \<Longrightarrow>  n \<in> list.set aq \<Longrightarrow> is_active_validator val (current_epoch_f state_ctxt) \<Longrightarrow> Validator.effective_balance_f val \<le> EJECTION_BALANCE config \<Longrightarrow>
    exit_epoch_f val = FAR_FUTURE_EPOCH 
       \<Longrightarrow>
       val \<lparr>activation_eligibility_epoch_f := current_epoch_f state_ctxt + 1, exit_epoch_f := new_exit_epoch ec state_ctxt,
           withdrawable_epoch_f := new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config), activation_epoch_f := current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD\<rparr> =
        registered_validator val ec aq state_ctxt n"
  by (clarsimp simp: registered_validator_def Let_unfold)


lemma max_le_left[simp]:
 "(x :: 'f :: linorder) \<le> max x y"
  by (clarsimp simp: max_def)

lemma sep_mp_mp: "((\<lambda>s. P \<and> Q s) \<longrightarrow>* R) s \<Longrightarrow> P \<Longrightarrow> (Q \<longrightarrow>* R) s"
  apply (clarsimp)
  done



lemma registered_validator_not_eligible_simp: "is_active_validator val (current_epoch_f state_ctxt) \<longrightarrow>
       \<not> Validator.effective_balance_f val \<le> EJECTION_BALANCE config \<Longrightarrow>  n \<in> list.set aq \<Longrightarrow> \<not> is_eligible_for_activation_queue val \<Longrightarrow>
  registered_validator val ec (aq :: 64 word list) (state_ctxt :: StateContext) n = val\<lparr>activation_epoch_f := current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD\<rparr> "
  apply (clarsimp simp: registered_validator_def)
  by (case_tac " is_active_validator val (current_epoch_f state_ctxt)"; clarsimp)


lemma registered_validator_not_eligible_simp': "is_active_validator val (current_epoch_f state_ctxt) \<longrightarrow>
       \<not> Validator.effective_balance_f val \<le> EJECTION_BALANCE config \<Longrightarrow>  \<not>n \<in> list.set aq \<Longrightarrow>  is_eligible_for_activation_queue val \<Longrightarrow>
  registered_validator val ec (aq :: 64 word list) (state_ctxt :: StateContext) n = val\<lparr>activation_eligibility_epoch_f := current_epoch_f state_ctxt + 1\<rparr> "
  apply (clarsimp simp: registered_validator_def Let_unfold)
  by (case_tac " is_active_validator val (current_epoch_f state_ctxt)"; clarsimp)


lemma registered_validator_not_eligible_simp'': "is_active_validator val (current_epoch_f state_ctxt) \<Longrightarrow>
        Validator.effective_balance_f val \<le> EJECTION_BALANCE config \<Longrightarrow>  \<not>n \<in> list.set aq \<Longrightarrow>  \<not>is_eligible_for_activation_queue val \<Longrightarrow> exit_epoch_f val = FAR_FUTURE_EPOCH \<Longrightarrow>
  registered_validator val ec (aq :: 64 word list) (state_ctxt :: StateContext) n = val\<lparr>exit_epoch_f := new_exit_epoch ec state_ctxt, withdrawable_epoch_f := new_exit_epoch ec state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config)\<rparr> "
  by (clarsimp simp: registered_validator_def)


lemma registered_validator_not_eligible_simp''': "(is_active_validator val (current_epoch_f state_ctxt) \<longrightarrow>
        \<not>Validator.effective_balance_f val \<le> EJECTION_BALANCE config) \<Longrightarrow>  \<not>n \<in> list.set aq \<Longrightarrow>  \<not>is_eligible_for_activation_queue val \<Longrightarrow>
  registered_validator val ec (aq :: 64 word list) (state_ctxt :: StateContext) n = val "
  apply (clarsimp simp: registered_validator_def)
  by (case_tac " is_active_validator val (current_epoch_f state_ctxt)"; clarsimp)

lemma registered_validator_another_simp[simp]:
"word_of_nat xa \<in> list.set final_activation_queue \<Longrightarrow> \<not> is_eligible_for_activation_queue (unsafe_var_list_index b (word_of_nat xa)) \<Longrightarrow> exit_epoch_f (unsafe_var_list_index b (word_of_nat xa)) = FAR_FUTURE_EPOCH
         \<Longrightarrow> Validator.effective_balance_f (unsafe_var_list_index b (word_of_nat xa)) \<le> EJECTION_BALANCE config \<Longrightarrow> is_active_validator (unsafe_var_list_index b (word_of_nat xa)) (current_epoch_f state_ctxt) \<Longrightarrow>
     (registered_validator (unsafe_var_list_index b (word_of_nat xa)) aa final_activation_queue state_ctxt (word_of_nat xa)) =
      unsafe_var_list_index b (word_of_nat xa)\<lparr>exit_epoch_f := new_exit_epoch aa state_ctxt,
                                               withdrawable_epoch_f := new_exit_epoch aa state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config), 
                                               activation_epoch_f := current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD\<rparr>"
  by (clarsimp simp: registered_validator_def Let_unfold)

lemma is_active_registered[simp]: "is_active_validator (unsafe_var_list_index b (word_of_nat xa)) (current_epoch_f state_ctxt) \<Longrightarrow>  word_of_nat xa \<in> list.set final_activation_queue \<Longrightarrow>
    exit_epoch_f (unsafe_var_list_index b (word_of_nat xa)) = FAR_FUTURE_EPOCH \<Longrightarrow>
    Validator.effective_balance_f (unsafe_var_list_index b (word_of_nat xa)) \<le> EJECTION_BALANCE config \<Longrightarrow>  current_epoch_f state_ctxt + 1 < new_exit_epoch aa state_ctxt \<Longrightarrow>
    current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD \<le> current_epoch_f state_ctxt + 1 \<Longrightarrow>
    is_active_validator (registered_validator (unsafe_var_list_index b (word_of_nat xa)) aa final_activation_queue state_ctxt (word_of_nat xa)) (current_epoch_f state_ctxt + 1)"
  by (clarsimp simp: registered_validator_def Let_unfold is_active_validator_def)



lemma epoch_triangle_ineq: "a \<le> (b :: Epoch) \<Longrightarrow> b \<le> max b c + d \<Longrightarrow> a \<le> max a c + d"
  by (smt (verit, del_insts) add_diff_cancel_right' epoch_to_u64.simps less_eq_Epoch_def max.orderI max_def
                             order_trans plus_Epoch_def plus_minus_no_overflow_ab word_le_plus_either)

lemma max_epoch_commute: "max a b = max b (a :: Epoch)"
  apply (clarsimp simp: max_def less_eq_Epoch_def)
  by (simp add: epoch_to_u64_bij nle_le)

lemma epoch_triangle_ineq_alt: "a \<le> (b :: 64 word) \<Longrightarrow> b < b + d \<Longrightarrow> c \<le> max b c + d \<Longrightarrow> c \<le> max a c + d"
  by (smt (verit, best) add.commute chain_safe le_no_overflow
                        max.orderI max_def order.strict_implies_order)

lemma epoch_triangle_ineq': "a \<le> (b :: Epoch) \<Longrightarrow> c \<le> max b c + 1 \<Longrightarrow> c \<le> max a c + 1"
  by (smt (verit, ccfv_SIG) epoch_to_u64.simps epoch_triangle_ineq less_eq_Epoch_def linorder_not_le max.absorb1 
            max.absorb_iff2 one_Epoch_def order_less_imp_le plus_Epoch_def unat_1 unat_plus_simple word_overflow_unat)


lemma foldr_sep_empty[simp]: "(foldr (\<and>*) (map (\<lambda>x. \<box>) xs) \<box>) = sep_empty"
  by (induct xs; clarsimp)

lemma foldr_pure_empty[simp]: "xs \<noteq> [] \<Longrightarrow> foldr (\<and>*) (map (\<lambda>x s. \<box> s \<and> P) xs) \<box> = (\<lambda>s. P \<and> sep_empty s) "
  apply (induct xs; clarsimp)
  by (case_tac xs; clarsimp)

lemma " a + 1 \<le> 2 + a \<Longrightarrow> a - (n - a) < a \<Longrightarrow> a \<le> n \<Longrightarrow> n \<noteq> 0 \<Longrightarrow>  (a :: u64) \<le> a + 1" 
  by (metis cancel_comm_monoid_add_class.diff_cancel diff_zero nle_le not_less_iff_gr_or_eq plus_1_less word_order.extremum)

lemma " a + 1 - n < a + 1 \<Longrightarrow>
       n < a + 1 \<Longrightarrow> (a :: u64) - n < a"
  by (metis plus_one_helper sub_wrap word_not_le)

lemma "fold f xs n = foldl (\<lambda>a b. f b a) n xs"
  apply (induct_tac xs; clarsimp)
  by (simp add: foldl_conv_fold)

lemma update_nil_simp[simp]: "is_active_validator (unsafe_var_list_index b (word_of_nat xa)) (current_epoch_f state_ctxt) \<longrightarrow> exit_epoch_f (unsafe_var_list_index b (word_of_nat xa)) = FAR_FUTURE_EPOCH \<longrightarrow> \<not> Validator.effective_balance_f (unsafe_var_list_index b (word_of_nat xa)) \<le> EJECTION_BALANCE config \<Longrightarrow>
          update_exit_cache state_ctxt (unsafe_var_list_index b (word_of_nat xa)) aa = aa"
  by (clarsimp simp: update_exit_cache_def)

lemma registered_validator_another_simplifier[simp]: "is_active_validator (unsafe_var_list_index b (word_of_nat xa)) (current_epoch_f state_ctxt) \<longrightarrow> exit_epoch_f (unsafe_var_list_index b (word_of_nat xa)) = FAR_FUTURE_EPOCH \<longrightarrow> \<not> Validator.effective_balance_f (unsafe_var_list_index b (word_of_nat xa)) \<le> EJECTION_BALANCE config 
  \<Longrightarrow> word_of_nat xa \<in> list.set final_activation_queue \<Longrightarrow>
       \<not> is_eligible_for_activation_queue (unsafe_var_list_index b (word_of_nat xa)) \<Longrightarrow> 
      registered_validator (unsafe_var_list_index b (word_of_nat xa)) aa final_activation_queue state_ctxt (word_of_nat xa) = 
        unsafe_var_list_index b (word_of_nat xa)\<lparr>activation_epoch_f := current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD\<rparr>"
  apply (clarsimp simp: registered_validator_def Let_unfold)
  by (safe; clarsimp?)




lemma registered_validator_another_simplifier'[simp]: "is_active_validator (unsafe_var_list_index b (word_of_nat xa)) (current_epoch_f state_ctxt) \<longrightarrow> exit_epoch_f (unsafe_var_list_index b (word_of_nat xa)) = FAR_FUTURE_EPOCH \<longrightarrow> \<not> Validator.effective_balance_f (unsafe_var_list_index b (word_of_nat xa)) \<le> EJECTION_BALANCE config 
  \<Longrightarrow> \<not>word_of_nat xa \<in> list.set final_activation_queue \<Longrightarrow>
        is_eligible_for_activation_queue (unsafe_var_list_index b (word_of_nat xa)) \<Longrightarrow> 
      registered_validator (unsafe_var_list_index b (word_of_nat xa)) aa final_activation_queue state_ctxt (word_of_nat xa) = 
        unsafe_var_list_index b (word_of_nat xa)\<lparr>activation_eligibility_epoch_f := current_epoch_f state_ctxt + 1\<rparr>"
  apply (clarsimp simp: registered_validator_def Let_unfold split: if_splits)
  by (intro conjI impI; clarsimp?)


lemma registered_validator_another_simplifier''[simp]: "is_active_validator (unsafe_var_list_index b (word_of_nat xa)) (current_epoch_f state_ctxt) \<Longrightarrow> exit_epoch_f (unsafe_var_list_index b (word_of_nat xa)) = FAR_FUTURE_EPOCH \<Longrightarrow>  Validator.effective_balance_f (unsafe_var_list_index b (word_of_nat xa)) \<le> EJECTION_BALANCE config 
  \<Longrightarrow> \<not>word_of_nat xa \<in> list.set final_activation_queue \<Longrightarrow>
        \<not> is_eligible_for_activation_queue (unsafe_var_list_index b (word_of_nat xa)) \<Longrightarrow> 
      registered_validator (unsafe_var_list_index b (word_of_nat xa)) aa final_activation_queue state_ctxt (word_of_nat xa) = 
        unsafe_var_list_index b (word_of_nat xa)\<lparr>exit_epoch_f := new_exit_epoch aa state_ctxt, withdrawable_epoch_f := new_exit_epoch aa state_ctxt + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config)\<rparr>"
  by (clarsimp simp: registered_validator_def Let_unfold)


lemma registered_validator_another_simplifier'''[simp]: "is_active_validator (unsafe_var_list_index b (word_of_nat xa)) (current_epoch_f state_ctxt) \<longrightarrow> exit_epoch_f (unsafe_var_list_index b (word_of_nat xa)) = FAR_FUTURE_EPOCH \<longrightarrow> \<not> Validator.effective_balance_f (unsafe_var_list_index b (word_of_nat xa)) \<le> EJECTION_BALANCE config 
  \<Longrightarrow> \<not>word_of_nat xa \<in> list.set final_activation_queue \<Longrightarrow>
        \<not> is_eligible_for_activation_queue (unsafe_var_list_index b (word_of_nat xa)) \<Longrightarrow> 
      registered_validator (unsafe_var_list_index b (word_of_nat xa)) aa final_activation_queue state_ctxt (word_of_nat xa) = 
        unsafe_var_list_index b (word_of_nat xa)"
  apply (clarsimp simp: registered_validator_def Let_unfold)
  by (safe; clarsimp)



lemma defines pure_cond: "pure_cond state_ctxt \<equiv> \<lambda>(n :: 64 word, ec :: ExitCache, aq :: ActivationQueue, vs :: Validator VariableList) 
                                                  (n' :: 64 word, ec' :: ExitCache, aq' :: ActivationQueue, vs' :: Validator VariableList).
                            get_max_exit_epoch ec \<le> get_max_exit_epoch ec' \<and> n' < n' + 1 \<and>
                            get_max_exit_epoch ec' \<le> max (get_max_exit_epoch ec') (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1 \<and> n \<le> n' \<and>
                            current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD \<le> max (get_max_exit_epoch ec') (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1 \<and>
                            (\<forall>n\<in>ran (exit_epoch_counts_f ec'). n < n + 1) \<and> (\<forall>n\<in>ran (exit_epoch_counts_f ec). n < n + 1) \<and>
                            max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1 \<le> max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1 + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) \<and>
                            max (get_max_exit_epoch ec') (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1 \<le> max (get_max_exit_epoch ec') (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1 + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config)" and
         transformation: "transformation state_ctxt final_activation_queue \<equiv>
                                        \<lambda>(n :: 64 word, ec :: ExitCache, aq :: ActivationQueue, vs :: Validator VariableList) (x :: nat).
                                         (if is_active_validator (registered_validator (unsafe_var_list_index vs (word_of_nat x)) ec final_activation_queue state_ctxt (word_of_nat x)) (next_epoch_f state_ctxt)
                                               then n + 1 else n, 
                                                  update_exit_cache state_ctxt (unsafe_var_list_index vs (word_of_nat x)) ec,
                                                  add_if_could_be_eligible_for_activation aq (word_of_nat x) ((unsafe_var_list_index vs (word_of_nat x))\<lparr>activation_eligibility_epoch_f := if is_eligible_for_activation_queue (unsafe_var_list_index vs (word_of_nat x)) then current_epoch_f state_ctxt + 1 else activation_eligibility_epoch_f (unsafe_var_list_index vs (word_of_nat x))\<rparr>) (next_epoch_f state_ctxt),
                                                  VariableList ((local.var_list_inner vs)[unat ((word_of_nat :: nat \<Rightarrow> 64 word) x) := registered_validator (unsafe_var_list_index vs (word_of_nat x)) ec final_activation_queue state_ctxt (word_of_nat x)]))"



shows  "\<And>(next_epoch_num_active_validators :: ((BeaconState \<times> ('b \<Rightarrow> 'b heap_value option),
        64 word option) lens)).
  (\<And>x. hoare_triple (lift (P x)) (c x) R) \<Longrightarrow> xs = [0..<length (var_list_inner vs)] \<Longrightarrow> 
  hoare_triple (lift (\<lambda>s.  (\<forall>p\<in>(pairs (scanl (\<lambda>b a. transformation state_ctxt final_activation_queue a b) xs  (n, ec, aq, vs) )). pure_cond state_ctxt (fst p) (snd p)) \<and>
     next_epoch_f state_ctxt = current_epoch_f state_ctxt + 1 \<and> length (var_list_inner vs) < 2 ^ 64 \<and> n + of_nat (length (var_list_inner vs)) > n \<and> 
       current_epoch_f state_ctxt + 1 < current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD \<and>
       current_epoch_f state_ctxt \<le> current_epoch_f state_ctxt + 1 \<and>
       current_epoch_f state_ctxt + 1 \<le> current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD \<and>
       get_max_exit_epoch ec \<le> max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1 \<and>
       current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD \<le> max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1 \<and>
        (\<forall>n\<in>ran (exit_epoch_counts_f ec). n < n + 1) \<and>
       max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1 \<le> 
       max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1 + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) \<and>
                           
    ((\<forall>p\<in>(pairs (scanl (\<lambda>b a. transformation state_ctxt final_activation_queue a b) xs  (n, ec, aq, vs) )). pure_cond state_ctxt (fst p) (snd p)) \<and>
       next_epoch_f state_ctxt = current_epoch_f state_ctxt + 1 \<and>
       current_epoch_f state_ctxt + 1 < current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD \<and>
       current_epoch_f state_ctxt \<le> current_epoch_f state_ctxt + 1 \<and>
       current_epoch_f state_ctxt + 1 \<le> current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD \<and>
       get_max_exit_epoch ec \<le> max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1 \<and>
       current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD \<le> max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1 
       \<longrightarrow>
     (next_epoch_num_active_validators \<mapsto>\<^sub>l n \<and>* exit_cache \<mapsto>\<^sub>l ec \<and>* next_epoch_activation_queue \<mapsto>\<^sub>l aq \<and>* validators \<mapsto>\<^sub>l vs \<and>*
      ((case foldl (transformation state_ctxt final_activation_queue) (n, ec, aq, vs) [0..<length (local.var_list_inner vs)] of
          (n, ec, aq, vs) \<Rightarrow> next_epoch_num_active_validators \<mapsto>\<^sub>l n \<and>* exit_cache \<mapsto>\<^sub>l ec \<and>* next_epoch_activation_queue \<mapsto>\<^sub>l aq \<and>* validators \<mapsto>\<^sub>l vs) \<longrightarrow>* P (map (\<lambda>_. ()) xs))) s)))
    (bindCont (forM xs (\<lambda>i. do {
     let n = of_nat i;
     validator <- mut (validators !? n);
     let validator_info = ValidatorInfo.fields n (Validator.effective_balance_f v)
                                               base_reward is_eligible (slashed_f v) is_active_current_epoch
                                               is_active_previous_epoch p_p c_p ;
     _  <- process_single_registry_update validator validator_info ec final_activation_queue next_epoch_activation_queue state_ctxt;
     v  <- read validator;
     _  <- when (is_active_validator v (next_epoch_f state_ctxt)) (next_epoch_num_active_validators := next_epoch_num_active_validators .+ 1);
     return ()})) c) R"
   apply (rule hoare_weaken_pre)
   apply (rule mapM_fake)
    apply (simp only: Let_unfold)                                              

    apply (simp only: bindCont_assoc[symmetric])
  using [[unify_search_bound = 500]]   
    apply (rule var_list_index_lens_wp)
    apply (rule process_single_registry_update_wp)
    apply (rule read_beacon_wp_ex)
    apply (rule when_wp)
    apply (simp only: bindCont_assoc[symmetric] | rule new_state_context_wp'  new_slashings_context_wp' read_beacon_wp_ex add_wp' write_beacon_wp' wp)

     apply (rule read_beacon_wp_ex)
     apply (rule add_wp')
     apply (rule write_beacon_wp)
     apply (simp)
  apply (simp)
   apply (fastforce)

  apply (rule lift_mono')
  apply (rule predicate1I)
  apply (subst mapM_is_sequence_map)
apply (rule_tac g="\<lambda>_. ()" and n="(n,ec,aq,vs)" and P="\<lambda>x.  
          (\<lambda>s. sep_empty s \<and> next_epoch_f state_ctxt = current_epoch_f state_ctxt + 1 \<and> current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD > current_epoch_f state_ctxt + 1 \<and>
               current_epoch_f state_ctxt \<le> current_epoch_f state_ctxt + 1 \<and>
               current_epoch_f state_ctxt + 1 \<le> current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD \<and> max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) \<le> max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1
               ) " and
      Q = "\<lambda>x. sep_empty" and
      S = "\<lambda>(n, ec, aq, vs) s. (next_epoch_num_active_validators \<mapsto>\<^sub>l n \<and>* exit_cache \<mapsto>\<^sub>l ec \<and>* next_epoch_activation_queue \<mapsto>\<^sub>l aq \<and>*  validators \<mapsto>\<^sub>l vs) s \<and> n \<ge> 0 " and 
      D = "(\<lambda>(x, y). pure_cond state_ctxt x y)" and
                 h = "\<lambda>a b. transformation state_ctxt final_activation_queue b a" and
          I="(\<lambda>s. sep_empty s)"  in sequenceI_rewriting''')
     apply (clarsimp)
  apply (thin_tac "(_ \<and>* _) x")

   apply (rule_tac x="(unsafe_var_list_index b (word_of_nat xa))" in exI)
   apply (simp only: sep_conj_ac)
   apply (sep_drule (direct) split_var_list[where n="(word_of_nat xa)" for xa])  


  apply (sep_cancel)+
   apply (rule_tac x="(unsafe_var_list_index b (word_of_nat xa))" in exI)

   apply (safe)
      apply (rule_tac x=aa in exI)
      apply (safe)
        prefer 5
        apply (rule exI, sep_cancel+)
           apply (clarsimp simp: Let_unfold)
              apply (sep_cancel)+
  apply (clarsimp split: prod.splits)
        apply (rule_tac x="registered_validator (unsafe_var_list_index b (word_of_nat xa)) aa final_activation_queue state_ctxt (word_of_nat xa)" in exI)
              apply (intro impI conjI; clarsimp?)
               apply (clarsimp simp: sep_conj_ac)
  apply (subst registered_validator_def, clarsimp)
        apply (sep_cancel)+

           apply (rule_tac x=" a" in exI)
           apply (sep_cancel)+
                apply (intro conjI impI)
  apply (fastforce simp: pure_cond transformation)
               apply (sep_cancel)+

  apply (simp add: transformation pure_cond)
                apply (sep_mp)
                apply (sep_drule spec, sep_mp)
                apply (clarsimp simp add: update_exit_cache_def)
                apply (sep_mp)
                apply (clarsimp)
  apply (subst registered_validator_def, clarsimp)
  apply (sep_cancel)
               apply (sep_cancel)+
 apply (sep_mp)
               apply (sep_drule spec, sep_mp)
  apply (simp add: transformation pure_cond)
               apply (sep_mp)
  apply (simp add: update_exit_cache_def)
               apply (sep_mp, assumption)
              apply (simp add: transformation pure_cond)
  using epoch_triangle_ineq apply blast
             apply (simp add: transformation pure_cond)
  using epoch_triangle_ineq' apply blast
                      apply (simp add: transformation pure_cond)
                      apply (simp add: transformation pure_cond)

  apply (clarsimp)
                      apply fastforce
                     apply (simp add: transformation pure_cond)
                     apply (simp add: transformation pure_cond)

                   apply (simp add: transformation pure_cond)
                   apply (simp add: transformation pure_cond)

                  apply fastforce

          apply (rule_tac x=ab in exI)
          apply (sep_cancel)+
          apply (simp add: Let_unfold)
          apply (sep_cancel)+
          apply (rule exI, intro conjI impI)
           apply (sep_cancel)+
           apply (rule exI, sep_cancel+)
            apply (intro conjI impI)
                   apply (clarsimp simp:  pure_cond transformation registered_validator_def)
            apply (sep_cancel)+
            apply (clarsimp split: prod.splits)
            apply (simp add: transformation pure_cond)
               apply (sep_mp)
                  apply (clarsimp simp: registered_validator_def)
  apply (sep_mp)
               apply (sep_drule spec, sep_mp, assumption)
           apply (sep_cancel)+
apply (clarsimp split: prod.splits)
            apply (simp add: transformation pure_cond)
               apply (sep_mp)
            apply (clarsimp simp: registered_validator_def)
  apply (sep_mp)
               apply (sep_drule spec, sep_mp)
           apply (assumption)
                apply (simp add: transformation pure_cond)
               apply (simp add: transformation pure_cond)
  apply (fastforce simp: transformation pure_cond)
             apply (fastforce simp: transformation pure_cond)
        apply (rule exI)
        apply (sep_cancel)+
        apply (simp add: Let_unfold)
        apply (sep_cancel)+
 apply (rule exI, intro conjI impI)
         apply (sep_cancel)+
         apply (rule exI, sep_cancel+)
         apply (intro conjI impI)
  apply (fastforce simp: pure_cond transformation registered_validator_def)
          apply (sep_cancel)+
apply (clarsimp split: prod.splits)
            apply (simp add: transformation pure_cond)
               apply (sep_mp)
            apply (clarsimp simp: registered_validator_def)
  apply (sep_mp)
               apply (sep_drule spec, sep_mp, assumption)
  apply (sep_cancel)+
apply (clarsimp split: prod.splits)
            apply (simp add: transformation pure_cond)
               apply (sep_mp)
            apply (clarsimp simp: registered_validator_def)
  apply (sep_mp)
            apply (sep_drule spec, sep_mp, assumption)
           apply (simp add: transformation pure_cond)
           apply (simp add: transformation pure_cond)
         apply (simp add: transformation pure_cond)
         apply (simp add: transformation pure_cond)
  apply (meson order_le_less)

  apply (clarsimp)

       apply (rule exI, sep_cancel+)
       apply (clarsimp simp: Let_unfold)
  apply (sep_cancel)
apply (rule exI, intro conjI impI)
         apply (sep_cancel)+
         apply (rule exI, sep_cancel+)
               apply (intro conjI impI)
  apply (fastforce simp: pure_cond transformation registered_validator_def)
  apply (sep_cancel)+
apply (clarsimp split: prod.splits)
            apply (simp add: transformation pure_cond)
               apply (sep_mp)
            apply (clarsimp simp: registered_validator_def)
  apply (sep_mp)
               apply (sep_drule spec, sep_mp, assumption)
               apply (sep_cancel)+
apply (clarsimp split: prod.splits)
               apply (sep_mp)
            apply (simp add: transformation pure_cond)
            apply (clarsimp simp: registered_validator_def)
  apply (sep_mp)
               apply (sep_drule spec, sep_mp, assumption)
            apply (clarsimp)

                apply (simp add: transformation pure_cond)

      apply (rule_tac x=aa in exI, intro conjI impI)
                    apply (meson epoch_triangle_ineq)
  apply (meson epoch_triangle_ineq')

                apply (simp add: transformation pure_cond)

  apply (meson order_le_less)
                apply (clarsimp)
                apply (rule exI, sep_cancel+)
                apply (rule exI)
                apply (intro conjI impI)
                 apply (sep_cancel)+
                 apply (rule exI, sep_cancel+)
                 apply (intro conjI impI)
                  apply (clarsimp)                  apply (clarsimp)
  apply (sep_cancel)+
                 apply (sep_mp)
               apply (sep_drule spec, sep_mp)

            apply (clarsimp simp: update_exit_cache_def)
            apply (sep_mp)
               apply (assumption)

                apply (clarsimp)
                apply (sep_cancel)+
                apply (sep_drule spec, sep_mp)
apply (clarsimp simp: update_exit_cache_def)
            apply (sep_mp)
               apply (assumption)
              apply (simp add: transformation pure_cond)
  using epoch_triangle_ineq apply blast

              apply (simp add: transformation pure_cond)
  using epoch_triangle_ineq' apply blast
           apply (simp add: transformation pure_cond)
          apply (meson epoch_triangle_ineq)
  apply (meson epoch_triangle_ineq')
           apply (simp add: transformation pure_cond)
  apply (meson order_le_less)

  apply (clarsimp)
            apply (rule exI, sep_cancel+)
apply (rule exI, intro conjI impI)
           apply (sep_cancel)+
apply (rule exI, sep_cancel+)
               apply (intro conjI impI)
  apply (fastforce simp: pure_cond transformation registered_validator_def)
              apply (sep_cancel)+
       apply (clarsimp split: prod.splits)
            apply (sep_mp)
            apply (clarsimp simp: registered_validator_not_eligible_simp)
        apply (sep_drule spec, sep_mp)
  apply (assumption)
           apply (sep_cancel)+
           apply (clarsimp split: prod.splits)
           apply (sep_drule spec, sep_mp, assumption)
          apply (rule_tac x=aa in exI)
          apply (intro conjI impI)
              apply (simp add: transformation pure_cond)
  using epoch_triangle_ineq apply blast

              apply (simp add: transformation pure_cond)
  using epoch_triangle_ineq' apply blast
            apply (simp add: transformation pure_cond)
              apply (fastforce simp add: transformation pure_cond)

             apply (rule exI, sep_cancel+)
             apply (simp add: Let_unfold)
             apply (sep_cancel)+
apply (rule exI, intro conjI impI)
         apply (sep_cancel)+
         apply (rule exI, sep_cancel+)
               apply (intro conjI impI)
                defer
  apply (sep_cancel)+
apply (clarsimp split: prod.splits)
            apply (simp add: transformation pure_cond)
               apply (sep_mp)
            apply (clarsimp simp: registered_validator_def)
  apply (sep_mp)
               apply (sep_drule spec, sep_mp)
            apply (clarsimp simp: update_exit_cache_def)
            apply (sep_mp)
               apply (assumption)
              apply (sep_cancel)+
              apply (simp add: transformation pure_cond)
            apply (clarsimp simp: registered_validator_not_eligible_simp)
              apply (clarsimp simp: registered_validator_def)
              apply (sep_drule spec, sep_mp)
 apply (clarsimp simp: update_exit_cache_def)
              apply (sep_mp)
              apply (assumption)
          apply (simp add: transformation pure_cond)
              apply (simp add: transformation pure_cond)
              apply (simp add: transformation pure_cond)
              apply (fastforce simp add: transformation pure_cond)

           apply (rule exI, sep_cancel+)
           apply (simp add: Let_unfold)
           apply (intro conjI impI)
  apply (sep_cancel)+
apply (rule exI, intro conjI impI)
         apply (sep_cancel)+
         apply (rule exI, sep_cancel+)
           apply (intro conjI impI)
  apply (fastforce simp: pure_cond)
                apply (sep_cancel)+
            apply (clarsimp simp: registered_validator_not_eligible_simp split: prod.splits)
               apply (sep_cancel)+
              apply (simp add: transformation pure_cond)
              apply (simp add: transformation pure_cond)
              apply (simp add: transformation pure_cond)
            apply (sep_cancel)+
apply (rule exI, intro conjI impI)
         apply (sep_cancel)+
         apply (rule exI, sep_cancel+)
               apply (intro conjI impI)
  apply (fastforce simp: pure_cond transformation registered_validator_def)
              apply (sep_cancel)+
              apply (clarsimp  split: prod.splits)
              apply (clarsimp simp: transformation pure_cond registered_validator_not_eligible_simp registered_validator_not_eligible_simp'  split: prod.splits)

       apply (sep_drule spec, sep_mp, assumption)


             apply (sep_cancel)+
              apply (clarsimp simp: transformation pure_cond registered_validator_not_eligible_simp registered_validator_not_eligible_simp'  split: prod.splits)
             apply (sep_drule spec, sep_mp, assumption)
            apply (rule_tac x=aa in exI)
  apply (intro conjI impI)
              apply (simp add: transformation pure_cond)
  using epoch_triangle_ineq apply blast

              apply (simp add: transformation pure_cond)
  using epoch_triangle_ineq' apply blast
                 apply (fastforce simp: pure_cond transformation registered_validator_def)
  apply (fastforce simp: transformation pure_cond)
  apply (rule exI | sep_cancel+ | intro conjI impI | 
         clarsimp simp: registered_validator_not_eligible_simp registered_validator_not_eligible_simp' registered_validator_not_eligible_simp''  split: prod.splits |
         (sep_drule sep_mp_mp, erule_tac x=xa in ballE, fastforce, fastforce) | (sep_drule spec, sep_mp) |  (clarsimp simp add: transformation pure_cond) | sep_mp)+
                 apply (clarsimp simp add: update_exit_cache_def)
             apply (sep_mp, assumption)
 apply (rule exI | sep_cancel+ | intro conjI impI | 
         clarsimp simp: registered_validator_not_eligible_simp registered_validator_not_eligible_simp' registered_validator_not_eligible_simp''  split: prod.splits |
         (sep_drule sep_mp_mp, erule_tac x=xa in ballE, fastforce, fastforce) | (sep_drule spec, sep_mp) | sep_mp)+
 apply (simp add: update_exit_cache_def transformation registered_validator_not_eligible_simp registered_validator_not_eligible_simp' registered_validator_not_eligible_simp'')
            apply (sep_mp, assumption)

 apply (rule exI | sep_cancel+ | intro conjI impI | 
         clarsimp simp: registered_validator_not_eligible_simp registered_validator_not_eligible_simp' registered_validator_not_eligible_simp''  split: prod.splits |
         (sep_drule sep_mp_mp, erule_tac x=xa in ballE, fastforce, fastforce) | (sep_drule spec, sep_mp) | sep_mp)+
         apply (simp add: transformation pure_cond)
        apply (simp add: transformation pure_cond)
        apply (simp add: transformation pure_cond)
        apply (simp add: transformation pure_cond)
        apply (fastforce simp add: transformation pure_cond)

 apply (rule exI | sep_cancel+ | intro conjI impI | 
         clarsimp simp: registered_validator_not_eligible_simp registered_validator_not_eligible_simp' registered_validator_not_eligible_simp''  split: prod.splits |
         (sep_drule sep_mp_mp, erule_tac x=xa in ballE, fastforce, fastforce) | (sep_drule spec, sep_mp) | sep_mp)+
              apply (fastforce simp: pure_cond transformation registered_validator_def)

 apply (rule exI | sep_cancel+ | intro conjI impI | 
         clarsimp simp: registered_validator_not_eligible_simp registered_validator_not_eligible_simp' registered_validator_not_eligible_simp''  split: prod.splits |
         (sep_drule sep_mp_mp, erule_tac x=xa in ballE, fastforce, fastforce) | (sep_drule spec, sep_mp) | sep_mp)+
      apply (clarsimp simp: transformation pure_cond)
      apply (sep_mp, assumption)
     apply (sep_cancel)+

 apply (rule exI | sep_cancel+ | intro conjI impI | 
         clarsimp simp: registered_validator_not_eligible_simp registered_validator_not_eligible_simp' registered_validator_not_eligible_simp''  split: prod.splits |
         (sep_drule sep_mp_mp, erule_tac x=xa in ballE, fastforce, fastforce) | (sep_drule spec, sep_mp) | (clarsimp simp add: transformation pure_cond) | sep_mp)+


  apply (clarsimp simp: foldl_conv_fold)
    apply (sep_mp, fastforce)
   defer
   apply (fastforce simp: pure_cond transformation registered_validator_def)
  by (fastforce)

  


definition mk_val_info :: "Validator VariableList \<Rightarrow> Epoch \<Rightarrow> Epoch \<Rightarrow> ParticipationFlags VariableList \<Rightarrow> ParticipationFlags VariableList \<Rightarrow> BaseRewardsCache \<Rightarrow> nat \<Rightarrow> ValidatorInfo"
  where "mk_val_info vs curr_epoch prev_epoch cep pep brc n = (make_validator_info (unsafe_var_list_index vs (word_of_nat n)) curr_epoch prev_epoch
                                            (unsafe_var_list_index cep (word_of_nat n)) (unsafe_var_list_index pep (word_of_nat n)) brc n)"

lemma make_mk_simp: "make_validator_info vs[n]! curr_epoch prev_epoch cep[n]! pep[n]! brc n = mk_val_info vs curr_epoch prev_epoch cep pep brc n"
  by (clarsimp simp: mk_val_info_def index_var_list_def)


definition "new_effective_balance' effective_balances_ctxt eff_balance balance \<equiv>
             (if balance + downward_threshold_f effective_balances_ctxt
                 < eff_balance \<or>
                  eff_balance + upward_threshold_f effective_balances_ctxt
                 < balance
              then min (balance -
                        balance mod EFFECTIVE_BALANCE_INCREMENT config)
                    MAX_EFFECTIVE_BALANCE
              else eff_balance)"



lemma updated_balance_fold: "slashed_f v' \<Longrightarrow> target_withdrawable_epoch_f slashings_ctxt = withdrawable_epoch_f v' \<Longrightarrow> 
              saturating_sub
               (processed_reward (inactive_penalty_delta (Validator.effective_balance_f v) i val_info) (map (penalise state_ctxt val_info) [0, 1])
                 (map (reward rewards_ctxt state_ctxt val_info) [0, 1, 2]) b val_info)
               (Validator.effective_balance_f v' div EFFECTIVE_BALANCE_INCREMENT config * adjusted_total_slashing_balance_f slashings_ctxt div total_active_balance_f progressive_balances * EFFECTIVE_BALANCE_INCREMENT config)
          =   updated_balance val_info v v' i slashings_ctxt progressive_balances rewards_ctxt state_ctxt b"
  by (clarsimp simp: updated_balance_def)

lemma updated_balance_fold': "slashed_f v' \<longrightarrow> \<not>target_withdrawable_epoch_f slashings_ctxt = withdrawable_epoch_f v' \<Longrightarrow>
 processed_reward (inactive_penalty_delta (Validator.effective_balance_f v) i val_info) (map (penalise state_ctxt val_info) [0, 1])
               (map (reward rewards_ctxt state_ctxt val_info) [0, 1, 2]) b val_info =  updated_balance val_info v v' i slashings_ctxt progressive_balances rewards_ctxt state_ctxt b"
  by (clarsimp simp: updated_balance_def)

definition single_slashing where
  "single_slashing validator balance effective_balance_increment slashings_ctxt progressive_balances \<equiv>
                                 (if Validator.slashed_f validator \<and> 
                                            target_withdrawable_epoch_f slashings_ctxt = withdrawable_epoch_f validator
                                          then
                                             saturating_sub balance (effective_balance_increment * adjusted_total_slashing_balance_f slashings_ctxt div total_active_balance_f progressive_balances *
                                             EFFECTIVE_BALANCE_INCREMENT config)
                                          else balance)"

lemma process_single_slashing'[wp]:
   "(\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow>
   hoare_triple (lift (\<lambda>s. let effective_balance = Validator.effective_balance_f validator in
                           let effective_balance_increment = (effective_balance div EFFECTIVE_BALANCE_INCREMENT config) in
                           let result = single_slashing validator balance effective_balance_increment slashings_ctxt progressive_balances in 
                        safe_mul (adjusted_total_slashing_balance_f slashings_ctxt) effective_balance_increment \<and>
                        total_active_balance_f progressive_balances \<noteq> 0  \<and>
                         safe_mul (EFFECTIVE_BALANCE_INCREMENT config)
                         (effective_balance_increment * adjusted_total_slashing_balance_f slashings_ctxt div total_active_balance_f progressive_balances) \<and>
                        
                         (safe_mul (adjusted_total_slashing_balance_f slashings_ctxt) effective_balance_increment \<and>
                           total_active_balance_f progressive_balances \<noteq> 0  \<and>
                           safe_mul (EFFECTIVE_BALANCE_INCREMENT config)
                          (effective_balance_increment * adjusted_total_slashing_balance_f slashings_ctxt div total_active_balance_f progressive_balances) \<longrightarrow>
                          P result s)))
    (bindCont (process_single_slashing balance validator slashings_ctxt progressive_balances) c) Q"
  apply (rule hoare_weaken_pre, wp)
  by (clarsimp simp: single_slashing_def)



lemma effective_balance_f_simp'[simp]:"ValidatorInfo.effective_balance_f (mk_val_info vs curr_epoch prev_epoch cep pep brc n) = Validator.effective_balance_f (vs[n]!)"
  by (clarsimp simp: mk_val_info_def index_var_list_def make_validator_info_def)

lemma var_map_index_id'[simp]: " n = length (var_list_inner vs) \<Longrightarrow> n < 2 ^ 64 \<Longrightarrow> VariableList (map (\<lambda>x. unsafe_var_list_index vs ((word_of_nat x) :: 64 word)) [0..<n]) = vs"
  apply (case_tac vs; clarsimp simp: unsafe_var_list_index_def)
  apply (intro nth_equalityI; clarsimp)
  apply (unat_arith, clarsimp)
  by (subst unat_of_nat64', clarsimp, clarsimp)


definition 
   updated_effective_balance_validators :: "EffectiveBalancesContext \<Rightarrow> StateContext \<Rightarrow> RewardsAndPenaltiesContext \<Rightarrow> SlashingsContext \<Rightarrow> Epoch \<Rightarrow> Epoch \<Rightarrow> ProgressiveBalancesCache \<Rightarrow>
                                            64 word VariableList \<Rightarrow> 64 word VariableList \<Rightarrow> BaseRewardsCache \<Rightarrow> ParticipationFlags VariableList \<Rightarrow> ParticipationFlags VariableList \<Rightarrow>
                                            Validator VariableList \<Rightarrow> Validator VariableList"
   where "updated_effective_balance_validators effective_balances_ctxt state_ctxt rewards_ctxt slashings_ctxt prev_epoch curr_epoch progressive_balances bs is brc pep cep vs =
         VariableList
          (map (\<lambda>x. update_effective_balance (vs[x]!)
                      (updated_balance (make_validator_info (vs[x]!) curr_epoch prev_epoch (cep[x]!) (pep[x]!) brc x) (vs[x]!) (vs[x]!) (is[x]!) slashings_ctxt progressive_balances rewards_ctxt state_ctxt
                        (bs[x]!))
                      effective_balances_ctxt)
            [0..<length (local.var_list_inner vs)])"

definition 
   updated_balances :: "StateContext \<Rightarrow> RewardsAndPenaltiesContext \<Rightarrow> SlashingsContext \<Rightarrow> Epoch \<Rightarrow> Epoch \<Rightarrow> ProgressiveBalancesCache \<Rightarrow>
                                            Validator VariableList \<Rightarrow> 64 word VariableList \<Rightarrow> BaseRewardsCache \<Rightarrow> ParticipationFlags VariableList \<Rightarrow> ParticipationFlags VariableList \<Rightarrow>
                                             64 word VariableList \<Rightarrow> 64 word VariableList"
   where "updated_balances state_ctxt rewards_ctxt slashings_ctxt prev_epoch curr_epoch progressive_balances vs is brc pep cep bs =         
          VariableList
          (map (\<lambda>x. updated_balance (make_validator_info (vs[x]!) curr_epoch prev_epoch (cep[x]!) (pep[x]!) brc x) (vs[x]!) (vs[x]!) (is[x]!) slashings_ctxt progressive_balances rewards_ctxt state_ctxt
                      (bs[x]!))
            [0..<length (local.var_list_inner bs)])"

definition updated_inactivity_scores 
  where "updated_inactivity_scores state_ctxt rewards_ctxt slashings_ctxt prev_epoch curr_epoch progressive_balances brc pep cep vs is =  VariableList 
    (map (\<lambda>x. single_inactivity_update (is[x]!) (make_validator_info (vs[x]!) curr_epoch prev_epoch (cep[x]!) (pep[x]!) brc x) state_ctxt) [0..<length (local.var_list_inner vs)])"


lemma fold_pair_split: "fold (\<lambda>n (a,b). (f a n, g b n)) xs n = ((fold (\<lambda>n a. f a n) xs (fst n)), (fold (\<lambda>n b. g b n) xs (snd n))) "
  by (induct xs arbitrary: n; clarsimp)


definition updated_ebrc :: "StateContext \<Rightarrow> RewardsAndPenaltiesContext \<Rightarrow>
                            ProgressiveBalancesCache \<Rightarrow> EffectiveBalancesContext \<Rightarrow> 
                            SlashingsContext \<Rightarrow> BaseRewardsCache \<Rightarrow> Epoch \<Rightarrow> Epoch \<Rightarrow> ParticipationFlags VariableList \<Rightarrow>
                            ParticipationFlags VariableList \<Rightarrow> 64 word VariableList \<Rightarrow> 64 word VariableList \<Rightarrow> Validator VariableList \<Rightarrow> BaseRewardsCache \<Rightarrow> BaseRewardsCache"
  where "updated_ebrc state_ctxt rewards_ctxt progressive_balances effective_balances_ctxt slashings_ctxt brc prev_epoch curr_epoch pep cep bs is vs ebrc \<equiv> (fold
      (\<lambda>x ebrc. ebrc
          \<lparr>effective_balances_f :=
             effective_balances_f ebrc @
             [new_effective_balance' effective_balances_ctxt (Validator.effective_balance_f (vs[x]!))
               (updated_balance (make_validator_info (vs[x]!) curr_epoch prev_epoch (cep[x]!) (pep[x]!) brc x) (vs[x]!) (vs[x]!) (is[x]!) slashings_ctxt progressive_balances rewards_ctxt state_ctxt
                 (bs[x]!))]\<rparr>)
      [0..<length (local.var_list_inner vs)] ebrc)"

definition updated_epb :: "StateContext \<Rightarrow> RewardsAndPenaltiesContext \<Rightarrow>
                            ProgressiveBalancesCache \<Rightarrow> EffectiveBalancesContext \<Rightarrow> 
                            SlashingsContext \<Rightarrow> BaseRewardsCache \<Rightarrow> Epoch \<Rightarrow> Epoch \<Rightarrow> ParticipationFlags VariableList \<Rightarrow>
                            ParticipationFlags VariableList \<Rightarrow> 64 word VariableList \<Rightarrow> 64 word VariableList \<Rightarrow> Validator VariableList \<Rightarrow> ProgressiveBalancesCache \<Rightarrow> ProgressiveBalancesCache"
  where "updated_epb state_ctxt rewards_ctxt progressive_balances effective_balances_ctxt slashings_ctxt brc prev_epoch curr_epoch pep cep bs is vs epb \<equiv>
      (fold
      (\<lambda>x epb.
          updated_nepb epb
           (update_effective_balance (vs[x]!)
             (updated_balance (make_validator_info (vs[x]!) curr_epoch prev_epoch (cep[x]!) (pep[x]!) brc x) (vs[x]!) (vs[x]!) (is[x]!) slashings_ctxt progressive_balances rewards_ctxt state_ctxt
                 (bs[x]!))
             effective_balances_ctxt)
           (cep[x]!) (current_epoch_f state_ctxt + 1) (Validator.effective_balance_f (vs[x]!)))
      [0..<length (local.var_list_inner vs)] epb)"



definition "previous_participating_attesting_balances epb cep v = {previous_epoch_flag_attesting_balances_f epb ! n' |n'. n' \<le> length (participation_flag_weights cep[v]!) \<and> has_flag cep[v]! n'}"

definition "valid_transition effective_balances_ctxt bs state_ctxt rewards_ctxt progressive_balances slashings_ctxt is epb brc pep  cep prev_epoch curr_epoch n vs\<equiv> 
          let v_info = make_validator_info (index_var_list vs n) curr_epoch prev_epoch (index_var_list cep n) (index_var_list pep n) brc n in
                   total_active_balance_f epb \<le> total_active_balance_f epb + single_effective_balance_updated (updated_balance v_info (index_var_list vs n)  (index_var_list vs n)  (index_var_list is n) slashings_ctxt progressive_balances rewards_ctxt state_ctxt  (index_var_list bs n)) effective_balances_ctxt vs[n]! \<and>
                   total_active_balance_f epb \<le> total_active_balance_f epb + Validator.effective_balance_f (vs[n]!) \<and>
                   (\<forall>previous_epoch_flag_attesting_balance\<in>(previous_participating_attesting_balances epb cep n).
                       previous_epoch_flag_attesting_balance \<le> previous_epoch_flag_attesting_balance + (single_effective_balance_updated (updated_balance v_info (vs[n]!) (vs[n]!) (is[n]!) slashings_ctxt progressive_balances rewards_ctxt state_ctxt bs[n]!) effective_balances_ctxt vs[n]! - ValidatorInfo.effective_balance_f v_info) \<and>
                       ValidatorInfo.effective_balance_f v_info - single_effective_balance_updated (updated_balance v_info (vs[n]!) (vs[n]!) (is[n]!) slashings_ctxt progressive_balances rewards_ctxt state_ctxt (bs[n]!)) effective_balances_ctxt vs[n]! \<le> previous_epoch_flag_attesting_balance)"

definition safe_transitions_main_loop
  where "safe_transitions_main_loop effective_balances_ctxt slashings_ctxt progressive_balances rewards_ctxt state_ctxt curr_epoch prev_epoch cep pep brc bs is vs ebrc epb \<equiv> 
   \<forall>(v, (ebrc, epb), _)\<in>(trans (\<lambda>n (ebrc, epb).
               let v_info = make_validator_info (index_var_list vs n) curr_epoch prev_epoch (index_var_list cep n) (index_var_list pep n) brc n in
               let new_balance = updated_balance v_info  (index_var_list vs n)  (index_var_list vs n)  (index_var_list is n) slashings_ctxt progressive_balances rewards_ctxt state_ctxt  (index_var_list bs n) in
               (ebrc\<lparr>effective_balances_f := effective_balances_f ebrc @ [new_effective_balance' effective_balances_ctxt (Validator.effective_balance_f vs[n]!) new_balance]\<rparr>,
                updated_nepb epb (update_effective_balance vs[n]! new_balance effective_balances_ctxt) cep[n]! (current_epoch_f state_ctxt + 1) (Validator.effective_balance_f vs[n]!)))
                [0..<length (local.var_list_inner vs)] (ebrc, epb)). valid_transition effective_balances_ctxt bs state_ctxt rewards_ctxt progressive_balances slashings_ctxt is epb brc pep  cep prev_epoch curr_epoch v vs
                "



definition pre_pure: 
"pre_pure epb ebrc effective_balances_ctxt final_activation_queue pep cep prev_epoch curr_epoch bs brc ec progressive_balances slashings_ctxt rewards_ctxt vs is xs state_ctxt \<equiv>
       epoch_to_u64 prev_epoch \<le> epoch_to_u64 prev_epoch + 1 \<and> (local.var_list_inner vs) \<noteq> [] \<and>  length (base_rewards_f brc) < 2^64 \<and>
       (next_epoch_f state_ctxt = current_epoch_f state_ctxt + 1) \<and>
       safe_transitions_main_loop effective_balances_ctxt slashings_ctxt progressive_balances rewards_ctxt state_ctxt curr_epoch prev_epoch cep pep brc bs is vs ebrc epb \<and>
       ( current_epoch_f state_ctxt + 1 < current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) \<and>
       (\<forall>x\<in>list.set xs. safe_mul (unsafe_var_list_index is ((word_of_nat :: nat => 64 word) x)) (Validator.effective_balance_f (unsafe_var_list_index vs ((word_of_nat :: nat => 64 word) x)))) \<and>
       ( current_epoch_f state_ctxt \<le> current_epoch_f state_ctxt + 1) \<and>
       ( safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR) \<and>
       ( safe_mul INACTIVITY_PENALTY_QUOTIENT_ALTAIR (INACTIVITY_SCORE_BIAS config)) \<and>
       ( active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0) \<and>
       (\<forall>x\<in>list.set xs. safe_mul (adjusted_total_slashing_balance_f slashings_ctxt) (Validator.effective_balance_f (unsafe_var_list_index vs ((word_of_nat :: nat => 64 word) x)) div EFFECTIVE_BALANCE_INCREMENT config)) \<and>
       ( total_active_balance_f progressive_balances \<noteq> 0) \<and>
       (\<forall>x\<in>list.set xs. safe_mul (EFFECTIVE_BALANCE_INCREMENT config) (Validator.effective_balance_f (unsafe_var_list_index vs ((word_of_nat :: nat => 64 word) x)) div EFFECTIVE_BALANCE_INCREMENT config * adjusted_total_slashing_balance_f slashings_ctxt div total_active_balance_f progressive_balances)) \<and>
       ( current_epoch_f state_ctxt + 1 \<le> current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) \<and>
       ( get_max_exit_epoch ec \<le> max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1) \<and>
       ( current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD \<le> max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1) \<and>
       (\<forall>x\<in>list.set xs. (word_of_nat :: nat => 64 word) x < (word_of_nat :: nat => 64 word) (length (effective_balances_f brc))) \<and>
       (\<forall>x\<in>list.set xs. effective_balances_f brc ! unat ((word_of_nat :: nat => 64 word) x) div EFFECTIVE_BALANCE_INCREMENT config < (word_of_nat :: nat => 64 word) (length (base_rewards_f brc))) \<and>
       (\<forall>x\<in>list.set xs. unsafe_var_list_index is ((word_of_nat :: nat => 64 word) x) \<le> unsafe_var_list_index is ((word_of_nat :: nat => 64 word) x) + INACTIVITY_SCORE_BIAS config) \<and>
       ( 3 \<le> length (unslashed_participating_increments_array_f rewards_ctxt)) \<and>
       (\<forall>x\<in>list.set xs. safe_mul TIMELY_SOURCE_WEIGHT (base_rewards_f brc ! unat (effective_balances_f brc ! unat ((word_of_nat :: nat => 64 word) x) div EFFECTIVE_BALANCE_INCREMENT config))) \<and>
       (\<forall>x\<in>list.set xs. safe_mul (TIMELY_SOURCE_WEIGHT * base_rewards_f brc ! unat (effective_balances_f brc ! unat ((word_of_nat :: nat => 64 word) x) div EFFECTIVE_BALANCE_INCREMENT config)) (unslashed_participating_increments_array_f rewards_ctxt ! 0)) \<and>
       (\<forall>x\<in>list.set xs. safe_mul TIMELY_TARGET_WEIGHT (base_rewards_f brc ! unat (effective_balances_f brc ! unat ((word_of_nat :: nat => 64 word) x) div EFFECTIVE_BALANCE_INCREMENT config))) \<and>
       (\<forall>x\<in>list.set xs. safe_mul (TIMELY_TARGET_WEIGHT * base_rewards_f brc ! unat (effective_balances_f brc ! unat ((word_of_nat :: nat => 64 word) x) div EFFECTIVE_BALANCE_INCREMENT config)) (unslashed_participating_increments_array_f rewards_ctxt ! Suc 0)) \<and>
       (\<forall>x\<in>list.set xs. safe_mul TIMELY_HEAD_WEIGHT (base_rewards_f brc ! unat (effective_balances_f brc ! unat ((word_of_nat :: nat => 64 word) x) div EFFECTIVE_BALANCE_INCREMENT config))) \<and>
       (\<forall>x\<in>list.set xs. safe_mul (TIMELY_HEAD_WEIGHT * base_rewards_f brc ! unat (effective_balances_f brc ! unat ((word_of_nat :: nat => 64 word) x) div EFFECTIVE_BALANCE_INCREMENT config)) (unslashed_participating_increments_array_f rewards_ctxt ! 2)) \<and>
       (\<forall>x\<in>list.set xs.
           unsafe_var_list_index bs ((word_of_nat :: nat => 64 word) x)
           \<le> unsafe_var_list_index bs ((word_of_nat :: nat => 64 word) x) +
              (reward rewards_ctxt state_ctxt (make_validator_info (unsafe_var_list_index vs ((word_of_nat :: nat => 64 word) x)) curr_epoch prev_epoch (unsafe_var_list_index cep ((word_of_nat :: nat => 64 word) x)) (unsafe_var_list_index pep ((word_of_nat :: nat => 64 word) x)) brc x) 0 +
               (reward rewards_ctxt state_ctxt (make_validator_info (unsafe_var_list_index vs ((word_of_nat :: nat => 64 word) x)) curr_epoch prev_epoch (unsafe_var_list_index cep ((word_of_nat :: nat => 64 word) x)) (unsafe_var_list_index pep ((word_of_nat :: nat => 64 word) x)) brc x) (Suc 0) + reward rewards_ctxt state_ctxt (make_validator_info (unsafe_var_list_index vs ((word_of_nat :: nat => 64 word) x)) curr_epoch prev_epoch (unsafe_var_list_index cep ((word_of_nat :: nat => 64 word) x)) (unsafe_var_list_index pep ((word_of_nat :: nat => 64 word) x)) brc x) 2))) \<and>
       (\<forall>x\<in>list.set xs.
           let inactive_pd = inactive_penalty_delta (Validator.effective_balance_f (unsafe_var_list_index vs ((word_of_nat :: nat => 64 word) x))) (unsafe_var_list_index is ((word_of_nat :: nat => 64 word) x)) (make_validator_info (unsafe_var_list_index vs ((word_of_nat :: nat => 64 word) x)) curr_epoch prev_epoch (unsafe_var_list_index cep ((word_of_nat :: nat => 64 word) x)) (unsafe_var_list_index pep ((word_of_nat :: nat => 64 word) x)) brc x)
           in unat (reward rewards_ctxt state_ctxt (make_validator_info (unsafe_var_list_index vs ((word_of_nat :: nat => 64 word) x)) curr_epoch prev_epoch (unsafe_var_list_index cep ((word_of_nat :: nat => 64 word) x)) (unsafe_var_list_index pep ((word_of_nat :: nat => 64 word) x)) brc x) 0) +
              (unat (reward rewards_ctxt state_ctxt (make_validator_info (unsafe_var_list_index vs ((word_of_nat :: nat => 64 word) x)) curr_epoch prev_epoch (unsafe_var_list_index cep ((word_of_nat :: nat => 64 word) x)) (unsafe_var_list_index pep ((word_of_nat :: nat => 64 word) x)) brc x) (Suc 0)) + unat (reward rewards_ctxt state_ctxt (make_validator_info (unsafe_var_list_index vs ((word_of_nat :: nat => 64 word) x)) curr_epoch prev_epoch (unsafe_var_list_index cep ((word_of_nat :: nat => 64 word) x)) (unsafe_var_list_index pep ((word_of_nat :: nat => 64 word) x)) brc x) 2)) +
              unat inactive_pd
              < 2 ^ 64 \<and>
              unat (penalise state_ctxt (make_validator_info (unsafe_var_list_index vs ((word_of_nat :: nat => 64 word) x)) curr_epoch prev_epoch (unsafe_var_list_index cep ((word_of_nat :: nat => 64 word) x)) (unsafe_var_list_index pep ((word_of_nat :: nat => 64 word) x)) brc x) 0) + unat (penalise state_ctxt (make_validator_info (unsafe_var_list_index vs ((word_of_nat :: nat => 64 word) x)) curr_epoch prev_epoch (unsafe_var_list_index cep ((word_of_nat :: nat => 64 word) x)) (unsafe_var_list_index pep ((word_of_nat :: nat => 64 word) x)) brc x) (Suc 0)) + unat inactive_pd
              < 2 ^ 64) \<and>
       (\<forall>x\<in>{0..<length (local.var_list_inner vs)}.
           let upd_balance =
                 updated_balance (make_validator_info (unsafe_var_list_index vs (word_of_nat x)) curr_epoch prev_epoch (unsafe_var_list_index cep (word_of_nat x)) (unsafe_var_list_index pep (word_of_nat x)) brc x) (unsafe_var_list_index vs (word_of_nat x)) (unsafe_var_list_index vs (word_of_nat x)) (unsafe_var_list_index is (word_of_nat x)) slashings_ctxt progressive_balances rewards_ctxt state_ctxt
                  (unsafe_var_list_index bs (word_of_nat x));
               upd_val = vs[x]!
           in upd_balance \<le> upd_balance + downward_threshold_f effective_balances_ctxt \<and>
              total_active_balance_f epb \<le> total_active_balance_f epb + min (upd_balance - upd_balance mod EFFECTIVE_BALANCE_INCREMENT config) MAX_EFFECTIVE_BALANCE \<and>
              Validator.effective_balance_f upd_val \<le> Validator.effective_balance_f upd_val + upward_threshold_f effective_balances_ctxt \<and>
              total_active_balance_f epb \<le> total_active_balance_f epb + Validator.effective_balance_f upd_val \<and>
              (\<forall>n. n \<le> length (participation_flag_weights (unsafe_var_list_index cep (word_of_nat x))) \<and> has_flag (unsafe_var_list_index cep (word_of_nat x)) n \<longrightarrow>
                   (upd_balance - upd_balance mod EFFECTIVE_BALANCE_INCREMENT config \<le> Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) \<longrightarrow> Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) - (upd_balance - upd_balance mod EFFECTIVE_BALANCE_INCREMENT config) \<le> previous_epoch_flag_attesting_balances_f epb ! n) \<and>
                   (Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) \<le> Validator.effective_balance_f upd_val \<longrightarrow> previous_epoch_flag_attesting_balances_f epb ! n \<le> previous_epoch_flag_attesting_balances_f epb ! n + (Validator.effective_balance_f upd_val - Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)))) \<and>
                   Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) - Validator.effective_balance_f upd_val \<le> previous_epoch_flag_attesting_balances_f epb ! n \<and>
                   previous_epoch_flag_attesting_balances_f epb ! n \<le> previous_epoch_flag_attesting_balances_f epb ! n + (min (upd_balance - upd_balance mod EFFECTIVE_BALANCE_INCREMENT config) MAX_EFFECTIVE_BALANCE - Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x))))) \<and>
       (\<forall>x\<in>{0..<length (local.var_list_inner vs)}. Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) < MAX_EFFECTIVE_BALANCE) \<and>
       (\<forall>x\<in>{0..<length (local.var_list_inner vs)}.
           \<forall>n. n \<le> length (participation_flag_weights (unsafe_var_list_index cep (word_of_nat x))) \<and> has_flag (unsafe_var_list_index cep (word_of_nat x)) n \<longrightarrow>
               (let upd_balance =
                      updated_balance (make_validator_info (unsafe_var_list_index vs (word_of_nat x)) curr_epoch prev_epoch (unsafe_var_list_index cep (word_of_nat x)) (unsafe_var_list_index pep (word_of_nat x)) brc x) (unsafe_var_list_index vs (word_of_nat x))
                       (updated_validator (unsafe_var_list_index vs (word_of_nat x)) ec state_ctxt final_activation_queue brc (unsafe_var_list_index pep (word_of_nat x)) (unsafe_var_list_index cep (word_of_nat x)) prev_epoch curr_epoch x) (unsafe_var_list_index is (word_of_nat x)) slashings_ctxt progressive_balances rewards_ctxt state_ctxt (unsafe_var_list_index bs (word_of_nat x))
                in (upd_balance - upd_balance mod EFFECTIVE_BALANCE_INCREMENT config \<le> Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) \<longrightarrow> Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) - (upd_balance - upd_balance mod EFFECTIVE_BALANCE_INCREMENT config) \<le> previous_epoch_flag_attesting_balances_f epb ! n) \<and>
                   previous_epoch_flag_attesting_balances_f epb ! n \<le> previous_epoch_flag_attesting_balances_f epb ! n + (min (upd_balance - upd_balance mod EFFECTIVE_BALANCE_INCREMENT config) MAX_EFFECTIVE_BALANCE - Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)))))
" 

lemma main_loop_wp[wp]:

 
  shows "\<And>(next_epoch_num_active_validators :: ((BeaconState \<times> ('b \<Rightarrow> 'b heap_value option),
        64 word option) lens)).
  (\<And>x. hoare_triple (lift (P x)) (c x) Q) \<Longrightarrow> (curr_epoch \<noteq> GENESIS_EPOCH) \<Longrightarrow> length (var_list_inner vs) < 2^64 \<Longrightarrow> xs = [0..<(length (var_list_inner vs))] \<Longrightarrow> length (var_list_inner bs) = length (var_list_inner vs) \<Longrightarrow>
  length (var_list_inner is) = length (var_list_inner vs) \<Longrightarrow>  length (var_list_inner pep) = length (var_list_inner vs) \<Longrightarrow>  length (var_list_inner cep) = length (var_list_inner vs) \<Longrightarrow>   
 hoare_triple (lift (\<lambda>s. pre_pure epb ebrc effective_balances_ctxt final_activation_queue pep cep prev_epoch curr_epoch bs brc ec progressive_balances slashings_ctxt rewards_ctxt vs is xs state_ctxt \<and> 
                         (validators \<mapsto>\<^sub>l vs \<and>* balances \<mapsto>\<^sub>l bs \<and>*  inactivity_scores \<mapsto>\<^sub>l is \<and>* base_rewards_cache \<mapsto>\<^sub>l brc \<and>* 
                          previous_epoch_participation \<mapsto>\<^sub>l pep \<and>*  current_epoch_participation \<mapsto>\<^sub>l cep \<and>* 
                         next_epoch_base_reward_cache \<mapsto>\<^sub>l ebrc \<and>* nepb \<mapsto>\<^sub>l epb \<and>* (validators \<mapsto>\<^sub>l
         updated_effective_balance_validators effective_balances_ctxt state_ctxt rewards_ctxt slashings_ctxt prev_epoch curr_epoch progressive_balances bs is brc pep cep vs \<and>*
       balances \<mapsto>\<^sub>l
         updated_balances state_ctxt rewards_ctxt slashings_ctxt prev_epoch curr_epoch progressive_balances vs is brc pep cep bs \<and>*
       previous_epoch_participation \<mapsto>\<^sub>l pep \<and>*
       current_epoch_participation \<mapsto>\<^sub>l cep \<and>*
       inactivity_scores \<mapsto>\<^sub>l
         updated_inactivity_scores state_ctxt rewards_ctxt slashings_ctxt prev_epoch curr_epoch progressive_balances brc pep cep vs is \<and>*
       base_rewards_cache \<mapsto>\<^sub>l brc \<and>*
       next_epoch_base_reward_cache \<mapsto>\<^sub>l updated_ebrc state_ctxt rewards_ctxt progressive_balances effective_balances_ctxt slashings_ctxt brc prev_epoch curr_epoch pep cep bs is vs ebrc \<and>*
       nepb \<mapsto>\<^sub>l updated_epb state_ctxt rewards_ctxt progressive_balances effective_balances_ctxt slashings_ctxt brc prev_epoch curr_epoch pep cep bs is vs epb \<longrightarrow>* P (map (\<lambda>_. ()) xs))) s))
 (bindCont (forM xs (\<lambda>i. do {
     let n = of_nat i;
     validator <- mut (validators !? n);
     balance   <- mut (balances !? n);
     inactivity_score <- mut (inactivity_scores !? n);
     prev_participation <- mut (previous_epoch_participation !? n);
     curr_participation <- mut (current_epoch_participation !? n);
     v <- read validator;
     let is_active_current_epoch = is_active_validator v curr_epoch;
     let is_active_previous_epoch = is_active_validator v prev_epoch;
     x <- prev_epoch .+ (Epoch 1);
     let is_eligible = is_active_previous_epoch \<or> (slashed_f v \<and> x < withdrawable_epoch_f v);
     brc <- read base_rewards_cache;
     base_reward <- get_cached_base_reward brc n;
     p_p <- read prev_participation;
     c_p <- read curr_participation;
     let validator_info = ValidatorInfo.fields n (Validator.effective_balance_f v)
                                               base_reward is_eligible (slashed_f v) is_active_current_epoch
                                               is_active_previous_epoch p_p c_p ;
     _ <- when (curr_epoch \<noteq> GENESIS_EPOCH) (do {
            is <- read inactivity_score; 
            _  <- (inactivity_score := process_single_inactivity_update is validator_info state_ctxt);
            (balance := process_single_reward_and_penalty balance is validator_info rewards_ctxt state_ctxt)
          });
     v  <- read validator;
     _  <- (balance := process_single_slashing balance v slashings_ctxt progressive_balances);
     _  <- process_single_effective_balance_update balance validator validator_info nepb next_epoch_base_reward_cache effective_balances_ctxt state_ctxt c_p;
     return ()
   })) c) Q"
  apply (rule hoare_weaken_pre)
   apply (rule mapM_fake)
    apply (simp only: Let_unfold)

    apply (simp only: bindCont_assoc[symmetric])
  using [[unify_search_bound = 500]]   
    apply (rule var_list_index_lens_wp)
  using [[unify_search_bound = 500]]   
    apply (rule var_list_index_lens_wp)
  apply (rule var_list_index_lens_wp)
    apply (rule var_list_index_lens_wp)
    apply (rule var_list_index_lens_wp)
    apply (rule read_beacon_wp_ex)
    apply (simp add: epoch_unsigned_add_def)
apply (simp only: bindCont_assoc[symmetric] | rule new_state_context_wp'  new_slashings_context_wp' read_beacon_wp_ex add_wp' write_beacon_wp' wp)
    apply (rule add_wp')
  apply (rule return_triple')

    apply (simp)
    apply (rule read_beacon_wp_ex)
    apply (rule_tac v=xh and x=brc in hoare_eqI')
    apply (rule_tac brc=brc in get_cached_base_reward_wp)
    apply (rule read_beacon_wp_ex)
  apply (rule read_beacon_wp_ex)
  apply (simp)
    apply (rule read_beacon_wp_ex)

    apply (rule_tac v=xi and x="(base_rewards_f brc ! unat (effective_balances_f brc ! unat ((word_of_nat x) :: 64 word) div EFFECTIVE_BALANCE_INCREMENT config))" in hoare_eqI')
  

    apply (rule read_beacon_wp_ex)
    apply (rule process_single_inactivity_update_wp)
    apply (rule write_beacon_wp')
    apply (rule read_beacon_wp_ex)
    apply (rule process_single_reward_and_penalty_wp')
  prefer 3
    apply (simp only: effective_balance_fields base_reward_fields index_fields rewardable_simp)
  apply (simp only: make_validator_info_def[symmetric])
  prefer 2
    apply (rule write_beacon_wp')
    apply (rule read_beacon_wp_ex)
  apply (rule read_beacon_wp_ex)
    apply (rule process_single_slashing')
    apply (rule write_beacon_wp)
    apply (rule process_single_effective_balance_update_wp')
  apply (simp)
  (*  apply (rule when_wp)
apply (simp only: bindCont_assoc[symmetric] | rule new_state_context_wp'  new_slashings_context_wp' read_beacon_wp_ex add_wp' write_beacon_wp' wp)

     apply (rule read_beacon_wp_ex)
     apply (rule add_wp')
     apply (rule write_beacon_wp)
     apply (assumption)
    apply (assumption)
 *)

  apply (rule lift_mono')
  apply (rule predicate1I)
   apply (subst mapM_is_sequence_map)
  apply (simp only: make_validator_info_def[symmetric])


   apply (rule_tac P="\<lambda>x.  lcomp (v_list_lens (word_of_nat x)) validators \<mapsto>\<^sub>l (unsafe_var_list_index vs (word_of_nat x)) \<and>* 
                           lcomp (v_list_lens (word_of_nat x)) balances \<mapsto>\<^sub>l (unsafe_var_list_index bs (word_of_nat x)) \<and>* lcomp (v_list_lens (word_of_nat x)) inactivity_scores \<mapsto>\<^sub>l (unsafe_var_list_index is (word_of_nat x)) \<and>*
                           lcomp (v_list_lens (word_of_nat x)) previous_epoch_participation \<mapsto>\<^sub>l (unsafe_var_list_index pep (word_of_nat x)) \<and>*
                           lcomp (v_list_lens (word_of_nat x)) current_epoch_participation \<mapsto>\<^sub>l (unsafe_var_list_index cep (word_of_nat x)) \<and>* 
          (\<lambda>s. sep_empty s \<and> next_epoch_f state_ctxt = current_epoch_f state_ctxt + 1 \<and> current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD > current_epoch_f state_ctxt + 1 \<and>
               safe_mul (unsafe_var_list_index is (word_of_nat x)) (Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x))) \<and> current_epoch_f state_ctxt \<le> current_epoch_f state_ctxt + 1 \<and>
               safe_mul (active_increments_f rewards_ctxt) WEIGHT_DENOMINATOR \<and>  safe_mul INACTIVITY_PENALTY_QUOTIENT_ALTAIR (INACTIVITY_SCORE_BIAS config) \<and> active_increments_f rewards_ctxt * WEIGHT_DENOMINATOR \<noteq> 0 \<and>
               safe_mul (adjusted_total_slashing_balance_f slashings_ctxt)  (Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) div EFFECTIVE_BALANCE_INCREMENT config) \<and> 
               total_active_balance_f progressive_balances \<noteq> 0 \<and> 
               safe_mul (EFFECTIVE_BALANCE_INCREMENT config) 
                        (Validator.effective_balance_f  (unsafe_var_list_index vs (word_of_nat x)) div EFFECTIVE_BALANCE_INCREMENT config *  adjusted_total_slashing_balance_f slashings_ctxt div total_active_balance_f progressive_balances) \<and>
               current_epoch_f state_ctxt + 1 \<le> current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD \<and> max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) \<le> max (get_max_exit_epoch ec) (current_epoch_f state_ctxt + 1 + MAX_SEED_LOOKAHEAD) + 1 \<and>
                word_of_nat x < word_of_nat (length (effective_balances_f brc)) \<and> effective_balances_f brc ! unat (word_of_nat x) div EFFECTIVE_BALANCE_INCREMENT config < word_of_nat (length (base_rewards_f brc)) \<and>
               unsafe_var_list_index is (word_of_nat x) \<le> unsafe_var_list_index is (word_of_nat x) + INACTIVITY_SCORE_BIAS config \<and> 3 \<le> length (unslashed_participating_increments_array_f rewards_ctxt) \<and>
               (\<forall>n\<in>{0,1,2}. safe_mul (PARTICIPATION_FLAG_WEIGHTS ! n) (base_rewards_f brc ! unat (effective_balances_f brc ! unat (word_of_nat x) div EFFECTIVE_BALANCE_INCREMENT config)) \<and>
                            safe_mul (PARTICIPATION_FLAG_WEIGHTS ! n * base_rewards_f brc ! unat (effective_balances_f brc ! unat (word_of_nat x) div EFFECTIVE_BALANCE_INCREMENT config)) (unslashed_participating_increments_array_f rewards_ctxt ! n)) \<and>
             (let rewards = map (reward rewards_ctxt state_ctxt (make_validator_info (unsafe_var_list_index vs (word_of_nat x)) curr_epoch prev_epoch (unsafe_var_list_index cep (word_of_nat x)) (unsafe_var_list_index pep (word_of_nat x)) brc x)) [0, 1, 2]
                in unsafe_var_list_index bs (word_of_nat x) \<le> unsafe_var_list_index bs (word_of_nat x) + sum_list rewards \<and>
              (let penalties = map (penalise state_ctxt (make_validator_info (unsafe_var_list_index vs (word_of_nat x)) curr_epoch prev_epoch (unsafe_var_list_index cep (word_of_nat x)) (unsafe_var_list_index pep (word_of_nat x)) brc x)) [0, 1] in
              (let inactive_pd = inactive_penalty_delta (Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x))) 
                                (unsafe_var_list_index is (word_of_nat x)) (make_validator_info (unsafe_var_list_index vs (word_of_nat x)) curr_epoch prev_epoch (unsafe_var_list_index cep (word_of_nat x)) (unsafe_var_list_index pep (word_of_nat x)) brc x) in
                   sum_list (map unat rewards) + unat inactive_pd < 2 ^ 64 \<and> sum_list (map unat penalties) + unat inactive_pd < 2 ^ 64))) \<and> 
            (let upd_balance = updated_balance (make_validator_info (unsafe_var_list_index vs (word_of_nat x)) curr_epoch prev_epoch (unsafe_var_list_index cep (word_of_nat x)) (unsafe_var_list_index pep (word_of_nat x)) brc x) (unsafe_var_list_index vs (word_of_nat x)) (unsafe_var_list_index vs (word_of_nat x))
                          (unsafe_var_list_index is (word_of_nat x)) slashings_ctxt progressive_balances rewards_ctxt state_ctxt (unsafe_var_list_index bs (word_of_nat x)) in
        (let upd_val = vs[x]! in 
          upd_balance \<le> upd_balance + downward_threshold_f effective_balances_ctxt \<and> 
           total_active_balance_f epb \<le> total_active_balance_f epb + min (upd_balance - upd_balance mod  EFFECTIVE_BALANCE_INCREMENT config) MAX_EFFECTIVE_BALANCE \<and>
           Validator.effective_balance_f upd_val \<le> Validator.effective_balance_f upd_val + upward_threshold_f effective_balances_ctxt \<and> 
           total_active_balance_f epb \<le> total_active_balance_f epb + Validator.effective_balance_f upd_val \<and> 
         (\<forall>n\<in>{n. n \<le> length (participation_flag_weights (unsafe_var_list_index cep (word_of_nat x))) \<and> has_flag (unsafe_var_list_index cep (word_of_nat x)) n}.
           (upd_balance -
           upd_balance mod
           EFFECTIVE_BALANCE_INCREMENT config
           \<le> Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) \<longrightarrow>
           Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) -
           (upd_balance - upd_balance mod EFFECTIVE_BALANCE_INCREMENT config)
           \<le> previous_epoch_flag_attesting_balances_f epb ! n) \<and>
          (Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) \<le> Validator.effective_balance_f upd_val \<longrightarrow>
           previous_epoch_flag_attesting_balances_f epb ! n \<le> previous_epoch_flag_attesting_balances_f epb ! n + (Validator.effective_balance_f upd_val - Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)))) \<and>
          Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) - Validator.effective_balance_f upd_val \<le> previous_epoch_flag_attesting_balances_f epb ! n \<and>
          previous_epoch_flag_attesting_balances_f epb ! n
            \<le> previous_epoch_flag_attesting_balances_f epb ! n + (min (upd_balance -  upd_balance mod EFFECTIVE_BALANCE_INCREMENT config) MAX_EFFECTIVE_BALANCE - Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x))))))
          \<and> Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) < MAX_EFFECTIVE_BALANCE \<and>
            (\<forall>n\<in>{n. n \<le> length (participation_flag_weights (unsafe_var_list_index cep (word_of_nat x))) \<and> has_flag (unsafe_var_list_index cep (word_of_nat x)) n}.         
           let upd_balance = (updated_balance (make_validator_info (unsafe_var_list_index vs (word_of_nat x)) curr_epoch prev_epoch (unsafe_var_list_index cep (word_of_nat x)) (unsafe_var_list_index pep (word_of_nat x)) brc x) (unsafe_var_list_index vs (word_of_nat x)) (updated_validator (unsafe_var_list_index vs (word_of_nat x)) ec state_ctxt final_activation_queue brc (unsafe_var_list_index pep (word_of_nat x)) (unsafe_var_list_index cep (word_of_nat x)) prev_epoch curr_epoch x)
            (unsafe_var_list_index is (word_of_nat x)) slashings_ctxt progressive_balances rewards_ctxt state_ctxt (unsafe_var_list_index bs (word_of_nat x))) in
           let upd_val = (updated_validator (unsafe_var_list_index vs (word_of_nat x)) ec state_ctxt final_activation_queue brc (unsafe_var_list_index pep (word_of_nat x)) (unsafe_var_list_index cep (word_of_nat x)) prev_epoch curr_epoch x) in
          (upd_balance - upd_balance mod EFFECTIVE_BALANCE_INCREMENT config
           \<le> Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) \<longrightarrow>
           Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) - (upd_balance -upd_balance mod EFFECTIVE_BALANCE_INCREMENT config)
           \<le> previous_epoch_flag_attesting_balances_f epb ! n) \<and>
          (Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) \<le> Validator.effective_balance_f upd_val \<longrightarrow>
           previous_epoch_flag_attesting_balances_f epb ! n \<le> previous_epoch_flag_attesting_balances_f epb ! n + (Validator.effective_balance_f upd_val - Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)))) \<and>
          Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x)) - Validator.effective_balance_f upd_val \<le> previous_epoch_flag_attesting_balances_f epb ! n \<and>
          previous_epoch_flag_attesting_balances_f epb ! n
          \<le> previous_epoch_flag_attesting_balances_f epb ! n +
             (min (upd_balance -  upd_balance mod EFFECTIVE_BALANCE_INCREMENT config) MAX_EFFECTIVE_BALANCE -  Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat x))))) " and
Q = "\<lambda>x. lcomp (v_list_lens (word_of_nat x)) validators \<mapsto>\<^sub>l  update_effective_balance  (unsafe_var_list_index vs (word_of_nat x))
                                                            (updated_balance
                                                             (make_validator_info (unsafe_var_list_index vs (word_of_nat x)) curr_epoch prev_epoch (unsafe_var_list_index cep (word_of_nat x)) (unsafe_var_list_index pep (word_of_nat x)) brc x)
                                                             (unsafe_var_list_index vs (word_of_nat x)) 
                                                             ((unsafe_var_list_index vs (word_of_nat x))) (unsafe_var_list_index is (word_of_nat x))
                                                              slashings_ctxt progressive_balances rewards_ctxt state_ctxt (unsafe_var_list_index bs (word_of_nat x))) effective_balances_ctxt \<and>*
        lcomp (v_list_lens (word_of_nat x)) balances \<mapsto>\<^sub>l updated_balance
                                                             (make_validator_info (unsafe_var_list_index vs (word_of_nat x)) curr_epoch prev_epoch (unsafe_var_list_index cep (word_of_nat x)) (unsafe_var_list_index pep (word_of_nat x)) brc x)
                                                             (unsafe_var_list_index vs (word_of_nat x)) 
                                                             ((unsafe_var_list_index vs (word_of_nat x))) (unsafe_var_list_index is (word_of_nat x))
                                                              slashings_ctxt progressive_balances rewards_ctxt state_ctxt (unsafe_var_list_index bs (word_of_nat x)) \<and>*
        lcomp (v_list_lens (word_of_nat x)) previous_epoch_participation \<mapsto>\<^sub>l (unsafe_var_list_index pep (word_of_nat x)) \<and>* lcomp (v_list_lens (word_of_nat x)) current_epoch_participation \<mapsto>\<^sub>l (unsafe_var_list_index cep (word_of_nat x))  \<and>*
        lcomp (v_list_lens (word_of_nat x)) inactivity_scores \<mapsto>\<^sub>l single_inactivity_update (unsafe_var_list_index is (word_of_nat x)) (make_validator_info (unsafe_var_list_index vs (word_of_nat x)) curr_epoch prev_epoch (unsafe_var_list_index cep (word_of_nat x)) (unsafe_var_list_index pep (word_of_nat x)) brc x) state_ctxt" and 
                 S = "\<lambda>(ebrc, epb). next_epoch_base_reward_cache \<mapsto>\<^sub>l ebrc \<and>* nepb \<mapsto>\<^sub>l epb" and 
                 h = "\<lambda> n (ebrc,epb). let v_info = (make_validator_info (unsafe_var_list_index vs (word_of_nat n)) curr_epoch prev_epoch 
                                                       (unsafe_var_list_index cep (word_of_nat n)) (unsafe_var_list_index pep (word_of_nat n)) brc n) in
                                     let new_balance = updated_balance v_info (unsafe_var_list_index vs (word_of_nat n)) (unsafe_var_list_index vs (word_of_nat n)) (unsafe_var_list_index is (word_of_nat n))
                                                             slashings_ctxt progressive_balances rewards_ctxt state_ctxt (unsafe_var_list_index bs (word_of_nat n)) 
                                           in (ebrc\<lparr>effective_balances_f := 
                                                      effective_balances_f ebrc @ [new_effective_balance' effective_balances_ctxt (Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat n))) new_balance]\<rparr>,
                                                 updated_nepb epb (update_effective_balance (unsafe_var_list_index vs (word_of_nat n)) new_balance effective_balances_ctxt)
                                                        (unsafe_var_list_index cep (word_of_nat n)) (current_epoch_f state_ctxt + 1) 
                                                        (Validator.effective_balance_f (unsafe_var_list_index vs (word_of_nat n)))  )    " and
          I="base_rewards_cache \<mapsto>\<^sub>l brc \<and>* (\<lambda>s. sep_empty s \<and> epoch_to_u64 prev_epoch \<le> epoch_to_u64 prev_epoch + 1 \<and> length (base_rewards_f brc) \<le> 2 ^ 64 - 1)" and
          D="\<lambda>n (ebrc,epb) (ebrc',epb'). let v_info = (make_validator_info (vs[n]!) curr_epoch prev_epoch 
                                                       (cep[n]!) (unsafe_var_list_index pep (word_of_nat n)) brc n) in
                                          total_active_balance_f epb \<le> total_active_balance_f epb + single_effective_balance_updated (updated_balance v_info (vs[n]!) (vs[n]!) (is[n]!)
                                                             slashings_ctxt progressive_balances rewards_ctxt state_ctxt (bs[n]!) ) effective_balances_ctxt (vs[n]!) \<and>                                                                           
                                          total_active_balance_f epb \<le> total_active_balance_f epb + Validator.effective_balance_f (vs[n]!) \<and>
                                          (\<forall>previous_epoch_flag_attesting_balance\<in>{ (previous_epoch_flag_attesting_balances_f epb ! n') | n'. n' \<le> length (participation_flag_weights (cep[n]!)) \<and> has_flag (cep[n]!) n'}.
                                               previous_epoch_flag_attesting_balance \<le> 
                                               previous_epoch_flag_attesting_balance +
                                                   (single_effective_balance_updated (updated_balance v_info (vs[n]!) (vs[n]!) (is[n]!)
                                                             slashings_ctxt progressive_balances rewards_ctxt state_ctxt (bs[n]!) ) effective_balances_ctxt (vs[n]!) - ValidatorInfo.effective_balance_f v_info) \<and>
                                               ValidatorInfo.effective_balance_f v_info - single_effective_balance_updated (updated_balance v_info (vs[n]!) (vs[n]!) (is[n]!)
                                                             slashings_ctxt progressive_balances rewards_ctxt state_ctxt (bs[n]!) ) effective_balances_ctxt (vs[n]!) \<le> previous_epoch_flag_attesting_balance) " and
          n="(ebrc, epb)" and R=P and g="\<lambda>_. ()" in sequenceI_rewriting4)

  apply (erule exE)
     apply (simp only: mk_val_info_def[symmetric] index_var_list_lens_comp_def[symmetric] index_var_list_def[symmetric])
  apply (elim conjE)
 apply (rule_tac x="vs[xa]!" in exI)
    apply (sep_cancel)+
apply (rule_tac x="bs[xa]!" in exI)
     apply (sep_cancel)+
 apply (rule_tac x="is[xa]!" in exI)
      apply (sep_cancel)+
    apply (rule_tac x="pep[xa]!" in exI)
    apply (sep_cancel)+

    apply (rule_tac x="cep[xa]!" in exI)
    apply (simp only: sep_conj_ac prod.split mk_val_info_def[symmetric] make_mk_simp updated_balance_fold updated_balance_fold' split: prod.splits)


    apply (sep_cancel)+
   apply ((rule exI, sep_cancel+) | intro conjI impI ; clarsimp?)
   apply (intro conjI impI)
  apply (clarsimp)
    apply ((rule exI, sep_cancel+) | intro conjI impI ; clarsimp?)
    apply (intro conjI impI)
        apply (rule refl)
  apply (clarsimp)
      apply (clarsimp)
      apply (assumption)
      apply (clarsimp)
  apply (assumption)
    apply ((rule exI, sep_cancel+) | intro conjI impI ; clarsimp?)
        apply ((rule exI, sep_cancel+) | intro conjI impI ; clarsimp?)
    apply ((rule exI, sep_cancel+) | intro conjI impI ; clarsimp?)
  apply (intro conjI impI allI ballI letI)
  apply (rule refl)
    apply ((rule exI, sep_cancel+) | intro conjI impI ; clarsimp?)
    apply ((rule exI, sep_cancel+) | intro conjI impI ; clarsimp?)
  apply (sep_cancel)+
         apply ((rule exI, sep_cancel+) | intro conjI impI ; clarsimp?)

    apply (clarsimp)
  apply (simp only: mk_val_info_def[symmetric] index_var_list_lens_comp_def[symmetric] index_var_list_def[symmetric] make_mk_simp)

  apply (intro conjI impI allI ballI letI)
                      apply (clarsimp)

  apply (simp add: PARTICIPATION_FLAG_WEIGHTS_def)
                      apply fastforce
  apply (simp only: mk_val_info_def[symmetric] make_mk_simp index_var_list_lens_comp_def[symmetric] index_var_list_def[symmetric])

                      apply (clarsimp elim!: letE)
  

             apply (clarsimp elim!: letE)
                  apply (clarsimp elim!: letE)
                   apply (sep_cancel)+

                 apply (clarsimp elim!: letE)
                   apply (sep_cancel)+

                apply (clarsimp elim!: letE)

                   apply (rule exI, sep_cancel+)
      apply (clarsimp)

    apply (rule exI, sep_cancel+)
                 apply (clarsimp)
  apply (intro conjI impI allI ballI letI)

        apply (clarsimp elim!: letE)

                      apply (sep_cancel)+
                      apply (simp only: Let_unfold)
                   
       apply (clarsimp)
  apply (rule_tac exI, rule conjI) defer
                
                     apply ( intro conjI impI exI)
                      apply (fastforce)
                      apply (fastforce) apply (fastforce)
                     apply (fastforce)
                      apply (sep_cancel)+
  apply (erule sep_conj_impl)
                      apply (fastforce simp: single_slashing_def new_effective_balance'_def updated_balance_def)
                      apply (sep_cancel)+
                      apply (sep_drule (direct) sep_not_true )
                      apply (sep_cancel)+
                      apply (simp add: new_effective_balance'_def single_effective_balance_updated_def update_effective_balance_def)
  apply (intro conjI impI; clarsimp, sep_cancel+)
                      apply (sep_cancel)+
                     apply (metis One_nat_def PARTICIPATION_FLAG_WEIGHTS_def Zero_not_Suc add_eq_self_zero length_Suc_conv less_one nat_neq_iff plus_1_eq_Suc)
                    apply (clarsimp)
                   apply (clarsimp simp: Let_unfold elim!: letE)
                   apply (clarsimp simp: Let_unfold elim!: letE)
                   apply (clarsimp simp: Let_unfold elim!: letE)
                   apply (clarsimp simp: Let_unfold elim!: letE)
               apply (clarsimp simp: Let_unfold elim!: letE)
               apply (sep_cancel)+
              apply (rule exI, sep_cancel+)+
              apply (clarsimp)
              apply (sep_cancel)+
  apply (rule exI, erule conjI)
              apply (intro exI conjI)
  apply (fastforce)
  apply (fastforce)
  apply (fastforce)
                       apply (fastforce)

               apply (sep_cancel)+
 apply (erule sep_conj_impl)
                apply (fastforce simp: single_slashing_def new_effective_balance'_def updated_balance_def)
apply (sep_cancel)+
                      apply (sep_drule (direct) sep_not_true )
                      apply (sep_cancel)+
                      apply (simp add: new_effective_balance'_def single_effective_balance_updated_def update_effective_balance_def)
  apply (intro conjI impI; clarsimp, sep_cancel+)
               apply (sep_cancel)+
              apply (metis One_nat_def PARTICIPATION_FLAG_WEIGHTS_def Suc_le_lessD add.commute list.size(3) list.size(4) numeral_2_eq_2 order.refl plus_1_eq_Suc)
apply (rule TrueI)
                   apply (clarsimp simp: Let_unfold elim!: letE)
                   apply (clarsimp simp: Let_unfold elim!: letE)
                   apply (clarsimp simp: Let_unfold elim!: letE)
                   apply (clarsimp simp: Let_unfold elim!: letE)
        apply (clarsimp simp: Let_unfold elim!: letE)
  apply (sep_cancel)+
apply (rule exI, sep_cancel+)+
              apply (clarsimp)
              apply (sep_cancel)+
  apply (rule exI, erule conjI)
              apply (intro exI conjI)
  apply (fastforce)
  apply (fastforce)
          apply (fastforce)                      apply (fastforce)

apply (sep_cancel)+
 apply (erule sep_conj_impl)
                apply (fastforce simp: single_slashing_def new_effective_balance'_def updated_balance_def)
apply (sep_cancel)+
                      apply (sep_drule (direct) sep_not_true )
                      apply (sep_cancel)+
                      apply (simp add: new_effective_balance'_def single_effective_balance_updated_def update_effective_balance_def)
  apply (intro conjI impI; clarsimp, sep_cancel+)
      apply (sep_cancel)+
     apply (clarsimp)
  apply (subgoal_tac "(\<exists>x. x < length (local.var_list_inner vs))")
      apply (clarsimp simp: split_foldr_map_sep_conj split_foldr_map_conj restore_variablelist local.foldr_pure_empty)
      apply (intro conjI; clarsimp simp: pre_pure)

        apply (sep_cancel)+
        apply (clarsimp)
        apply (sep_mp)
        apply (clarsimp split: prod.splits)
        apply (clarsimp simp: updated_effective_balance_validators_def)
        apply (fold index_var_list_def)
  apply (clarsimp simp: sep_conj_ac)
        apply (sep_mp)
  apply (clarsimp simp: updated_inactivity_scores_def)
        apply (sep_mp)
        apply (clarsimp simp: updated_balances_def)
        apply (sep_mp)
  apply (clarsimp simp: Let_unfold fold_pair_split updated_ebrc_def updated_epb_def, sep_mp)
      apply (sep_cancel)+
     apply (clarsimp simp: pre_pure)
     apply (rule_tac x=0 in exI, fastforce)
    apply (clarsimp simp: pre_pure safe_transitions_main_loop_def valid_transition_def previous_participating_attesting_balances_def )
    apply (fastforce)
   apply (assumption)
  apply (fastforce)
  done


lemma fold_flags_is_map_flags: "foldrM (\<lambda>flag_index all_deltas. do {flag_index_deltas <- get_flag_index_deltas flag_index;return (all_deltas @ [flag_index_deltas])}) xs n = 
       do {xs <- mapM (\<lambda>flag_index. get_flag_index_deltas flag_index) xs; return (n@xs)} "
  apply (induct xs arbitrary: n; clarsimp)
  apply (clarsimp simp: foldrM_cons)
  by (clarsimp simp: bindCont_assoc[symmetric])

lemma get_eligible_validator_indices[wp]: "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>
     hoare_triple (lift (\<lambda>s. previous_epoch (current_epoch bs) \<le> previous_epoch (current_epoch bs) + 1 \<and> 
                             (previous_epoch (current_epoch bs) \<le> previous_epoch (current_epoch bs) + 1 \<longrightarrow>
                             (beacon_slots \<mapsto>\<^sub>l bs \<and>* validators \<mapsto>\<^sub>l vs \<and>* (validators \<mapsto>\<^sub>l vs \<and>* beacon_slots \<mapsto>\<^sub>l bs  \<longrightarrow>*
                               P (eligible_validator_indices (previous_epoch (current_epoch bs)) (previous_epoch (current_epoch bs) + 1) vs )))s) )) (bindCont (get_eligible_validator_indices) next) Q"
  apply (rule hoare_weaken_pre, simp add: get_eligible_validator_indices_def)
   apply (wp)
   apply (simp add: epoch_unsigned_add_def, wp)
  apply (clarsimp)
  apply (sep_cancel)+
  apply (intro conjI impI)
   apply (simp add: less_eq_Epoch_def one_Epoch_def plus_Epoch_def)
  apply (rule exI, sep_cancel+)
  apply (sep_mp)
  by (simp add: less_eq_Epoch_def one_Epoch_def plus_Epoch_def)

lemma ref_read_index: "(do {v <- read validators; (var_list_index v index)}) \<le> (do {v <- mut (var_list_index_lens validators index);  read v})"
  apply (rule le_funI)
  apply (clarsimp simp: read_beacon_def getState_def bindCont_def var_list_index_lens_def lens_ocomp_def)
  apply (clarsimp simp: Sup_le_iff)
  apply (intro conjI impI)
   apply (rule_tac i="(a, b)" in SUP_upper2, clarsimp)
   apply (clarsimp simp: fail_def return_def test_restricts_Nondet)
  apply (clarsimp simp: lens_oocomp_def)
  apply (clarsimp)
  apply (rule_tac i="(a, b)" in SUP_upper2, clarsimp)
  apply (clarsimp simp: return_def)
  apply (clarsimp simp: return_def test_restricts_Nondet)
  apply (clarsimp simp: v_list_lens_def var_list_index_def lens_oocomp_def)
  apply (intro conjI impI)
   apply (clarsimp simp: return_def)
   apply (case_tac y; clarsimp)
  apply (clarsimp simp: fail_def)
    apply (rule seq_mono; clarsimp)
   apply (case_tac y; clarsimp)
   apply (erule notE)
   apply (unat_arith, clarsimp)
   apply (subst unat_of_nat64', clarsimp)
   apply (clarsimp)
  apply (clarsimp simp: fail_def)
  done


lemma refine_in_hoare: "hoare_triple P (bindCont m' a) R \<Longrightarrow> m \<le> m' \<Longrightarrow>  hoare_triple P (bindCont m a) R"  
  apply (clarsimp simp: hoare_triple_def run_def bindCont_def)
  apply (rule order_trans)
   apply (drule le_funD)
   apply (assumption)
  apply (assumption)
  done

definition "get_base_reward_per_increment_pre bs vs \<equiv> (\<forall>x\<in>list.set (active_validator_indices (current_epoch bs) vs). x < var_list_len vs) \<and>           
                                                     (\<forall>xs\<in>lists_of (list.set (active_validator_indices (current_epoch bs) vs)).                                            
                                                      EFFECTIVE_BALANCE_INCREMENT config < max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>xs. Validator.effective_balance_f (unsafe_var_list_index vs a)) + 1 \<and>
                                                       safe_mul (BASE_REWARD_FACTOR config) (EFFECTIVE_BALANCE_INCREMENT config) \<and>
                                                      (\<Sum>a\<leftarrow>xs. Validator.effective_balance_f (unsafe_var_list_index vs a)) < max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>xs. Validator.effective_balance_f (unsafe_var_list_index vs a)) + 1)"


definition "base_reward_incr vs xs \<equiv> sqrt' (max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>xs. Validator.effective_balance_f (unsafe_var_list_index vs a))) div (EFFECTIVE_BALANCE_INCREMENT config * BASE_REWARD_FACTOR config)"

lemma get_base_reward_per_increment_pre[wp]: "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>
     hoare_triple (lift (\<lambda>s. get_base_reward_per_increment_pre bs vs  \<and> 
                             (beacon_slots \<mapsto>\<^sub>l bs \<and>* validators \<mapsto>\<^sub>l vs \<and>* 
                              (beacon_slots \<mapsto>\<^sub>l bs \<and>* validators \<mapsto>\<^sub>l vs \<longrightarrow>* (\<lambda>s. \<forall>xs\<in>lists_of (list.set (active_validator_indices (current_epoch bs) vs)).  P (base_reward_incr vs xs) s)) )s ) ) 
                   (bindCont (get_base_reward_per_increment) next) Q"
  apply (rule hoare_weaken_pre, simp add: get_base_reward_per_increment_def)
   apply (wp)
  apply (clarsimp)
  apply (sep_cancel)+
  apply (intro conjI impI)
   apply (fastforce simp: get_base_reward_per_increment_pre_def)
  apply (intro conjI impI allI ballI)
   apply (fastforce simp: get_base_reward_per_increment_pre_def)
   apply (fastforce simp: get_base_reward_per_increment_pre_def)
    apply (fastforce simp: get_base_reward_per_increment_pre_def)
  apply (simp add: brf_not_zero mult.commute safe_mul_not_zeroI)
   apply (sep_mp)
  by (fastforce simp: base_reward_incr_def)
  

definition "base_reward vs bs index = (Validator.effective_balance_f (var_list_inner vs ! unat index) div EFFECTIVE_BALANCE_INCREMENT config ) * (base_reward_incr vs (SOME xs. xs \<in> lists_of (list.set (active_validator_indices (current_epoch bs) vs))))"


lemma "distinct xs \<Longrightarrow> distinct ys \<Longrightarrow> list.set xs = list.set ys \<Longrightarrow> sum_list xs = sum_list (ys :: ('c :: comm_monoid_add) list)"
  by (clarsimp simp: Groups_List.comm_monoid_add_class.distinct_sum_list_conv_Sum)


lemma bij_exists: "length xs = length xs' \<Longrightarrow> distinct xs \<Longrightarrow> distinct xs' \<Longrightarrow> list.set xs = list.set xs' \<Longrightarrow> \<exists>f. map f xs = xs'" oops


lemma abcd: "y \<notin> C \<Longrightarrow> A = insert y C \<Longrightarrow> A - {y} = C"
  by (intro set_eqI iffI; clarsimp?)


lemma sum_lists_eq: "length xs = length xs' \<Longrightarrow> distinct xs \<Longrightarrow> distinct xs' \<Longrightarrow> list.set xs = list.set xs' \<Longrightarrow> (\<Sum>a\<leftarrow>xs. f a) = (\<Sum>a\<leftarrow>xs'. (f a :: 'd :: comm_monoid_add))" 
  apply (induct xs xs' rule: list_induct2; clarsimp)
  apply (case_tac "list.set xs = list.set ys"; clarsimp)
   apply (simp add: insert_eq_iff)
   apply (metis insertI1)
  by (metis List.finite_set sum.insert sum_list_distinct_conv_sum_set)


lemma all_sums_eq: 
"xs \<in> lists_of (list.set (active_validator_indices epoch vs)) \<Longrightarrow>  xs'\<in>lists_of (list.set (active_validator_indices epoch vs)) \<Longrightarrow>
       base_reward_incr vs  xs = base_reward_incr vs xs'"
  apply (clarsimp simp: base_reward_incr_def)
  apply (rule arg_cong[where x="(\<Sum>a\<leftarrow>xs. Validator.effective_balance_f (unsafe_var_list_index vs a))"])
  apply (rule sum_lists_eq)
     apply (clarsimp simp: lists_of_def)
     apply (metis distinct_card)
     apply (clarsimp simp: lists_of_def)
     apply (clarsimp simp: lists_of_def)
  by (clarsimp simp: lists_of_def)

definition "base_reward_pre vs bs flag_index \<equiv> flag_index < var_list_len vs \<and> get_base_reward_per_increment_pre bs vs \<and>
                        safe_mul (base_reward_incr vs (SOME xs. xs \<in> lists_of (list.set (active_validator_indices (current_epoch bs) vs)))) (Validator.effective_balance_f (var_list_inner vs ! unat flag_index) div EFFECTIVE_BALANCE_INCREMENT config )"                  

lemma get_base_reward_wp[wp]: "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>
     hoare_triple (lift (\<lambda>s. base_reward_pre vs bs flag_index \<and> 
                  (validators \<mapsto>\<^sub>l vs \<and>* beacon_slots \<mapsto>\<^sub>l bs \<and>* 
                    (validators \<mapsto>\<^sub>l vs \<and>* beacon_slots \<mapsto>\<^sub>l bs \<longrightarrow>* ( P (base_reward vs bs flag_index) )))s ))
                   (bindCont (get_base_reward flag_index) next) Q"
  apply (rule hoare_weaken_pre, simp add: get_base_reward_def )
   apply (wp)
   apply (simp only: var_list_index_def)
   apply (wp)
  apply (clarsimp simp: base_reward_pre_def)
  apply (intro exI conjI impI; clarsimp?)
   apply (sep_cancel)+
   apply (clarsimp simp:)
   apply (intro conjI impI)
  apply (fastforce)
    apply (sep_cancel)+
   apply (sep_mp)
   apply (clarsimp)
   apply (intro conjI impI)
    apply (subst (asm) all_sums_eq)
      defer
      apply (assumption)
     apply (cases vs; clarsimp)
    apply (cases vs; clarsimp simp: base_reward_def)
    apply (subst (asm) all_sums_eq) back
      defer
      apply (assumption)
     apply (fastforce)
    apply force
   apply (rule someI_ex)
   apply (clarsimp simp: lists_of_def)
   apply (rule_tac x=xs in exI)
   apply (fastforce)
apply (rule someI_ex)
   apply (clarsimp simp: lists_of_def)
   apply (rule_tac x=xs in exI)
  by (fastforce)

lemma all_active_indices_valid: "x \<in> list.set (active_validator_indices epoch vs) \<Longrightarrow> length (var_list_inner vs) < 2^64 \<Longrightarrow>  x < var_list_len vs"
  apply (clarsimp simp: active_validator_indices_def enumerate_def in_set_zip_iff )
  apply (cases vs; clarsimp)
  apply (unat_arith, clarsimp)
  by (clarsimp simp: unat_of_nat64')


definition "in_activity_leak bs fc  \<equiv> MIN_EPOCHS_TO_INACTIVITY_PENALTY config < raw_epoch (previous_epoch (current_epoch bs)) - raw_epoch (Checkpoint.epoch_f fc)"

definition "previous_unslashed_participating_indices bs vs pep flag_index = 
   {x \<in> list.set (active_validator_indices (previous_epoch (current_epoch bs)) vs). has_flag (unsafe_var_list_index pep x) flag_index \<and> \<not> slashed_f (unsafe_var_list_index vs x)}"

definition "penalty' vs bs pep index flag_index  \<equiv> if (index \<notin> previous_unslashed_participating_indices bs vs pep flag_index  \<and> flag_index \<noteq> TIMELY_HEAD_FLAG_INDEX ) then  base_reward vs bs index * PARTICIPATION_FLAG_WEIGHTS ! flag_index div WEIGHT_DENOMINATOR
                                                     else 0"


definition "arb_active_validator_indices epoch vs \<equiv> (SOME xs. xs \<in> lists_of (list.set (active_validator_indices epoch vs)))"

definition "eligible vs pep flag_index x \<equiv> has_flag (unsafe_var_list_index pep x) flag_index \<and> \<not> slashed_f (unsafe_var_list_index vs x)" 

definition "reward' vs bs fc pep index flag_index \<equiv>
           (if (index \<in>  previous_unslashed_participating_indices bs vs pep flag_index \<and> \<not> in_activity_leak bs fc) then
           (base_reward vs bs index * PARTICIPATION_FLAG_WEIGHTS ! flag_index * (max (EFFECTIVE_BALANCE_INCREMENT config)
          (\<Sum>a\<leftarrow>(filter (eligible vs pep flag_index) (arb_active_validator_indices (previous_epoch (current_epoch bs)) vs)). Validator.effective_balance_f (unsafe_var_list_index vs a)) div EFFECTIVE_BALANCE_INCREMENT config) div (max (EFFECTIVE_BALANCE_INCREMENT config)
          (\<Sum>a\<leftarrow>(arb_active_validator_indices (current_epoch bs) vs). Validator.effective_balance_f (unsafe_var_list_index vs a)) div EFFECTIVE_BALANCE_INCREMENT config * WEIGHT_DENOMINATOR)) 
           else 0)"


definition "get_flag_index_loop_safe vs bs flag_index pep n \<equiv> 
safe_mul (PARTICIPATION_FLAG_WEIGHTS ! flag_index) (base_reward vs bs n) \<and> 
  safe_mul WEIGHT_DENOMINATOR (max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>(arb_active_validator_indices (current_epoch bs) vs). Validator.effective_balance_f (unsafe_var_list_index vs a)) div EFFECTIVE_BALANCE_INCREMENT config) \<and>
  max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>(arb_active_validator_indices (current_epoch bs) vs). Validator.effective_balance_f (unsafe_var_list_index vs a)) div EFFECTIVE_BALANCE_INCREMENT config * WEIGHT_DENOMINATOR \<noteq> 0 \<and>
  safe_mul (max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>(filter (eligible vs pep flag_index) (arb_active_validator_indices (previous_epoch (current_epoch bs)) vs)). Validator.effective_balance_f (unsafe_var_list_index vs a)) div EFFECTIVE_BALANCE_INCREMENT config) (base_reward vs bs n * PARTICIPATION_FLAG_WEIGHTS ! flag_index)
    "

lemma foldr_conj_filter_split: 
  "foldr (\<and>*) (map f xs) \<box> = (foldr (\<and>*) (map f (filter P xs)) \<box> \<and>* foldr (\<and>*) (map f (filter (not P) xs)) \<box>)"
  apply (induct xs; clarsimp simp: pred_neg_def)
  apply (intro conjI impI)
  using sep.mult.left_commute apply blast
  by (simp add: sep_conj_assoc)

lemma concat_map_if_singleton_filter: 
  "concat (map2 (\<lambda>x y. if B x y then [f x y] else []) xs ys) = map (\<lambda>(x,y). f x y) (filter (\<lambda>(x,y). B x y) (zip xs ys))"
  apply (induct xs arbitrary: ys ; clarsimp?)
  apply (subst zip_Cons1)+
  by (clarsimp split: list.splits)

lemma zip_Cons2:
  "zip ys (x#xs) = (case ys of [] \<Rightarrow> [] | y#ys \<Rightarrow> (y,x)#zip ys xs)"
  by(auto split:list.split)

lemma zip_helper: "x \<noteq> [] \<Longrightarrow> zip (a # x) ([0..<length x] @ [length x]) = zip (a # butlast x) [0..<length x] @ [(last x, length x)]"
  apply (induct x arbitrary: a; clarsimp)
  by (smt (verit) Nil_is_append_conv One_nat_def add_Suc_shift but_last_zip butlast.simps(2) butlast_append 
      diff_Suc_1 diff_Suc_Suc last.simps last_append length_Cons length_append length_upt list.discI list.size(3) list.size(4) snoc_eq_iff_butlast zip_eq_Nil_iff)

lemma drop_length_cons[simp]: "drop (length x) (a # x) = [last (a # x)]"
  by (induct x arbitrary: a; clarsimp)

lemma drop_length_butlast: "n < length x \<Longrightarrow> drop (n) (a # x) = drop n (a # butlast x) @ [last (a # x)]"
  apply (induct x arbitrary: n a; clarsimp)
  apply (intro conjI impI; clarsimp)
  using less_Suc_eq_0_disj by force


lemma filter_list_eqI: "(\<And>x. x \<in> list.set xs \<Longrightarrow> P x \<longleftrightarrow> Q x) \<Longrightarrow> filter P xs = filter Q xs"
  by (induct xs; clarsimp)

lemma conv_is_map_Suc: "[Suc n..<length x] = map Suc [n..<length x - 1]"
 by (metis One_nat_def Suc_eq_plus1 list.map(1) map_Suc_upt
              move_it' upt.simps(1) zero_diff)


lemma dec_induct:
  "i \<le> j \<Longrightarrow> P i \<Longrightarrow> (\<And>n. i \<le> n \<Longrightarrow> n < j \<Longrightarrow> P n \<Longrightarrow> P (Suc n)) \<Longrightarrow> P j"
proof (induct j arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc j)
  from Suc.prems consider "i \<le> j" | "i = Suc j"
    by (auto simp add: le_Suc_eq)
  then show ?case
  proof cases
    case 1
    moreover have "j < Suc j" by simp
    moreover have "P j" using \<open>i \<le> j\<close> \<open>P i\<close>
    proof (rule Suc.hyps)
      fix q
      assume "i \<le> q"
      moreover assume "q < j" then have "q < Suc j"
        by (simp add: less_Suc_eq)
      moreover assume "P q"
      ultimately show "P (Suc q)" by (rule Suc.prems)
    qed
    ultimately show "P (Suc j)" by (rule Suc.prems)
  next
    case 2
    with \<open>P i\<close> show "P (Suc j)" by simp
  qed
qed

lemma "na < length x \<Longrightarrow> (drop na x) = x ! na # drop (Suc na) x"
  apply (induct x arbitrary: na ; clarsimp)
  by (simp add: drop_Suc_nth)



lemma inner_filter_is_zip_map: "n \<le> length x \<Longrightarrow> length x < 2^64 \<Longrightarrow>
       map g (filter (\<lambda>n. P ((VariableList x)[n]!)) [n..<length x]) = 
       map (\<lambda>(x,y). g y) (filter (\<lambda>(x,y). P x) (zip (drop n x) [n..<length x]))"
  apply (induct n arbitrary: rule: inc_induct)
   apply (clarsimp)
  apply (clarsimp)
  apply (clarsimp simp: upt_conv_Cons, intro conjI impI)
   apply (subst drop_Suc_nth, clarsimp)
  apply (clarsimp)
    apply (clarsimp simp: index_var_list_def unsafe_var_list_index_def)
  apply (clarsimp simp: unat_of_nat64')
   apply (subst drop_Suc_nth, clarsimp)
  apply (clarsimp)
    apply (clarsimp simp: index_var_list_def unsafe_var_list_index_def)
  by (clarsimp simp: unat_of_nat64')


lemma filter_is_zip_map: "n \<le> length (var_list_inner x) \<Longrightarrow> length (var_list_inner x) < 2^64 \<Longrightarrow>
       map g (filter (\<lambda>n. P (x[n]!)) [n..<length (var_list_inner x)]) = 
       map (\<lambda>(x,y). g y) (filter (\<lambda>(x,y). P x) (zip (drop n (var_list_inner x)) [n..<length (var_list_inner x)]))"
  apply (cases x)
  apply (simp only:)
  using inner_filter_is_zip_map 
  by auto

  


lemma flip_filter_zip: "map fst (filter (\<lambda>(x,y). P x y) (zip xs ys)) =  map snd ( filter (\<lambda>(x,y). P y x) (zip ys xs))"
  apply (induct xs arbitrary: ys; clarsimp?)
  by (case_tac ys; clarsimp)

lemma case_prod_fst_is_fst: "(\<lambda>(x,y). x) = fst"
  by (intro ext, clarsimp)
  
lemma filter_map_map_case: "filter (\<lambda>(x,y). P x) (zip xs (map f ys)) = map (\<lambda>(x,y). (x, f y)) (filter (\<lambda>(x,y). P x) (zip xs ys)) "
  apply (induct xs arbitrary: ys; clarsimp?)
  by (case_tac ys; clarsimp)

(* FIXME: something wrong with the locale imports here *)
lemma [simp]: "Helpers.verified_con.is_active_validator = is_active_validator"
  apply (intro ext)
  apply (case_tac xa; clarsimp)
  apply (case_tac x; clarsimp)
  apply (clarsimp simp: is_active_validator_def Helpers.verified_con.is_active_validator_def)
  apply (subst Helpers.verified_con.is_active_validator_def[where seq=seq and test=test and conj=conj and par=par and pgm=pgm and env=env])
  thm Helpers.verified_con.is_active_validator_def
  using verified_con_axioms apply blast
  by (clarsimp)


lemma eligible_validator_indices_eq: " length (var_list_inner vs) < 2^64 \<Longrightarrow> foldr (\<and>*) (map (\<lambda>xa. lens_oocomp (v_list_lens ((word_of_nat :: nat => 64 word) xa)) x \<mapsto>\<^sub>l f v ((word_of_nat xa) :: u64)) 
            (filter (\<lambda>n. is_active_validator vs[n]! (previous_epoch (current_epoch bs)) \<or> slashed_f vs[n]! \<and> previous_epoch (current_epoch bs) + 1 < withdrawable_epoch_f vs[n]!) 
            [0..<length (local.var_list_inner vs)]))
        \<box> =
       foldr (\<and>*) (map (\<lambda>n. lens_oocomp (v_list_lens n) x \<mapsto>\<^sub>l f v n) (eligible_validator_indices (previous_epoch (current_epoch bs)) (previous_epoch (current_epoch bs) + 1) vs)) \<box> "
  apply (subst comp_def[where f="\<lambda>n. lens_oocomp (v_list_lens n) x \<mapsto>\<^sub>l f v n" and g="word_of_nat", symmetric])
  apply (subst  map_comp_map[symmetric])
  apply (subst  comp_def)
  apply (subgoal_tac "(map word_of_nat 
                         (filter (\<lambda>n. is_active_validator vs[n]! (previous_epoch (current_epoch bs)) \<or> slashed_f vs[n]! \<and> previous_epoch (current_epoch bs) + 1 < withdrawable_epoch_f vs[n]!) 
                            [0..<length (local.var_list_inner vs)])) =
                       (eligible_validator_indices (previous_epoch (current_epoch bs)) (previous_epoch (current_epoch bs) + 1) vs)")
   apply (clarsimp)
  apply (clarsimp simp: eligible_validator_indices_def enumerate_def)
  apply (subst concat_map_if_singleton_filter)
  apply (subst filter_is_zip_map[where n=0, simplified])
   apply (clarsimp)
  apply (subst case_prod_fst_is_fst)
  apply (subst flip_filter_zip)
  apply (subst filter_map_map_case)
  by (clarsimp)

lemma foldr_map_split_merge: "(foldr (\<and>*) (map f (filter P xs)) \<box> \<and>* foldr (\<and>*) (map g (filter (not P) xs)) \<box>) =
      foldr (\<and>*) (map (\<lambda>x. if P x then f x else g x) xs) \<box>"
  apply (induct xs; clarsimp simp: pred_neg_def)
  apply (intro conjI impI; clarsimp?)
   apply (simp add: sep_conj_assoc)
  by (simp add: sep.mult.left_commute)

lemma foldr_map_split_mergeD: "(foldr (\<and>*) (map f (filter P xs)) \<box> \<and>* foldr (\<and>*) (map g (filter (not P) xs)) \<box>) h \<Longrightarrow>
      foldr (\<and>*) (map (\<lambda>x. if P x then f x else g x) xs) \<box> h"
  by (clarsimp simp: foldr_map_split_merge)

lemma merge_if_map: "(\<lambda>xb. if P xb then
              lens_oocomp (v_list_lens ((word_of_nat :: nat \<Rightarrow> 64  word) xb)) x \<mapsto>\<^sub>l f xb else
             lens_oocomp (v_list_lens ((word_of_nat :: nat \<Rightarrow> 64  word) xb)) x \<mapsto>\<^sub>l g xb) =
       (\<lambda>xb.   lens_oocomp (v_list_lens ((word_of_nat :: nat \<Rightarrow> 64  word) xb)) x \<mapsto>\<^sub>l (if P xb then 
                                                                   f xb else g xb)) " 
  by (intro ext; clarsimp split: if_splits)
  

definition "eligible_index prev_epoch curr_epoch vs n \<equiv> is_active_validator (vs[n]!) prev_epoch \<or> slashed_f (vs[n]!) \<and> curr_epoch < withdrawable_epoch_f (vs[n]!)"

definition "cond b f g = (\<lambda>n. if b n then f n else g n)"

lemma sum_lists_of_eq: "xs \<in> lists_of S \<Longrightarrow> ys \<in> lists_of S \<Longrightarrow> sum_list (map f xs) = sum_list (map (f :: 'e \<Rightarrow> 'd :: comm_monoid_add) ys)"
 apply (rule sum_lists_eq)
     apply (clarsimp simp: lists_of_def)
     apply (metis distinct_card)
     apply (clarsimp simp: lists_of_def)
     apply (clarsimp simp: lists_of_def)
  by (clarsimp simp: lists_of_def)

lemma sum_lists_ofE: "P (sum_list (map f xs)) \<Longrightarrow> xs \<in> lists_of S \<Longrightarrow> ys \<in> lists_of S \<Longrightarrow>  P (sum_list (map (f :: 'e \<Rightarrow> 'd :: comm_monoid_add) ys))"
  apply (subst sum_lists_of_eq[rotated -1], assumption, assumption)
  by (clarsimp)


lemma arb_active_is_lists_of[simp]: 
  "arb_active_validator_indices epoch vs \<in> lists_of (list.set (active_validator_indices epoch vs))"
  apply (clarsimp simp: arb_active_validator_indices_def)
  apply (rule someI_ex)
  apply (clarsimp simp: lists_of_def)
  apply (insert finite_distinct_list[where A="list.set (active_validator_indices epoch vs)"])
  apply (clarsimp)
  apply (fastforce)
  done

lemma filter_lists_of[intro]: 
  " xs \<in> lists_of S \<Longrightarrow> filter P xs \<in> lists_of ({x. x \<in> S \<and> P x})"
  by (clarsimp simp: lists_of_def)
 

lemma get_flag_index_deltas_wp[wp]: "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>  current_epoch bs \<noteq> GENESIS_EPOCH \<Longrightarrow>
     hoare_triple (lift (\<lambda>s. length (var_list_inner vs) < 2^64 \<and> 
                    Checkpoint.epoch_f f_c \<in> previous_epochs bs \<and> 
                   (\<forall>x\<in>list.set (eligible_validator_indices (previous_epoch (current_epoch bs)) (previous_epoch (current_epoch bs) + 1) vs). get_flag_index_loop_safe vs bs flag_index pep x \<and> base_reward_pre vs bs x) \<and>
                    previous_epoch (current_epoch bs) \<le> previous_epoch (current_epoch bs) + 1 \<and>
                    (validators \<mapsto>\<^sub>l vs \<and>* beacon_slots \<mapsto>\<^sub>l bs \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<and>* finalized_checkpoint \<mapsto>\<^sub>l f_c \<and>*
                     (finalized_checkpoint \<mapsto>\<^sub>l f_c \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep \<and>* 
                      current_epoch_participation \<mapsto>\<^sub>l cep \<and>* beacon_slots \<mapsto>\<^sub>l bs \<and>* validators \<mapsto>\<^sub>l vs \<longrightarrow>* P (map (cond (eligible_index (previous_epoch (current_epoch bs)) ((previous_epoch (current_epoch bs)) + 1) vs)
                                                                                                                  (\<lambda>n. reward' vs bs f_c pep (word_of_nat n) flag_index) (\<lambda>_. 0)) [0..<length (var_list_inner vs)],
                                                                                                               (map (cond (eligible_index (previous_epoch (current_epoch bs)) ((previous_epoch (current_epoch bs)) + 1) vs) 
                                                                                                                   (\<lambda>n. penalty' vs bs pep (word_of_nat n) flag_index) (\<lambda>_. 0)) [0..<length (var_list_inner vs)] )))) s))
                     (bindCont (get_flag_index_deltas flag_index) next) Q"
  apply (rule hoare_weaken_pre, simp add: get_flag_index_deltas_def)
   apply (simp only: bindCont_assoc[symmetric])
   apply (rule read_beacon_wp_ex)
   apply (rule alloc_wp)
   apply (rule alloc_wp)
   apply (rule get_previous_epoch_wp'')
  using [[unify_search_bound = 500]]   
  apply (rule_tac v=xa and x="(previous_epoch (slot_to_epoch config _))" in hoare_eqI')
   apply (rule get_previous_unslashed_participating_indices_wp)
    apply (rule hoare_let)
    apply (simp only: bindCont_assoc[symmetric])
    apply (rule get_total_balance_wp)
    apply (rule div_wp')
    apply (rule get_total_active_balance_wp)
    apply (rule div_wp')
    apply (rule get_eligible_validator_indices)
    apply (rule mapM_fake)
  apply (wp)
      apply (clarsimp)

      apply (assumption)
  apply (wp)
     apply (clarsimp)
     apply (assumption)
    apply (wp)
   defer
   apply (clarsimp)
  apply (rule exI)
   apply (sep_cancel)+
   apply (clarsimp)
   apply (sep_cancel)+
 apply (clarsimp)
   apply (sep_cancel)+
   apply (rule conjI, rule refl)
   apply (intro conjI impI)
   apply (sep_cancel)+
   apply (intro conjI impI)
    apply (clarsimp)
    apply (erule  all_active_indices_valid)
    apply (clarsimp)
   apply (clarsimp simp: )
   apply (sep_cancel)+
   apply (intro conjI impI)
 apply (clarsimp)
    apply (erule  all_active_indices_valid)
    apply (clarsimp)
   apply (clarsimp)
  apply (clarsimp simp: sep_conj_ac)
      apply (sep_cancel)+
    apply (simp add: mapM_is_sequence_map)
    apply (rule_tac P = "\<lambda>n. (\<lambda>s. base_reward_pre vs bs n \<and> get_flag_index_loop_safe vs bs flag_index pep n  \<and> ((lens_oocomp (v_list_lens n) x) \<mapsto>\<^sub>l 0 \<and>* (lens_oocomp (v_list_lens n) xa) \<mapsto>\<^sub>l 0 ) s)" and I="(\<lambda>s. Checkpoint.epoch_f f_c \<in> previous_epochs bs \<and> (beacon_slots \<mapsto>\<^sub>l bs \<and>* validators \<mapsto>\<^sub>l vs \<and>* finalized_checkpoint \<mapsto>\<^sub>l f_c) s)"
                     and Q="\<lambda>n. ((lens_oocomp (v_list_lens n) x) \<mapsto>\<^sub>l reward' vs bs f_c pep n flag_index \<and>* (lens_oocomp (v_list_lens n) xa) \<mapsto>\<^sub>l penalty' vs bs pep n flag_index) " and S="\<lambda>_. sep_empty" and 
                     g="undefined" and D ="\<lambda>_ _ _. True" in sequenceI_rewriting4)
      apply (clarsimp)
  apply (intro conjI impI)

      apply (rule exI, sep_cancel+)
      apply (rule exI, sep_cancel+)
  apply (intro conjI impI)
       apply (fastforce)
      apply (sep_cancel)+
            apply (clarsimp)
  apply (erule_tac x=xb in ballE; clarsimp)

             apply (intro conjI impI)
                 apply (fastforce simp: get_flag_index_loop_safe_def)
               apply (clarsimp simp: get_flag_index_loop_safe_def)
                apply (erule sum_lists_ofE, rule filter_lists_of, rule arb_active_is_lists_of, clarsimp simp: eligible_def)
  apply (clarsimp simp: get_flag_index_loop_safe_def)
               apply (erule sum_lists_ofE, rule arb_active_is_lists_of, clarsimp)
 apply (simp add: get_flag_index_loop_safe_def, elim conjE)
                apply (erule sum_lists_ofE, rule arb_active_is_lists_of, clarsimp)
                  apply (rule exI, sep_cancel)+
                  apply (clarsimp)
                  apply (sep_cancel)+
             apply (clarsimp simp: reward'_def penalty'_def previous_unslashed_participating_indices_def in_activity_leak_def)
             apply (subst (asm) sum_lists_of_eq, rule filter_lists_of, rule arb_active_is_lists_of, fastforce simp: eligible_def)+
             apply (subst (asm) sum_lists_of_eq,  rule arb_active_is_lists_of, fastforce)+
  apply (sep_mp, assumption)
                 apply (intro exI, sep_cancel+)
  apply (intro exI, sep_cancel+)
                 apply (clarsimp)
                 apply (sep_cancel)+
            apply (intro conjI impI)
  apply (fastforce simp: get_flag_index_loop_safe_def)
                  apply (clarsimp simp: WEIGHT_DENOMINATOR_def)
                  apply (rule exI, sep_cancel)+
                 apply (clarsimp)
                 apply (sep_cancel)+
            apply (clarsimp simp: reward'_def penalty'_def  in_activity_leak_def)
apply (subst (asm) sum_lists_of_eq, rule filter_lists_of, rule arb_active_is_lists_of, fastforce simp: eligible_def)+
             apply (subst (asm) sum_lists_of_eq,  rule arb_active_is_lists_of, fastforce)+
  apply (subgoal_tac "xb \<notin>previous_unslashed_participating_indices bs vs pep flag_index", clarsimp)
apply (sep_mp)
                  apply (assumption)
                 apply (clarsimp simp: previous_unslashed_participating_indices_def)
apply (intro exI, sep_cancel+)
  apply (intro exI, sep_cancel+)
                 apply (clarsimp)
          apply (sep_cancel)+
  apply (erule_tac x=xb in ballE; clarsimp)

           apply (intro conjI impI)
  apply (fastforce simp: get_flag_index_loop_safe_def)
  apply (clarsimp simp: get_flag_index_loop_safe_def)
                apply (erule sum_lists_ofE, rule filter_lists_of, rule arb_active_is_lists_of, clarsimp simp: eligible_def)
  apply (clarsimp simp: get_flag_index_loop_safe_def)
               apply (erule sum_lists_ofE, rule arb_active_is_lists_of, clarsimp)
 apply (simp add: get_flag_index_loop_safe_def, elim conjE)
                apply (erule sum_lists_ofE, rule arb_active_is_lists_of, clarsimp)
                  apply (rule exI, sep_cancel)+

                    apply (sep_cancel)+
  apply (clarsimp simp: reward'_def penalty'_def previous_unslashed_participating_indices_def in_activity_leak_def)
apply (subst (asm) sum_lists_of_eq, rule filter_lists_of, rule arb_active_is_lists_of, fastforce simp: eligible_def)+
         apply (subst (asm) sum_lists_of_eq,  rule arb_active_is_lists_of, fastforce)+
  apply (sep_cancel)+
                    apply (sep_mp, assumption)
apply (intro exI, sep_cancel+)
  apply (intro exI, sep_cancel+)
                 apply (clarsimp)
                   apply (sep_cancel)+
  apply (clarsimp simp: reward'_def penalty'_def  in_activity_leak_def sep_conj_ac)
apply (subst (asm) sum_lists_of_eq, rule filter_lists_of, rule arb_active_is_lists_of, fastforce simp: eligible_def)+
             apply (subst (asm) sum_lists_of_eq,  rule arb_active_is_lists_of, fastforce)+
  apply (subgoal_tac "xb \<notin>previous_unslashed_participating_indices bs vs pep flag_index", clarsimp)
apply (sep_mp)
                  apply (assumption)
          apply (clarsimp simp: previous_unslashed_participating_indices_def)
apply (intro exI, sep_cancel+)
  apply (intro exI, sep_cancel+)
                 apply (clarsimp)
         apply (sep_cancel)+
  apply (clarsimp simp: reward'_def penalty'_def previous_unslashed_participating_indices_def in_activity_leak_def sep_conj_ac)
apply (sep_mp)
         apply (assumption)
apply (intro exI, sep_cancel+)
  apply (intro exI, sep_cancel+)
                 apply (clarsimp)
        apply (sep_cancel)+
        apply (intro conjI impI)
          apply (fastforce simp: get_flag_index_loop_safe_def)
apply (clarsimp simp: WEIGHT_DENOMINATOR_def)
                 apply (rule exI, sep_cancel+)+
      apply (clarsimp)
  apply (sep_cancel)+
  apply (clarsimp simp: reward'_def penalty'_def previous_unslashed_participating_indices_def in_activity_leak_def sep_conj_ac)

apply (sep_mp)
        apply (assumption)
apply (intro exI, sep_cancel+)
  apply (intro exI, sep_cancel+)
                 apply (clarsimp)
       apply (sep_cancel)+
  apply (clarsimp simp: reward'_def penalty'_def previous_unslashed_participating_indices_def in_activity_leak_def sep_conj_ac)

apply (sep_mp)
       apply (assumption)
apply (intro exI, sep_cancel+)
  apply (intro exI, sep_cancel+)
                 apply (clarsimp)
       apply (sep_cancel)+
  apply (clarsimp simp: reward'_def penalty'_def previous_unslashed_participating_indices_def in_activity_leak_def sep_conj_ac)

apply (sep_mp)
      apply (assumption)
     apply (clarsimp simp: sep_conj_ac)
      apply (clarsimp simp: split_foldr_map_sep_conj split_foldr_map_conj restore_variablelist local.foldr_pure_empty)

  apply (subst (asm) restore_variablelist[symmetric])+
        apply (sep_cancel)+
  apply (subst (asm) foldr_conj_filter_split[where P="\<lambda>n. is_active_validator (vs[n]!) (previous_epoch (current_epoch bs)) \<or>
         (slashed_f (vs[n]!) \<and> (previous_epoch (current_epoch bs) + 1) < withdrawable_epoch_f (vs[n]!))"])
apply (subst (asm) foldr_conj_filter_split[where P="\<lambda>n. is_active_validator (vs[n]!) (previous_epoch (current_epoch bs)) \<or>
         (slashed_f (vs[n]!) \<and> (previous_epoch (current_epoch bs) + 1) < withdrawable_epoch_f (vs[n]!))"]) back back
        apply (clarsimp simp: sep_conj_ac)
        apply (sep_select_asm 3)
   apply (erule sep_conj_impl)
         apply (subst (asm)  eligible_validator_indices_eq)
  apply (fastforce)
  apply (fastforce)
         apply (subst (asm)  eligible_validator_indices_eq)
         apply (fastforce)
                 apply (sep_cancel)+

        apply (clarsimp simp: sep_conj_ac)
        apply (subst (asm)  eligible_validator_indices_eq[symmetric], fastforce)
        apply (subst (asm)  eligible_validator_indices_eq[symmetric], fastforce)
        apply (clarsimp simp: sep_conj_ac) 
  apply (sep_select_asm 9 6)
        apply (sep_drule foldr_map_split_mergeD, subst (asm) merge_if_map)
        apply (sep_select_asm 4 3)
        apply (sep_drule foldr_map_split_mergeD)
        apply ( subst (asm) merge_if_map)


   apply (clarsimp simp: split_foldr_map_sep_conj split_foldr_map_conj restore_variablelist local.foldr_pure_empty)
  apply (rule exI, sep_cancel+)+
    apply (clarsimp simp: cond_def eligible_index_def)
  by (fastforce)




lemma var_list_inner_wp[wp]:
         "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> 
           hoare_triple (lift (\<lambda>s. unat i < length (var_list_inner xs) \<and> length (var_list_inner xs) < 2^64 \<and> 
                                    (unat i < length (var_list_inner xs) \<longrightarrow> length (var_list_inner xs) < 2^64 \<longrightarrow>  P (var_list_inner xs ! unat i) s))) 
                         (do {v <- var_list_index xs i; next v}) Q"
  apply (unfold var_list_index_def, rule hoare_weaken_pre)
   apply (wp)
    apply (simp, fastforce)
   apply (clarsimp)
   apply (wp)
  apply (clarsimp)
  apply (intro conjI impI; clarsimp)
   apply (case_tac xs; clarsimp)
  apply (case_tac xs; clarsimp)
  by (unat_arith, clarsimp simp: unat_of_nat64')  


definition "inactivity_penalty vs is bs pep index \<equiv> 
         (if index \<notin> (previous_unslashed_participating_indices bs vs pep TIMELY_TARGET_FLAG_INDEX) 
             then (Validator.effective_balance_f (unsafe_var_list_index vs index)) * (unsafe_var_list_index is index)
                  div (INACTIVITY_SCORE_BIAS config * INACTIVITY_PENALTY_QUOTIENT_ALTAIR)
             else 0)"



lemma all_eligible_in_range[simp]: 
      "n \<in> list.set (eligible_validator_indices epoch epoch' vs) \<Longrightarrow>
       unat n < length (local.var_list_inner vs)"
  apply (clarsimp simp: eligible_validator_indices_def enumerate_def)
  by (smt (verit, ccfv_SIG) add_cancel_right_left add_lessD1 in_set_zip_iff length_map 
        less_imp_add_positive linorder_neqE_nat nth_map nth_upt unat_less_helper word_of_nat_less)

definition "inactivity_penalty' vs bs is pep\<equiv> (\<lambda>xb. if is_active_validator (vs[xb]!) (previous_epoch (current_epoch bs))\<or> slashed_f (vs[xb]!) \<and>
                                                                       previous_epoch (current_epoch bs) + 1 < withdrawable_epoch_f (vs[xb]!) then inactivity_penalty vs is bs pep (word_of_nat xb) else 0)"

 

lemma get_inactivity_penalty_deltas_wp[wp]: "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> current_epoch bs \<noteq> GENESIS_EPOCH \<Longrightarrow>
     hoare_triple (lift (\<lambda>s. length (var_list_inner vs) < 2^64 \<and> length (local.var_list_inner is) = length (local.var_list_inner vs)  \<and>
                   safe_mul INACTIVITY_PENALTY_QUOTIENT_ALTAIR (INACTIVITY_SCORE_BIAS config) \<and>  INACTIVITY_SCORE_BIAS config * INACTIVITY_PENALTY_QUOTIENT_ALTAIR \<noteq> 0 \<and>
                   (\<forall>i\<in>(list.set (eligible_validator_indices (previous_epoch (current_epoch bs)) (previous_epoch (current_epoch bs) + 1) vs)). 
                        safe_mul (local.var_list_inner is ! unat i) (Validator.effective_balance_f (local.var_list_inner vs ! unat i))) \<and>
                    previous_epoch (current_epoch bs) \<le> previous_epoch (current_epoch bs) + 1 \<and>
                    (validators \<mapsto>\<^sub>l vs \<and>* beacon_slots \<mapsto>\<^sub>l bs \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<and>* inactivity_scores \<mapsto>\<^sub>l is \<and>*
                     (inactivity_scores \<mapsto>\<^sub>l is \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep \<and>*  current_epoch_participation \<mapsto>\<^sub>l cep \<and>*
                       beacon_slots \<mapsto>\<^sub>l bs \<and>* validators \<mapsto>\<^sub>l vs \<longrightarrow>* P (map (\<lambda>_. 0) [0..<length (var_list_inner vs)],
                                                                      (map (inactivity_penalty' vs bs is pep) [0..<length (var_list_inner vs)] )))) s))
                     (bindCont (get_inactivity_penalty_deltas) next) Q"
  apply (unfold get_inactivity_penalty_deltas_def, rule hoare_weaken_pre)
   apply (simp only: bindCont_assoc[symmetric])
 apply (rule read_beacon_wp_ex)
   apply (rule alloc_wp)
   apply (rule alloc_wp)
   apply (rule get_previous_epoch_wp'')
  using [[unify_search_bound = 500]]   
  apply (rule_tac v=xa and x="(previous_epoch (slot_to_epoch config _))" in hoare_eqI')
   apply (rule get_previous_unslashed_participating_indices_wp)
    apply (rule get_eligible_validator_indices)
 apply (rule read_beacon_wp_ex)
 apply (rule read_beacon_wp_ex)
    apply (rule mapM_fake)
     apply (wp)
     apply (fastforce)
    apply (wp)
   defer
   apply (clarsimp)
   apply (rule exI, sep_cancel+)
  apply (clarsimp)
   apply (sep_cancel)+
   apply (clarsimp)
   apply (sep_cancel)+
   apply (intro conjI impI)
    apply (fastforce)
   apply (sep_cancel)+
   apply (intro conjI impI; clarsimp)
    apply (sep_cancel)+
  apply (rule exI)
    apply (sep_cancel)+
  apply (rule exI)
   apply (sep_cancel)+
    apply (simp add: mapM_is_sequence_map)

   apply (rule_tac P = "\<lambda>n. (\<lambda>s.  ((lens_oocomp (v_list_lens n) x) \<mapsto>\<^sub>l 0 \<and>* (lens_oocomp (v_list_lens n) xa) \<mapsto>\<^sub>l 0 ) s)"
               and I = "(validators \<mapsto>\<^sub>l vs \<and>* inactivity_scores \<mapsto>\<^sub>l is)"
                     and Q="\<lambda>n. ((lens_oocomp (v_list_lens n) x) \<mapsto>\<^sub>l 0 \<and>* (lens_oocomp (v_list_lens n) xa) \<mapsto>\<^sub>l inactivity_penalty vs is bs pep n) " and S="\<lambda>_. sep_empty" and 
                     g="undefined" and D ="\<lambda>_ _ _. True" in sequenceI_rewriting4)
     apply (clarsimp)
     apply (intro conjI impI)
  apply (intro exI)
      apply (sep_cancel)+
 apply (intro exI)
     apply (sep_cancel)+
  apply (rule exI, sep_cancel+)
      apply (intro conjI impI; (clarsimp elim: all_eligible_in_range)?)
  apply (sep_cancel)+
         apply (sep_mp)
         apply (clarsimp simp: inactivity_penalty_def previous_unslashed_participating_indices_def unsafe_var_list_index_def split: if_splits)
          apply (sep_mp, assumption)
  
  apply (clarsimp)
        apply (rule exI, sep_cancel+)
        apply (rule exI, sep_cancel+)
         apply (clarsimp simp: inactivity_penalty_def previous_unslashed_participating_indices_def unsafe_var_list_index_def split: if_splits)
        apply (sep_mp, assumption)
  apply (clarsimp)
  apply (clarsimp simp: sep_conj_ac)
       apply (clarsimp simp: split_foldr_map_sep_conj split_foldr_map_conj restore_variablelist local.foldr_pure_empty)
       apply (sep_cancel)+

  apply (subst (asm) restore_variablelist[symmetric])+
 apply (subst (asm) foldr_conj_filter_split[where P="\<lambda>n. is_active_validator (vs[n]!) (previous_epoch (current_epoch bs)) \<or>
         (slashed_f (vs[n]!) \<and> (previous_epoch (current_epoch bs) + 1) < withdrawable_epoch_f (vs[n]!))"])
apply (subst (asm) foldr_conj_filter_split[where P="\<lambda>n. is_active_validator (vs[n]!) (previous_epoch (current_epoch bs)) \<or>
         (slashed_f (vs[n]!) \<and> (previous_epoch (current_epoch bs) + 1) < withdrawable_epoch_f (vs[n]!))"]) back back
        apply (clarsimp simp: sep_conj_ac)
        apply (sep_select_asm 5)
  apply (erule sep_conj_impl)
        apply (subst (asm)  eligible_validator_indices_eq)
  apply (clarsimp)
        apply (sep_cancel)+
   apply (sep_select_asm 5)
  apply (erule sep_conj_impl)
        apply (subst (asm)  eligible_validator_indices_eq)
  apply (clarsimp)
        apply (sep_cancel)+

        apply (subst (asm)  eligible_validator_indices_eq[symmetric], fastforce)
        apply (subst (asm)  eligible_validator_indices_eq[symmetric], fastforce)
        apply (clarsimp simp: sep_conj_ac) 
       apply (sep_drule foldr_map_split_mergeD)
         apply ( subst (asm) merge_if_map)

       apply (sep_drule foldr_map_split_mergeD)
         apply ( subst (asm) merge_if_map)

       apply (clarsimp simp: split_foldr_map_sep_conj split_foldr_map_conj restore_variablelist local.foldr_pure_empty)
       apply (rule exI, sep_cancel+)+
       apply (clarsimp simp: inactivity_penalty'_def)
  by (fastforce)
  


definition increase_balance' ::
  "u64 \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
  where
  "increase_balance' i r \<equiv> do {
     orig_balance \<leftarrow> mut ( balances !? i) ;
     (orig_balance := orig_balance .+ r)
  }"

definition decrease_balance' ::
  "u64 \<Rightarrow> u64 \<Rightarrow> (unit, 'a) cont"
  where
  "decrease_balance' i r \<equiv> do {
     orig_balance \<leftarrow> mut ( balances !? i) ;
     (orig_balance := orig_balance .- r)
  }"

lemma increase_balance_ref: "increase_balance \<le> increase_balance'"
  apply (rule le_funI)+
  apply (clarsimp simp: increase_balance_def var_list_index_lens_def increase_balance'_def bindCont_def read_beacon_def getState_def var_list_index_def Sup_le_iff)
  apply (intro conjI impI)
   apply (clarsimp simp: fail_def)
   apply (rule_tac i="(a,b)" in SUP_upper2; clarsimp)
   apply (intro conjI impI; clarsimp simp: lens_oocomp_def)
   apply (clarsimp simp: fail_def)
  apply (clarsimp simp: return_def)
  apply (intro conjI impI)
   apply (rule_tac i="(a,b)" in SUP_upper2; clarsimp)
  apply (intro conjI impI; clarsimp simp: lens_oocomp_def)
    apply (clarsimp simp: fail_def v_list_lens_def split: if_splits)
  apply (rule seq_mono; clarsimp)
   apply (clarsimp simp: return_def)
   apply (clarsimp simp: test_restricts_Nondet return_def lens_oocomp_def)
   apply (clarsimp simp: v_list_lens_def split: if_splits)
   apply (clarsimp simp: word_unsigned_add_def Let_unfold)
   apply (intro conjI impI; clarsimp simp: return_def fail_def)
     apply (clarsimp simp: var_list_update_def return_def test_restricts_Nondet write_beacon_def getState_def bindCont_def )
     apply (case_tac y; clarsimp)
   apply (rule_tac i="(a,b)" in SUP_upper2; clarsimp)
  apply (intro conjI impI; clarsimp simp: lens_oocomp_def fail_def)
  apply (clarsimp simp: v_list_lens_def split: if_splits)
  by (unat_arith; clarsimp simp: unat_of_nat64')


lemma decrease_balance_ref:
 "decrease_balance \<le> decrease_balance'"
  apply (rule le_funI)+
  apply (clarsimp simp: decrease_balance'_def var_list_index_lens_def decrease_balance_def bindCont_def read_beacon_def getState_def var_list_index_def Sup_le_iff)
  apply (intro conjI impI)
   apply (clarsimp simp: fail_def)
   apply (rule_tac i="(a,b)" in SUP_upper2; clarsimp)
   apply (intro conjI impI; clarsimp simp: lens_oocomp_def)
   apply (clarsimp simp: fail_def)
  apply (clarsimp simp: return_def)
  apply (intro conjI impI)
   apply (rule_tac i="(a,b)" in SUP_upper2; clarsimp)
  apply (intro conjI impI; clarsimp simp: lens_oocomp_def)
    apply (clarsimp simp: fail_def v_list_lens_def split: if_splits)
  apply (rule seq_mono; clarsimp)
   apply (clarsimp simp: return_def)
   apply (clarsimp simp: test_restricts_Nondet return_def lens_oocomp_def)
   apply (clarsimp simp: v_list_lens_def split: if_splits)
   apply (clarsimp simp: word_unsigned_sub_def Let_unfold)
   apply (intro conjI impI; clarsimp simp: return_def fail_def)
     apply (clarsimp simp: var_list_update_def return_def test_restricts_Nondet write_beacon_def getState_def bindCont_def )
    apply (case_tac y; clarsimp)
    apply (unat_arith; clarsimp simp: unat_of_nat64')
    apply (rule seq_mono; clarsimp)
   apply (case_tac y; clarsimp)
   apply (rule_tac i="(a,b)" in SUP_upper2; clarsimp)
  apply (intro conjI impI; clarsimp simp: lens_oocomp_def fail_def)
  apply (clarsimp simp: v_list_lens_def split: if_splits)
  by (unat_arith; clarsimp simp: unat_of_nat64')




lemma increase_balance_wp[wp]: 
 "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> 
   hoare_triple (lift (\<lambda>s. \<exists>v.  v \<le> v + value \<and> ( v \<le> v + value \<longrightarrow> (lcomp (v_list_lens index) balances \<mapsto>\<^sub>l v \<and>* ((lcomp (v_list_lens index) balances \<mapsto>\<^sub>l v + value \<longrightarrow>* P ()) )) s))) 
       (bindCont (increase_balance index value) next) Q"
  apply (rule refine_in_hoare[rotated])
   apply (rule increase_balance_ref[THEN le_funD, THEN le_funD]) 
  apply (clarsimp)
  apply (clarsimp simp: increase_balance'_def)
  apply (rule hoare_weaken_pre)
   apply (simp only: bindCont_assoc[symmetric])
   apply ( rule wp)
  apply (rule read_beacon_wp_ex)
   apply (wp)
  apply (clarsimp)
  apply (rule exI)
  apply (sep_cancel)+

  apply (rule exI)
  apply (sep_cancel)+
  apply (intro conjI impI; clarsimp)
  by (sep_cancel)+


lemma decrease_balance_wp[wp]: 
 "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> 
   hoare_triple (lift (\<lambda>s. \<exists>v.  value \<le> v  \<and> ( value \<le> v \<longrightarrow> (lcomp (v_list_lens index) balances \<mapsto>\<^sub>l v \<and>* ((lcomp (v_list_lens index) balances \<mapsto>\<^sub>l v - value \<longrightarrow>* P ()) )) s))) 
       (bindCont (decrease_balance index value) next) Q"
  apply (rule refine_in_hoare[rotated])
   apply (rule decrease_balance_ref[THEN le_funD, THEN le_funD]) 
  apply (clarsimp)
  apply (clarsimp simp: decrease_balance'_def)
  apply (rule hoare_weaken_pre)
   apply (simp only: bindCont_assoc[symmetric])
   apply ( rule wp)
  apply (rule read_beacon_wp_ex)
   apply (wp)
  apply (clarsimp)
  apply (rule exI)
  apply (sep_cancel)+

  apply (rule exI)
  apply (sep_cancel)+
  apply (intro conjI impI; clarsimp)
  by (sep_cancel)+

lemma "length (local.var_list_inner bs) < 2^64 \<Longrightarrow>
       foldr (\<and>*) (map ((\<lambda>n. lens_oocomp (v_list_lens n) balances \<mapsto>\<^sub>l unsafe_var_list_index bs n) \<circ> word_of_nat) [0..<length (local.var_list_inner bs)]) \<box> = 
      ( balances \<mapsto>\<^sub>l bs)"
  apply (clarsimp simp: comp_def)
  apply (subst restore_variablelist)
  apply (rule arg_cong[where y=bs])
  by (case_tac bs; clarsimp)

definition "adjusted_balances bs rp \<equiv> VariableList (map (\<lambda>x. unsafe_var_list_index bs ((word_of_nat x) :: u64) + fst rp ! unat ((word_of_nat x) :: u64) - snd rp ! unat ((word_of_nat x) :: u64)) [0..<length (local.var_list_inner bs)])"
  

definition "safe_adjustments bs rp \<equiv> \<forall>n\<in>{n. n < length (var_list_inner bs)}. 
                                         (bs[n]!) \<le> (bs[n]!) + fst rp ! n \<and>  snd rp ! n \<le> (bs[n]!) + fst rp ! n"

lemma apply_rewards_and_penalties_wp: 
    "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>
      hoare_triple (lift  (\<lambda>s. length (var_list_inner vs) = length (var_list_inner bs)  \<and> safe_adjustments bs rp \<and>
                               length (local.var_list_inner bs) < 2^64 \<and>  (balances \<mapsto>\<^sub>l bs \<and>*  (balances \<mapsto>\<^sub>l adjusted_balances bs rp \<longrightarrow>* P ())) s))
        (bindCont (apply_rewards_and_penalties rp vs) next) Q"
  apply (rule hoare_weaken_pre)
   apply (unfold apply_rewards_and_penalties_def)
   apply (wp)
  apply (clarsimp simp:)
  apply (subst mapM_is_sequence_map)
   apply (rule_tac P = "\<lambda>n. (lens_oocomp (v_list_lens n) balances) \<mapsto>\<^sub>l unsafe_var_list_index bs n"
               and I = "sep_empty"
                     and Q="\<lambda>n. (lens_oocomp (v_list_lens n) balances) \<mapsto>\<^sub>l unsafe_var_list_index bs n + (fst rp ! unat n) - (snd rp ! unat n)" and S="\<lambda>_. sep_empty" and 
                     g="undefined" and D ="\<lambda>_ _ _. True" in sequenceI_rewriting4)
    apply (clarsimp)
    apply (rule_tac x=" bs[xb]!" in exI)
    apply (intro conjI impI)
      apply (clarsimp simp: safe_adjustments_def unat_of_nat64')
     apply (clarsimp simp: index_var_list_def)
  apply (sep_cancel)+
     apply (rule_tac x="bs[xb]! + (fst rp !  xb)" in exI)
     apply (intro conjI impI)
      apply (clarsimp simp: safe_adjustments_def unat_of_nat64')
      apply (clarsimp)
     apply (clarsimp simp: index_var_list_def)
      defer
      apply (clarsimp)
  apply (clarsimp simp: comp_def)
      apply (clarsimp simp: split_foldr_map_sep_conj split_foldr_map_conj restore_variablelist local.foldr_pure_empty)
      apply (clarsimp simp: adjusted_balances_def)
   apply (fastforce)
   apply (clarsimp simp: unat_of_nat64')
  by (sep_solve)



lemma apply_rewards_and_penalties_wp'[wp]: 
    "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>
      hoare_triple (lift  (\<lambda>s. \<exists>bs. length (var_list_inner vs) = length (var_list_inner bs)  \<and> safe_adjustments bs rp \<and>
                               length (local.var_list_inner bs) < 2^64 \<and>  (balances \<mapsto>\<^sub>l bs \<and>*  (balances \<mapsto>\<^sub>l adjusted_balances bs rp \<longrightarrow>* P ())) s))
        (bindCont (apply_rewards_and_penalties rp vs) next) Q"
  apply (rule hoare_assert_state_liftI)
  apply (drule lift_exD, clarsimp)
  apply (rule hoare_weaken_pre)
   apply (rule apply_rewards_and_penalties_wp)
   apply (fastforce)
  apply (clarsimp)
  apply (intro conjI)
     apply (fastforce)
    apply (fastforce)
   apply (fastforce)
  apply (unfold lift_def, clarsimp)
  apply (fastforce)
  done

lemma length_adjusted_balances_eq[simp]: 
 "length (local.var_list_inner (adjusted_balances bls rp)) = length (local.var_list_inner bls)"
  by (clarsimp simp: adjusted_balances_def)

lemma length_adjusted_balances_foldl_eq[simp]:
     "length (local.var_list_inner (foldl (\<lambda>bls n. adjusted_balances bls (flag_deltas vs bs pep f_c n)) bls [0..<length PARTICIPATION_FLAG_WEIGHTS])) =
      length (local.var_list_inner bls) "
  by (clarsimp simp: PARTICIPATION_FLAG_WEIGHTS_def)

definition "flag_deltas vs bs pep f_c xa\<equiv> 
    (map (cond (eligible_index (previous_epoch (current_epoch bs)) (previous_epoch (current_epoch bs) + 1) vs) (\<lambda>n. reward' vs bs f_c pep (word_of_nat n) xa) (\<lambda>_. 0)) [0..<length (local.var_list_inner vs)],
    map (cond (eligible_index (previous_epoch (current_epoch bs)) (previous_epoch (current_epoch bs) + 1) vs) (\<lambda>n. penalty' vs bs pep (word_of_nat n) xa) (\<lambda>_. 0)) [0..<length (local.var_list_inner vs)])"

definition "adjust_balance_pfw bls rp \<equiv> foldl (\<lambda>bls n. adjusted_balances bls (rp n)) bls [0..<length PARTICIPATION_FLAG_WEIGHTS]"

definition "inactivity_penalties_rp vs bs is pep \<equiv> (map (\<lambda>_. 0) [0..<length (local.var_list_inner vs)], map (inactivity_penalty' vs bs is pep) [0..<length (local.var_list_inner vs)])"

lemma "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> current_epoch bs \<noteq> GENESIS_EPOCH \<Longrightarrow>
      hoare_triple (lift (\<lambda>s. length (var_list_inner vs) < 2^64 \<and> length (local.var_list_inner is) = length (local.var_list_inner vs) \<and> length (var_list_inner bls) = length (var_list_inner vs) \<and>
                         Checkpoint.epoch_f f_c \<in> previous_epochs bs \<and> previous_epoch (current_epoch bs) \<le> previous_epoch (current_epoch bs) + 1 \<and>
                         safe_mul INACTIVITY_PENALTY_QUOTIENT_ALTAIR (INACTIVITY_SCORE_BIAS config) \<and>
                         (\<forall>(v, s, s')\<in>local.trans (\<lambda>n bls. adjusted_balances bls (flag_deltas vs bs pep f_c n)) [0..<length PARTICIPATION_FLAG_WEIGHTS] bls. safe_adjustments s (flag_deltas vs bs pep f_c v)) \<and>
                         (\<forall>i\<in>list.set (eligible_validator_indices (previous_epoch (current_epoch bs)) (previous_epoch (current_epoch bs) + 1) vs). 
                         safe_mul (local.var_list_inner is ! unat i) (Validator.effective_balance_f (local.var_list_inner vs ! unat i))) \<and> INACTIVITY_SCORE_BIAS config * INACTIVITY_PENALTY_QUOTIENT_ALTAIR \<noteq> 0 \<and>
                         safe_adjustments (adjust_balance_pfw bls (flag_deltas vs bs pep f_c)) (inactivity_penalties_rp vs bs is pep) \<and>
                        (\<forall>x\<in>list.set (eligible_validator_indices (previous_epoch (current_epoch bs)) (previous_epoch (current_epoch bs) + 1) vs).
                           \<forall>flag_index<(length (PARTICIPATION_FLAG_WEIGHTS)). get_flag_index_loop_safe vs bs flag_index pep x \<and> base_reward_pre vs bs x) \<and>
                       (validators \<mapsto>\<^sub>l vs \<and>* beacon_slots \<mapsto>\<^sub>l bs \<and>*  balances \<mapsto>\<^sub>l bls \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep  \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<and>* finalized_checkpoint \<mapsto>\<^sub>l f_c \<and>* inactivity_scores \<mapsto>\<^sub>l is \<and>*                       
                       (validators \<mapsto>\<^sub>l vs \<and>* inactivity_scores \<mapsto>\<^sub>l is \<and>* balances \<mapsto>\<^sub>l adjusted_balances (adjust_balance_pfw bls (flag_deltas vs bs pep f_c)) (inactivity_penalties_rp vs bs is pep) \<and>* finalized_checkpoint \<mapsto>\<^sub>l f_c \<and>* beacon_slots \<mapsto>\<^sub>l bs \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep  \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<longrightarrow>* P ())) s)) 
         (bindCont process_rewards_and_penalties next) Q"
  apply (rule hoare_weaken_pre)
   apply (simp add: process_rewards_and_penalties_def)
   apply (subst fold_flags_is_map_flags)
   apply (subst append.left_neutral)
   apply (wp)
    apply (simp)
  apply (simp add: bindCont_assoc[symmetric])
  apply (rule mapM_fake)
    apply (wp)
   apply (fastforce)
   apply (clarsimp)
  apply (clarsimp)
  apply (rule exI)

   apply (sep_cancel+)
  apply (subst mapM_is_sequence_map)
  apply (rule_tac P = "\<lambda>n. sep_empty"
               and I = "(validators \<mapsto>\<^sub>l vs \<and>* beacon_slots \<mapsto>\<^sub>l bs \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep  \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<and>* finalized_checkpoint \<mapsto>\<^sub>l f_c)"
                     and Q="\<lambda>n. sep_empty" and S="\<lambda>_. sep_empty" and 
                     g="flag_deltas vs bs pep f_c" and D ="\<lambda>_ _ _. True" in sequenceI_rewriting4)
  thm sequenceI_rewriting
     apply (clarsimp simp: sep_conj_ac)
     apply (intro conjI impI)
  prefer 4
        apply (sep_cancel)+
  apply (sep_mp, fastforce simp: flag_deltas_def)
        apply (fastforce)
        apply (fastforce)
     apply (clarsimp)
  apply (clarsimp)
       apply (sep_cancel)+
       apply (intro conjI)
        apply (clarsimp)
        apply (fastforce)
  apply (assumption)
  apply (fastforce)

  apply (sep_cancel)+
      apply (clarsimp simp: mapM_is_sequence_map)
  thm sequenceI_rewriting'
      apply (rule_tac P="\<lambda>_. sep_empty" and Q="\<lambda>_. sep_empty" and I="sep_empty" and S ="\<lambda>bs. ((\<lambda>s. sep_empty s \<and> length (local.var_list_inner vs) = length (var_list_inner bs)) \<and>*  balances \<mapsto>\<^sub>l bs) " and 
                      h="\<lambda>n bls. adjusted_balances bls  (flag_deltas vs bs pep f_c n)" and n="bls" and D="\<lambda>x bls bls'. safe_adjustments bls (flag_deltas vs bs pep f_c x)"  in  sequenceI_rewriting4)
       apply (clarsimp)
  apply (rule_tac x=n in exI) 
       apply (intro conjI)
         apply (clarsimp)
        apply (clarsimp)
  apply (clarsimp)
         apply (sep_solve)
        apply (clarsimp)
       apply (sep_cancel)+
     apply (rule_tac x="foldl (\<lambda>bls n. adjusted_balances bls (flag_deltas vs bs pep f_c n)) bls [0..<length PARTICIPATION_FLAG_WEIGHTS]" in exI)

     apply (intro conjI; clarsimp)
       apply (clarsimp simp: adjust_balance_pfw_def inactivity_penalties_rp_def)
     apply (clarsimp simp: foldl_conv_fold)
     apply (sep_cancel)+
       apply (clarsimp simp: adjust_balance_pfw_def inactivity_penalties_rp_def foldl_conv_fold)
     apply (sep_mp)
     apply (clarsimp)
    apply (fastforce)
  by (fastforce)

lemma test_ref_readI: 
  "\<tau> {x} ; f x \<le> \<tau> {x} ; g x \<Longrightarrow> \<tau> {x} ; f x \<le> (\<Squnion>x. \<tau> {x} ; g x)"
  by (meson SUP_upper UNIV_I order_trans)

lemma get_inactivity_score_ref: "get_inactivity_score index \<le> bindCont (mut ( inactivity_scores !? index)) read"
  apply (rule le_funI; clarsimp simp: get_inactivity_score_def bindCont_def read_beacon_def getState_def var_list_index_lens_def Sup_le_iff)
  apply (intro conjI impI; clarsimp simp: fail_def)
   apply (rule test_ref_readI; clarsimp simp: lens_oocomp_def fail_def return_def)
  apply (rule test_ref_readI; clarsimp simp: lens_oocomp_def fail_def return_def var_list_index_def)
  apply (intro conjI impI; clarsimp?)
    apply (rule seq_mono; fastforce)
   apply (clarsimp simp: test_restricts_Nondet)
   apply (clarsimp simp: return_def)
   apply (clarsimp simp: v_list_lens_def)
   apply (clarsimp split: if_splits)
   apply (unat_arith, clarsimp)
   apply (case_tac y; clarsimp)
   apply (clarsimp simp: v_list_lens_def)
   apply (clarsimp split: if_splits)
  by (unat_arith, clarsimp simp: unat_of_nat64')

lemma set_inactivity_score_ref: "set_inactivity_score index score \<le> bindCont (mut ( inactivity_scores !? index)) (\<lambda>i. write_to i score )"
  apply (rule le_funI; clarsimp simp: set_inactivity_score_def bindCont_def read_beacon_def var_list_update_def getState_def var_list_index_lens_def Sup_le_iff)
  apply (intro conjI impI; clarsimp simp: fail_def)
   apply (rule test_ref_readI; clarsimp simp: lens_oocomp_def fail_def return_def)
  apply (rule test_ref_readI; clarsimp simp: lens_oocomp_def fail_def return_def var_list_index_def)
  apply (intro conjI impI; clarsimp?)
    apply (rule seq_mono; fastforce)
   apply (clarsimp simp: test_restricts_Nondet)
   apply (clarsimp simp: return_def)
   apply (clarsimp simp: v_list_lens_def write_beacon_def getState_def bindCont_def test_restricts_Nondet)
   apply (case_tac y; clarsimp)
   apply (clarsimp simp: v_list_lens_def)
   apply (clarsimp split: if_splits)
  by (unat_arith, clarsimp simp: unat_of_nat64')



lemma get_inactivity_score_wp[wp]:
   "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>
      hoare_triple (lift (\<lambda>s. \<exists>v.  (lens_oocomp (v_list_lens index) inactivity_scores \<mapsto>\<^sub>l v \<and>* (lcomp (v_list_lens index) inactivity_scores \<mapsto>\<^sub>l v  \<longrightarrow>* P v)) s)) 
         (bindCont (get_inactivity_score index) next) Q"
  apply (rule refine_in_hoare[rotated], rule get_inactivity_score_ref)
  apply (rule hoare_weaken_pre)
   apply (simp add: var_list_index_lens_def)
  apply (simp add: bindCont_assoc[symmetric])
   apply (rule read_beacon_wp_ex)
  apply (rule read_beacon_wp_ex)
   apply (wp)
  apply (clarsimp)
  apply (intro exI, sep_cancel+)
  apply (intro exI, sep_cancel+)
  done

lemma set_inactivity_score_wp[wp]:
   "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>
      hoare_triple (lift (\<lambda>s. \<exists>v.  (lens_oocomp (v_list_lens index) inactivity_scores \<mapsto>\<^sub>l v \<and>* (lcomp (v_list_lens index) inactivity_scores \<mapsto>\<^sub>l score  \<longrightarrow>* P ())) s)) 
         (bindCont (set_inactivity_score index score) next) Q"
  apply (rule refine_in_hoare[rotated], rule set_inactivity_score_ref)
  apply (rule hoare_weaken_pre)
   apply (simp add: var_list_index_lens_def)
  apply (simp add: bindCont_assoc[symmetric])
   apply (rule read_beacon_wp_ex)
   apply (wp)
  apply (clarsimp)
  by (intro exI, sep_cancel+)


definition "activity_leak bs fc \<equiv> (MIN_EPOCHS_TO_INACTIVITY_PENALTY config < raw_epoch (previous_epoch (current_epoch bs)) - raw_epoch (Checkpoint.epoch_f fc))"

definition "update_inactivity_scores is vs pep bs fc index \<equiv> 
          (let f = (\<lambda>x. (if index \<in> unslashed_participating_indices TIMELY_TARGET_FLAG_INDEX (previous_epoch (current_epoch bs)) pep vs 
                            then x - min 1 x else x + INACTIVITY_SCORE_BIAS config)) in
            (if (\<not> activity_leak bs fc) then  f is - min (INACTIVITY_SCORE_RECOVERY_RATE config) (f is) else f is)) "


lemma notin_unslashed_participating_indices[simp]:
  "has_flag (unsafe_var_list_index pep x) TIMELY_TARGET_FLAG_INDEX \<longrightarrow> x \<in> list.set (active_validator_indices (previous_epoch (current_epoch bs)) vs) \<longrightarrow> slashed_f (unsafe_var_list_index vs x) \<Longrightarrow>
          x \<notin> unslashed_participating_indices TIMELY_TARGET_FLAG_INDEX (previous_epoch (current_epoch bs)) pep vs"
  by (clarsimp simp: unslashed_participating_indices_def)


definition "updated_inactivity_scores' vs bs pep fc is \<equiv> (VariableList (map (cond (eligible_index (previous_epoch (current_epoch bs)) (previous_epoch (current_epoch bs) + 1) vs)
               (\<lambda>x. update_inactivity_scores (is[x]!) vs pep bs fc (word_of_nat x)) (\<lambda>n. is[n]!)) ([0..<length(var_list_inner is)]) ))"

lemma "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> current_epoch bs \<noteq> GENESIS_EPOCH \<Longrightarrow>
      hoare_triple (lift (\<lambda>s. previous_epoch (current_epoch bs) \<le> previous_epoch (current_epoch bs) + 1 \<and> Checkpoint.epoch_f fc \<in> previous_epochs bs \<and> length (local.var_list_inner vs) < 2^64 \<and>
                       length (local.var_list_inner is) = length (local.var_list_inner vs) \<and>
                      ( \<forall>x\<in>list.set (eligible_validator_indices (previous_epoch (current_epoch bs)) (previous_epoch (current_epoch bs) + 1) vs). unsafe_var_list_index is x \<le> unsafe_var_list_index is x + INACTIVITY_SCORE_BIAS config) \<and>
                      
                       (validators \<mapsto>\<^sub>l vs \<and>* finalized_checkpoint \<mapsto>\<^sub>l fc \<and>* beacon_slots \<mapsto>\<^sub>l bs \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep  \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<and>* inactivity_scores \<mapsto>\<^sub>l is \<and>*                       
                       (validators \<mapsto>\<^sub>l vs \<and>* finalized_checkpoint \<mapsto>\<^sub>l fc \<and>* inactivity_scores \<mapsto>\<^sub>l  (updated_inactivity_scores' vs bs pep fc is) \<and>*  beacon_slots \<mapsto>\<^sub>l bs \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep  \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<longrightarrow>* P ())) s)) 
         (bindCont process_inactivity_updates next) Q"
  apply (rule hoare_weaken_pre)
  apply (clarsimp simp: process_inactivity_updates_def)
   apply (wp)
    apply (clarsimp)
    apply (fastforce)
   apply (wp)
      apply (clarsimp)
      apply (fastforce)
     apply (wp)
      apply (fastforce)
    apply (simp)
  apply (fastforce)
  apply (clarsimp)
  apply (sep_cancel)+

      apply (clarsimp simp: mapM_is_sequence_map)
  thm sequenceI_rewriting'
  apply (rule_tac P="\<lambda>x. lens_oocomp (v_list_lens x) inactivity_scores \<mapsto>\<^sub>l (unsafe_var_list_index is x)" and
        Q="\<lambda>x. lens_oocomp (v_list_lens x) inactivity_scores \<mapsto>\<^sub>l update_inactivity_scores (unsafe_var_list_index is x) vs pep bs fc x" and 
         I="finalized_checkpoint \<mapsto>\<^sub>l fc \<and>* validators \<mapsto>\<^sub>l vs \<and>* beacon_slots \<mapsto>\<^sub>l bs \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep \<and>* current_epoch_participation \<mapsto>\<^sub>l cep" and
             S ="\<lambda>bs. sep_empty " and 
                      h="\<lambda>n bls. undefined" and n="undefined" and D="\<lambda>x bls bls'. True"  in  sequenceI_rewriting4)
    apply (clarsimp)
    apply (intro conjI impI)
     apply (sep_cancel)+
     apply (intro exI conjI impI)
      apply (sep_cancel)+
      apply (rule exI, sep_cancel+)
      apply (intro conjI impI; clarsimp)
        apply (rule exI, sep_cancel+)
      apply (rule exI, sep_cancel+)
      apply (clarsimp simp: update_inactivity_scores_def activity_leak_def unslashed_participating_indices_def)
      apply (sep_mp)
      apply (assumption)
     apply (sep_cancel)+
        apply (rule exI, sep_cancel+)
     apply (intro conjI impI; clarsimp)

     apply (clarsimp simp: update_inactivity_scores_def activity_leak_def unslashed_participating_indices_def)
  apply (clarsimp simp: sep_conj_ac)
      apply (sep_mp, assumption)
    apply (sep_cancel)+
    apply (intro conjI exI impI)
     apply (sep_cancel)+
     apply (intro conjI impI)
      defer
        apply (rule exI, sep_cancel+)
      apply (intro conjI impI; clarsimp)
        apply (rule exI, sep_cancel+)
        apply (rule exI, sep_cancel+)
      apply (clarsimp simp: update_inactivity_scores_def activity_leak_def sep_conj_ac)
      apply (sep_mp, assumption)
     apply (sep_cancel)+

     apply (intro conjI impI)
      defer

      apply (rule exI, sep_cancel+)

    apply (intro conjI exI impI)
       apply (sep_cancel)+
      apply (clarsimp simp: update_inactivity_scores_def activity_leak_def sep_conj_ac)
      apply (sep_mp, assumption)
     apply (clarsimp)
     apply (sep_cancel)+
  thm restore_variablelist
  apply (clarsimp simp: split_foldr_map_sep_conj split_foldr_map_conj restore_variablelist local.foldr_pure_empty)
  apply (sep_drule is_split)
  apply (clarsimp)
  apply (subst (asm) restore_variablelist[symmetric]) 
apply (subst (asm) foldr_conj_filter_split[where P="\<lambda>n. is_active_validator (vs[n]!) (previous_epoch (current_epoch bs)) \<or>
         (slashed_f (vs[n]!) \<and> (previous_epoch (current_epoch bs) + 1) < withdrawable_epoch_f (vs[n]!))"])
     apply (clarsimp simp: sep_conj_ac eligible_validator_indices_eq)
  apply (sep_cancel+)
     apply (subst (asm) eligible_validator_indices_eq[symmetric], clarsimp)
     apply (clarsimp simp: sep_conj_ac) 
  apply (sep_select_asm 8)
       apply (sep_drule foldr_map_split_mergeD)
     apply ( subst (asm) merge_if_map)
     apply (clarsimp simp: split_foldr_map_sep_conj split_foldr_map_conj restore_variablelist local.foldr_pure_empty)
  apply (clarsimp simp: updated_inactivity_scores'_def cond_def eligible_index_def index_var_list_def)
     apply (sep_mp, assumption)
    apply (fastforce)
  apply (fastforce)
  by (fastforce)
                     





lemma var_list_update_wp[wp]:
   "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> 
       hoare_triple (lift (\<lambda>s. unat index < length (var_list_inner ls) \<and> length (var_list_inner ls) < 2^64 \<and> (length (var_list_inner ls) < 2^64 \<and> unat index < length (var_list_inner ls) \<longrightarrow> P (VariableList (list_update (var_list_inner ls) (unat index) val)) s)  ))
          (bindCont (var_list_update val ls index) next) Q"
  apply (rule hoare_weaken_pre)
   apply (subst var_list_update_def)
   apply (wp)
    apply (clarsimp)
    apply (fastforce)
   apply (wp)
  apply (clarsimp)
  apply (intro conjI impI; clarsimp)
   apply (unat_arith, clarsimp simp: unat_of_nat64')
   apply (case_tac ls; clarsimp)
  by (unat_arith, clarsimp simp: unat_of_nat64')


                                                                                                
lemma update_is_mut_ref: "update_validator v' index \<le> (do {v <- mut (var_list_index_lens validators index);  write_to v v'})"
  apply (rule le_funI, clarsimp simp: update_validator_def bindCont_def read_beacon_def var_list_index_lens_def var_list_update_def getState_def Sup_le_iff)
  apply (safe; clarsimp simp: fail_def return_def)
   apply (rule test_ref_readI, clarsimp)
   apply (intro conjI impI)
    apply (simp add: fail_def)
   apply (clarsimp)
   apply (clarsimp simp: lens_oocomp_def)
  apply (safe; clarsimp?)
   apply (rule test_ref_readI, clarsimp)
   apply (safe; clarsimp?)
    apply (clarsimp simp: lens_oocomp_def v_list_lens_def)
    apply (clarsimp split: if_splits)
    apply (clarsimp simp: fail_def)
  using seq_mono_right top_greatest apply blast
   apply (clarsimp simp: return_def)
   apply (clarsimp simp: write_beacon_def getState_def setState_def bindCont_def lens_oocomp_def v_list_lens_def)
   apply (clarsimp simp: test_restricts_Nondet setState_def pgm_test_pre seq.assoc[symmetric])
  apply (rule test_ref_readI, clarsimp)
   apply (safe; clarsimp?)
    apply (clarsimp simp: lens_oocomp_def v_list_lens_def fail_def)
      apply (clarsimp simp: lens_oocomp_def v_list_lens_def fail_def)
  apply (clarsimp split: if_splits)
  apply (erule notE)
  apply (case_tac y; clarsimp)
  apply (unat_arith, clarsimp)
  by (clarsimp simp: unat_of_nat64')


  
                                                                                             
lemma update_validator_wp[wp]: 
   "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>
      hoare_triple (lift (\<lambda>s. \<exists>v. (lens_oocomp (v_list_lens index) validators \<mapsto>\<^sub>l v \<and>* (lens_oocomp (v_list_lens index) validators \<mapsto>\<^sub>l v' \<longrightarrow>* P ())) s))
        (bindCont (update_validator v' index) next) Q"  
  apply (rule hoare_assert_state_liftI, clarsimp)
  apply (drule lift_exD, clarsimp)
  apply (rule refine_in_hoare[rotated], rule update_is_mut_ref)
  apply (rule hoare_weaken_pre)
   apply (wp)
  apply (unfold lift_def, clarsimp)
  apply (rule_tac x=S in exI, clarsimp)
  by (rule_tac x=v in exI, sep_solve)


lemma get_current_epoch_wp_ex[wp]: "(\<And>x. hoare_triple (lift (P x)) (f x) Q) \<Longrightarrow>
hoare_triple (lift (EXS v. (maps_to beacon_slots v \<and>* (maps_to beacon_slots v \<longrightarrow>* P (slot_to_epoch config v))))) (bindCont get_current_epoch f) Q" 
  apply (rule hoare_assert_state_liftI, clarsimp)
  apply (drule lift_exD, clarsimp)

  apply (rule hoare_weaken_pre, rule get_current_epoch_wp', assumption)
  apply (unfold lift_def, clarsimp)
  apply (rule_tac x=S in exI, clarsimp)
  by (sep_cancel)
 

lemma hoare_case_prod':
  "(\<And>a b. hoare_triple (P a b ) (f a b ) Q) \<Longrightarrow>
   hoare_triple (P (fst p) (snd p)) (case p of
                         (a, b) \<Rightarrow> f a b ) Q"
  by (clarsimp split: prod.splits)





definition "churn_limit bs vs \<equiv> max (MIN_PER_EPOCH_CHURN_LIMIT config) (word_of_nat (length (active_validator_indices (current_epoch bs) vs)) div CHURN_LIMIT_QUOTIENT config)"


definition "exit_queue_epoch vs bs= maximum (current_epoch bs + 1 +  MAX_SEED_LOOKAHEAD) (map exit_epoch_f (filter (\<lambda>v. exit_epoch_f v \<noteq> FAR_FUTURE_EPOCH) (local.var_list_inner vs)))"

definition "next_exit_epoch vs bs \<equiv> if length (filter (\<lambda>v. exit_epoch_f v = exit_queue_epoch vs bs) (var_list_inner vs)) < unat (churn_limit bs vs) then exit_queue_epoch vs bs  else exit_queue_epoch vs bs + 1"

definition "exit_validator bs index vs \<equiv> 
        if exit_epoch_f (local.var_list_inner vs ! unat index) = FAR_FUTURE_EPOCH 
        then 
          VariableList
           ((local.var_list_inner vs)
            [unat index := (local.var_list_inner vs ! unat index)
             \<lparr>exit_epoch_f := next_exit_epoch vs bs,
              withdrawable_epoch_f := next_exit_epoch vs bs + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config)\<rparr>])
        else 
           vs"

lemma less_unatI: "word_of_nat x < (y :: u64) \<Longrightarrow> x < 2^64 \<Longrightarrow> x < unat y"
  by (unat_arith, clarsimp simp: unat_of_nat64')

lemma rewrite_churn_helper: "length (local.var_list_inner vs) < 18446744073709551616 \<Longrightarrow>
        word_of_nat (length (filter (\<lambda>v. exit_epoch_f v = maximum (Epoch (epoch_to_u64 (current_epoch bs) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD)) (map exit_epoch_f (filter (\<lambda>v. exit_epoch_f v \<noteq> FAR_FUTURE_EPOCH) (local.var_list_inner vs)))) (local.var_list_inner vs))) < max (MIN_PER_EPOCH_CHURN_LIMIT config) (word_of_nat (length (active_validator_indices (current_epoch bs) vs)) div CHURN_LIMIT_QUOTIENT config) \<Longrightarrow>
         length (filter (\<lambda>v. exit_epoch_f v = maximum (Epoch (epoch_to_u64 (current_epoch bs) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD)) (map exit_epoch_f (filter (\<lambda>v. exit_epoch_f v \<noteq> FAR_FUTURE_EPOCH) (local.var_list_inner vs)))) (local.var_list_inner vs)) < unat (max (MIN_PER_EPOCH_CHURN_LIMIT config) (word_of_nat (length (active_validator_indices (current_epoch bs) vs)) div CHURN_LIMIT_QUOTIENT config))"  
  apply (drule less_unatI)
  apply (clarsimp)
   apply (rule le_less_trans, rule length_filter_le, assumption)
  by (assumption)

lemma initiate_validator_exit_wp: 
   "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>
          \<lblot>\<lless>\<lambda>s. (current_epoch bs) \<le>  (current_epoch bs) + 1 \<and>  unat index < length (local.var_list_inner vs) \<and> length (local.var_list_inner vs) < 2^64 \<and>
             (current_epoch bs) + 1 \<le>  (current_epoch bs) + 1 +  MAX_SEED_LOOKAHEAD \<and>  
           exit_queue_epoch vs bs \<le> next_exit_epoch vs bs \<and>
              next_exit_epoch vs bs
          \<le> next_exit_epoch vs bs + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) \<and>
            
           ( validators \<mapsto>\<^sub>l vs \<and>* beacon_slots \<mapsto>\<^sub>l bs \<and>*
             ( validators \<mapsto>\<^sub>l exit_validator bs index vs \<and>* beacon_slots \<mapsto>\<^sub>l bs  \<longrightarrow>* P ()))
            s\<then>\<rblot>  bindCont (initiate_validator_exit index) next \<lblot>Q\<rblot>"
  apply (unfold initiate_validator_exit_def)
  apply (rule hoare_weaken_pre)
  apply (simp only: bindCont_assoc[symmetric])
   apply (rule read_beacon_wp_ex)

   apply (rule var_list_inner_wp)
   apply (rule if_wp)
    apply (rule hoare_let)
  apply (simp only: bindCont_assoc[symmetric])
    apply (rule get_current_epoch_wp_ex)
    apply (rule compute_activation_exit_epoch)
    apply (rule hoare_let)
    apply (rule hoare_let)

    apply (simp only: bindCont_assoc[symmetric])
    apply (rule get_validator_churn_limit_spec')
   apply (rule if_wp)
     apply (wp)
    apply (subst epoch_unsigned_add_def)
    apply (simp only: bindCont_assoc[symmetric])
    apply (wp)
   apply (fastforce)
  apply (clarsimp)
  apply (rule exI)
  apply (intro conjI impI)
   apply (sep_cancel)+
   apply (intro conjI impI; clarsimp)
   apply (rule exI)
   apply (intro conjI impI)
    apply (sep_cancel)+
    apply (intro conjI impI; clarsimp)
apply (drule less_unatI)
  apply (clarsimp)
      apply (rule le_less_trans, rule length_filter_le, assumption)
  apply (clarsimp simp: plus_Epoch_def one_Epoch_def less_eq_Epoch_def)
    apply (sep_cancel)+
    apply (clarsimp simp: exit_validator_def next_exit_epoch_def exit_queue_epoch_def Let_unfold plus_Epoch_def one_Epoch_def churn_limit_def)
    apply (clarsimp split: if_splits)
    apply (intro conjI impI; (clarsimp simp: epoch_simp)?)
    apply (clarsimp simp: exit_validator_def less_eq_Epoch_def next_exit_epoch_def exit_queue_epoch_def Let_unfold plus_Epoch_def one_Epoch_def churn_limit_def)
     apply (sep_cancel)+
    apply (clarsimp simp: exit_validator_def less_eq_Epoch_def next_exit_epoch_def exit_queue_epoch_def Let_unfold plus_Epoch_def one_Epoch_def churn_limit_def)

     apply (sep_mp, assumption)
  apply (clarsimp simp: rewrite_churn_helper)
   apply (sep_cancel)+
   apply (intro conjI impI; clarsimp)
    apply (clarsimp simp: next_exit_epoch_def exit_queue_epoch_def plus_Epoch_def one_Epoch_def churn_limit_def split: if_splits)
   apply (sep_cancel)+
  apply (intro conjI impI; clarsimp simp: exit_validator_def less_eq_Epoch_def next_exit_epoch_def exit_queue_epoch_def Let_unfold plus_Epoch_def one_Epoch_def churn_limit_def split: if_splits)
  apply (erule notE)
  using word_of_nat_less apply blast
  apply (erule notE)
  using word_of_nat_less apply blast
    apply (sep_cancel)+
    apply (sep_mp)
    apply (clarsimp simp: epoch_simp)
  using word_of_nat_less apply blast
  apply (sep_cancel)+

    apply (clarsimp simp: exit_validator_def next_exit_epoch_def exit_queue_epoch_def Let_unfold plus_Epoch_def one_Epoch_def churn_limit_def)
  apply (sep_mp, assumption)
  apply (sep_cancel)+
  apply (clarsimp)
  apply (clarsimp simp: exit_validator_def)
  by (sep_solve)

lemma hoare_triple_lift_ex_allI: "\<forall>x. hoare_triple (lift (f x)) c Q \<Longrightarrow> hoare_triple (lift (EXS x. f x)) c Q"
 apply (rule hoare_assert_state_liftI, clarsimp)
  apply (drule lift_exD, clarsimp)
  apply (rule hoare_weaken_pre, fastforce)
  apply (unfold lift_def, clarsimp)
  apply (rule_tac x=S in exI, clarsimp)
  by (fastforce)


lemma initiate_validator_exit_wp_ex[wp]: 
   "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>
          \<lblot>\<lless>\<lambda>s. \<exists>bs vs.  (current_epoch bs) \<le>  (current_epoch bs) + 1 \<and>  unat index < length (local.var_list_inner vs) \<and> length (local.var_list_inner vs) < 2^64 \<and>
             (current_epoch bs) + 1 \<le>  (current_epoch bs) + 1 +  MAX_SEED_LOOKAHEAD \<and>  
           exit_queue_epoch vs bs \<le> next_exit_epoch vs bs \<and>
              next_exit_epoch vs bs
          \<le> next_exit_epoch vs bs + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config) \<and>
            
           ( validators \<mapsto>\<^sub>l vs \<and>* beacon_slots \<mapsto>\<^sub>l bs \<and>*
             ( validators \<mapsto>\<^sub>l exit_validator bs index vs \<and>* beacon_slots \<mapsto>\<^sub>l bs  \<longrightarrow>* P ())) s\<then>\<rblot>  
              bindCont (initiate_validator_exit index) next \<lblot>Q\<rblot>"
  apply (intro hoare_triple_lift_ex_allI allI)
  by (erule initiate_validator_exit_wp)

lemma filterM_is_mapM_concat: "filterM B xs = (do {xss <-(mapM (\<lambda>x. do {b <- B x; if b then return [x] else return []} ) xs);  return (concat xss)})" 
  apply (induct xs; clarsimp)
  apply (clarsimp simp: bindCont_assoc[symmetric])
  apply (rule bindCont_right_eqI)
  by (clarsimp split: if_splits)


lemma filterM_wp: assumes B_wp: "\<And>(f :: bool \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'a) x P Q. (\<And>x. hoare_triple (lift (P x)) (f x) (Q)) \<Longrightarrow> 
                                                    hoare_triple (lift ( (pre x) P)) (do { b <- B x; f b}) Q"
  shows"(\<And>x. hoare_triple (lift (P x)) (f x) Q) \<Longrightarrow>
        hoare_triple (\<lless>mapM (\<lambda>a b. pre a (\<lambda>c. if c then b [a] else b [])) xs (\<lambda>x. P (concat x))\<then>) (bindCont (filterM B xs) (f ::  bool list \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> 'a)) Q"
  apply (subst filterM_is_mapM_concat)
  apply (rule hoare_weaken_pre)
  apply (subst bindCont_assoc[symmetric])
   apply (rule mapM_fake)
  apply (subst bindCont_assoc[symmetric])
    apply (rule B_wp)
    apply (rule if_wp)
     apply (fastforce)
  apply (fastforce)
   apply (fastforce)
  apply (fastforce)
  done

fun pairs_list :: "'f list \<Rightarrow> ('f \<times> 'f) list" where
pairs_list_Nil:  "pairs_list [] = []" |
pairs_list_Single: "pairs_list [x] = []" |  
pairs_list_Pair: "pairs_list (x#y#xs) = (x,y) # pairs_list (y#xs) "   


lemma fold_conj_false_false[simp]: "fold (\<and>) xs False = False"
  by (induct xs; clarsimp)

lemma sortedByM_is_mapM_pairs: "sortedByM B xs = do { bs <- mapM (\<lambda>x. B (fst x) (snd x)) (pairs_list xs); return (fold (\<and>) bs True)}"
  apply (induct xs; clarsimp?)
  apply (case_tac xs; clarsimp)
  apply (clarsimp simp: bindCont_assoc[symmetric])
  apply (rule bindCont_right_eqI)
  apply (clarsimp)
  by (case_tac x; clarsimp)

lemma select_wp'[wp]: "(\<And>x. hoare_triple (lift (pre x)) (f x) Q) \<Longrightarrow> hoare_triple (lift (\<lambda>s. \<forall>x\<in>P. pre x s)) (do {x <- select P; f x}) Q"
  apply (clarsimp simp: select_def bindCont_def hoare_triple_def run_def)
  apply (subst Sup_le_iff)
  apply (clarsimp)
  apply (rule order_trans, assumption)
  apply (rule seq_mono_left)
  apply (subst assert_iso[symmetric])
  by (fastforce)

lemma todo_wp[wp]:" hoare_triple (lift \<top>) (bindCont todo f) Q"
  by (clarsimp simp: hoare_triple_def bindCont_def todo_def run_def)

lemma fold_true_iff: "fold (\<and>) xs True \<longleftrightarrow> (\<forall>b\<in>(list.set xs). b)"
  apply (induct xs; clarsimp)
  apply (safe; clarsimp?)
     apply (case_tac a; clarsimp)
  apply (case_tac a; clarsimp)
  apply (case_tac a; clarsimp)
  by fastforce

lemma rewrite_sorted: "(\<lambda>xa. if fold (\<and>) xa True then P xa else \<top>) = (\<lambda>x s. (\<forall>b\<in>(list.set x). b) \<longrightarrow> P x s)"
  apply (intro ext; clarsimp simp: fold_true_iff)
  apply (intro conjI impI)
   apply (blast)
  apply (blast)
  done

lemma sortBy_wp: assumes B_wp: "\<And>(f :: bool \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> 'a) x y P Q. (\<And>x. hoare_triple (lift (P x)) (f x) (Q)) \<Longrightarrow> 
                                                    hoare_triple (lift ( (pre x y) P)) (do { b <- B x y; f b}) Q"
  shows"(\<And>x. hoare_triple (lift (P x)) (f x) Q) \<Longrightarrow>
        hoare_triple (\<lless>\<lambda>s. \<forall>x\<in>{ys. list.set ys = list.set xs \<and> length ys = length xs}. mapM (\<lambda>x. pre (fst x) (snd x)) (pairs_list x) (\<lambda>xa s. (\<forall>b\<in>list.set xa. b) \<longrightarrow> P x s) s\<then>) 
   (bindCont (sortBy B xs) (f :: 'c list \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> 'a)) Q"
  apply (simp add: sortBy_def)
  apply (subst sortedByM_is_mapM_pairs)
  apply (rule hoare_weaken_pre)
   apply (subst bindCont_assoc[symmetric])+
  apply (rule select_wp')
   apply (rule mapM_fake)
    apply (rule B_wp)
    apply (fastforce)
   apply (wp)
    apply (fastforce)
  apply (wp)
  apply (simp only: rewrite_sorted)
  apply (fastforce)
  done

definition "eligible_for_activation v fc \<equiv> activation_eligibility_epoch_f v \<le> Checkpoint.epoch_f fc \<and> activation_epoch_f v = FAR_FUTURE_EPOCH"

lemma is_eligible_for_activation_wp[wp]:
  "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>
         hoare_triple (\<lless>\<lambda>s. \<exists>x. (finalized_checkpoint \<mapsto>\<^sub>l x \<and>* (finalized_checkpoint \<mapsto>\<^sub>l x \<longrightarrow>*
                           P (eligible_for_activation v x))) s\<then>) (bindCont (is_eligible_for_activation v) next) Q"
  apply (clarsimp simp: is_eligible_for_activation_def)
  apply (rule hoare_weaken_pre)
  apply (simp add: bindCont_assoc[symmetric])
   apply (rule read_beacon_wp_ex)
   apply (fastforce)
  by (fastforce simp: eligible_for_activation_def)

lemma "i < length xs \<Longrightarrow> xs[i := v] = take i xs @ [v] @ drop (i + 1) xs"
  by (simp add: upd_conv_take_nth_drop)


lemma concat_map_if_is_filter: "concat (map (\<lambda>x. if P x then [x] else []) xs) = filter P xs"
  by (induct xs; clarsimp)


lemma in_set_pairs_list_iff: "(a, b) \<in> list.set (pairs_list xs) \<longleftrightarrow> (\<exists>n. n + 1 < length xs \<and> xs ! n = a \<and> xs ! (n + 1) = b)"
  apply (intro iffI; clarsimp?)
  apply (induct xs arbitrary: a b; clarsimp)
   apply (case_tac xs; clarsimp)
   apply (elim disjE; clarsimp?)
    apply (rule_tac x=0 in exI, clarsimp)
   apply (drule meta_spec, drule meta_spec, drule meta_mp, fastforce)
   apply (clarsimp)
  apply (rule_tac x="n + 1" in exI, clarsimp)
    apply (induct xs arbitrary: a b; clarsimp)
  apply (case_tac xs; clarsimp)
  using less_Suc_eq_0_disj by fastforce


lemma pairs_list_sorted_wrt_simp: 
      "transp f \<Longrightarrow> 
       (\<forall>x\<in>list.set (pairs_list xs). case x of (n, n') \<Rightarrow>
                                     f n n') =
        sorted_wrt (\<lambda>n n'. f n n') xs"
  apply (intro iffI; clarsimp?)
  apply (induct xs; clarsimp simp: Ball_def in_set_pairs_list_iff)
   apply (intro iffI allI conjI impI; clarsimp?)
    apply (drule meta_mp)
     apply (clarsimp)
     apply (metis nth_Cons_Suc)
    apply (metis (mono_tags, lifting) in_set_conv_nth length_pos_if_in_set not_gr0 nth_Cons_0 sorted_wrt_nth_less transpE)
  apply (drule meta_mp)
     apply (clarsimp)
    apply (metis nth_Cons_Suc)
   apply (assumption)
  apply (clarsimp simp: in_set_pairs_list_iff)
  using sorted_wrt_iff_nth_Suc_transp by blast
  

lemma transpI_activation_eligibility_leprod:
        "transp (\<lambda>n n'. activation_eligibility_epoch_f (local.var_list_inner vs ! unat n) \<le> activation_eligibility_epoch_f (local.var_list_inner vs ! unat n') \<and>
                     (activation_eligibility_epoch_f (local.var_list_inner vs ! unat n') \<le> activation_eligibility_epoch_f (local.var_list_inner vs ! unat n) \<longrightarrow> n \<le> n'))"
  apply (intro transpI)
  by force

definition "sorted_by_activation_order vs aq \<equiv> {xs. list.set xs = list.set aq \<and> length xs = length aq \<and>
          sorted_wrt (\<lambda>n n'. lex_ord ((activation_eligibility_epoch_f (local.var_list_inner vs ! unat n)), n) ((activation_eligibility_epoch_f (local.var_list_inner vs ! unat n')), n')) xs}"

lemma sortBy_activation_eligibility_wp:
"(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> 
  hoare_triple (lift (\<lambda>s. list.set aq \<subseteq> word_of_nat `{0..<length (var_list_inner vs)} \<and> length (var_list_inner vs) < 2^64 \<and>
                         (validators \<mapsto>\<^sub>l vs \<and>* (validators \<mapsto>\<^sub>l vs \<longrightarrow>* (\<lambda>s. \<forall>xs\<in>sorted_by_activation_order vs aq. P xs s))) s)) 
 (do { activation_queue \<leftarrow> sortBy (\<lambda>index index'. do {
                                vals \<leftarrow> read validators;
                                val  \<leftarrow> var_list_index vals index;
                                val' \<leftarrow> var_list_index vals index';
                                let epoch  = activation_eligibility_epoch_f val;
                                let epoch' = activation_eligibility_epoch_f val';   
                                return (lex_ord ( epoch, index)  ( epoch', index'))}) aq; next activation_queue}) Q"
  apply (clarsimp simp: Let_unfold bindCont_assoc[symmetric])
  apply (rule hoare_weaken_pre)
   apply (rule sortBy_wp)
    apply (simp only: bindCont_assoc[symmetric])
   apply (rule read_beacon_wp_ex)
    apply (rule var_list_inner_wp)

    apply (rule var_list_inner_wp)
    apply (fastforce)
    apply (fastforce)
  apply (clarsimp)
  apply (clarsimp simp: mapM_is_sequence_map)
  apply (rule_tac P="\<lambda>x. sep_empty" and
        Q="\<lambda>x. sep_empty" and 
         I=" validators \<mapsto>\<^sub>l vs" and
             S ="\<lambda>bs. sep_empty " and g = "\<lambda>(n, n'). lex_ord ((activation_eligibility_epoch_f (local.var_list_inner vs ! unat n)), n) ((activation_eligibility_epoch_f (local.var_list_inner vs ! unat n')), n')"  and
                      h="\<lambda>n bls. undefined" and n="undefined" and D="\<lambda>x bls bls'. True"  in  sequenceI_rewriting4)
    apply (clarsimp)
  apply (rule_tac x=vs in exI)
    apply (sep_cancel)+
    apply (intro conjI impI)
       prefer 4
  apply (sep_mp, assumption)
      apply (clarsimp simp: in_set_pairs_list_iff)
      apply (drule_tac c="xa ! n" in subsetD)
  apply (metis Suc_lessD nth_mem)
      apply (clarsimp simp: image_iff unat_of_nat64')
     apply (assumption)
      apply (clarsimp simp: in_set_pairs_list_iff)
    apply (drule_tac c="xa ! Suc n" in subsetD)
  apply (metis Suc_lessD nth_mem)

      apply (clarsimp simp: image_iff unat_of_nat64')
  apply (clarsimp)
  apply (subst pairs_list_sorted_wrt_simp)
    apply (rule transpI_activation_eligibility_leprod)
   apply (sep_cancel)+
   apply (intro impI)
  apply (sep_mp)
   apply (erule_tac x=xa in ballE; clarsimp?)
   apply (clarsimp simp: sorted_by_activation_order_def)
  by (fastforce)

lemma filter_eligible_wp: "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow>
        hoare_triple (lift (finalized_checkpoint \<mapsto>\<^sub>l f_c \<and>* validators \<mapsto>\<^sub>l vs \<and>* 
       (finalized_checkpoint \<mapsto>\<^sub>l f_c \<and>* validators \<mapsto>\<^sub>l vs \<longrightarrow>*  P (filter (\<lambda>ab. eligible_for_activation (snd ab) f_c) (local.enumerate (local.var_list_inner vs))))))
            (do {potential_activation_queue \<leftarrow> filterM (\<lambda>(index,val). is_eligible_for_activation val) 
                                           (enumerate (var_list_inner vs));
                                         next potential_activation_queue}) Q"

   apply (subst filterM_is_mapM_concat)
  apply (simp only: bindCont_assoc[symmetric])
  apply (rule hoare_weaken_pre)
   apply (rule mapM_fake)
  apply (simp only: bindCont_assoc[symmetric])

    apply (rule hoare_case_prod)
    apply (rule is_eligible_for_activation_wp)
    apply (rule if_wp; fastforce)
   apply (fastforce)
apply (clarsimp simp: mapM_is_sequence_map)
  apply (rule_tac P="\<lambda>x. sep_empty" and
        Q="\<lambda>x. sep_empty" and 
         I="finalized_checkpoint \<mapsto>\<^sub>l f_c \<and>* validators \<mapsto>\<^sub>l vs" and
             S ="\<lambda>bs. sep_empty " and g = "\<lambda>ab. if eligible_for_activation (snd ab) f_c then [ab] else []"  and
                      h="\<lambda>n bls. undefined" and n="undefined" and D="\<lambda>x bls bls'. True"  in  sequenceI_rewriting4)
    apply (clarsimp)
    apply (clarsimp split: if_splits)
     apply (rule_tac x="f_c" in exI, clarsimp)
     apply (sep_cancel)+
     apply (sep_mp, assumption)

     apply (rule_tac x="f_c" in exI, clarsimp)
     apply (sep_cancel)+
    apply (sep_mp, assumption)
   apply (clarsimp)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (subst concat_map_if_is_filter)
  apply (assumption)
  by (fastforce)

lemma sortBy_cong: "(f = g) \<Longrightarrow> (bindCont (sortBy f xs) next) = 
                                (bindCont (sortBy g xs) next)" by fastforce

lemma [simp]: "length (local.var_list_inner (exit_validator b e xs)) = length (var_list_inner xs)"
  by (clarsimp simp: exit_validator_def)

lemma le_var_list_lenD: "a < var_list_len vs \<Longrightarrow> length (local.var_list_inner vs) < 2^64 \<Longrightarrow>
                         unat a < length (local.var_list_inner vs)" 
  apply (case_tac vs; clarsimp)
  using unat_less_helper by blast

definition "activate_if_eligible p bs vs \<equiv> if is_eligible_for_activation_queue (snd p) then
                                               (VariableList ((local.var_list_inner vs)[unat (fst p) := (snd p)\<lparr>activation_eligibility_epoch_f := Epoch (epoch_to_u64 (current_epoch bs) + 1)\<rparr>])) 
                                            else vs"


definition "eject_active_validator bs vs n \<equiv> let activated_validator = (if is_eligible_for_activation_queue (snd n)
                                                                             then
                                                                                 ((snd n)\<lparr>activation_eligibility_epoch_f := Epoch (epoch_to_u64 (current_epoch bs) + 1)\<rparr>)
                                                                             else (snd n))
                                              in 
                                                 if (is_active_validator activated_validator (current_epoch bs) \<and>
                                                       Validator.effective_balance_f activated_validator \<le> EJECTION_BALANCE config)
                                                   then exit_validator bs (fst n) (activate_if_eligible n bs vs)
                                                   else (activate_if_eligible n bs vs)"


lemma [simp]: "is_eligible_for_activation_queue (snd p) \<Longrightarrow> activate_if_eligible p bs vs = (VariableList ((local.var_list_inner vs)[unat (fst p) := (snd p)\<lparr>activation_eligibility_epoch_f := Epoch (epoch_to_u64 (current_epoch bs) + 1)\<rparr>]))"
  by (clarsimp simp: activate_if_eligible_def)

lemma [simp]:  "\<not>is_eligible_for_activation_queue (snd p) \<Longrightarrow> activate_if_eligible p bs vs = vs"
  by (clarsimp simp: activate_if_eligible_def)

lemma var_list_update_idemp: "unsafe_var_list_index n a = b \<Longrightarrow> VariableList ((local.var_list_inner n)[unat a := b]) = n" 
  by (case_tac n, clarsimp simp: unsafe_var_list_index_def)

definition "eject_all_validators bs vs \<equiv> fold (\<lambda>n vs. eject_active_validator bs vs n) (local.enumerate (local.var_list_inner vs)) vs"

find_theorems "[?n..<?m] = ?n # _"

lemma uptD: "[0..<n] = z # zs \<Longrightarrow> 0 = z \<and> [1..<n] = zs"
  apply (case_tac "n = 0", clarsimp)
  apply (subst (asm) upt_conv_Cons, clarsimp)
  by (clarsimp)


lemma zip_tail_split: "length xs = length ys \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> zip xs ys = (zip (butlast xs) (butlast ys)) @ [(last xs, last ys)]"
  apply (induct rule:list_induct2; clarsimp)
  by (safe; clarsimp)

lemma length_eject_active_validator[simp]: "length (var_list_inner (eject_active_validator bs vs n)) = length (var_list_inner vs)" 
  by (clarsimp simp: eject_active_validator_def Let_unfold)

lemma butlast_map_map: "butlast (map f xs) = map f (butlast xs)"
  by (induct xs; clarsimp)

lemma butlast_upt: "(butlast [0..<n]) = [0..<n - 1]"
  by (induct n; clarsimp)


lemma length_ejecting_eq': "length (local.var_list_inner (fold (\<lambda>n vs. eject_active_validator bs vs n) (local.enumerate (local.var_list_inner vs)) ys)) = length (var_list_inner ys)"
  apply (induct \<open>(local.var_list_inner vs)\<close>  arbitrary: vs ys rule: rev_induct, clarsimp)
   apply (clarsimp simp: enumerate_def)
 apply (clarsimp simp: enumerate_def)
  apply (subst zip_tail_split; clarsimp?)
  apply (clarsimp simp: butlast_map_map)
  apply (drule_tac x="VariableList (butlast (var_list_inner vs))" in meta_spec)
  apply (drule_tac x="ys" in meta_spec)

  apply (drule meta_mp)
   apply (clarsimp)
   apply (metis butlast_snoc)
  by (clarsimp simp: butlast_upt)


lemma length_ejecting_eq: "length (local.var_list_inner (fold (\<lambda>n vs. eject_active_validator bs vs n) (local.enumerate (local.var_list_inner vs)) vs)) = 
       length (var_list_inner vs)"
  by (rule length_ejecting_eq') 
  
lemma [simp]: "enumerate [] = []" by (clarsimp simp: enumerate_def)

lemma "xs \<noteq> [] \<Longrightarrow>(map word_of_nat [0..<length xs]) @ [word_of_nat (length xs)] = 0#(map word_of_nat [1..<length xs]) @ [word_of_nat (length xs)]"
  apply (clarsimp)
  by (simp add: upt_rec)

lemma length_enuemrate_simp[simp]: "length (enumerate xs) = length xs"
  by (clarsimp simp: enumerate_def)

lemma enumerate_nth: "n < length xs \<Longrightarrow> length xs < 2^64 \<Longrightarrow>  enumerate xs ! n = (word_of_nat n, xs ! n)"
  by (clarsimp simp: enumerate_def)

lemma enumerate_simp [simp]: "xs \<noteq> [] \<Longrightarrow> length xs < 2 ^ 64 \<Longrightarrow> enumerate (xs) = (0,hd xs)# (zip (map word_of_nat [1..<length xs]) (tl xs))" 
  apply (rule nth_equalityI, clarsimp)
  apply (clarsimp)
  apply (subst enumerate_nth; clarsimp?)
    apply (case_tac i; clarsimp)
   apply (case_tac xs; clarsimp)
  by (simp add: nth_tl)







definition "linorder_on P S \<equiv> totalp_on S P \<and> reflp_on S P \<and> antisymp_on S P \<and> transp_on S P"

lemma linorder_asymp: "linorder_on P S \<Longrightarrow> P x y \<Longrightarrow> P y x \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x = y"
  by (clarsimp simp: linorder_on_def antisymp_on_def)

primrec insort_with :: "('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'c list \<Rightarrow> 'c list" where
  "insort_with f x [] = [x]" |
  "insort_with f x (y#ys) =
  (if f x y then (x#y#ys) else y#(insort_with f x ys))"

definition sort_with :: "('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'c list \<Rightarrow> 'c list" where
  "sort_with f xs = foldr (insort_with f) xs []"


lemma set_insort_simp: "list.set (insort_with P a xs) = insert a (list.set xs)"
  apply (induct xs; clarsimp)
  by (intro set_eqI iffI; clarsimp)

lemma set_sort_with_eq: " list.set (sort_with P xs) = list.set xs" 
  apply (induct xs; clarsimp simp: sort_with_def)
  apply (case_tac "(foldr (insort_with P) xs [])"; clarsimp simp: set_insort_simp)
  apply (intro set_eqI iffI; clarsimp)
  apply (elim disjE; clarsimp?)
    apply blast
  apply blast
  by blast

lemma set_sort_with_eq': " list.set (foldr (insort_with P) xs []) = list.set xs" 
  by (metis set_sort_with_eq sort_with_def)

lemma transp_on_insert: "transp_on (insert a (list.set xs)) P \<Longrightarrow> transp_on (list.set xs) P"
  by (meson subset_insertI transp_on_subset)

lemma reflp_on_insert: "reflp_on (insert a (list.set xs)) P \<Longrightarrow> reflp_on (list.set xs) P"
  apply (rule reflp_onI)
  by (simp add: reflp_onD)

lemma asymp_on_insert: "antisymp_on (insert a (list.set xs)) P \<Longrightarrow> antisymp_on (list.set xs) P"
  apply (rule antisymp_onI)
  by (simp add: antisymp_onD)

lemma totalp_on_insert: "totalp_on (insert a (list.set xs)) P \<Longrightarrow> totalp_on (list.set xs) P"
  apply (rule totalp_onI)
  by (simp add: totalp_onD)

lemma "antisymp_on S P \<Longrightarrow> reflp_on S P \<Longrightarrow> totalp_on S P \<Longrightarrow> a \<in> S \<Longrightarrow> aa \<in>S \<Longrightarrow> \<not> P a aa \<Longrightarrow> P aa a "
  by (metis reflp_onD totalp_onD)

lemma sorted_wrt_insort: "sorted_wrt P xs \<Longrightarrow> transp_on (list.set (x#xs)) P \<Longrightarrow> reflp_on (list.set (x#xs)) P \<Longrightarrow> antisymp_on (list.set (x#xs)) P \<Longrightarrow>
                           totalp_on (list.set (x#xs)) P \<Longrightarrow>  sorted_wrt P (insort_with P x xs)"
  apply (induct xs arbitrary: x; clarsimp)
  apply (intro conjI impI; clarsimp?)
    apply (meson insertCI transp_onD)
   apply (metis insertCI insertE reflp_onD set_insort_simp totalp_onD)
  by (metis List.set_insert asymp_on_insert insert_commute reflp_on_insert totalp_on_insert transp_on_insert)
 


lemma sorted_wrt_sort_with: "transp_on (list.set xs) P \<Longrightarrow> reflp_on (list.set xs) P \<Longrightarrow>
                             antisymp_on (list.set xs) P \<Longrightarrow> totalp_on (list.set xs) P \<Longrightarrow>  sorted_wrt P (sort_with P xs)" 
  apply (induct xs; clarsimp simp: sort_with_def)
  apply (drule meta_mp)
   apply (erule transp_on_insert)
  apply (drule meta_mp)
   apply (erule reflp_on_insert)
  apply (drule meta_mp)
   apply (erule asymp_on_insert)
  apply (drule meta_mp, erule totalp_on_insert)
  apply (case_tac "(foldr (insort_with P) xs [])"; clarsimp simp: set_insort_simp)
  apply (safe)
    apply (case_tac "x=a"; clarsimp?)
  apply (simp add: reflp_onD)
    apply (erule_tac x=x in ballE; clarsimp?)
    apply (rule transp_onD, assumption)
        apply (blast)
       defer
  apply (metis insertCI list.simps(15) set_sort_with_eq')
      apply (blast)
     apply (blast)
    apply (metis insertCI list.set_intros(1) reflp_onD set_sort_with_eq' totalp_on_def)
  apply (metis antisymp_on_subset insert_mono list.simps(15) reflp_on_subset set_sort_with_eq' 
               sorted_wrt_insort subset_insertI totalp_on_subset transp_on_subset)
  by (metis insertI2 list.set_intros(1) set_sort_with_eq')


lemma distinct_insort: "distinct xs \<Longrightarrow> x \<notin> list.set xs \<Longrightarrow>  distinct (insort_with P x xs)"
  apply (induct xs; clarsimp)
  by (simp add: set_insort_simp)

lemma distinct_sort_with: "distinct xs \<Longrightarrow> distinct (sort_with P xs)" 
  apply (induct xs; clarsimp simp: sort_with_def)
  apply (case_tac "(foldr (insort_with P) xs [])"; clarsimp)
  apply (intro conjI impI; clarsimp?)
     apply (metis list.set_intros(1) set_sort_with_eq sort_with_def)
    apply (metis list.set_intros(2) set_sort_with_eq')
   apply (metis insert_iff list.set_intros(1) set_insort_simp set_sort_with_eq')
  by (metis distinct_insort insert_iff list.simps(15) set_sort_with_eq')

lemma length_insort_with[simp]: "length (insort_with P x xs) = Suc (length xs)"
  by (induct xs; clarsimp)

lemma length_sort_worth[simp]: 
 "length (sort_with P xs) = length xs "
  by (induct xs; clarsimp simp: sort_with_def)

lemma sort_with_empty[simp]: "sort_with P [] = []"
  by (clarsimp simp: sort_with_def)

lemma linorder_on_unique_list: "length x = length xs \<Longrightarrow> 
       linorder_on P (list.set xs) \<Longrightarrow> distinct xs \<Longrightarrow> list.set x = list.set xs \<Longrightarrow> distinct x \<Longrightarrow> sorted_wrt P x \<Longrightarrow> sorted_wrt P xs \<Longrightarrow> x = xs"
  apply (induct rule: list_induct2; clarsimp)
  apply (drule meta_mp)
   apply (meson asymp_on_insert linorder_on_def reflp_on_insert totalp_on_insert transp_on_insert)
  apply (case_tac "x = y"; clarsimp?)
   apply (simp add: insert_eq_iff)
  apply (erule notE) back back
  apply (subgoal_tac "P x y \<and> P y x", clarsimp)
      apply (metis insertCI linorder_asymp)
     apply (intro conjI)
   apply (metis insert_iff linorder_on_def reflp_on_def)
  by (metis insert_iff linorder_on_def reflp_onD)


lemma ex1_linorder_list: "linorder_on P S \<Longrightarrow> finite S \<Longrightarrow>  Ex1 (\<lambda>xs. list.set xs = S \<and> distinct xs \<and> sorted_wrt P xs)"
  apply (subgoal_tac "\<exists>xs. list.set xs = S \<and> distinct xs")
   apply (clarsimp)
   apply (rule_tac a="sort_with P xs" in ex1I)
    apply (intro conjI impI; clarsimp?)
      apply (rule set_sort_with_eq distinct_sort_with)+
  apply (assumption)
    apply (rule sorted_wrt_sort_with; clarsimp simp: linorder_on_def)
  using linorder_on_unique_list
   apply (metis distinct_card distinct_sort_with linorder_on_def set_sort_with_eq sorted_wrt_sort_with)
  using finite_distinct_list by blast
   
  

lemma distinct_set_length_eq: "list.set xs = list.set ys \<Longrightarrow> length xs = length ys \<Longrightarrow> distinct xs \<Longrightarrow> distinct ys"
  by (metis card_distinct distinct_card)

lemma only_one_sorted_by_activation_order: 
"xs \<in> sorted_by_activation_order vs aq \<Longrightarrow> ys \<in> sorted_by_activation_order vs aq \<Longrightarrow> distinct aq \<Longrightarrow>  xs = ys "
  apply (clarsimp simp: sorted_by_activation_order_def)
  apply (subgoal_tac "linorder_on (\<lambda>n n'. activation_eligibility_epoch_f (local.var_list_inner vs ! unat n) \<le> activation_eligibility_epoch_f (local.var_list_inner vs ! unat n') \<and> (activation_eligibility_epoch_f (local.var_list_inner vs ! unat n') \<le> activation_eligibility_epoch_f (local.var_list_inner vs ! unat n) \<longrightarrow> n \<le> n'))
                      (list.set aq)")
   apply (subgoal_tac "finite (list.set aq)")
    apply (frule ex1_linorder_list, assumption)
    apply (clarsimp)
    apply (erule_tac x=xs in allE)
    apply (erule_tac x=ys in allE)
    apply (clarsimp)
  apply (subgoal_tac "distinct xs \<and> distinct ys")
     apply blast
    apply (intro conjI)
     apply (rule distinct_set_length_eq, erule sym, clarsimp, clarsimp)
  apply (rule distinct_set_length_eq, erule sym, clarsimp, clarsimp)
   apply (clarsimp)
  apply (clarsimp simp: linorder_on_def)
  apply (intro conjI)
     apply (clarsimp simp: totalp_on_def)
     apply fastforce
    apply (clarsimp simp: reflp_on_def)
   apply (clarsimp simp: antisymp_on_def)
  using transpI_activation_eligibility_leprod transp_on_subset by fastforce


lemma word_of_nat_inj_64:
  assumes bounded: "x < 2 ^ 64" "y < 2 ^ 64"
  assumes of_nats: "of_nat x = (of_nat y :: 64 word)"
  shows "x = y"
  apply (rule word_of_nat_inj[OF _ _ of_nats])
  using bounded
  using len64 apply presburger
using bounded
  using len64 by presburger

lemma distinct_fst_enumerate: "length vs < 2^64 \<Longrightarrow> distinct (map fst (filter P (local.enumerate vs)))"
  apply (rule distinct_map_filter)
  apply (subst distinct_map)
  apply (intro conjI)
   apply (clarsimp simp: enumerate_def)
   apply (rule distinct_zipI1)
  apply (subst distinct_map)
   apply (clarsimp)
   apply (rule inj_onI; clarsimp)
   apply (rule word_of_nat_inj_64; clarsimp)
  apply (rule inj_onI; clarsimp)
  apply (clarsimp simp: enumerate_def in_set_zip_iff)
  apply (drule word_of_nat_inj_64[rotated -1])
  by (clarsimp)+


lemma length_eject_all_validators[simp]:
 "length (local.var_list_inner (eject_all_validators bs vs)) = length (local.var_list_inner vs)"
  apply (clarsimp simp: eject_all_validators_def)
  apply (induct \<open>(local.var_list_inner vs)\<close> arbitrary: vs)
   apply (clarsimp)
  by (metis length_ejecting_eq )

term "updated_inactivity_scores' vs bs pep fc is"


definition "valid_transitions_process_registry_updates vs bs \<equiv> 
           \<forall>(v, s, s')\<in>local.trans (\<lambda>n vs. eject_active_validator bs vs n) (local.enumerate (local.var_list_inner vs)) vs.
             unsafe_var_list_index vs (fst v) = unsafe_var_list_index s (fst v) \<and> unat (fst v) < length (local.var_list_inner s) \<and> exit_queue_epoch (activate_if_eligible v bs s) bs \<le> next_exit_epoch (activate_if_eligible v bs s) bs \<and> next_exit_epoch (activate_if_eligible v bs s) bs \<le> next_exit_epoch (activate_if_eligible v bs s) bs + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config)"


definition "registry_updated_validators bs vs fc \<equiv> let sorted_validators = (SOME xs. xs \<in> sorted_by_activation_order (eject_all_validators bs vs) (map fst (filter (\<lambda>ab. eligible_for_activation (snd ab) fc) (local.enumerate (local.var_list_inner (eject_all_validators bs vs)))))) in
         update_var_list_by (unat ` list.set (take (unat (max (MIN_PER_EPOCH_CHURN_LIMIT config) (word_of_nat (length (active_validator_indices (current_epoch bs) (fold (\<lambda>n vs. eject_active_validator bs vs n) (local.enumerate (local.var_list_inner vs)) vs))) div CHURN_LIMIT_QUOTIENT config))) sorted_validators))
         ((\<lambda>x. unsafe_var_list_index (eject_all_validators bs vs) (word_of_nat x) \<lparr>activation_epoch_f := (current_epoch bs) + 1 +  MAX_SEED_LOOKAHEAD\<rparr>)) (eject_all_validators bs vs)"

lemma "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> current_epoch bs \<noteq> GENESIS_EPOCH \<Longrightarrow>
      hoare_triple (lift (\<lambda>s. previous_epoch (current_epoch bs) \<le> previous_epoch (current_epoch bs) + 1 \<and> Checkpoint.epoch_f fc \<in> previous_epochs bs \<and> length (local.var_list_inner vs) < 2^64 \<and>
                       length (local.var_list_inner is) = length (local.var_list_inner vs) \<and> current_epoch bs + 1 \<le> current_epoch bs + 1 \<and> current_epoch bs + 1 \<le> current_epoch bs + 1 + MAX_SEED_LOOKAHEAD \<and>
                       exit_queue_epoch vs bs \<le> next_exit_epoch vs bs \<and> valid_transitions_process_registry_updates vs bs \<and>
                      ( \<forall>x\<in>list.set (eligible_validator_indices (previous_epoch (current_epoch bs)) (previous_epoch (current_epoch bs) + 1) vs). unsafe_var_list_index is x \<le> unsafe_var_list_index is x + INACTIVITY_SCORE_BIAS config) \<and>
                      
                       (validators \<mapsto>\<^sub>l vs \<and>* finalized_checkpoint \<mapsto>\<^sub>l fc \<and>* beacon_slots \<mapsto>\<^sub>l bs \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep  \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<and>* inactivity_scores \<mapsto>\<^sub>l is \<and>*                       
                       (validators \<mapsto>\<^sub>l registry_updated_validators bs vs fc \<and>* finalized_checkpoint \<mapsto>\<^sub>l fc \<and>* inactivity_scores \<mapsto>\<^sub>l is \<and>*  beacon_slots \<mapsto>\<^sub>l bs \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep  \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<longrightarrow>* P ())) s)) 
         (bindCont process_registry_updates next) Q"
    apply (rule hoare_weaken_pre)
   apply (clarsimp simp: process_registry_updates_def)
  apply (simp only: bindCont_assoc[symmetric])
   apply (rule read_beacon_wp_ex)
   apply (rule mapM_fake)
  apply (rule hoare_case_prod)
  apply (simp only: bindCont_assoc[symmetric])

    apply (rule get_current_epoch_wp_ex)

     apply (rule if_wp)
  apply (simp only: epoch_unsigned_add_def bindCont_assoc[symmetric])

     apply (rule add_wp')
     apply (wp)
      apply (fastforce)
    apply (wp)
     apply (fastforce)
  apply (rule read_beacon_wp_ex)
   apply (rule filter_eligible_wp)
   apply (subst sortBy_cong) defer
    apply (rule sortBy_activation_eligibility_wp)
    apply (rule get_validator_churn_limit_spec')
   apply (rule mapM_fake)
     apply (simp only: bindCont_assoc[symmetric])
     apply (rule var_list_index_lens_wp)
     apply (rule get_current_epoch_wp_ex)
     apply (rule compute_activation_exit_epoch)
  apply (rule read_beacon_wp_ex)
     apply (rule write_beacon_wp')
     apply (fastforce)
    apply (fastforce)
   apply (clarsimp)
  apply (rule_tac x=vs in exI)
   apply (sep_cancel)+
apply (clarsimp simp: mapM_is_sequence_map)
  apply (rule_tac P="\<lambda>x. sep_empty" and
        Q="\<lambda>x. sep_empty" and 
         I="beacon_slots \<mapsto>\<^sub>l bs" and
             S ="\<lambda>vs s.  length (local.var_list_inner vs) < 2^64 \<and> (validators \<mapsto>\<^sub>l vs) s " and g = "\<lambda>ab. undefined ab"  and
                      h="\<lambda>n vs . eject_active_validator bs vs n" and n="vs" and D="\<lambda>x vs' vs''. unsafe_var_list_index vs (fst x) = unsafe_var_list_index vs' (fst x) \<and> unat (fst x) < length (var_list_inner vs') \<and>
                                                                                                                               exit_queue_epoch (activate_if_eligible x bs vs') bs \<le>
                                                                                                                               next_exit_epoch (activate_if_eligible x bs vs') bs \<and>
                                                                                                                               next_exit_epoch (activate_if_eligible x bs vs') bs \<le>
                                                                                                                               next_exit_epoch (activate_if_eligible x bs vs') bs + Epoch (MIN_VALIDATOR_WITHDRAWABILITY_DELAY config)"  in  sequenceI_rewriting4)
     apply (clarsimp)
     apply (rule_tac x=bs in exI)
     apply (intro conjI impI; clarsimp?)
              apply (sep_cancel)+
              apply (sep_select_asm 2, (drule_tac n=a in split_var_list)) back
              apply (rule exI, sep_cancel+)
              apply (rule_tac x=bs in exI)
              apply (intro conjI impI; clarsimp?)
  apply (metis epoch_always_bounded epoch_to_u64.simps less_eq_Epoch_def one_Epoch_def plus_Epoch_def)
               apply (sep_drule spec)
  apply (sep_drule (direct) sep_mp_frame_gen, assumption)
               apply (rule_tac x="VariableList ((local.var_list_inner n)[unat a := b\<lparr>activation_eligibility_epoch_f := Epoch (epoch_to_u64 (current_epoch bs) + 1)\<rparr>])" in exI)
              apply (intro conjI; clarsimp?)

               apply (sep_cancel)+
               apply (clarsimp simp: eject_active_validator_def)
               apply (sep_mp, assumption)
  apply (sep_cancel)+
              apply (clarsimp)
 apply (sep_select_asm 2, (drule_tac n=a in split_var_list)) back
  apply (rule exI, sep_cancel+)

              apply (rule_tac x=bs in exI)
  apply (intro conjI impI; clarsimp?)
              apply (metis epoch_always_bounded epoch_to_u64.simps less_eq_Epoch_def one_Epoch_def plus_Epoch_def)
             apply (rule_tac x=n in exI)
  apply (intro conjI impI; clarsimp?)
 apply (sep_drule spec)
  apply (sep_drule (direct) sep_mp_frame_gen, assumption)
             apply (subst (asm) var_list_update_idemp)
              apply (clarsimp simp: enumerate_def in_set_zip_iff)
              apply (clarsimp simp: unsafe_var_list_index_def unat_of_nat64')
  apply (sep_cancel+)
               apply (clarsimp simp: eject_active_validator_def)

       apply (sep_mp, assumption)
      apply (sep_cancel)+
   apply (clarsimp)
 apply (sep_select_asm 2, (drule_tac n=a in split_var_list)) back
      apply (rule exI, sep_cancel+)
  apply (sep_drule spec)
  apply (sep_drule (direct) sep_mp_frame_gen, assumption)
      apply (clarsimp simp: eject_active_validator_def)
  apply (clarsimp split: if_splits)
      apply (sep_mp, assumption)
           apply (sep_cancel)+
           apply (clarsimp simp: eject_active_validator_def)
 apply (sep_select_asm 2, (drule_tac n=a in split_var_list)) back
           apply (rule exI, sep_cancel+)
apply (sep_drule spec)
           apply (sep_drule (direct) sep_mp_frame_gen, assumption)
           apply (subst (asm) var_list_update_idemp)
apply (clarsimp simp: enumerate_def in_set_zip_iff)
      apply (clarsimp simp: unsafe_var_list_index_def unat_of_nat64')
  apply (clarsimp split: if_splits)
           apply (sep_solve)

    apply (clarsimp simp: split_foldr_map_sep_conj split_foldr_map_conj restore_variablelist local.foldr_pure_empty)
    apply (sep_cancel)+
    apply (clarsimp simp: split_foldr_map_sep_conj split_foldr_map_conj restore_variablelist local.foldr_pure_empty)

    apply (rule exI, sep_cancel+)
    apply (intro conjI impI)
      defer
      defer
      apply (sep_cancel)+
  apply (clarsimp)
  apply (sep_cancel)+
  apply (subst (asm) eject_all_validators_def[symmetric])+
apply (rule_tac P="\<lambda>x. (lens_oocomp (v_list_lens x)) validators \<mapsto>\<^sub>l unsafe_var_list_index (eject_all_validators bs vs) x" and
        Q="\<lambda>x. (lens_oocomp (v_list_lens x)) validators \<mapsto>\<^sub>l (unsafe_var_list_index (eject_all_validators bs vs) x)\<lparr>activation_epoch_f := Epoch (epoch_to_u64 (current_epoch bs) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD)\<rparr>" and 
         I="beacon_slots \<mapsto>\<^sub>l bs" and
             S ="\<lambda>vs s.  sep_empty s " and g = "\<lambda>ab. undefined ab"  and
                      h="\<lambda>n vs . undefined" and n="vs" and D="\<lambda>x vs' vs''. True"  in  sequenceI_rewriting4)
        apply (clarsimp)
        apply (rule exI, sep_cancel+)
        apply (rule_tac x=bs in exI)
        apply (sep_cancel)+
        apply (clarsimp)
        apply (intro conjI impI; clarsimp?)
         apply (clarsimp simp: plus_Epoch_def one_Epoch_def)
        apply (rule exI, sep_cancel+)
        apply (sep_mp, clarsimp)
       apply (clarsimp)
       apply (sep_cancel)+
  apply (sep_drule split_vars_by_list[where l=validators])
        defer
        apply (clarsimp simp: sep_conj_ac)
        apply (sep_cancel)+
        apply (sep_drule spec[where x="\<lambda>x. unsafe_var_list_index (eject_all_validators bs vs) x\<lparr>activation_epoch_f := Epoch (epoch_to_u64 (current_epoch bs) + 1 + epoch_to_u64 MAX_SEED_LOOKAHEAD)\<rparr>"])
        apply (clarsimp simp: sep_conj_ac)

        apply (sep_mp)
defer
       apply (fastforce)
      defer
      apply (intro ext; clarsimp)
     apply (clarsimp simp: image_iff)
     apply (clarsimp simp: enumerate_def in_set_zip_iff length_ejecting_eq)
     defer
      apply (subst length_ejecting_eq, clarsimp)
     apply (rule refl)
    apply (clarsimp simp: registry_updated_validators_def)
    apply (subst (asm) only_one_sorted_by_activation_order[where xs="(SOME x. x \<in> P)" for P], rule someI_ex, fastforce)
      apply (assumption)
  apply (clarsimp)
  apply (rule distinct_fst_enumerate)
     apply (clarsimp)
    apply (clarsimp simp: plus_Epoch_def one_Epoch_def comp_def)
    apply (sep_mp)
  apply (assumption)
   apply (fastforce simp: valid_transitions_process_registry_updates_def)
  apply (rule_tac x=n in bexI)
   apply (clarsimp)
  by (clarsimp)
 

lemma word_of_nat_sum_unat_list[simp]: "word_of_nat (sum_list (map unat xs)) = sum_list xs"
  by (induct xs; clarsimp)

lemma sum_vector_wp[wp]: "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> 
      hoare_triple (lift (\<lambda>s. sum_list (map unat (vector_inner vs) ) < 2 ^ 64 \<and> 
                             (sum_list (map unat (vector_inner vs) ) < 2 ^ 64 \<longrightarrow> 
                               P (word_of_nat (sum_list (map unat (vector_inner vs) ))) s))) 
     (bindCont (sum_vector vs) next) Q"
  apply (clarsimp simp: sum_vector_def) 
  apply (subst safe_sum_def[symmetric])
  apply (rule hoare_weaken_pre, rule sum_list_wp, fastforce)
  by (clarsimp)


lemma enumerate_snd_is[simp]: " (a, b) \<in> list.set (local.enumerate (local.var_list_inner vs))  \<Longrightarrow> 
                               length (var_list_inner vs) < 2^64 \<Longrightarrow> b = unsafe_var_list_index vs a "
  by (clarsimp simp: enumerate_def in_set_zip_iff unsafe_var_list_index_def unat_of_nat64')
 



definition "slashed_balances total_balance adjusted_total_slashing_balance curr_epoch vs bls  \<equiv>
               VariableList (map (\<lambda>x. slash_balance total_balance curr_epoch adjusted_total_slashing_balance (vs[x]!) (bls[x]!)) [0..<length (local.var_list_inner vs)])"

lemma in_enumerate_iff: 
      "length (local.var_list_inner vs) < 2^64 \<Longrightarrow>
       (a, b) \<in> list.set (local.enumerate (local.var_list_inner vs)) \<longleftrightarrow> unat a \<in> {0..<length (local.var_list_inner vs)} \<and> b = unsafe_var_list_index vs a"
  apply (clarsimp simp: enumerate_def in_set_zip_iff)
  apply (intro iffI; clarsimp simp: unat_of_nat64')
   apply (unat_arith; clarsimp simp: unsafe_var_list_index_def unat_of_nat64')
  apply (rule_tac x="unat a" in exI)
  apply (clarsimp)
  by (unat_arith; clarsimp simp: unsafe_var_list_index_def unat_of_nat64')



lemma forM_slashings_helper: 
  "\<And>current_epoch. (\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> 
     hoare_triple (lift (\<lambda>s. current_epoch \<le> current_epoch + Epoch (EPOCHS_PER_SLASHINGS_VECTOR config div 2) \<and>  safe_mul adjusted_total_slashing_balance (EFFECTIVE_BALANCE_INCREMENT config) \<and> 
                     length (var_list_inner vs) < 2^64  \<and> length (var_list_inner bls) = length (var_list_inner vs) \<and>
                     (\<forall>x\<in>{0..<length(var_list_inner vs)}. 
                            Validator.effective_balance_f (vs[x]!) div (EFFECTIVE_BALANCE_INCREMENT config * adjusted_total_slashing_balance) div 
                                                                (total_balance * EFFECTIVE_BALANCE_INCREMENT config) \<le> (bls[x]!)) \<and>
                     EFFECTIVE_BALANCE_INCREMENT config * adjusted_total_slashing_balance \<noteq> 0 \<and>  safe_mul (EFFECTIVE_BALANCE_INCREMENT config) total_balance \<and> total_balance * EFFECTIVE_BALANCE_INCREMENT config \<noteq> 0 \<and>
                   (balances \<mapsto>\<^sub>l bls \<and>* validators \<mapsto>\<^sub>l vs \<and>* (balances \<mapsto>\<^sub>l (slashed_balances total_balance adjusted_total_slashing_balance current_epoch vs bls) \<and>* validators \<mapsto>\<^sub>l vs \<longrightarrow>* P (map (\<lambda>_. ()) (local.enumerate (local.var_list_inner vs))))) s )) 
      (bindCont (forM (enumerate (var_list_inner vs))
     (\<lambda>(index,validator). do {
        vec <- word_unsigned_div (EPOCHS_PER_SLASHINGS_VECTOR config) 2;
        epoch <- epoch_unsigned_add current_epoch (Epoch vec);
        when (slashed_f validator \<and> epoch = withdrawable_epoch_f validator)
            (do { let increment = EFFECTIVE_BALANCE_INCREMENT config;
                   x <- increment .* adjusted_total_slashing_balance;
                   pen_num <- word_unsigned_div (Validator.effective_balance_f validator) x;
                   y <- total_balance .* increment;
                   penalty <- word_unsigned_div pen_num y;
                   decrease_balance index penalty})})) next) Q"
  apply (rule hoare_weaken_pre)
   apply (rule mapM_fake)
  apply (rule hoare_case_prod)
    apply (simp only: bindCont_assoc[symmetric])

    apply (rule div_wp')
    apply (simp only: epoch_unsigned_add_def)
    apply (simp only: bindCont_assoc[symmetric])

    apply (rule add_wp')
    apply (simp only: Let_unfold)
    apply (wp)
    apply (fastforce)+
  apply (clarsimp simp: mapM_is_sequence_map)
  apply (rule_tac P="\<lambda>x s. unat (fst x) < length (local.var_list_inner bls) \<and> (lens_oocomp (v_list_lens (fst x)) balances \<mapsto>\<^sub>l unsafe_var_list_index bls (fst x) \<and>*
                                                                               (lens_oocomp (v_list_lens (fst x)) validators \<mapsto>\<^sub>l unsafe_var_list_index vs (fst x) )) s" and
        Q="\<lambda>x. (lens_oocomp (v_list_lens (fst x)) balances \<mapsto>\<^sub>l slash_balance total_balance current_epoch adjusted_total_slashing_balance  (unsafe_var_list_index vs (fst x))  (unsafe_var_list_index bls (fst x)) \<and>*
               (lens_oocomp (v_list_lens (fst x)) validators \<mapsto>\<^sub>l unsafe_var_list_index vs (fst x) ) )" and 
         I="\<lambda>s. sep_empty s" and g = "\<lambda>_. ()" and
             S ="\<lambda>bs. sep_empty " and 
                      h="\<lambda>n bls. undefined" and n="undefined" and D="\<lambda>x bls bls'. True"  in  sequenceI_rewriting4)
    apply (clarsimp)
    apply (intro conjI impI; clarsimp?)
       apply (metis epoch_to_u64.simps less_eq_Epoch_def plus_Epoch_def)
      apply (rule exI)
      apply (intro conjI impI)
       defer
       apply (sep_cancel)+
       apply (clarsimp simp: slash_balance_def)
       apply (sep_mp)
       apply (subgoal_tac "(unsafe_var_list_index vs a) = b", clarsimp)
        apply (sep_mp, assumption)
       apply (rule sym, erule enumerate_snd_is, clarsimp)
      apply (metis epoch_to_u64.simps less_eq_Epoch_def plus_Epoch_def)
     apply (clarsimp simp: slash_balance_def split: if_splits)
      apply (subgoal_tac "(unsafe_var_list_index vs a) = b", clarsimp)
       apply (rule sym, erule enumerate_snd_is, clarsimp)
     apply (sep_mp, assumption)
  apply (clarsimp)
    apply (clarsimp simp: split_foldr_map_sep_conj split_foldr_map_conj restore_variablelist local.foldr_pure_empty)
    apply (intro conjI impI, clarsimp simp: enumerate_def)
  apply (clarsimp simp: enumerate_def in_set_zip_iff unsafe_var_list_index_def unat_of_nat64')

    apply (sep_cancel)+
    apply (clarsimp simp: slash_balance_restore)
    apply (clarsimp simp: slashed_balances_def)
    apply (sep_mp)
    apply (clarsimp)
   apply (fastforce)
  apply (clarsimp simp: in_enumerate_iff index_var_list_def unat_of_nat64')
  by (erule_tac x="unat a" in ballE; clarsimp simp: unat_of_nat64')
 

lemma active_validator_indice_is_valid[simp]:
      " length (var_list_inner vs) < 2^64 \<Longrightarrow> 
        \<forall>x\<in>list.set (active_validator_indices (current_epoch bs) vs). x < var_list_len vs"
  apply (clarsimp simp: active_validator_indices_def in_enumerate_iff)
  apply (unat_arith)
  apply (clarsimp simp: unat_of_nat64')
  by (cases vs; clarsimp simp: unat_of_nat64')


lemma sum_arb_effective_balance: 
      "xs \<in> lists_of (list.set (active_validator_indices epoch vs)) \<Longrightarrow>
       (\<Sum>a\<leftarrow>(arb_active_validator_indices epoch vs). Validator.effective_balance_f (unsafe_var_list_index vs a)) = 
       (\<Sum>a\<leftarrow>xs. Validator.effective_balance_f (unsafe_var_list_index vs a))"
  apply (rule sum_lists_of_eq)
   apply (rule arb_active_is_lists_of)
  by (assumption)
  

definition "total_balance vs epoch \<equiv> (max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>(arb_active_validator_indices epoch vs). Validator.effective_balance_f (unsafe_var_list_index vs a)))"
definition "adjusted_total_slashing_balance sls balance \<equiv> min (word_of_nat (sum_list (map unat (local.vector_inner sls))) * PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX) balance"


lemma "(\<And>x. hoare_triple (lift (P x)) (next x) Q) \<Longrightarrow> current_epoch bs \<noteq> GENESIS_EPOCH \<Longrightarrow>
      hoare_triple (lift (\<lambda>s. previous_epoch (current_epoch bs) \<le> previous_epoch (current_epoch bs) + 1 \<and> Checkpoint.epoch_f fc \<in> previous_epochs bs \<and> length (local.var_list_inner vs) < 2^64 \<and>
                       length (local.var_list_inner bls) = length (local.var_list_inner vs) \<and> current_epoch bs + 1 \<le> current_epoch bs + 1 + MAX_SEED_LOOKAHEAD \<and>
                        current_epoch bs \<le> current_epoch bs + Epoch (EPOCHS_PER_SLASHINGS_VECTOR config div 2) \<and>
                        safe_mul (min (word_of_nat (sum_list (map unat (local.vector_inner sls))) * PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX) (max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>arb_active_validator_indices (current_epoch bs) vs. Validator.effective_balance_f (unsafe_var_list_index vs a)))) (EFFECTIVE_BALANCE_INCREMENT config) \<and>
                        sum_list (map unat (local.vector_inner sls)) < 2^64 \<and>  safe_mul PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX (word_of_nat (sum_list (map unat (local.vector_inner sls)))) \<and>
                         max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>arb_active_validator_indices (current_epoch bs) vs. Validator.effective_balance_f (unsafe_var_list_index vs a)) * EFFECTIVE_BALANCE_INCREMENT config \<noteq> 0 \<and>
                        safe_mul (EFFECTIVE_BALANCE_INCREMENT config) (max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>arb_active_validator_indices (current_epoch bs) vs. Validator.effective_balance_f (unsafe_var_list_index vs a))) \<and>
                        EFFECTIVE_BALANCE_INCREMENT config * min (word_of_nat (sum_list (map unat (local.vector_inner sls))) * PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX) (max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>arb_active_validator_indices (current_epoch bs) vs. Validator.effective_balance_f (unsafe_var_list_index vs a))) \<noteq> 0 \<and>
                        (\<forall>x\<in>(word_of_nat `{0..<length (var_list_inner vs)}).
                              Validator.effective_balance_f (unsafe_var_list_index vs x) div (EFFECTIVE_BALANCE_INCREMENT config * min (word_of_nat (sum_list (map unat (local.vector_inner sls))) * PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX) (max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>arb_active_validator_indices (current_epoch bs) vs. Validator.effective_balance_f (unsafe_var_list_index vs a)))) div
                               (max (EFFECTIVE_BALANCE_INCREMENT config) (\<Sum>a\<leftarrow>arb_active_validator_indices (current_epoch bs) vs. Validator.effective_balance_f (unsafe_var_list_index vs a)) * EFFECTIVE_BALANCE_INCREMENT config) \<le> unsafe_var_list_index bls x) \<and>
                      ( \<forall>x\<in>list.set (eligible_validator_indices (previous_epoch (current_epoch bs)) (previous_epoch (current_epoch bs) + 1) vs). unsafe_var_list_index is x \<le> unsafe_var_list_index is x + INACTIVITY_SCORE_BIAS config) \<and>
                      
                       (balances \<mapsto>\<^sub>l bls \<and>* slashings \<mapsto>\<^sub>l sls \<and>* validators \<mapsto>\<^sub>l vs \<and>* finalized_checkpoint \<mapsto>\<^sub>l fc \<and>* beacon_slots \<mapsto>\<^sub>l bs \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep  \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<and>* inactivity_scores \<mapsto>\<^sub>l is \<and>*                       
                       (balances \<mapsto>\<^sub>l slashed_balances (total_balance vs (current_epoch bs)) (adjusted_total_slashing_balance sls (total_balance vs (current_epoch bs))) (current_epoch bs)  vs bls \<and>* slashings \<mapsto>\<^sub>l sls \<and>* validators \<mapsto>\<^sub>l vs \<and>* finalized_checkpoint \<mapsto>\<^sub>l fc \<and>* inactivity_scores \<mapsto>\<^sub>l  is \<and>*  beacon_slots \<mapsto>\<^sub>l bs \<and>* previous_epoch_participation \<mapsto>\<^sub>l pep  \<and>* current_epoch_participation \<mapsto>\<^sub>l cep \<longrightarrow>* P ())) s)) 
         (bindCont process_slashings next) Q"
  apply (unfold process_slashings_def)
  apply (rule hoare_weaken_pre)
  apply (clarsimp simp: bindCont_assoc[symmetric])
   apply (rule get_current_epoch_wp')
   apply (rule get_total_active_balance_wp)
   apply (rule read_beacon_wp_ex)
   apply (rule sum_vector_wp)
   apply (rule mul_wp')
   apply (rule read_beacon_wp_ex)
   apply (rule forM_slashings_helper)
   apply (fastforce)
  apply (clarsimp)
  apply (sep_cancel)+
  apply (intro conjI impI; clarsimp)
  apply (rule exI, sep_cancel+)
  apply (clarsimp)
  apply (intro exI, sep_cancel+)
  apply (intro conjI impI; clarsimp simp: sum_arb_effective_balance)
       apply (fastforce)
      apply (erule_tac x=x in ballE)
  apply (clarsimp simp: index_var_list_def sum_arb_effective_balance)
      apply (fastforce)
         apply (sep_cancel)+
         apply (clarsimp simp: sep_conj_ac)
         apply (sep_mp)
         apply (clarsimp simp: total_balance_def adjusted_total_slashing_balance_def sum_arb_effective_balance)
  by (sep_mp, assumption)


(* process_justification_and_finalization;
    _ \<leftarrow> process_inactivity_updates;
    _ \<leftarrow> process_rewards_and_penalties;
    _ \<leftarrow> process_registry_updates;
    _ \<leftarrow> process_slashings;*)



end
end