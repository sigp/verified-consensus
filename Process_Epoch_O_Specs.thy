theory Process_Epoch_O_Specs
imports ProcessEpoch_O
begin

locale extended_hl_pre =  extended_vc  + hoare_logic
begin

declare [[show_sorts=false]]
declare [[show_types=false]]

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
     apply (erule lift_mono, clarsimp, sep_solve)
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

lemma sub_wp[wp]: "hoare_triple (lift (P (n - m))) (c (n - m)) Q \<Longrightarrow>
  hoare_triple (lift (\<lambda>s. n \<ge>  m \<and> (n \<ge>  m \<longrightarrow> P (n - m) s))) 
(do {x <- (n .- m); c x}) Q"
  apply (rule hoare_weaken_pre)
   apply (clarsimp simp:  word_unsigned_sub_def )
   apply (simp only: Let_unfold)
   apply (wp, clarsimp simp: bindCont_return')
  apply (safe)
  apply (simp add: word_sub_le_iff)
  apply (erule notE)
  apply (clarsimp simp: lift_def)
  using word_sub_le_iff by blast


lemma get_current_epoch_wp[wp]: "hoare_triple (lift (P (slot_to_epoch config v))) (f (slot_to_epoch config v)) Q \<Longrightarrow>
hoare_triple (lift (maps_to beacon_slots v \<and>* (maps_to beacon_slots v \<longrightarrow>* P (slot_to_epoch config v)))) (bindCont get_current_epoch f) Q"
  apply (clarsimp simp: get_current_epoch_def)
  apply (rule hoare_weaken_pre)
  apply (clarsimp simp: bindCont_assoc[symmetric] bindCont_return')
   apply (rule read_beacon_wp, fastforce)
  apply (rule order_refl)
  done

lemma if_wp[wp]: 
  "(B \<Longrightarrow> hoare_triple  ( lift S) ( bindCont P c) R) \<Longrightarrow> (\<not>B \<Longrightarrow> hoare_triple ( lift S') (bindCont Q c) R) \<Longrightarrow>
   hoare_triple ( lift (if B then S else S'))  (do {x <- (if B then P else Q); c x}) R"
  apply (clarsimp split: if_splits)
  done

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

definition "previous_epoch epoch \<equiv> 
    if epoch = GENESIS_EPOCH then GENESIS_EPOCH else Epoch (epoch_to_u64 epoch - 1)"


lemma previous_genesis[simp]: "previous_epoch GENESIS_EPOCH = GENESIS_EPOCH"
  by (clarsimp simp: previous_epoch_def)

lemma previous_is_self_simp[simp]: "previous_epoch e = e \<longleftrightarrow> e = GENESIS_EPOCH"
  apply (clarsimp simp: previous_epoch_def GENESIS_EPOCH_def) 
  by (metis diff_0_right diff_left_imp_eq epoch_to_u64.simps zero_neq_one)

declare lift_mono[elim!]

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




lemma add_zero_simp:"(bindCont ((a :: u64) .+ (0 :: u64)) f) = f a" sorry


lemma unsigned_add_commute[intro]:" word_unsigned_add b a = a .+ b "
  apply (rule ext; clarsimp simp: Let_unfold word_unsigned_add_def)
  apply (safe; clarsimp simp: add.commute)
  using olen_add_eqv apply auto[1]
  using olen_add_eqv apply auto[1]
  done



lemma unsigned_word_add_shuffle:" bindCont (word_unsigned_add a  n) (\<lambda>y. bindCont (b .+ y) f) = bindCont (b .+ n) (\<lambda>y. bindCont ( a .+ y) f) "
  apply (clarsimp simp: word_unsigned_add_def Let_unfold, safe; (clarsimp simp: bindCont_return' bindCont_return split: if_splits)?)
      apply (simp add: add.left_commute)
  using olen_add_eqv word_random apply blast
  using olen_add_eqv word_random apply blast
   apply (metis add.left_commute le_no_overflow)
  by (simp add: add.left_commute le_no_overflow)


lemma foldrM_elems_cons: "foldrM word_unsigned_add ([a,b]) n = foldrM word_unsigned_add ([b,a]) n"
  apply (clarsimp simp: foldrM_cons)
  using unsigned_word_add_shuffle 
  by (metis bindCont_assoc bindCont_return)




lemma word_unsigned_add_shuffle2: "bindCont (word_unsigned_add x y) (\<lambda>x. x .+ z) = bindCont (x .+ z) (\<lambda>x. x .+ y)"
  apply (clarsimp simp: word_unsigned_add_def Let_unfold, safe; (clarsimp simp: bindCont_return' bindCont_return split: if_splits)?)
      apply (simp add: add.commute add.left_commute)
  apply (smt (verit, ccfv_threshold) no_olen_add word_le_def)
    apply (metis (no_types, lifting) add.commute olen_add_eqv word_random)
   apply (metis add.assoc add.commute olen_add_eqv word_plus_mono_right)
  by (metis (no_types, opaque_lifting) add.commute group_cancel.add2 nle_le olen_add_eqv word_add_increasing word_plus_mcs_4')

  

lemma foldrM_shift: "foldrM word_unsigned_add (a#xs) n = (do {x <- foldrM word_unsigned_add (xs) n; word_unsigned_add x a})   "
  apply (induct xs arbitrary: n a; clarsimp?)
   apply (clarsimp simp: foldrM_def bindCont_return' k_comp_def bindCont_return)
   apply (rule unsigned_add_commute)
  apply (clarsimp simp: foldrM_cons)
  apply (clarsimp simp: bindCont_assoc)
  apply (subst bindCont_assoc[symmetric])
  apply (subst bindCont_assoc[symmetric])
  apply (rule bindCont_right_eqI)
  apply (rule word_unsigned_add_shuffle2)
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
  apply (clarsimp simp: lift_def)
  apply (clarsimp simp: bindCont_return)
  apply (rule hoare_weaken_pre, assumption)
  apply (clarsimp)
  done




definition "lists_of S \<equiv> {xs. distinct xs \<and> list.set xs = S}"

lemma maps_to_is_valid:"(maps_to l v \<and>* R) s \<Longrightarrow> valid (l) (Some v)"
  apply (clarsimp simp: sep_conj_def maps_to_def )
  sorry

lemma valid_validator_some_simp[simp]: 
"valid validators (Some xs) = (let ys = Invariants.var_list_inner xs in sum_list (map (unat o effective_balance_f) ys) < 2^(64) \<and> distinct ys \<and> length ys < 2^64 )"
  apply (clarsimp simp: validators_def)
  sorry
  

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
   apply (subst sum_list_map_remove1[where x=a]) back
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


lemma get_total_balance_wp[wp]:"(\<And>x xs (v :: Validator VariableList). distinct xs \<Longrightarrow> list.set xs = S \<Longrightarrow> x = max (EFFECTIVE_BALANCE_INCREMENT config) (sum_list (map (effective_balance_f \<circ> unsafe_var_list_index v) xs)) \<Longrightarrow>
    hoare_triple (lift (P x)) (f x) Q) 
  \<Longrightarrow> hoare_triple (lift ((maps_to validators v \<and>* (maps_to validators v \<longrightarrow>* (\<lambda>s. (\<forall>x\<in>S. x < var_list_len v) \<and>  ((\<forall>x\<in>S. x < var_list_len v) \<longrightarrow> (\<forall>xs\<in>lists_of S. P (max (EFFECTIVE_BALANCE_INCREMENT config) (sum_list (map (effective_balance_f \<circ> unsafe_var_list_index v) xs))) s)  )))) ))
   (do {b <- get_total_balance S; f b}) Q"
  apply (clarsimp simp: get_total_balance_def, rule hoare_weaken_pre)
   apply (wp)
   apply (clarsimp)
   apply (atomize)
   apply (erule_tac allE)
   apply (erule_tac x=aa in allE)
  apply (erule_tac x=a in allE)
   apply (fastforce)
  apply (clarsimp)
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

lemma lift_option_wp[wp]: "(\<And>x. v = Some x \<Longrightarrow> hoare_triple (lift (P x)) (f x) Q) \<Longrightarrow> 
  hoare_triple (lift (\<lambda>s. v \<noteq> None \<and> (v \<noteq> None \<longrightarrow> P (the v) s))) (do {b <- lift_option v; f b}) Q"
  apply (unfold lift_option_def)
  apply (rule hoare_assert_stateI, clarsimp)
  apply (intro conjI impI)
   apply (clarsimp simp: lift_def)
  apply (clarsimp simp: lift_def)
  apply (rule hoare_weaken_pre, assumption)
  apply (clarsimp)
  apply (clarsimp simp: lift_def)
  apply (blast)
  done

lemma getState_wp_spec[wp]: " (\<And>s. hoare_triple (P s) (c s) Q) \<Longrightarrow> 
  hoare_triple (\<lambda>x. P x x) (bindCont getState c) Q"
  apply (clarsimp simp: getState_def hoare_triple_def bindCont_def run_def Sup_le_iff assert_galois_test test_restricts_Nondet)
  apply (atomize)
  apply (erule_tac x=a in allE)
  apply (erule_tac x=b in allE)
  apply (erule order_trans[rotated])
  using seq_mono_left test.hom_mono by force

lemma getState_wp_alt: "(\<And>s. P s \<Longrightarrow> hoare_triple ((=) s) (c s) Q) \<Longrightarrow> 
  hoare_triple P (bindCont getState c) Q "
  by (clarsimp simp: getState_def hoare_triple_def bindCont_def run_def Sup_le_iff assert_galois_test test_restricts_Nondet)


lemma hoare_subgoalI: "(\<And>s. P \<Longrightarrow> hoare_triple P' f Q) \<Longrightarrow> hoare_triple (\<lambda>s. P  \<and> (P  \<longrightarrow> P' s)) f Q"
  apply (rule hoare_assert_stateI)
  apply (rule hoare_weaken_pre)
   apply (clarsimp)
   apply (assumption)
  apply (clarsimp)
  done

lemma [simp]: "((\<lambda>a. the (u64_of a)) \<circ> u64) = id "
  by (intro ext; clarsimp)

text \<open>lemma translate_ProgressiveBalancesCacheI:"(extended_vc.maps_to current_epoch_flag_attesting_balances (list (map u64 (current_epoch_flag_attesting_balances_f pbc))) \<and>*
        extended_vc.maps_to previous_epoch_flag_attesting_balances (list (map u64 (previous_epoch_flag_attesting_balances_f pbc))) \<and>*
        extended_vc.maps_to total_active_balance (u64 (total_active_balance_f pbc)) \<and>*
        extended_vc.maps_to progressive_balances_cache (list [ptr total_active_balance, ptr previous_epoch_flag_attesting_balances, ptr current_epoch_flag_attesting_balances])) s \<Longrightarrow> translate_ProgressiveBalancesCache progressive_balances_cache pbc s"
  apply (clarsimp simp: translate_ProgressiveBalancesCache_def)
  apply (intro exI)
  apply (sep_solve)
  done
\<close>
lemma [simp]: "ProgressiveBalancesCache.fields (total_active_balance_f pbc) (previous_epoch_flag_attesting_balances_f pbc) (current_epoch_flag_attesting_balances_f pbc) = pbc"
  by (clarsimp simp: ProgressiveBalancesCache.defs)

text \<open>lemma read_ProgressiveBalancesCache_wp[wp]:"hoare_triple (P pbc) (f pbc) Q \<Longrightarrow> 
hoare_triple (translate_ProgressiveBalancesCache progressive_balances_cache pbc \<and>* (translate_ProgressiveBalancesCache progressive_balances_cache pbc \<longrightarrow>* P (pbc)))  
  (do {b <- read_ProgressiveBalancesCache progressive_balances_cache; f b}) Q" 
  apply (rule hoare_assert_stateI)
  apply (subst (asm) translate_ProgressiveBalancesCache_def)
  apply (clarsimp simp: sep_conj_exists1)
  find_theorems "((\<lambda>s. \<exists>x. ?f x s) \<and>* ?R)" 
  apply (rule hoare_weaken_pre, unfold read_ProgressiveBalancesCache_def, wp)
     apply (rule_tac v=xb and x="(map u64 (previous_epoch_flag_attesting_balances_f pbc))" in  hoare_eqI)
   apply (simp)
   apply (wp)

   apply (rule mapM_wp[where g="the o u64_of"])
     apply (simp only: comp_def)
     apply (rule_tac v="(u64_of xc)" in lift_option_wp)
     apply (clarsimp)
     apply (assumption)
  apply (clarsimp)
     apply (erule hoare_eqI)
    apply (wp)
     apply (rule_tac v=xc and x="(map u64 (current_epoch_flag_attesting_balances_f pbc))" in  hoare_eqI)

   apply (rule mapM_wp[where g="the o u64_of"])
     apply (simp only: comp_def)

      apply (rule_tac v="(u64_of xd)" in lift_option_wp)
    apply (clarsimp)
  apply (assumption)
    apply (clarsimp)
   apply (clarsimp)
     apply (erule hoare_eqI)

    apply (clarsimp)
    apply (safe)
    apply (sep_cancel)+
    apply (clarsimp)
    apply (sep_cancel)+
  apply (clarsimp)
  apply (intro conjI impI; clarsimp?)

    apply (sep_cancel)+
    apply clarsimp
   apply (intro conjI impI)
    apply (sep_drule translate_ProgressiveBalancesCacheI, assumption)
   apply (sep_drule translate_ProgressiveBalancesCacheI, assumption)
    apply (sep_cancel)+

  apply (intro conjI impI)
      apply (sep_drule translate_ProgressiveBalancesCacheI, assumption)
      apply (sep_drule translate_ProgressiveBalancesCacheI, assumption)
  apply (clarsimp)
  done

  \<close>
lemma process_fast_spec: "hoare_triple (lift (maps_to beacon_slots b \<and>* maps_to progressive_balances_cache pbc \<and>* R)) process_justification_and_finalization_fast
   (lift (maps_to beacon_slots b \<and>* maps_to progressive_balances_cache pbc \<and>* R))"
  apply (unfold process_justification_and_finalization_fast_def, rule hoare_weaken_pre, wp)
   apply (simp only: gen_epoch_add_zero)
   apply (wp)
   apply (clarsimp)
   apply (wp)
  apply (safe)
  apply (sep_cancel)+
  apply (clarsimp)
  apply (sep_cancel)+
  done

lemma active_validator_indices_are_bound: "x \<in> list.set (active_validator_indices e v) \<Longrightarrow> length (local.var_list_inner v) \<le> 2 ^ 64 - 1 \<Longrightarrow> x < var_list_len v"
  apply (clarsimp simp: active_validator_indices_def)
  apply (erule bounded_enumerate)
  apply (clarsimp)
  done

lemma [simp]: "Epoch x \<le> Epoch y \<longleftrightarrow> x \<le> y"
  by (safe; clarsimp simp: less_eq_Epoch_def)

lemma [simp]: "epoch_to_u64 GENESIS_EPOCH = 0"
  by (clarsimp simp: GENESIS_EPOCH_def)

lemma "hoare_triple (lift (maps_to beacon_slots b \<and>* maps_to previous_epoch_participation pep \<and>*
   maps_to current_epoch_participation cep \<and>*  maps_to validators v \<and>*  R \<and>* R')) process_justification_and_finalization (lift (maps_to beacon_slots b \<and>* maps_to validators v \<and>*  maps_to previous_epoch_participation pep \<and>* maps_to current_epoch_participation cep \<and>* R \<and>* R'))"
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

end
end